import { test, expect, beforeAll, afterAll, spyOn } from 'bun:test'
// Every case here runs a proxy configured to terminate TLS, so each is
// skipped where this runtime cannot terminate it in-process.
import { describeWithTls as describe } from '../helpers/emitted-connections.js'
import { connect, createServer, type AddressInfo, type Server } from 'node:net'
import type { LookupFunction, Socket } from 'node:net'
import {
  connect as tlsConnect,
  createServer as createTlsServer,
} from 'node:tls'
import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import {
  createHttpProxyServer,
  type HttpProxyServerOptions,
} from '../../src/sandbox/http-proxy.js'
import { createMitmCA } from '../../src/sandbox/mitm-ca.js'
import { mintLeafCert } from '../../src/sandbox/mitm-leaf.js'
import {
  readRequestTarget,
  type RequestInfo,
} from '../../src/sandbox/request-filter.js'
import { SentinelRegistry } from '../../src/sandbox/credential-sentinel.js'
import {
  AwsPairRegistry,
  createSigv4Planner,
} from '../../src/sandbox/credential-aws-pairs.js'
import { signSigv4, UNSIGNED_PAYLOAD } from '../../src/sandbox/aws-sigv4.js'
import { SandboxManager } from '../../src/sandbox/sandbox-manager.js'

const FIXTURE_DIR = join(import.meta.dir, '..', 'fixtures', 'tls-terminate')
const CA_CERT = join(FIXTURE_DIR, 'ca.crt')
const CA_KEY = join(FIXTURE_DIR, 'ca.key')
const CA_PEM = readFileSync(CA_CERT, 'utf8')

const UPSTREAM_NAME = 'upstream.test'

/** Request target as the client writes it, and as it must reach upstream. */
type Case = [sent: string, forwarded: string]

// TLS-terminated, no filterRequest: origin-form targets go out untouched.
const TLS_UNCHANGED: Case[] = [
  ['/a/../b', '/a/../b'],
  ['/a/./b/%2e%2e/c', '/a/./b/%2e%2e/c'],
  ['/a/%2E%2E/b', '/a/%2E%2E/b'],
  ['//k/x', '//k/x'],
  ['/a?', '/a?'],
  ['/a\\b', '/a\\b'],
  ['/a;p=1/b;q?x=1', '/a;p=1/b;q?x=1'],
  ['/a#frag', '/a#frag'],
]

// Plain HTTP, no filterRequest: the path and query of the parsed absolute
// URI, with a leading `//` kept.
const PLAIN_UNCHANGED: Case[] = [
  ['/a/../b', '/b'],
  ['/a/%2e%2e/b', '/b'],
  ['//k/x', '//k/x'],
  ['/a?', '/a'],
  ['/a\\b', '/a/b'],
  ['/a;p=1/b;q?x=1', '/a;p=1/b;q?x=1'],
]

// With filterRequest. Ambiguous: as spelled, and normalized.
const AMBIGUOUS: Case[] = [
  ['/a/../b', '/b'],
  ['/a/./b', '/a/b'],
  ['/a/..', '/'],
  ['/a/.', '/a/'],
  ['/a/%2e%2e/b', '/b'],
  ['/a/.%2E/b', '/b'],
  ['/a/%2e/b', '/a/b'],
  ['/a;/../b', '/b'],
  ['/a//../b', '/a/b'],
  ['//k/x', '/k/x'],
  ['///k?q=1', '/k?q=1'],
  ['/a\\b', '/a/b'],
  ['/\\k', '/k'],
  ['/a#frag', '/a'],
  ['/a?x#frag', '/a?x'],
]

// Not ambiguous: normalizing leaves them alone, or only escapes a character
// or drops an empty query.
const UNAMBIGUOUS = [
  '/',
  '/a/b/?x=1',
  '/a//b',
  '/a/b//',
  '/a%2Fb',
  '/a%2f..%2fb',
  '/a/..%2fb',
  '/a/%252e%252e/b',
  '/a/...',
  '/a/..b',
  '/a/.hidden',
  '/a/..;/b',
  '/a;p=1/b;q?x=1',
  '/a?x=../y&z=//&w=\\',
  '/%61%7e',
  '/a%zz',
  '/a?',
  '/a??',
  '/a{b}|c^d"e<f>g`h',
  `/a?q='x'&r="y"`,
]

const lookup = ((_hostname, options, callback) => {
  const all = typeof options === 'object' && options.all
  if (all) callback(null, [{ address: '127.0.0.1', family: 4 }])
  else callback(null, '127.0.0.1', 4)
}) as LookupFunction

/** Records the request target of every request head, off the wire. */
function recordTargets(
  seen: string[],
  heads: string[] = [],
): (socket: Socket) => void {
  return socket => {
    let buf = ''
    socket.on('error', () => {})
    socket.on('data', chunk => {
      buf += chunk.toString('latin1')
      for (let end; (end = buf.indexOf('\r\n\r\n')) >= 0; ) {
        seen.push(buf.slice(0, buf.indexOf('\r\n')).split(' ')[1]!)
        heads.push(buf.slice(0, end))
        buf = buf.slice(end + 4)
        socket.write('HTTP/1.1 200 OK\r\ncontent-length: 0\r\n\r\n')
      }
    })
  }
}

type Reply = { status: number; text: string }

/** Writes one request head and resolves with the reply, read to its end. */
function exchange(socket: Socket, head: string): Promise<Reply> {
  return new Promise((resolve, reject) => {
    let buf = ''
    socket.on('data', chunk => {
      buf += chunk.toString('latin1')
      if (!buf.includes('\r\n\r\n')) return
      if (
        /^transfer-encoding: chunked/im.test(buf) &&
        !/\r\n0\r\n\r\n$/.test(buf)
      )
        return
      socket.destroy()
      resolve({
        status: Number(/^HTTP\/1\.1 (\d+)/.exec(buf)?.[1] ?? 0),
        text: buf,
      })
    })
    socket.once('error', reject)
    socket.once('close', () => reject(new Error('closed before a reply')))
    socket.write(Buffer.from(head, 'latin1'))
  })
}

describe('request target forwarding', () => {
  const ca = createMitmCA({ caCertPath: CA_CERT, caKeyPath: CA_KEY })
  const tlsSeen: string[] = []
  const tlsHeads: string[] = []
  const plainSeen: string[] = []
  const hookSeen: { url: string; info?: RequestInfo }[] = []
  const denied: { method: string; url: string; reason: string }[] = []
  const servers: Server[] = []
  let tlsPort: number
  let plainPort: number
  let noHookPort: number
  /** A proxy with an allow-all hook, by its ambiguousRequestTarget. */
  const hookPort = { default: 0, refuse: 0, asSpelled: 0, normalize: 0 }
  let base: HttpProxyServerOptions

  async function listen(server: Server): Promise<number> {
    servers.push(server)
    await new Promise<void>(r => server.listen(0, '127.0.0.1', () => r()))
    return (server.address() as AddressInfo).port
  }

  beforeAll(async () => {
    const leaf = mintLeafCert(ca, UPSTREAM_NAME)
    const cert = leaf.certPem.match(
      /-----BEGIN CERTIFICATE-----[\s\S]*?-----END CERTIFICATE-----\r?\n?/,
    )![0]
    tlsPort = await listen(
      createTlsServer(
        { cert, key: leaf.keyPem },
        recordTargets(tlsSeen, tlsHeads),
      ),
    )
    plainPort = await listen(createServer(recordTargets(plainSeen)))
    base = {
      filter: () => true,
      mitmCA: ca,
      tlsTerminateUpstreamCA: CA_PEM,
      lookupFor: () => lookup,
    }
    noHookPort = await listen(createHttpProxyServer(base))
    for (const mode of [
      'default',
      'refuse',
      'asSpelled',
      'normalize',
    ] as const) {
      hookPort[mode] = await listen(
        createHttpProxyServer({
          ...base,
          ambiguousRequestTarget: mode === 'default' ? undefined : mode,
          filterRequest: async (request, info) => {
            hookSeen.push({ url: request.url, info })
            return { action: 'allow' }
          },
        }),
      )
    }
  })

  afterAll(async () => {
    for (const s of servers) {
      await new Promise<void>(r => s.close(() => r()))
    }
  })

  type Sent = Reply & { forwarded: string | undefined }

  /** A fresh TLS-terminated tunnel to the upstream. */
  async function tunnel(proxyPort: number): Promise<Socket> {
    const authority = `${UPSTREAM_NAME}:${tlsPort}`
    const raw = await new Promise<Socket>((resolve, reject) => {
      const socket = connect(proxyPort, '127.0.0.1', () => {
        socket.write(
          `CONNECT ${authority} HTTP/1.1\r\nHost: ${authority}\r\n\r\n`,
        )
      })
      socket.once('error', reject)
      socket.once('data', () => resolve(socket))
    })
    return new Promise<Socket>((resolve, reject) => {
      const t = tlsConnect(
        { socket: raw, ca: CA_PEM, servername: UPSTREAM_NAME },
        () => resolve(t),
      )
      t.once('error', reject)
    })
  }

  /** One request over a fresh tunnel, and the target upstream saw. */
  async function sendTls(
    proxyPort: number,
    target: string,
    headers: string[] = [],
  ): Promise<Sent> {
    const authority = `${UPSTREAM_NAME}:${tlsPort}`
    const tls = await tunnel(proxyPort)
    const before = tlsSeen.length
    const lines = [`GET ${target} HTTP/1.1`, `Host: ${authority}`, ...headers]
    const reply = await exchange(tls, lines.join('\r\n') + '\r\n\r\n')
    expect(tlsSeen.length - before).toBe(reply.status === 200 ? 1 : 0)
    return { ...reply, forwarded: tlsSeen[before] }
  }

  /** One absolute-form GET through the proxy, and the target upstream saw. */
  async function sendPlain(proxyPort: number, target: string): Promise<Sent> {
    const authority = `127.0.0.1:${plainPort}`
    const before = plainSeen.length
    const head = `GET http://${authority}${target} HTTP/1.1\r\nHost: ${authority}\r\n\r\n`
    const socket = await new Promise<Socket>((resolve, reject) => {
      const s = connect(proxyPort, '127.0.0.1', () => resolve(s))
      s.once('error', reject)
    })
    const reply = await exchange(socket, head)
    expect(plainSeen.length - before).toBe(reply.status === 200 ? 1 : 0)
    return { ...reply, forwarded: plainSeen[before] }
  }

  const LEGS = [
    ['TLS-terminated', sendTls],
    ['plain HTTP', sendPlain],
  ] as const

  describe('no hook: target forwarded unchanged', () => {
    test.each(TLS_UNCHANGED)('TLS-terminated %s', async (sent, forwarded) => {
      expect((await sendTls(noHookPort, sent)).forwarded).toBe(forwarded)
    })

    test.each(PLAIN_UNCHANGED)('plain HTTP %s', async (sent, forwarded) => {
      expect((await sendPlain(noHookPort, sent)).forwarded).toBe(forwarded)
    })
  })

  describe.each(LEGS)('with a hook, %s', (_leg, send) => {
    // The upstream may act on either form, and the hook has not said that it
    // judged both: neither is sent.
    describe.each(['default', 'refuse'] as const)('%s', mode => {
      test.each(AMBIGUOUS)('%s is refused, loudly', async sent => {
        const asked = hookSeen.length
        const reply = await send(hookPort[mode], sent)
        expect(reply.status).toBe(400)
        expect(reply.text).toMatch(
          /^x-proxy-error: ambiguous-request-target\r$/im,
        )
        expect(reply.text).toContain('network.ambiguousRequestTarget')
        expect(reply.forwarded).toBeUndefined()
        expect(hookSeen.length).toBe(asked)
      })
    })

    test.each(AMBIGUOUS)(
      'asSpelled: %s goes out as spelled, and the hook gets both forms',
      async (sent, normalized) => {
        expect((await send(hookPort.asSpelled, sent)).forwarded).toBe(sent)
        expect(hookSeen.at(-1)!.info?.requestTarget).toBe(sent)
        expect(hookSeen.at(-1)!.info?.normalizedRequestTarget).toBe(normalized)
      },
    )

    test.each(AMBIGUOUS)(
      'normalize: %s goes out as %s, and the hook gets both forms',
      async (sent, normalized) => {
        const reply = await send(hookPort.normalize, sent)
        expect(reply.forwarded).toBe(normalized)
        expect(hookSeen.at(-1)!.info?.requestTarget).toBe(sent)
        expect(hookSeen.at(-1)!.info?.normalizedRequestTarget).toBe(normalized)
        expect(hookSeen.at(-1)!.url.endsWith(normalized)).toBe(true)
      },
    )

    test.each(UNAMBIGUOUS)('%s goes out byte for byte', async sent => {
      for (const mode of ['default', 'asSpelled'] as const) {
        expect((await send(hookPort[mode], sent)).forwarded).toBe(sent)
        expect(hookSeen.at(-1)!.info?.requestTarget).toBe(sent)
      }
      const { forwarded } = await send(hookPort.normalize, sent)
      expect(forwarded).toBe(hookSeen.at(-1)!.info?.normalizedRequestTarget)
    })

    // What a rule on request.url alone judges is the parsed URL. By default
    // nothing goes out whose spelling says anything else.
    test('a prefix rule on request.url is not got around in either direction', async () => {
      const port = await listen(
        createHttpProxyServer({
          ...base,
          filterRequest: async request => ({
            action: new URL(request.url).pathname.startsWith('/allowed/')
              ? 'allow'
              : 'deny',
          }),
        }),
      )
      expect((await send(port, '/allowed/x')).forwarded).toBe('/allowed/x')
      for (const target of [
        '/allowed/../secret',
        '/allowed/%2e%2e/secret',
        '/allowed\\..\\secret',
        '//secret',
        '/secret',
        // Under /secret/ to an upstream that takes the path literally.
        '/secret/../allowed/x',
        '/secret/%2E%2E/allowed/x',
        '/secret\\..\\allowed/x',
      ]) {
        const reply = await send(port, target)
        expect([400, 403]).toContain(reply.status)
        expect(reply.forwarded).toBeUndefined()
      }
    })

    test('asSpelled: a hook can refuse an ambiguous target itself, where and how it likes', async () => {
      const port = await listen(
        createHttpProxyServer({
          ...base,
          ambiguousRequestTarget: 'asSpelled',
          filterRequest: async (_request, info) =>
            info!.requestTargetIsAmbiguous === false
              ? { action: 'allow' }
              : { action: 'deny', status: 422 },
        }),
      )
      expect((await send(port, `/a{b}?q='x'`)).status).toBe(200)
      expect((await send(port, '/a/../b')).status).toBe(422)
    })

    test('a value that is none of the three refuses', async () => {
      const port = await listen(
        createHttpProxyServer({
          ...base,
          ambiguousRequestTarget: 'spelled' as 'asSpelled',
          filterRequest: async () => ({ action: 'allow' }),
        }),
      )
      expect((await send(port, '/a/../b')).status).toBe(400)
    })

    test('a refusal leaves a warn-level debug line', async () => {
      const warn = spyOn(console, 'warn').mockImplementation(() => {})
      const error = spyOn(console, 'error').mockImplementation(() => {})
      process.env.SRT_DEBUG = '1'
      try {
        await send(hookPort.default, '/a/../b')
        expect(warn.mock.calls.flat().join('\n')).toContain(
          'ambiguous request-target',
        )
      } finally {
        delete process.env.SRT_DEBUG
        warn.mockRestore()
        error.mockRestore()
      }
    })

    test('a refusal is reported like a denial of the hook', async () => {
      const port = await listen(
        createHttpProxyServer({
          ...base,
          filterRequest: async () => ({ action: 'allow' }),
          onFilterRequestDenied: d => denied.push(d),
          denyHeader: 'X-Deny-Reason',
        }),
      )
      denied.length = 0
      const reply = await send(port, '/a/../b?q=1')
      expect(reply.status).toBe(400)
      expect(reply.text).toMatch(/^x-deny-reason: bad_request\r$/im)
      expect(denied).toHaveLength(1)
      expect(denied[0]!.method).toBe('GET')
      expect(denied[0]!.url).toMatch(/^https?:\/\/[^/]+\/a\/\.\.\/b\?q=1$/)
      expect(denied[0]!.reason).toContain('ambiguous request-target')
    })
  })

  test('a refused upload does not keep its tunnel', async () => {
    const tls = await tunnel(hookPort.default)
    const closed = new Promise<void>(r => tls.once('close', () => r()))
    let reply = ''
    tls.on('error', () => {})
    tls.on('data', chunk => (reply += chunk.toString('latin1')))
    // A body announced and never sent: nothing else ends this connection.
    tls.write(
      `PUT /a/../b HTTP/1.1\r\nHost: ${UPSTREAM_NAME}:${tlsPort}\r\n` +
        'Content-Length: 1000000\r\n\r\nstart',
    )
    await closed
    expect(reply).toStartWith('HTTP/1.1 400 ')
  }, 3000)

  describe('with a hook: an absolute-form target', () => {
    test('in a tunnel, its path and query are read like an origin-form target', async () => {
      const abs = `https://${UPSTREAM_NAME}:${tlsPort}`
      expect((await sendTls(hookPort.default, `${abs}/a//b?x`)).forwarded).toBe(
        '/a//b?x',
      )
      expect((await sendTls(hookPort.default, abs)).forwarded).toBe('/')
      expect((await sendTls(hookPort.default, `${abs}?x`)).forwarded).toBe(
        '/?x',
      )
      expect((await sendTls(hookPort.default, `${abs}/a/../b`)).status).toBe(
        400,
      )
      expect(
        (await sendTls(hookPort.asSpelled, `${abs}//a/../b`)).forwarded,
      ).toBe('//a/../b')
      expect(hookSeen.at(-1)!.info?.normalizedRequestTarget).toBe('/b')
    })
  })

  // The service takes the path literally: `a/../b.txt` is a key, and the
  // signature covers the path as it arrives.
  describe('a request signed over its path', () => {
    const REAL = {
      accessKeyId: 'AKIAIOSFODNN7EXAMPLE',
      secretAccessKey: 'wJalrXUtnFEMI/K7MDENG/bPxRfiCYEXAMPLEKEY',
    }
    const SIGNED: Case[] = [
      ['//lead.txt', '/lead.txt'],
      ['/a/../b.txt', '/b.txt'],
      ['/a/..', '/'],
      ['/bucket/../up.txt', '/up.txt'],
    ]
    const amz = {
      'x-amz-content-sha256': UNSIGNED_PAYLOAD,
      'x-amz-date': '20260101T000000Z',
    }
    const authorizationFor = (target: string, creds: typeof REAL): string =>
      signSigv4({
        method: 'GET',
        requestTarget: target,
        headers: amz,
        hostHeader: `${UPSTREAM_NAME}:${tlsPort}`,
        signedHeaders: ['host', ...Object.keys(amz)],
        payloadHash: UNSIGNED_PAYLOAD,
        amzDate: amz['x-amz-date'],
        scope: { date: '20260101', region: 'us-east-1', service: 's3' },
        ...creds,
      }).authorization
    const sendSigned = (port: number, target: string, creds: typeof REAL) =>
      sendTls(port, target, [
        ...Object.entries(amz).map(([k, v]) => `${k}: ${v}`),
        `Authorization: ${authorizationFor(target, creds)}`,
      ])
    const receivedAuthorization = (): string | undefined =>
      /^authorization: (.*)$/im.exec(tlsHeads.at(-1)!)?.[1]

    describe('by the client', () => {
      test.each(SIGNED)('asSpelled: %s still verifies', async sent => {
        const reply = await sendSigned(hookPort.asSpelled, sent, REAL)
        expect(reply.forwarded).toBe(sent)
        expect(receivedAuthorization()).toBe(authorizationFor(sent, REAL))
      })

      test.each(SIGNED)('default: %s is refused', async sent => {
        expect((await sendSigned(hookPort.default, sent, REAL)).status).toBe(
          400,
        )
      })

      test.each(SIGNED)(
        'normalize: %s arrives as %s, which it is not signed for',
        async (sent, normalized) => {
          const reply = await sendSigned(hookPort.normalize, sent, REAL)
          expect(reply.forwarded).toBe(normalized)
          expect(receivedAuthorization()).not.toBe(
            authorizationFor(normalized, REAL),
          )
        },
      )
    })

    describe('again by the proxy, for a masked credential', () => {
      const sentinels = new SentinelRegistry()
      const pairs = new AwsPairRegistry()
      const eq = (h: string, p: string): boolean => h === p
      const FAKE = {
        accessKeyId: sentinels.register('AKID', REAL.accessKeyId, [
          UPSTREAM_NAME,
        ]),
        secretAccessKey: sentinels.register('SECRET', REAL.secretAccessKey, [
          UPSTREAM_NAME,
        ]),
      }
      pairs.register({
        accessKeyIdSentinel: FAKE.accessKeyId,
        realAccessKeyId: REAL.accessKeyId,
        realSecretAccessKey: REAL.secretAccessKey,
        injectHosts: [UPSTREAM_NAME],
      })
      const resigning = (
        ambiguousRequestTarget: HttpProxyServerOptions['ambiguousRequestTarget'],
      ): Promise<number> =>
        listen(
          createHttpProxyServer({
            ...base,
            ambiguousRequestTarget,
            filterRequest: async () => ({ action: 'allow' }),
            mutateHeaders: (headers, host) =>
              sentinels.substituteInHeaders(headers, host, eq),
            planSigv4: createSigv4Planner(pairs, undefined, eq),
          }),
        )

      test.each(SIGNED)(
        'asSpelled: %s is signed for the path the client named',
        async sent => {
          const reply = await sendSigned(
            await resigning('asSpelled'),
            sent,
            FAKE,
          )
          expect(reply.forwarded).toBe(sent)
          expect(receivedAuthorization()).toBe(authorizationFor(sent, REAL))
        },
      )

      test.each(SIGNED)('default: %s is never signed', async sent => {
        const reply = await sendSigned(await resigning(undefined), sent, FAKE)
        expect(reply.status).toBe(400)
      })

      test.each(SIGNED)(
        'normalize: %s is signed for %s, the bytes forwarded',
        async (sent, normalized) => {
          const reply = await sendSigned(
            await resigning('normalize'),
            sent,
            FAKE,
          )
          expect(reply.forwarded).toBe(normalized)
          expect(receivedAuthorization()).toBe(
            authorizationFor(normalized, REAL),
          )
        },
      )
    })
  })

  // A runtime that takes such a byte decodes it, and would not send the
  // client's bytes back out.
  test.each(['default', 'asSpelled', 'normalize'] as const)(
    'with a hook, %s: a byte outside printable ASCII is never forwarded',
    async mode => {
      for (const target of ['/\xc3\xa9', '/a?q=\xe9']) {
        const before = plainSeen.length
        // Some runtimes' parsers refuse it themselves.
        const reply = await sendPlain(hookPort[mode], target).catch(() => null)
        expect([undefined, 400]).toContain(reply?.status)
        expect(plainSeen.length).toBe(before)
      }
    },
  )
})

describe('readRequestTarget', () => {
  test.each(AMBIGUOUS)('%s is ambiguous', (raw, normalized) => {
    const want = { spelled: raw, normalized, ambiguous: true }
    expect(readRequestTarget(raw, 'GET')).toEqual(want)
    expect(readRequestTarget(`http://h.test:8080${raw}`, 'GET')).toEqual(want)
  })

  test.each(UNAMBIGUOUS)('%s is not', raw => {
    expect(readRequestTarget(raw, 'GET')).toMatchObject({
      spelled: raw,
      ambiguous: false,
    })
  })

  test.each([
    ['*', '*'],
    ['http://h.test', '/'],
    ['HTTPS://u:p@h.test?x', '/?x'],
    ['http://[::1]:80/a?', '/a?'],
  ])('%s is spelled %s', (raw, spelled) => {
    expect(readRequestTarget(raw, 'OPTIONS')).toMatchObject({
      spelled,
      ambiguous: false,
    })
  })

  // Only an escape the parser ADDS is the same resource: `%2F` is not `/`.
  test('an escape is not its character', () => {
    expect(readRequestTarget('/a%7Bb', 'GET')?.normalized).toBe('/a%7Bb')
    expect(readRequestTarget('/a%5Cb', 'GET')?.ambiguous).toBe(false)
    expect(readRequestTarget('/a%5C../b', 'GET')?.spelled).toBe('/a%5C../b')
  })

  test.each([
    '*',
    '*x',
    'h.test/x',
    'http://[::1/x',
    'ftp://h.test/x',
    // The URL parser reads another authority, or another path, than the
    // spelling has.
    'http:///h.test/x',
    'http:/h.test/x',
    'http://h.test\\x',
    'http://h.test\\@other.test/x',
    'http://h.test#x',
    '/é',
    '/a b',
    '/a\tb',
    '/a\x7f',
  ])('%p has no spelling to forward', raw => {
    expect(readRequestTarget(raw, 'GET')).toBeUndefined()
  })
})

describe('network.ambiguousRequestTarget', () => {
  const seen: string[] = []
  const upstream = createServer(recordTargets(seen))
  let port: number

  beforeAll(async () => {
    await new Promise<void>(r => upstream.listen(0, '127.0.0.1', () => r()))
    port = (upstream.address() as AddressInfo).port
  })

  afterAll(async () => {
    await SandboxManager.reset()
    await new Promise<void>(r => upstream.close(() => r()))
  })

  test.each([
    [undefined, 400, undefined],
    ['refuse', 400, undefined],
    ['asSpelled', 200, '/a/../b'],
    ['normalize', 200, '/b'],
  ] as const)('%p: %d', async (ambiguousRequestTarget, status, forwarded) => {
    await SandboxManager.reset()
    await SandboxManager.initialize({
      network: {
        allowedDomains: ['127.0.0.1'],
        deniedDomains: [],
        filterRequest: async () => ({ action: 'allow' }),
        ambiguousRequestTarget,
      },
      filesystem: { denyRead: [], allowWrite: [], denyWrite: [] },
    })
    const auth = Buffer.from(`srt:${SandboxManager.getProxyAuthToken()}`)
    const socket = await new Promise<Socket>((resolve, reject) => {
      const s = connect(SandboxManager.getProxyPort()!, '127.0.0.1', () =>
        resolve(s),
      )
      s.once('error', reject)
    })
    const recorded = (): number =>
      SandboxManager.getSandboxViolationStore()
        .getViolations()
        .filter(v => v.line.includes('ambiguous request-target')).length
    const before = recorded()
    seen.length = 0
    const reply = await exchange(
      socket,
      `GET http://127.0.0.1:${port}/a/../b HTTP/1.1\r\nHost: 127.0.0.1:${port}\r\n` +
        `Proxy-Authorization: Basic ${auth.toString('base64')}\r\n\r\n`,
    )
    expect(reply.status).toBe(status)
    expect(seen).toEqual(forwarded === undefined ? [] : [forwarded])
    expect(recorded() - before).toBe(status === 400 ? 1 : 0)
  })
})
