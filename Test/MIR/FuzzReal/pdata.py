"""Minimal Plutus Data CBOR codec.

Data is represented as:
  ('C', idx, [fields])   constructor
  ('M', [(k, v), ...])   map
  ('L', [items])         list
  ('I', int)             integer
  ('B', bytes)           bytestring
"""


def decode(buf):
    v, pos = _dec(buf, 0)
    assert pos == len(buf), (pos, len(buf))
    return v


def _head(buf, pos):
    ib = buf[pos]
    major, info = ib >> 5, ib & 31
    pos += 1
    if info < 24:
        return major, info, pos
    if info == 24:
        return major, buf[pos], pos + 1
    if info == 25:
        return major, int.from_bytes(buf[pos:pos + 2], 'big'), pos + 2
    if info == 26:
        return major, int.from_bytes(buf[pos:pos + 4], 'big'), pos + 4
    if info == 27:
        return major, int.from_bytes(buf[pos:pos + 8], 'big'), pos + 8
    if info == 31:
        return major, None, pos
    raise ValueError('bad info %d' % info)


def _items(buf, pos, n, f):
    out = []
    if n is None:
        while buf[pos] != 0xff:
            x, pos = f(buf, pos)
            out.append(x)
        return out, pos + 1
    for _ in range(n):
        x, pos = f(buf, pos)
        out.append(x)
    return out, pos


def _raw(buf, pos):
    major, val, pos = _head(buf, pos)
    if major == 0:
        return ('I', val), pos
    if major == 1:
        return ('I', -1 - val), pos
    if major == 2:
        if val is None:
            chunks = b''
            while buf[pos] != 0xff:
                c, pos = _raw(buf, pos)
                chunks += c[1]
            return ('B', chunks), pos + 1
        return ('B', bytes(buf[pos:pos + val])), pos + val
    if major == 4:
        xs, pos = _items(buf, pos, val, _dec)
        return ('L', xs), pos
    if major == 5:
        def pair(b, p):
            k, p = _dec(b, p)
            v, p = _dec(b, p)
            return (k, v), p
        xs, pos = _items(buf, pos, val, pair)
        return ('M', xs), pos
    if major == 6:
        return ('T', val), pos
    raise ValueError('bad major %d' % major)


def _dec(buf, pos):
    v, pos = _raw(buf, pos)
    if v[0] != 'T':
        return v, pos
    tag = v[1]
    if 121 <= tag <= 127 or 1280 <= tag <= 1400:
        inner, pos = _dec(buf, pos)
        idx = tag - 121 if tag <= 127 else tag - 1280 + 7
        return ('C', idx, inner[1]), pos
    if tag == 102:
        inner, pos = _dec(buf, pos)
        return ('C', inner[1][0][1], inner[1][1][1]), pos
    if tag in (2, 3):
        b, pos = _raw(buf, pos)
        n = int.from_bytes(b[1], 'big')
        return ('I', n if tag == 2 else -1 - n), pos
    raise ValueError('bad tag %d' % tag)


def _h(major, n):
    if n < 24:
        return bytes([major << 5 | n])
    if n < 256:
        return bytes([major << 5 | 24, n])
    if n < 65536:
        return bytes([major << 5 | 25]) + n.to_bytes(2, 'big')
    if n < 2 ** 32:
        return bytes([major << 5 | 26]) + n.to_bytes(4, 'big')
    return bytes([major << 5 | 27]) + n.to_bytes(8, 'big')


def _arr(items):
    if not items:
        return b'\x80'
    return b'\x9f' + b''.join(encode(x) for x in items) + b'\xff'


def encode(d):
    k = d[0]
    if k == 'I':
        n = d[1]
        if 0 <= n < 2 ** 64:
            return _h(0, n)
        if -2 ** 64 <= n < 0:
            return _h(1, -1 - n)
        m = n if n >= 0 else -1 - n
        b = m.to_bytes((m.bit_length() + 7) // 8, 'big')
        return _h(6, 2 if n >= 0 else 3) + encode(('B', b))
    if k == 'B':
        b = d[1]
        if len(b) <= 64:
            return _h(2, len(b)) + b
        return b'\x5f' + b''.join(_h(2, len(b[i:i + 64])) + b[i:i + 64]
                                  for i in range(0, len(b), 64)) + b'\xff'
    if k == 'L':
        return _arr(d[1])
    if k == 'M':
        return _h(5, len(d[1])) + b''.join(encode(a) + encode(b) for a, b in d[1])
    if k == 'C':
        i = d[1]
        if i < 7:
            return _h(6, 121 + i) + _arr(d[2])
        if i < 128:
            return _h(6, 1280 + i - 7) + _arr(d[2])
        return _h(6, 102) + b'\x82' + encode(('I', i)) + _arr(d[2])
    raise ValueError(d)
