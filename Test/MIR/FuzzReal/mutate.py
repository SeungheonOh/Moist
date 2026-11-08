"""Mutations of the user-supplied Data of a validator's cases (datums,
redeemers, parameters, and for the edge-case validators every argument).

Data is represented as in pdata.py. `cases(validator, rows, max_depth)`
returns `(label, [Data])` for every base case, every case derived from one
(alternative redeemers and script purposes), and every mutation of a node up
to `max_depth` below a mutation site.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import pdata  # noqa: E402


def get(d, path):
    for i in path:
        if d[0] == 'C':
            d = d[2][i]
        elif d[0] == 'M':
            d = d[1][i // 2][i % 2]
        else:
            d = d[1][i]
    return d


def put(d, path, new):
    if not path:
        return new
    i, rest = path[0], path[1:]
    if d[0] == 'C':
        fs = list(d[2])
        fs[i] = put(fs[i], rest, new)
        return ('C', d[1], fs)
    if d[0] == 'L':
        xs = list(d[1])
        xs[i] = put(xs[i], rest, new)
        return ('L', xs)
    if d[0] == 'M':
        xs = list(d[1])
        k, v = xs[i // 2]
        if i % 2 == 0:
            xs[i // 2] = (put(k, rest, new), v)
        else:
            xs[i // 2] = (k, put(v, rest, new))
        return ('M', xs)
    raise ValueError(d)


def children(d):
    if d[0] == 'C':
        return list(range(len(d[2])))
    if d[0] == 'L':
        return list(range(len(d[1])))
    if d[0] == 'M':
        return list(range(2 * len(d[1])))
    return []


OTHERS = [('I', 7), ('B', b'\x01\x02'), ('C', 0, []), ('L', []), ('M', [])]


def node_mutations(d):
    out = []
    for o in OTHERS:
        if o[0] != d[0]:
            out.append(('kind:' + o[0], o))
    if d[0] == 'C':
        out.append(('idx+1', ('C', d[1] + 1, d[2])))
        if d[1] != 0:
            out.append(('idx0', ('C', 0, d[2])))
        out.append(('extraI', ('C', d[1], d[2] + [('I', 0)])))
        out.append(('extraB', ('C', d[1], d[2] + [('B', b'')])))
        if d[2]:
            out.append(('dropLast', ('C', d[1], d[2][:-1])))
    if d[0] == 'L':
        out.append(('appendI', ('L', d[1] + [('I', 3)])))
        out.append(('appendB', ('L', d[1] + [('B', b'\x05')])))
        if d[1]:
            out.append(('dropLast', ('L', d[1][:-1])))
            out.append(('dup', ('L', d[1] + [d[1][-1]])))
    if d[0] == 'I':
        out.append(('neg', ('I', -1 - d[1])))
    if d[0] == 'B':
        out.append(('flip', ('B', bytes([d[1][0] ^ 1]) + d[1][1:] if d[1] else b'\x00')))
    return out


def walk(d, path, depth, max_depth):
    yield path, d
    if depth < max_depth:
        for i in children(d):
            yield from walk(get(d, [i]), path + [i], depth + 1, max_depth)


def sites(validator, args):
    """(name, arg index, path) of user-supplied Data in a case's arguments."""
    if validator == 'Sample':
        return [('withdraw', 0, [], [])]
    ctx_ix = len(args) - 1
    ctx = args[ctx_ix]
    out = [('redeemer', ctx_ix, [1], [])]
    if validator == 'Hydra':
        si = get(ctx, [2])
        if si[0] == 'C' and si[1] == 1 and si[2][1][1] == 0:
            own = si[2][0]
            # keep the spent input's inline datum consistent with the script info
            mirrors = []
            for k, inp in enumerate(get(ctx, [0, 0])[1]):
                if inp[2][0] == own and inp[2][1][2][2][1] == 2:
                    mirrors.append([0, 0, k, 1, 2, 0])
            out.append(('datum', ctx_ix, [2, 1, 0], mirrors))
        outs = get(ctx, [0, 2])[1]
        if outs and outs[0][2][2][1] == 2:
            out.append(('outdatum', ctx_ix, [0, 2, 0, 2, 0], []))
    if validator in ('Voting', 'Certifying', 'Constitution', 'Sample', 'Settings', 'Crowdfund'):
        for k in range(ctx_ix):
            out.append(('param%d' % k, k, [], []))
    if validator in ('Vesting', 'Crowdfund', 'Settings'):
        si = get(ctx, [2])
        if si[0] == 'C' and si[1] == 1 and si[2][1][1] == 0:
            own = si[2][0]
            mirrors = []
            for k, inp in enumerate(get(ctx, [0, 0])[1]):
                if inp[2][0] == own and inp[2][1][2][2][1] == 2:
                    mirrors.append([0, 0, k, 1, 2, 0])
            out.append(('datum', ctx_ix, [2, 1, 0], mirrors))
        for k, o in enumerate(get(ctx, [0, 2])[1]):
            if o[2][2][1] == 2:
                out.append(('outdatum%d' % k, ctx_ix, [0, 2, k, 2, 0], []))
    if validator == 'ProgrammableLogicGlobal':
        out.append(('param', 0, [], []))
        for k, inp in enumerate(get(ctx, [0, 1])[1]):
            if inp[2][1][2][2][1] == 2:
                out.append(('refdatum%d' % k, ctx_ix, [0, 1, k, 1, 2, 0], []))
    return out


def derived(validator, args):
    """Extra base cases derived from an exported one."""
    out = []
    ctx_ix = len(args) - 1
    ctx = args[ctx_ix]
    if validator == 'Hydra':
        import hashlib
        h = ('B', hashlib.sha256(b'').digest())
        e = ('L', [])
        reds = [('close%d' % i, ('C', 3, [r])) for i, r in enumerate([
                    ('C', 0, []), ('C', 1, [e]), ('C', 2, [e]), ('C', 3, [e, h]),
                    ('C', 4, [e, h]), ('C', 5, [e, h])])]
        reds += [('contest%d' % i, ('C', 4, [r])) for i, r in enumerate([
                    ('C', 0, [e]), ('C', 1, [e, h]), ('C', 2, [e]), ('C', 3, [e, h]), ('C', 4, [e])])]
        reds += [('fanout', ('C', 6, [('I', 1), ('I', 0), ('I', 0)])), ('collect', ('C', 0, [])),
                 ('abort', ('C', 5, [])),
                 ('increment', ('C', 1, [('C', 0, [e, ('I', 1), ('C', 0, [('B', b'\xaa' * 28), ('I', 0)])])])),
                 ('decrement', ('C', 2, [('C', 0, [e, ('I', 1), ('I', 0)])]))]

        def no_parties(c):
            spots = [[2, 1, 0]]
            for k, inp in enumerate(get(c, [0, 0])[1]):
                if inp[2][1][2][2][1] == 2:
                    spots.append([0, 0, k, 1, 2, 0])
            outs = get(c, [0, 2])[1]
            if outs and outs[0][2][2][1] == 2:
                spots.append([0, 2, 0, 2, 0])
            for sp in spots:
                try:
                    st = get(c, sp)
                except (IndexError, TypeError):
                    continue
                if st[0] == 'C' and st[1] in (0, 1) and st[2] and st[2][0][0] == 'C':
                    c = put(c, sp + [0, 2 if st[1] == 0 else 1], e)
            return c
        for pname, c0 in [('', ctx), ('noparties', no_parties(ctx))]:
            if pname:
                a = list(args)
                a[ctx_ix] = c0
                out.append((pname, a))
            for rname, red in reds:
                a = list(args)
                a[ctx_ix] = put(c0, [1], red)
                out.append(((pname + '-' if pname else '') + rname, a))
    if validator == 'ProgrammableLogicGlobal':
        if get(ctx, [0, 4])[1]:
            a = list(args)
            a[ctx_ix] = put(ctx, [0, 4], ('M', []))
            out.append(('nomint', a))
        prog = ('C', 1, [('B', b'\x12' * 28)])
        c2 = put(ctx, [0, 4], ('M', []))
        moved = False
        for k, inp in enumerate(get(c2, [0, 0])[1]):
            if inp[2][1][2][0][2][0] == prog:
                c2 = put(c2, [0, 0, k, 1, 0, 0], ('C', 1, [('B', b'\x99' * 28)]))
                moved = True
        if moved:
            a = list(args)
            a[ctx_ix] = c2
            out.append(('nomint-noprog', a))
        for tag, info in [('minting', ('C', 0, [('B', b'\x13' * 28)])),
                          ('spending', ('C', 1, [('C', 0, [('B', b'\x5e\x12'), ('I', 0)]), ('C', 1, [])]))]:
            a = list(args)
            a[ctx_ix] = put(ctx, [2], info)
            out.append((tag, a))
    return out



CONTEXT_VALIDATORS = ('Voting', 'Certifying', 'Vesting', 'Sample', 'Constitution', 'Crowdfund',
                      'Settings', 'Hydra', 'ProgrammableLogicGlobal')


def all_sites(validator, args):
    if validator in CONTEXT_VALIDATORS:
        return sites(validator, args)
    return [('arg%d' % k, k, [], []) for k in range(len(args))]


def cases(validator, rows, max_depth):
    """`rows`: (name, [Data]) of cases.csv. Returns unique (label, [Data])."""
    seen = set()
    out = []
    bases = []
    for name, args in rows:
        bases.append((name, args))
        if validator in CONTEXT_VALIDATORS:
            for dname, dargs in derived(validator, args):
                bases.append((name + '+' + dname, dargs))

    def add(label, args):
        key = ';'.join(pdata.encode(x).hex() for x in args)
        if key not in seen:
            seen.add(key)
            out.append((label, key))

    for bname, args in bases:
        add('%s|base||' % bname, args)
        for name, ai, path, mirrors in all_sites(validator, args):
            try:
                base = get(args[ai], path)
            except (IndexError, TypeError):
                continue
            for sub, node in walk(base, [], 0, max_depth):
                for mname, new in node_mutations(node):
                    a2 = list(args)
                    a2[ai] = put(a2[ai], path + sub, new)
                    for m in mirrors:
                        try:
                            a2[ai] = put(a2[ai], m + sub, new)
                        except (IndexError, TypeError):
                            pass
                    add('%s|%s|%s|%s' % (bname, name, '.'.join(map(str, sub)), mname), a2)
    return out
