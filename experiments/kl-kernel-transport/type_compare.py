"""Exact raw DAG comparison with a declaration-scoped, fixed relocation rule.

No DAG/name normalization and no comparison memo. Only six explicit declaration
pairs may differ at the reviewed outer forall slots. Raw interning stays exact.
"""
from dataclasses import dataclass
import hashlib
import json

RULE_VERSION = 'kl-kernel-anonymous-owner-v1'
B = 'OAI.RepresentationTheory.KazhdanLusztig.BottSamelson'
C = 'OAI.RepresentationTheory.KazhdanLusztig.KernelTransportCompat'
G = 'OAI.LinearAlgebra.KernelTransport'
OLD = 'OAI.KLInvariance.'
NEW = 'OAI.LinearEquiv.'
CHILDREN = {'app': (1, 2), 'lam': (3, 4), 'forall': (3, 4),
            'let': (2, 3, 4), 'proj': (3,)}
CONSTRUCTORS = {'bvar', 'sort', 'const', 'app', 'lam', 'forall', 'let', 'lit', 'proj'}
SLOTS = (
    ('kernelSourceEquiv', 3079144783, ((1, 3), (3, 7), (4, 10), (6, 15), (7, 18), (9, 23), (10, 26))),
    ('kernelTargetEquiv', 730193490, ((1, 3), (3, 7), (4, 10), (6, 15), (7, 18), (9, 23), (10, 26))),
    ('kernelMixedEquiv', 358217602, ((1, 3), (3, 7), (4, 10), (6, 15), (7, 18), (8, 22), (9, 26),
                                  (11, 32), (12, 35), (13, 39), (14, 43), (16, 49), (17, 52),
                                  (18, 56), (19, 60), (21, 66), (22, 69))),
)


class Mismatch(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise Mismatch(message)


@dataclass(frozen=True)
class Rule:
    left: str
    right: str
    old_owner: str
    new_owner: str
    context_id: int
    slots: tuple


RULES = {(OLD + name, target + name): Rule(OLD + name, target + name, B, owner, h, slots)
         for name, h, slots in SLOTS for target, owner in ((OLD, C), (NEW, G))}
EXPECTED_NEW = {NEW + name: G for name, _, _ in SLOTS}
EXPECTED_MOVES = {OLD + name: C for name, _, _ in SLOTS}


def name_tree(owner, h, s):
    tree = ['anonymous']
    for part in ['inst', '_@', *owner.split('.')]:
        tree = ['str', tree, part]
    return ['num', ['str', ['str', ['num', tree, h], '_hygCtx'], '_hyg'], s]


def name_repr(owner, h, s):
    # Exact expected repr for this fixed Name shape, never a parser or replacement.
    return ('Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum '
            f'`inst.«_@».{owner} {h}) "_hygCtx") "_hyg") {s}')


def valid_name(tree):
    if type(tree) is not list or not tree:
        return False
    if tree == ['anonymous']:
        return True
    if len(tree) != 3 or tree[0] not in ('str', 'num') or not valid_name(tree[1]):
        return False
    return (type(tree[2]) is str if tree[0] == 'str'
            else type(tree[2]) is int and tree[2] >= 0)


@dataclass
class Dump:
    nodes: dict
    canonical: dict
    names: dict
    rows: dict
    owners: dict
    modules: set
    excluded: dict
    raw_projection_sha256: str = ''


def load_dump(path, intern, expected_modules):
    nodes, canonical, names, rows, owners, excluded = {}, {}, {}, {}, {}, {}
    modules, owner, raw = set(), None, hashlib.sha256()
    with path.open('rb') as stream:
        for data in stream:
            fields = data.decode().rstrip('\n').split('\t')
            tag = fields[0]
            if tag != 'NAME':
                raw.update(data)
            if tag == 'MODULE':
                owner = fields[1]
                require(owner not in modules, 'Duplicate module: ' + owner)
                modules.add(owner)
            elif tag == 'NODE':
                _, number, payload = fields
                number, node = int(number), json.loads(payload)
                require(number not in nodes and node[0] in CONSTRUCTORS, 'Invalid/duplicate node')
                key = list(node)
                for i in CHILDREN.get(node[0], ()):
                    key[i] = canonical[int(node[i])]
                nodes[number] = node
                canonical[number] = intern.setdefault(tuple(key), len(intern))
            elif tag == 'NAME':
                _, number, payload = fields
                number, tree = int(number), json.loads(payload)
                require(number in nodes and nodes[number][0] in ('forall', 'lam')
                        and number not in names and valid_name(tree), 'Invalid/duplicate Name supplement')
                names[number] = tree
            elif tag == 'TYPE':
                _, name, levels, number, kind = fields
                require(owner is not None and name not in rows, 'Duplicate/unowned declaration: ' + name)
                require(int(number) in nodes, 'Missing type node')
                rows[name] = (json.loads(levels), int(number), kind)
                owners[name] = owner
            elif tag == 'EXCLUDED':
                _, module, private, internal = fields
                require(module not in excluded, 'Duplicate exclusion count')
                excluded[module] = dict(private=int(private), internal=int(internal))
            else:
                raise Mismatch('Unknown dump row: ' + tag)
    require(modules == set(expected_modules), 'Module coverage mismatch')
    require(set(excluded) == modules, 'Missing exclusion counts')
    require(set(names) == {i for i, n in nodes.items() if n[0] in ('forall', 'lam')},
            'Missing structured binder Name')
    require(rows, 'Empty public declaration export')
    return Dump(nodes, canonical, names, rows, owners, modules, excluded, raw.hexdigest())


def raw_equal(left, right, ldecl, rdecl):
    x, y = left.rows[ldecl], right.rows[rdecl]
    return x[0] == y[0] and x[2] == y[2] and left.canonical[x[1]] == right.canonical[y[1]]


def compare_pair(left, right, ldecl, rdecl):
    require(ldecl in left.rows and rdecl in right.rows, 'Missing declaration')
    x, y = left.rows[ldecl], right.rows[rdecl]
    require(x[0] == y[0] and x[2] == y[2], 'Universe parameters/kind changed: ' + rdecl)
    rule = RULES.get((ldecl, rdecl))
    if rule is None:
        require(raw_equal(left, right, ldecl, rdecl), 'Exact type changed: ' + rdecl)
        return []
    require(left.owners[ldecl] == rule.old_owner and right.owners[rdecl] == rule.new_owner,
            'Unexpected rule owner: ' + rdecl)
    slots, accepted = dict(rule.slots), []

    def walk(i, j, slot, position):
        # No global or local relaxed memo: sharing never carries permission.
        if left.canonical[i] == right.canonical[j]:
            return
        a, b = left.nodes[i], right.nodes[j]
        require(a[0] == b[0] and len(a) == len(b), 'Expression shape changed: ' + position)
        for k in range(len(a)):
            if k in CHILDREN.get(a[0], ()):
                next_slot = slot + 1 if a[0] == 'forall' and k == 4 and slot is not None else None
                walk(int(a[k]), int(b[k]), next_slot, position + '/' + a[0] + '.' + str(k))
            elif a[k] != b[k]:
                require(a[0] == 'forall' and k == 1 and slot in slots,
                        'Unpermitted expression field changed: ' + position + '/' + str(k))
                s = slots[slot]
                require(a[2] == b[2] == 'Lean.BinderInfo.instImplicit', 'Changed binderInfo')
                require(left.names.get(i) == name_tree(rule.old_owner, rule.context_id, s)
                        and right.names.get(j) == name_tree(rule.new_owner, rule.context_id, s),
                        'Unexpected structured binder Name')
                require(a[1] == name_repr(rule.old_owner, rule.context_id, s)
                        and b[1] == name_repr(rule.new_owner, rule.context_id, s),
                        'Raw Name/supplement disagreement')
                accepted.append(dict(rule_version=RULE_VERSION, left_declaration=ldecl,
                                     right_declaration=rdecl, old_owner=rule.old_owner,
                                     new_owner=rule.new_owner, slot=slot, context_id=rule.context_id,
                                     scope=s, position=position + '/forall.1',
                                     before=a[1], after=b[1], before_name=left.names[i], after_name=right.names[j]))

    walk(x[1], y[1], 0, '')
    require(sorted(a['slot'] for a in accepted) == sorted(slots),
            'Expected relocation fields missing/duplicated: ' + rdecl)
    return accepted


def compare_public(left, right, manifest):
    require(manifest['new_declarations'] == EXPECTED_NEW
            and manifest['moved_declarations'] == EXPECTED_MOVES, 'Unexpected API policy manifest')
    require(len(left.rows) == manifest['reference_public_count'] == 3899, 'Reference count changed')
    require(len(right.rows) == manifest['final_public_count'] == 3902, 'Final count changed')
    require(set(right.rows) == set(left.rows) | set(EXPECTED_NEW), 'Declaration set changed')
    moves = {n: right.owners[n] for n in left.rows if left.owners[n] != right.owners[n]}
    require(moves == EXPECTED_MOVES, 'Owner map changed')
    for n, owner in EXPECTED_NEW.items():
        require(right.owners[n] == owner and right.rows[n][2] == 'def', 'New API owner/kind changed')
    strict_bad = [n for n in left.rows if not raw_equal(left, right, n, n)]
    require(set(strict_bad) == set(EXPECTED_MOVES), 'Unexpected raw strict differences')
    accepted = []
    for n in left.rows:
        accepted.extend(compare_pair(left, right, n, n))
    for name, _, _ in SLOTS:
        accepted.extend(compare_pair(left, right, OLD + name, NEW + name))
    require(len(accepted) == 62, 'Unexpected accepted field count')
    return dict(rule_version=RULE_VERSION, exact_old_declarations=3896,
                raw_strict_mismatches=sorted(strict_bad), accepted_differences=accepted,
                comparison='Exact except explicitly permitted anonymous-instance owner relocation markers')
