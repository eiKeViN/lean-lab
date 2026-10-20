#!/usr/bin/env python3
"""Mutation tests for the reviewed exception and immutable shared DAG context."""
import argparse
import copy
import json
import sys
from pathlib import Path
import tempfile
import unittest

sys.dont_write_bytecode = True
import type_compare as tc

parser = argparse.ArgumentParser()
parser.add_argument('--before', type=Path)
parser.add_argument('--after', type=Path)
args, rest = parser.parse_known_args()


def recanonicalize(*dumps):
    intern = {}
    for data in dumps:
        data.canonical.clear()
        for i, node in data.nodes.items():
            key = list(node)
            for k in tc.CHILDREN.get(node[0], ()):
                key[k] = data.canonical[int(node[k])]
            data.canonical[i] = intern.setdefault(tuple(key), len(intern))
    return intern


def fixture():
    def build(side):
        nodes, names, rows, owners = {}, {}, {}, {}

        def add(node, tree=None):
            i = len(nodes)
            nodes[i] = node
            if tree is not None:
                names[i] = tree
            return i

        domain = add(['const', '`Ring', '[]'])
        result = add(['const', '`KernelTransportResult', '[]'])
        for short, h, pairs in tc.SLOTS:
            for prefix, owner in ([(tc.OLD, tc.B)] if side == 'left'
                                  else [(tc.OLD, tc.C), (tc.NEW, tc.G)]):
                slotmap = dict(pairs)
                body = result
                for slot in reversed(range(max(slotmap) + 2)):
                    if slot in slotmap:
                        n = tc.name_repr(owner, h, slotmap[slot])
                        tree = tc.name_tree(owner, h, slotmap[slot])
                        info = 'Lean.BinderInfo.instImplicit'
                    else:
                        n, tree, info = '`user' + str(slot), ['str', ['anonymous'], 'user' + str(slot)], 'Lean.BinderInfo.implicit'
                    body = add(['forall', n, info, str(domain), str(body)], tree)
                rows[prefix + short] = ('[`u]', body, 'def')
                owners[prefix + short] = owner
        for n in range(3896):
            name = 'OAI.Unmoved.decl' + str(n)
            rows[name], owners[name] = ('[]', result, 'theorem'), 'OAI.Unmoved'
        modules = set(owners.values())
        return tc.Dump(nodes, {}, names, rows, owners, modules,
                       {m: {'private': 0, 'internal': 0} for m in modules})
    left, right = build('left'), build('right')
    recanonicalize(left, right)
    return left, right


def at_slot(data, declaration, slot):
    i = data.rows[declaration][1]
    for _ in range(slot):
        i = int(data.nodes[i][4])
    return i


def manifest():
    return dict(new_declarations=tc.EXPECTED_NEW, moved_declarations=tc.EXPECTED_MOVES,
                reference_public_count=3899, final_public_count=3902)


class ComparisonTests(unittest.TestCase):
    def setUp(self):
        self.left, self.right = fixture()

    def reject(self, rule, mutate):
        left, right = copy.deepcopy(self.left), copy.deepcopy(self.right)
        mutate(left, right)
        recanonicalize(left, right)
        with self.assertRaises(tc.Mismatch):
            tc.compare_pair(left, right, rule.left, rule.right)

    def test_all_six_pairs_and_exact_unmoved(self):
        result = tc.compare_public(self.left, self.right, manifest())
        self.assertEqual(len(result['accepted_differences']), 62)
        self.assertEqual(result['exact_old_declarations'], 3896)
        self.assertEqual({a['rule_version'] for a in result['accepted_differences']}, {tc.RULE_VERSION})

    def test_each_allowed_slot_rejects_changed_scope_and_context_id(self):
        for rule in tc.RULES.values():
            for slot, scope in rule.slots:
                for h, s in ((rule.context_id + 1, scope), (rule.context_id, scope + 1)):
                    with self.subTest(pair=rule.right, slot=slot, h=h, s=s):
                        def mutate(left, right):
                            i = at_slot(right, rule.right, slot)
                            right.names[i] = tc.name_tree(rule.new_owner, h, s)
                            right.nodes[i][1] = tc.name_repr(rule.new_owner, h, s)
                        self.reject(rule, mutate)

    def test_owner_and_reverse_owner_rejected(self):
        for rule in tc.RULES.values():
            for owner in ('OAI.WrongOwner', rule.old_owner):
                def mutate(left, right):
                    slot, s = rule.slots[0]
                    i = at_slot(right, rule.right, slot)
                    right.names[i] = tc.name_tree(owner, rule.context_id, s)
                    right.nodes[i][1] = tc.name_repr(owner, rule.context_id, s)
                self.reject(rule, mutate)
            with self.assertRaises(tc.Mismatch):
                tc.compare_pair(self.right, self.left, rule.right, rule.left)

    def test_all_name_components_and_extra_scope_rejected(self):
        for rule in tc.RULES.values():
            for component in ('inst', '_@', '_hygCtx', '_hyg'):
                def mutate(left, right):
                    i = at_slot(right, rule.right, rule.slots[0][0])
                    def edit(tree):
                        if len(tree) == 3:
                            if tree[0] == 'str' and tree[2] == component:
                                tree[2] += '_changed'
                            edit(tree[1])
                    edit(right.names[i])
                self.reject(rule, mutate)
            def extra(left, right):
                i = at_slot(right, rule.right, rule.slots[0][0])
                right.names[i] = ['num', right.names[i], 123]
            self.reject(rule, extra)

    def test_missing_name_or_raw_name_disagreement_rejected(self):
        for rule in tc.RULES.values():
            for mode in ('missing', 'raw', 'tree-only'):
                def mutate(left, right):
                    i = at_slot(right, rule.right, rule.slots[0][0])
                    if mode == 'missing':
                        del right.names[i]
                    elif mode == 'raw':
                        right.nodes[i][1] += '_changed'
                    else:
                        right.names[i][2] += 1
                self.reject(rule, mutate)

    def test_binder_info_user_name_and_unlisted_slot_rejected(self):
        for rule in tc.RULES.values():
            for info in ('Lean.BinderInfo.default', 'Lean.BinderInfo.implicit'):
                def mutate(left, right):
                    right.nodes[at_slot(right, rule.right, rule.slots[0][0])][2] = info
                self.reject(rule, mutate)
            def user_name(left, right):
                right.nodes[at_slot(right, rule.right, 0)][1] = '`renamedUser'
            self.reject(rule, user_name)
            def unlisted(left, right):
                i = at_slot(right, rule.right, 0)
                right.nodes[i][1] = tc.name_repr(rule.new_owner, rule.context_id, 3)
                right.nodes[i][2] = 'Lean.BinderInfo.instImplicit'
                right.names[i] = tc.name_tree(rule.new_owner, rule.context_id, 3)
            self.reject(rule, unlisted)

    def test_const_universe_parameter_type_result_and_bvar_rejected(self):
        for rule in tc.RULES.values():
            for mode in ('constant', 'owner-in-constant', 'constant-universe', 'domain', 'result', 'bvar'):
                def mutate(left, right):
                    if mode == 'constant':
                        right.nodes[0][1] = '`Field'
                    elif mode == 'owner-in-constant':
                        left.nodes[0][1] = '`' + rule.old_owner + '.constant'
                        right.nodes[0][1] = '`' + rule.new_owner + '.constant'
                    elif mode == 'constant-universe':
                        right.nodes[0][2] = '[Lean.Level.zero]'
                    elif mode == 'result':
                        right.nodes[1][1] = '`DifferentResult'
                    elif mode == 'domain':
                        right.nodes[at_slot(right, rule.right, 1)][3] = '1'
                    else:
                        left.nodes[0] = ['bvar', '0']
                        right.nodes[0] = ['bvar', '1']
                self.reject(rule, mutate)

    def test_level_parameters_and_kind_rejected(self):
        for rule in tc.RULES.values():
            for levels, kind in (('[`v]', 'def'), ('[`u]', 'axiom')):
                def mutate(left, right):
                    _, node, _ = right.rows[rule.right]
                    right.rows[rule.right] = levels, node, kind
                self.reject(rule, mutate)

    def test_nested_forall_lambda_and_let_rejected(self):
        for rule in tc.RULES.values():
            for ctor in ('forall', 'lam', 'let'):
                def mutate(left, right):
                    for data, decl, owner in ((left, rule.left, rule.old_owner), (right, rule.right, rule.new_owner)):
                        n = tc.name_repr(owner, rule.context_id, 3)
                        i = len(data.nodes)
                        node = [ctor, n, 'Lean.BinderInfo.instImplicit', '0', '1'] if ctor != 'let' else [ctor, n, '0', '0', '1', 'false']
                        data.nodes[i] = node
                        if ctor != 'let':
                            data.names[i] = tc.name_tree(owner, rule.context_id, 3)
                        # An extra binder inside the root binder's domain, never an outer slot.
                        data.nodes[data.rows[decl][1]][3] = str(i)
                # Topological sort is needed because the fixture appended the domain child.
                left, right = copy.deepcopy(self.left), copy.deepcopy(self.right)
                mutate(left, right)
                for data in (left, right):
                    last = max(data.nodes)
                    data.nodes = {**{last: data.nodes[last]}, **{i: n for i, n in data.nodes.items() if i != last}}
                    # The inserted child depends on nodes 0/1, which stay first.
                    data.nodes = {0: data.nodes[0], 1: data.nodes[1], **{i: n for i, n in data.nodes.items() if i not in (0, 1)}}
                recanonicalize(left, right)
                with self.assertRaises(tc.Mismatch):
                    tc.compare_pair(left, right, rule.left, rule.right)

    def test_declaration_set_count_owner_and_manifest_rejected(self):
        for mode in ('missing', 'extra', 'same-count-replacement', 'owner', 'manifest', 'kind'):
            left, right = copy.deepcopy(self.left), copy.deepcopy(self.right)
            policy = copy.deepcopy(manifest())
            name = next(iter(tc.EXPECTED_NEW))
            if mode == 'missing':
                del right.rows['OAI.Unmoved.decl0']
            elif mode == 'extra':
                right.rows['OAI.Extra'] = right.rows[name]
                right.owners['OAI.Extra'] = tc.G
            elif mode == 'same-count-replacement':
                right.rows['OAI.Extra'] = right.rows.pop('OAI.Unmoved.decl0')
                right.owners['OAI.Extra'] = right.owners.pop('OAI.Unmoved.decl0')
            elif mode == 'owner':
                right.owners['OAI.Unmoved.decl0'] = tc.C
            elif mode == 'manifest':
                policy['final_public_count'] = 3903
            else:
                levels, node, _ = right.rows[name]
                right.rows[name] = levels, node, 'axiom'
            with self.assertRaises(tc.Mismatch):
                tc.compare_public(left, right, policy)

    def test_shared_dag_declaration_context_both_orders_and_immutable(self):
        for rule in tc.RULES.values():
            left, right = copy.deepcopy(self.left), copy.deepcopy(self.right)
            alias = 'OAI.Unmoved.shared'
            left.rows[alias], right.rows[alias] = left.rows[rule.left], right.rows[rule.right]
            left.owners[alias] = right.owners[alias] = 'OAI.Unmoved'
            original = copy.deepcopy((left, right))
            for order in ((True, False), (False, True), (True, False)):
                for allowed in order:
                    if allowed:
                        self.assertEqual(len(tc.compare_pair(left, right, rule.left, rule.right)), len(rule.slots))
                    else:
                        with self.assertRaises(tc.Mismatch):
                            tc.compare_pair(left, right, alias, alias)
            self.assertEqual((left, right), original)

    def test_shared_dag_outer_slot_vs_nested_domain_both_orders(self):
        for rule in tc.RULES.values():
            left, right = copy.deepcopy(self.left), copy.deepcopy(self.right)
            self.assertEqual(len(tc.compare_pair(left, right, rule.left, rule.right)), len(rule.slots))
            # Reuse the same existing allowed-slot node pair as a root domain.
            # This is acyclic: those nodes are descendants of the root body.
            left.nodes[left.rows[rule.left][1]][3] = str(at_slot(left, rule.left, rule.slots[-1][0]))
            right.nodes[right.rows[rule.right][1]][3] = str(at_slot(right, rule.right, rule.slots[-1][0]))
            recanonicalize(left, right)
            for _ in range(2):
                with self.assertRaises(tc.Mismatch):
                    tc.compare_pair(left, right, rule.left, rule.right)
                self.assertEqual(len(tc.compare_pair(self.left, self.right, rule.left, rule.right)), len(rule.slots))

    def test_structured_name_parser_and_global_intern_unchanged(self):
        self.assertFalse(tc.valid_name(['num', ['anonymous'], True]))
        self.assertFalse(tc.valid_name(['str', ['anonymous'], 3]))
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'dump'
            # A small actual wire-format fixture: no names rewritten at load time.
            lines = ['MODULE\tOAI.Test', 'NODE\t0\t["sort","u"]',
                     'NODE\t1\t["forall","`x","Lean.BinderInfo.implicit","0","0"]',
                     'NAME\t1\t["str",["anonymous"],"x"]',
                     'TYPE\tOAI.Test.f\t"[]"\t1\tdef', 'EXCLUDED\tOAI.Test\t0\t0']
            path.write_text('\n'.join(lines) + '\n')
            intern = {}
            data = tc.load_dump(path, intern, {'OAI.Test'})
            self.assertIn(('forall', '`x', 'Lean.BinderInfo.implicit', 0, 0), intern)
            before = copy.deepcopy((intern, data))
            tc.compare_pair(data, data, 'OAI.Test.f', 'OAI.Test.f')
            self.assertEqual((intern, data), before)
            for replacement in ('', 'NAME\t1\t["num",["anonymous"],true]'):
                path.write_text('\n'.join(lines[:3] + ([replacement] if replacement else []) + lines[4:]) + '\n')
                with self.assertRaises(tc.Mismatch):
                    tc.load_dump(path, {}, {'OAI.Test'})
            path.write_text('\n'.join(lines) + '\n')
            with self.assertRaises(tc.Mismatch):
                tc.load_dump(path, {}, {'OAI.WrongModule'})

    @unittest.skipUnless(args.before and args.after, 'Real exports supplied by aggregate runner')
    def test_actual_exported_types(self):
        intern = {}
        policy = json.loads((Path(__file__).parent / 'api-manifest.json').read_text())
        left = tc.load_dump(args.before, intern, policy['reference_modules'])
        right = tc.load_dump(args.after, intern, policy['reference_modules'] + policy['added_modules'])
        snapshot = copy.deepcopy((left, right, intern))
        result = tc.compare_public(left, right, policy)
        self.assertEqual(len(result['accepted_differences']), 62)
        self.assertEqual((left, right, intern), snapshot)


if __name__ == '__main__':
    unittest.main(argv=[__file__, *rest], verbosity=2)
