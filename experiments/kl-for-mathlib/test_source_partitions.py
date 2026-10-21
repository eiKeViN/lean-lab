#!/usr/bin/env python3
"""Negative source-lineage cases; no Lean build or network."""
import copy
import unittest
from source_partitions import digest, expand_units

TEXT = ('namespace X\nopen Polynomial\nnoncomputable section\n\n'
        'theorem first : True := by\n  trivial\n\n'
        'theorem second : True := by\n  trivial\n\nend\nend X\n')
LINES = TEXT.splitlines(True)
PARENT = dict(id='unit', source='Source.lean', start=1, end=12,
              sha256=digest(TEXT), prefix='section\n', suffix='end\n')
PARTS = {'unit': dict(opening_end=4, closing_start=11, parts=[
    dict(id='unit/first', start=1, end=7, sha256=digest(''.join(LINES[:7]))),
    dict(id='unit/second', start=8, end=12, sha256=digest(''.join(LINES[7:])))])}


def expand(spec=PARTS, units=None):
    return expand_units(units or [PARENT], spec, lambda _: TEXT)


class PartitionChecks(unittest.TestCase):
    def test_complete_identity_and_scope_frames(self):
        result = expand()
        raw = [''.join(LINES[u['start']-1:u['end']]) for u in result]
        self.assertEqual(''.join(raw), TEXT)
        self.assertEqual(result[0]['suffix'], 'end\nend X\nend\n')
        self.assertEqual(result[1]['prefix'], 'section\n'+''.join(LINES[:4]))

    def test_unchanged_unpartitioned_units(self):
        self.assertEqual(expand({}), [PARENT])

    def test_reject_gap(self):
        spec = copy.deepcopy(PARTS); spec['unit']['parts'][1]['start'] = 9
        with self.assertRaises(RuntimeError): expand(spec)

    def test_reject_overlap(self):
        spec = copy.deepcopy(PARTS); spec['unit']['parts'][1]['start'] = 7
        with self.assertRaises(RuntimeError): expand(spec)

    def test_reject_incomplete_tail(self):
        spec = copy.deepcopy(PARTS); part = spec['unit']['parts'][-1]
        part['end'] = 11; part['sha256'] = digest(''.join(LINES[7:11]))
        with self.assertRaises(RuntimeError): expand(spec)

    def test_reject_piece_hash_change(self):
        spec = copy.deepcopy(PARTS); spec['unit']['parts'][0]['sha256'] = '0'*64
        with self.assertRaises(RuntimeError): expand(spec)

    def test_reject_parent_hash_change(self):
        parent = dict(PARENT, sha256='0'*64)
        with self.assertRaises(RuntimeError): expand(units=[parent])

    def test_reject_copied_declaration_in_frame(self):
        spec = copy.deepcopy(PARTS); spec['unit']['opening_end'] = 6
        with self.assertRaises(RuntimeError): expand(spec)

    def test_reject_proof_body_as_closing_frame(self):
        spec = copy.deepcopy(PARTS); spec['unit']['closing_start'] = 9
        with self.assertRaises(RuntimeError): expand(spec)

    def test_reject_cut_inside_proof(self):
        spec = copy.deepcopy(PARTS); spec['unit']['parts'][0].update(end=8, sha256=digest(''.join(LINES[:8])))
        spec['unit']['parts'][1].update(start=9, sha256=digest(''.join(LINES[8:])))
        with self.assertRaises(RuntimeError): expand(spec)

    def test_reject_duplicate_or_parent_id(self):
        for name in ('unit', 'unit/first'):
            spec = copy.deepcopy(PARTS); spec['unit']['parts'][1]['id'] = name
            with self.assertRaises(RuntimeError): expand(spec)

    def test_reject_unknown_parent(self):
        with self.assertRaises(RuntimeError): expand({'unknown': PARTS['unit']})

    def test_reject_piece_source_or_context_override(self):
        for key in ('source', 'prefix', 'suffix', 'parent'):
            spec = copy.deepcopy(PARTS); spec['unit']['parts'][0][key] = 'override'
            with self.assertRaises(RuntimeError): expand(spec)

    def test_reject_unknown_partition_fields(self):
        spec = copy.deepcopy(PARTS); spec['unit']['unchecked'] = True
        with self.assertRaises(RuntimeError): expand(spec)


if __name__ == '__main__':
    unittest.main()
