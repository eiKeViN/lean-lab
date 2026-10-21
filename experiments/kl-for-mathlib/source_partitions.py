"""Partition immutable units at declaration boundaries, copying scope only."""
import hashlib
import re
from source_check import uncomment


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def context_only(text, closing=False):
    for line in uncomment(text).splitlines():
        line = line.strip()
        if not line:
            continue
        if ';' in line or re.search(r'\b(def|theorem|lemma|axiom|instance|abbrev|structure|class|inductive)\b', line):
            raise RuntimeError('A copied scope frame contains a declaration')
        pattern = r'end(?:\s+[\w.]+)?' if closing else r'(?:namespace\s+[\w.]+|open(?:\s+scoped)?\s+[\w. ]+|(?:noncomputable\s+)?section(?:\s+\w+)?|universe\s+[\w ]+)'
        if not re.fullmatch(pattern, line):
            raise RuntimeError('Not a supported scope-only frame: ' + line)


def expand_units(units, partitions, read_text):
    """All original bytes occur once; additions are original opening/end frames."""
    by_id = {u['id']: u for u in units}
    if len(by_id) != len(units) or set(partitions) - set(by_id):
        raise RuntimeError('Unknown or duplicate parent source unit')
    result = []
    for parent in units:
        if parent['id'] not in partitions:
            result.append(parent)
            continue
        spec = partitions[parent['id']]
        if set(spec) != {'opening_end', 'closing_start', 'parts'}:
            raise RuntimeError('Unexpected partition metadata fields')
        lines = read_text(parent['source']).splitlines(True)
        start, end = parent['start'], parent['end']
        if digest(''.join(lines[start-1:end])) != parent['sha256']:
            raise RuntimeError('Immutable parent source hash mismatch')
        opening_end, closing_start = spec['opening_end'], spec['closing_start']
        if not start <= opening_end < closing_start <= end:
            raise RuntimeError('Invalid scope frame ranges')
        opening = ''.join(lines[start-1:opening_end])
        closing = ''.join(lines[closing_start-1:end])
        context_only(opening)
        context_only(closing, closing=True)
        cursor = start
        if len(spec['parts']) < 2:
            raise RuntimeError('A partition needs multiple complete pieces')
        for part in spec['parts']:
            if set(part) != {'id', 'start', 'end', 'sha256'}:
                raise RuntimeError('A source piece may not override its source or context')
            if part['id'] in by_id or not part['id'].startswith(parent['id'] + '/'):
                raise RuntimeError('A piece needs a distinct parent-qualified ID')
            lo, hi = part['start'], part['end']
            if lo != cursor or hi < lo or hi > end:
                raise RuntimeError('Partition gap, overlap or out-of-range slice')
            if lo != start and not re.match(r'\s*(?:noncomputable\s+)?(?:def|theorem|lemma|abbrev|structure|class|inductive)\s', uncomment(lines[lo-1])):
                raise RuntimeError('Partition cut is not at a declaration start')
            raw = ''.join(lines[lo-1:hi])
            if digest(raw) != part['sha256']:
                raise RuntimeError('Source piece hash mismatch')
            result.append(dict(parent, **part, parent=parent['id'],
                               prefix=parent['prefix'] + (opening if lo != start else ''),
                               suffix=(closing if hi != end else '') + parent['suffix']))
            cursor = hi + 1
        if cursor != end + 1:
            raise RuntimeError('Partition does not cover the complete parent')
    if len({u['id'] for u in result}) != len(result):
        raise RuntimeError('Duplicate expanded source unit ID')
    return result
