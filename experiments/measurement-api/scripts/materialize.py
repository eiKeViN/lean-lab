#!/usr/bin/env python3
"""Generate a module adapter and isolated before/after clients; preserve upstream."""
from pathlib import Path
import argparse
import difflib
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-evidence', action='store_true',
                        help='record an intentional reviewed adapter/comparator change')
    args = parser.parse_args()
    pins = json.loads((ROOT / 'provenance/upstream.json').read_text())
    source = ROOT / '../../projects/quantum-experiments/pmf-environment/Verified/PMFBridgeDraft/Bridge.lean'
    original_bridge = source.read_text()
    digest = lambda s: hashlib.sha256(s.encode()).hexdigest()
    if digest(original_bridge) != pins['bridge_sha256']:
        raise RuntimeError('Bridge baseline differs; preserve it and review the adaptation')
    adapted_bridge = 'module\n\n' + original_bridge.replace('import ', 'public import ')
    adapted_bridge = adapted_bridge.replace('noncomputable section',
                                            '@[expose] public section\nnoncomputable section', 1)
    target = ROOT / 'vendor/bridge/PMFBridgeDraft/Bridge.lean'
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(adapted_bridge)

    path = ROOT / 'vendor/physlib/QuantumInfo/ResourceTheory/HypothesisTesting.lean'
    before = path.read_text()
    baselines = json.loads((ROOT / 'provenance/physlib-sources.json').read_text())
    if digest(before) != baselines['QuantumInfo/ResourceTheory/HypothesisTesting.lean']:
        raise RuntimeError('Hypothesis-testing source differs from the pinned baseline')
    start = before.index('      --Turn it into a POVM (probably want to have lemmas around this ideally)')
    end = before.index('    rw [hΦ₁, hΦ₂]', start)
    replacement = '''      obtain ⟨Φ, hρ, hσ⟩ := POVM.binary_channel_for_pair
        T T.prop.right ρ σ p q
        (by simpa [p] using hT₂)
        (by dsimp only [q]; rw [← hT₁])
      exact ⟨Φ, hρ.symm, hσ.symm⟩
'''
    after = before[:start] + replacement + before[end:]
    after = after.replace('module\n', 'module\n\npublic import MeasurementAPI.BinaryChannel\n', 1)
    generated = ROOT / 'generated/Comparison'
    generated.mkdir(parents=True, exist_ok=True)
    (generated / 'HypothesisBefore.lean').write_text(before)
    (generated / 'HypothesisAfter.lean').write_text(after)
    evidence = ROOT / 'evidence'
    evidence.mkdir(exist_ok=True)

    def record(name, contents):
        path = evidence / name
        if args.write_evidence:
            path.write_text(contents)
        elif not path.exists() or path.read_text() != contents:
            raise RuntimeError(f'Reviewed evidence differs: {path}; do not silently update it')

    record('hypothesis.patch', ''.join(difflib.unified_diff(
        before.splitlines(keepends=True), after.splitlines(keepends=True),
        fromfile='Physlib/HypothesisTesting.lean', tofile='Experiment/HypothesisTesting.lean', n=0)))
    record('bridge-module.patch', ''.join(difflib.unified_diff(
        original_bridge.splitlines(keepends=True), adapted_bridge.splitlines(keepends=True),
        fromfile='Existing/PMFBridgeDraft/Bridge.lean', tofile='Adapter/PMFBridgeDraft/Bridge.lean', n=0)))
    record('comparison-sources.json', json.dumps({
        'bridge_source': str(source.relative_to(ROOT)),
        'bridge_original_sha256': digest(original_bridge),
        'bridge_adapter_sha256': digest(adapted_bridge),
        'bridge_adapter_scope': 'module/public import/expose only; proof bodies unchanged',
        'hypothesis_original_sha256': digest(before),
        'hypothesis_after_sha256': digest(after),
        'changed_proof': 'OptimalHypothesisRate.Ref81Lem5 binary-channel construction',
        'hypothesis_declaration_signatures': 'unchanged'
    }, indent=2) + '\n')
    print('Generated a visibility-only bridge adapter and the complete isolated before/after clients.')


if __name__ == '__main__':
    main()
