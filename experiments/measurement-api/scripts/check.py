#!/usr/bin/env python3
"""Check pinned sources, real clients, public types and actual printed axioms."""
from pathlib import Path
import argparse
import json
import re

from common import ROOT, logged, sha, source_identity

API = ['POVM.' + n for n in [
    'ext', 'mapEffects', 'mapEffects_mats', 'pullback', 'measure_apply', 'measure_pullback',
    'coarsegrain', 'coarsegrain_mats', 'coarsegrain_id', 'coarsegrain_comp',
    'mapEffects_coarsegrain', 'binary', 'binary_zero', 'measure_binary', 'measureDiscard_binary',
    'measure_coarsegrain', 'observe_pipeline', 'binary_channel_for_pair',
    'ofKraus', 'ofKraus_mats_mat', 'measure_ofKraus', 'effect_le_one', 'sum_mats_le_one']]
API += ['ProbDistribution.' + n for n in [
    'pushforward', 'toPMF_pushforward', 'pushforward_id', 'pushforward_comp', 'pushforward_apply']]
CONTRACTS = ['MeasurementAPI.Contracts.' + n for n in [
    'pullback_coarsegrain', 'two_relabelings', 'channel_composition', 'pmf_consumer',
    'unused_label', 'unused_label_probability', 'zeroDimPOVM']]
CONTRACTS += ['MeasurementAPI.ProcessSeparation.' + n for n in [
    'Qubit', 'preserve', 'reset', 'preserve_normalized', 'reset_normalized', 'preserveProcess',
    'resetProcess', 'same_POVM', 'same_probabilities', 'same_branch_trace', 'processes_ne',
    'inputOne', 'output_states_ne']]
NAMES = API + CONTRACTS
TARGETS = ['MeasurementAPI', 'Contracts.Pipeline', 'Contracts.ProcessSeparation',
           'Comparison.HypothesisBefore', 'Comparison.HypothesisAfter']
STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def audit_source(name, imports, commands):
    path = ROOT / 'generated' / (name + '.lean')
    path.write_text('module\n\n' + ''.join('public import ' + m + '\n' for m in imports)
                    + '\n' + '\n'.join(commands) + '\n')
    return str(path.relative_to(ROOT))


def parse_axioms(text, names):
    found = {name: [x.strip() for x in body.split(',') if x.strip()]
             for name, body in re.findall(r"'([^']+)' depends on axioms:\s*\[(.*?)\]",
                                          text, re.DOTALL)}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
        found[name] = []
    missing = set(names) - set(found)
    if missing:
        raise RuntimeError(f'Missing axiom output: {sorted(missing)}')
    for name in names:
        extra = set(found[name]) - STANDARD_AXIOMS
        if extra:
            raise RuntimeError(f'Unexpected axiom dependencies of {name}: {sorted(extra)}')
    return {name: found[name] for name in names}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', action='store_true', help='save a compact reviewed run snapshot')
    args = parser.parse_args()
    report = dict(source_identity_before='not_run', compilation='not_run', public_types='not_run',
                  printed_axioms='not_run', full_client_comparison='not_run',
                  source_identity_after='not_run', targets=TARGETS)
    (ROOT / 'results').mkdir(exist_ok=True)
    try:
        report['identity'] = source_identity()
        report['source_identity_before'] = 'passed'
        logged(['lean', '--version'], 'checked-lean-version')
        version = (ROOT / 'results/checked-lean-version.log').read_text().strip()
        if 'version 4.35.0,' not in version:
            raise RuntimeError('Actual Lean executable version differs from the pin')
        report['actual_lean_version'] = version
        logged(['python3', 'scripts/materialize.py'], 'materialize-check')
        report['build'] = logged(['lake', 'build', *TARGETS], 'build-current')
        report['compilation'] = 'passed'
        imports = ['Contracts.Pipeline', 'Contracts.ProcessSeparation']
        types = audit_source('PublicAPI', imports, ['#check @' + n for n in NAMES])
        logged(['lake', 'env', 'lean', types], 'public-types')
        report['public_types'] = 'passed'
        axioms = audit_source('AxiomsAPI', imports, ['#print axioms ' + n for n in NAMES])
        logged(['lake', 'env', 'lean', axioms], 'api-axioms')
        report['api_and_contract_axioms'] = parse_axioms(
            (ROOT / 'results/api-axioms.log').read_text(), NAMES)
        report['printed_axioms'] = 'passed_standard_axioms_only'
        client_name = 'OptimalHypothesisRate.Ref81Lem5'
        client_types, client_axioms = {}, {}
        for side in ['Before', 'After']:
            module = 'Comparison.Hypothesis' + side
            path = audit_source('ClientType' + side, [module], ['#check @' + client_name])
            logged(['lake', 'env', 'lean', path], 'client-type-' + side.lower())
            client_types[side] = (ROOT / ('results/client-type-' + side.lower() + '.log')).read_text()
            path = audit_source('ClientAxioms' + side, [module], ['#print axioms ' + client_name])
            logged(['lake', 'env', 'lean', path], 'client-axioms-' + side.lower())
            client_axioms[side] = parse_axioms(
                (ROOT / ('results/client-axioms-' + side.lower() + '.log')).read_text(), [client_name])
        if client_types['Before'] != client_types['After']:
            raise RuntimeError('Before/after client public signatures differ')
        if client_axioms['Before'] != client_axioms['After']:
            raise RuntimeError('Before/after client axiom sets differ')
        report['full_client_comparison'] = 'passed_same_signature_and_axiom_set'
        report['client_axioms'] = client_axioms
        report['source_identity_after'] = 'passed' if source_identity() == report['identity'] else 'failed'
        if report['source_identity_after'] != 'passed':
            raise RuntimeError('Source identity changed during checks')
        report['checked_api_declarations'] = len(API)
        report['checked_contract_declarations'] = len(CONTRACTS)
        phys = ROOT / '.lake/build/lib/lean/QuantumInfo'
        report['compiled_physlib_dependency_modules'] = sorted(
            'QuantumInfo.' + str(p.relative_to(phys).with_suffix('')).replace('/', '.')
            for p in phys.rglob('*.olean'))
        inputs = [ROOT / 'lakefile.toml', ROOT / 'lake-manifest.json', ROOT / 'lean-toolchain',
                  ROOT / 'MeasurementAPI.lean']
        inputs += sorted((ROOT / 'MeasurementAPI').glob('*.lean'))
        inputs += sorted((ROOT / 'Contracts').glob('*.lean'))
        inputs += sorted((ROOT / 'scripts').glob('*.py'))
        inputs += sorted((ROOT / 'provenance').glob('*.json'))
        report['checked_inputs_sha256'] = {str(p.relative_to(ROOT)): sha(p) for p in inputs}
        report['scope'] = ('Fresh compilation of local modules and complete isolated client variants; '
                           'fixed official dependency cache; no independent whole-dependency kernel replay')
        if args.record:
            (ROOT / 'evidence/acceptance.json').write_text(json.dumps(report, indent=2) + '\n')
            (ROOT / 'evidence/public-types.txt').write_text((ROOT / 'results/public-types.log').read_text())
            (ROOT / 'evidence/hypothesis-type.txt').write_text(client_types['Before'])
        print(f'Passed: {len(API)} API and {len(CONTRACTS)} contract declarations; '
              'complete before/after client signatures and axioms agree.')
        return 0
    except Exception as error:
        report['error'] = str(error)
        print('FAILED:', error)
        return 1
    finally:
        (ROOT / 'results/report.json').write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    raise SystemExit(main())
