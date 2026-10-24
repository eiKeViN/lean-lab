from pathlib import Path
import json
r=Path('results/module-final/structure');raw=json.loads((r/'raw-comparison.json').read_text());old='OAI.KLInvariance.LocalCover.splitEquiv.match_3';new='OAI.KLInvariance.LocalCover.splitEquiv.match_6'
assert raw['old_count']==raw['new_count']==198
assert raw['missing']==[old] and raw['added']==[new] and not raw['changed'] and raw['relocated']==0
assert 'Historical names/types/levels/attributes/kernel/defeq/axioms: 136; unavailable=[]; actual old helpers=20' in (r/'preflight-v3.log').read_text()
assert f'Historical names/types/levels/attributes/kernel/defeq/axioms: 135; unavailable=[{old}]; actual old helpers=20' in (r/'ordinary-consumer.log').read_text()
s=json.loads((r/'restoration.json').read_text());assert s['production_sources_restored'] and s['artifact_bytes_identical'] and s['restored_build_exit']==0
assert json.loads((r/'restored-ready.json').read_text())['exit_code']==0
out=dict(candidate_producers_compiled=4,old_public_types_checked=136,modern_historical_types_checked=135,actual_old_helpers_kernel_checked=20,strict_comparison=raw,accepted_for_delivery=False,blocker='Existing LocalCover matcher name is unavailable; no compatibility definition or policy exemption authorized.',candidate_full_downstream_regression='not run after known unaccepted matcher failure',production_sources_restored=True,restored_oleans_identical=True,accepted_25_full_downstream_ready=True)
(r/'trial-classification.json').write_text(json.dumps(out,indent=2)+'\n');print('diagnostic classified; strict name boundary remains unaccepted')
