import json,sys
from module_all import policy,compare_public
policy();print(json.dumps(compare_public(sys.argv[1]),indent=2))
