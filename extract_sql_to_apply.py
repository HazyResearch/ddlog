#! /usr/bin/python

import json;
import sys;

pp = json.load(sys.stdin);
p = next(x for x in pp if x["partition_types"] == sys.argv[1]);

print("\n".join(p["sql_to_apply"]));

