#!/usr/bin/env python
from __future__ import print_function

vps = [100, 100] # voters per senator

f = open("input/senator_voted_for.tsv", "w")
for i in range(len(vps)):
    f.write(str(i) + "\t" + "0\n")
f.close()

f = open("input/voter_voted_for.tsv", "w")
index = 0
for i in range(len(vps)):
    for j in range(vps[i]):
        f.write(str(index) + "\t" + str(i) + "\n")
        index += 1
f.close()

f = open("input/proposition.tsv", "w")
f.write("0\t\\N")
f.close()

f = open("input/senator.tsv", "w")
for i in range(len(vps)):
    f.write(str(i) + "\t\\N\n")
f.close()

f = open("input/yay_vote.tsv", "w")
index = 0
for i in range(len(vps)):
    for j in range(vps[i]):
        f.write(str(index) + "\t\\N\n")
        index += 1
f.close()

f = open("input/nay_vote.tsv", "w")
index = 0
for i in range(len(vps)):
    for j in range(vps[i]):
        f.write(str(index) + "\t\\N\n")
        index += 1
f.close()
