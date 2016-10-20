#! /usr/bin/python

from __future__ import print_function

import sys
import argparse

parser = argparse.ArgumentParser(description='Process some integers.')
parser.add_argument('compute', type=float, help='cost to compute a variable sample')
parser.add_argument('broadcast', type=float, help='cost to broadcast from master to all workers')
parser.add_argument('comm_mw', type=float, help='cost to transmit from master to a worker')
parser.add_argument('comm_wm', type=float, help='cost to transmit from a worker to master')

args = parser.parse_args()

print("v_A", args.compute)
print("v_B", args.compute + args.broadcast)
print("v_C", 0.0)
print("v_D", args.comm_wm)

print("v_Au", args.compute + args.comm_wm)
print("v_Bu", args.compute + args.broadcast + args.comm_wm)
print("v_Cu", args.comm_mw)
print("v_Du", args.comm_wm + args.comm_mw)

print("w_C", args.compute)
print("w_D", args.compute)
print("w_Cu", args.compute)
print("w_Du", args.compute)

print("f_A", 0.0)
print("f_C", 0.0)
print("f_D", args.comm_wm)
print("f_E", args.comm_mw)
print("f_G", args.comm_wm + args.comm_mw)

print("f_Cu", 0.0)
print("f_Du", 0.0)
print("f_Eu", 0.0)
print("f_Gum", args.comm_mw)
print("f_Guw", args.comm_wm)
print("f_Gumw", 0.0)
