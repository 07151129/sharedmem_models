#!/usr/bin/env python2.7

from copy import deepcopy
import re
import sys
import xml.etree.ElementTree as ET

flags = "sfa"
if (len(sys.argv) > 2):
    flags = sys.argv[2]

NCORES = 2

INST_DICT = {
    "kind": None,
    "addr": None,
    "val": None,
    "gprs[0]": None,
    "stalled": None,
    "flushing": None,
    "acq_rel": None
}

re_inst_kind = re.compile(r"core(\d).minstb.kind")
re_inst_addr = re.compile(r"core(\d).minstb.addr")
re_inst_val = re.compile(r"core(\d).minstb.val")
re_inst_acq_rel = re.compile(r"core(\d).minstb.acq_rel")
re_gprs = re.compile(r"core(\d).gprs\[0\]")
re_stalled = re.compile(r"core(\d).stalled")
re_wb_flushing = re.compile(r"core(\d).wb.flushing")

tree = ET.parse(sys.argv[1])
root = tree.getroot()

cores_set = set()
for node in root.iter("node"):
    for state in node.iter("state"):
        for val in state.iter("value"):
            var = val.get("variable")
            if (re.match(re_inst_addr, var)):
                cores_set.add(int(re.match(re_inst_addr, var).group(1)))
NCORES = len(cores_set)

insts = []
loops = []
for i in root.iter("loops"):
    if (i.text.strip(" ")):
        loops += i.text.strip(" ").split(",")
loops = [int(i) - 1 for i in loops]

for node in root.iter("node"):
    for state in node.iter("state"):
        inst_c = [deepcopy(INST_DICT) for _ in xrange(0, NCORES)]

        for val in state.iter("value"):
            var = val.get("variable")

            if (re.match(re_inst_addr, var)):
                inst_c[int(re.match(re_inst_addr, var).group(1))]["addr"] = val.text
            elif (re.match(re_inst_kind, var)):
                inst_c[int(re.match(re_inst_kind, var).group(1))]["kind"] = val.text
            elif (re.match(re_inst_val, var)):
                inst_c[int(re.match(re_inst_val, var).group(1))]["val"] = val.text
            elif (re.match(re_inst_acq_rel, var)):
                inst_c[int(re.match(re_inst_acq_rel, var).group(1))]["acq_rel"] = val.text
            elif (re.match(re_gprs, var)):
                inst_c[int(re.match(re_gprs, var).group(1))]["gprs[0]"] = val.text
            elif (re.match(re_stalled, var)):
                inst_c[int(re.match(re_stalled, var).group(1))]["stalled"] = (True if val.text == "TRUE" else False)
            elif (re.match(re_wb_flushing, var)):
                inst_c[int(re.match(re_wb_flushing, var).group(1))]["flushing"] = (True if val.text == "TRUE" else False)
    insts.append(inst_c)

def dump_inst(i):
    ret = ""
    if i["kind"] == "MEM_INST_LDL":
        ret += "LDL r0 <- %s" % i["addr"][5:]
    elif i["kind"] == "MEM_INST_STL":
        ret += "STL r0 -> %s // (r0=%s)" % (i["addr"][5:], i["gprs[0]"][5:])
    elif i["kind"] == "MEM_INST_STV":
        ret += "STV %s -> %s" % (i["val"][5:], i["addr"][5:])
    elif i["kind"] == "MEM_INST_REL":
        ret += "REL"
    elif i["kind"] == "MEM_INST_ACQ":
        ret += "ACQ"
    elif i["kind"] == "MEM_INST_NOP":
        ret += "NOP"

    if (any([i["stalled"] and "s" in flags, i["flushing"] and "f" in flags, i["acq_rel"] and "a" in flags])):
        ret += " ("
    if (i["stalled"] and "s" in flags):
        ret += "S"
    if (i["flushing"] and "f" in flags):
        ret += "F"
    if (i["acq_rel"] and "a" in flags):
        if (i["kind"] == "MEM_INST_LDL"):
            ret += "A"
        else:
            ret += "R"
    if (any([i["stalled"] and "s" in flags, i["flushing"] and "f" in flags, i["acq_rel"] and "a" in flags])):
        ret += ")"
    return ret

for st, ic in enumerate(insts):
    l = "%-2d: " % (st+1)
    for i in ic:
        l += "%-32s " % dump_inst(i)
    if (st in loops):
        l += "%-16s" % "(loops)"
    print l
