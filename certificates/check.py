#!/usr/bin/env python3
"""Checker for monotone.certificate.v1 artifacts.

Re-reads one certificate artifact, verifies its internal
consistency, and recomputes its overall reading from the
per-dimension verdicts under the reading rule stated in spec.md
section 6: certified requires every dimension improving or flat
with a coverage discharge; any regressed or unmeasured dimension
blocks the certified reading. A regressed dimension whose recorded
values do not regress, or an improving or flat verdict whose
recorded values contradict it, refuses the artifact by name.
Prints the recomputed reading. Exit 0 exactly when the artifact is
consistent and its printed reading equals the recomputed reading.
"""
import json
import sys

CERTIFYING = {"improving", "flat"}
VERDICTS = CERTIFYING | {"regressed", "unmeasured"}
DIMENSIONS = {
    "coverage", "fidelity", "solvability", "reconversibility",
    "reweightability", "speed", "setup",
}


def fail(msg):
    print(f"REFUSED: {msg}")
    return 1


def main(path):
    with open(path) as fh:
        cert = json.load(fh)
    if cert.get("schema") != "monotone.certificate.v1":
        return fail("schema is not monotone.certificate.v1")
    dims = cert.get("dimensions", [])
    names = [d["name"] for d in dims]
    if set(names) != DIMENSIONS or len(names) != len(DIMENSIONS):
        return fail(f"dimension set mismatch: {sorted(names)}")
    for d in dims:
        v = d.get("verdict")
        if v not in VERDICTS:
            return fail(f"{d['name']}: unknown verdict {v!r}")
        if v == "unmeasured":
            if not d.get("gap") or not d.get("closingRoute"):
                return fail(f"{d['name']}: unmeasured without a named gap and closing route")
            continue
        if "earlierValue" not in d or "laterValue" not in d:
            return fail(f"{d['name']}: measured verdict without both values")
        if not d.get("coverage"):
            return fail(f"{d['name']}: measured verdict without a coverage discharge")
        if not d.get("evidence"):
            return fail(f"{d['name']}: measured verdict without evidence references")
        e, l = d["earlierValue"], d["laterValue"]
        if v == "improving" and not l > e:
            return fail(f"{d['name']}: improving but {l} <= {e}")
        if v == "flat" and not l == e:
            return fail(f"{d['name']}: flat but {l} != {e}")
        if v == "regressed" and not l < e:
            return fail(f"{d['name']}: regressed but {l} >= {e}")
    blocked = [d["name"] for d in dims if d["verdict"] not in CERTIFYING]
    recomputed = "certified" if not blocked else "not certified"
    print(f"subject: {cert['subject']}")
    print(f"earlier: {cert['earlier']}")
    print(f"later:   {cert['later']}")
    for d in dims:
        line = f"  {d['name']}: {d['verdict']}"
        if "earlierValue" in d:
            line += f" ({d['earlierValue']} -> {d['laterValue']})"
        print(line)
    if blocked:
        print(f"blocking dimensions: {', '.join(blocked)}")
    print(f"recomputed reading: {recomputed}")
    print(f"printed reading:    {cert.get('reading')}")
    if cert.get("reading") != recomputed:
        return fail("printed reading differs from recomputed reading")
    print("CONSISTENT")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
