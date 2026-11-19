#!/usr/bin/env python3
"""Counts what recorded streams exercise: events by kind and the branches of
the binding (spec/EtcdBinding.tla). A 0 row means the streams say nothing
about that branch. `ready` rows also count `mem` reports. Rows for later
writes, snapshots, read indexes, batching, transfers, forwarding and
membership are 0 for streams without those features.

    scripts/coverage.py STREAM_OR_DIR...

Each argument is a stream file, or a directory searched for *.ndjson and
kit/stream.ndjson.
"""
import collections
import glob
import json
import os
import sys

ROWS = [
    "boot: first", "boot: restart, last write had happened", "boot: restart, last write taken back",
    "boot: restart, nothing announced since the last send",
    "ready: election started", "ready: election started again by a candidate",
    "ready: later term adopted", "ready: later term adopted by a leader",
    "ready: vote for another", "ready: term adopted and vote in one write",
    "ready: becomes leader", "ready: candidate becomes follower", "ready: leader becomes follower",
    "ready: leader stores", "ready: follower stores", "ready: follower stores several entries",
    "ready: follower deletes a suffix", "ready: follower stores part of a request",
    "ready: leader commits", "ready: follower commits on a request",
    "ready: follower commits on a heartbeat", "ready: follower commits on a request it stores nothing of",
    "ready: stores and commits in one write", "ready: role only, no write",
    "send: vote", "send: vote granted", "send: vote refused", "send: vote granted again",
    "send: request", "send: request, several entries", "send: request, no entries",
    "send: heartbeat", "send: heartbeat with a commit index",
    "send: acknowledgement", "send: acknowledgement of the commit index (AckCommitted)",
    "send: request refused", "send: heartbeat answered",
    "recv: request", "recv: request delivered again", "recv: heartbeat", "recv: other",
    "apply", "apply: after a restart, from index 1", "apply: several entries",
]
LATER = [
    "write: made later", "write: several waiting", "write: after the node has moved on to a later term",
    "send: request for entries not on the leader's disk", "apply: before the commit index is on disk",
    "boot: restart with writes waiting", "mem: leader commits what is not on its own disk",
    "snap", "send: snap", "log replaced by a snapshot", "restore", "boot: from a snapshot",
    "readreq", "read", "send: readindex",
    "flush", "flush: one more input in the same write", "net: a write for several inputs",
    "net: nothing to write",
    "send: timeoutnow", "ready: election started because the leader said so",
    "send: prop", "ready: leader appends what a follower passed on",
    "member: leader appends a change of one step", "member: leader appends a joint change",
    "member: leader appends the change that leaves a joint configuration",
    "member: raft itself appends the change that leaves", "member: follower stores a change",
    "conf", "conf: a voter added", "conf: a voter removed", "conf: joint configuration entered",
    "conf: joint configuration left", "conf: by a leader", "conf: a leader removed from the voters",
    "conf: after a restart, applied again",
    "member: elected with voters a change made", "member: elected in a joint configuration",
    "member: elected by a node that was not a voter at the start",
    "member: a leader that is not a voter commits",
    "member: boot from a snapshot with voters a change made", "member: restore with voters a change made",
]


def cover(path, c):
    last = {}       # node -> last index on disk, as announced
    hs = {}         # node -> (term, vote, commit) as announced
    role = {}
    pend = {}       # node -> message being handled
    seen = collections.defaultdict(set)   # node -> requests handled
    wrote = {}      # node -> a write was announced and nothing reported after it
    booted = set()
    granted = set()
    queued = collections.Counter()   # node -> writes reported and not made
    batch = {}                       # node -> `flush` reports of the write being announced
    dhs = {}                         # node -> (term, vote, commit) on disk, of a node that batches
    disk = {}                        # node -> (commit, last index) on disk
    applied_since_boot = {}
    conf = {}       # node -> (voters, outgoing) raft counts with
    first = {}      # node -> the voters it started with
    confed = {}     # node -> highest index of a change it has told raft of, since its first start
    for line in open(path):
        if not line.strip():
            continue
        ev = json.loads(line)
        n, e = ev.get("node"), ev.get("e")
        for x in ev.get("entries", []) if e in ("ready", "mem", "write", "net") else []:
            if x["type"] != "conf":
                continue
            if ev.get("role") == "leader" and e in ("ready", "mem"):
                v = x["value"]
                c["member: leader appends " + ("the change that leaves a joint configuration" if v["leave"]
                                              else "a joint change" if v["joint"] else "a change of one step")] += 1
                if v["leave"] and ev.get("by") in ("apply", "write", "recv", "batch"):
                    c["member: raft itself appends the change that leaves"] += 1
            elif ev.get("role") != "leader":
                c["member: follower stores a change"] += 1
        if e in ("ready", "mem") and ev.get("role") == "leader":
            cf = conf.get(n)
            if cf and role.get(n) != "leader":
                if cf != (first.get(n), []):
                    c["member: elected with voters a change made"] += 1
                if cf[1]:
                    c["member: elected in a joint configuration"] += 1
                if n not in (first.get(n) or [n]):
                    c["member: elected by a node that was not a voter at the start"] += 1
            if cf and n not in cf[0] + cf[1] and ev["commit"] > hs.get(n, (0, "", 0))[2]:
                c["member: a leader that is not a voter commits"] += 1
        if e == "conf":
            c["conf"] += 1
            old = conf.get(n, ([], []))
            c["conf: a voter added"] += bool(set(ev["voters"]) - set(old[0]))
            c["conf: a voter removed"] += bool(set(old[0]) - set(ev["voters"]))
            c["conf: joint configuration entered"] += bool(ev["outgoing"] and not old[1])
            c["conf: joint configuration left"] += bool(old[1] and not ev["outgoing"])
            if role.get(n) == "leader":
                c["conf: by a leader"] += 1
                c["conf: a leader removed from the voters"] += n in old[0] and n not in ev["voters"]
            c["conf: after a restart, applied again"] += ev["index"] <= confed.get(n, 0)
            confed[n] = max(confed.get(n, 0), ev["index"])
            conf[n] = (ev["voters"], ev["outgoing"])
        elif e == "restore" and "voters" in ev:
            c["member: restore with voters a change made"] += (ev["voters"], ev["outgoing"]) != (first.get(n), [])
            conf[n] = (ev["voters"], ev["outgoing"])
        if e == "boot" and "voters" in ev:
            first.setdefault(n, ev["voters"])
            conf[n] = (ev["voters"], ev["outgoing"])
            c["member: boot from a snapshot with voters a change made"] += conf[n] != (first[n], [])
        if e == "boot":
            if queued[n]:
                c["boot: restart with writes waiting"] += 1
            queued[n] = 0
            disk[n] = (ev["commit"], ev["lastIndex"])
            if ev.get("applied"):
                c["boot: from a snapshot"] += 1
            if n not in booted:
                c["boot: first"] += 1
            elif not wrote.get(n):
                c["boot: restart, nothing announced since the last send"] += 1
            elif (ev["term"], ev["vote"], ev["commit"]) == hs.get(n) and ev["lastIndex"] == last.get(n, 0):
                c["boot: restart, last write had happened"] += 1
            else:
                c["boot: restart, last write taken back"] += 1
            booted.add(n)
            hs[n] = (ev["term"], ev["vote"], ev["commit"])
            last[n] = ev["lastIndex"]
            role[n] = "follower"
            pend[n] = None
            wrote[n] = False
            applied_since_boot[n] = 0
        elif e == "recv":
            m = ev["msg"]
            pend[n] = m
            if m["type"] == "app":
                key = json.dumps(m, sort_keys=True)
                c["recv: request delivered again" if key in seen[n] else "recv: request"] += 1
                seen[n].add(key)
            elif m["type"] == "hb":
                c["recv: heartbeat"] += 1
            else:
                c["recv: other"] += 1
        elif e == "write":
            c["write: made later"] += 1
            if queued[n] > 1:
                c["write: several waiting"] += 1
            if ev["term"] < hs.get(n, (0, "", 0))[0]:
                c["write: after the node has moved on to a later term"] += 1
            queued[n] = max(0, queued[n] - 1)
            d = disk.get(n, (0, 0))
            dl = ev["snap"]["index"] if "snap" in ev else (ev["first"] - 1 + len(ev["entries"]) if ev["entries"] else d[1])
            disk[n] = (ev["commit"], dl)
        elif e == "flush":
            c["flush"] += 1
            c["flush: one more input in the same write"] += ev["more"]
            batch[n] = batch.get(n, 0) * ev["more"] + 1
            queued[n] = max(0, queued[n] - 1)
        elif e == "net":
            if batch.get(n, 0) > 1:
                c["net: a write for several inputs"] += 1
            if not ev["entries"] and (ev["term"], ev["vote"], ev["commit"]) == dhs.get(n):
                c["net: nothing to write"] += 1
            dhs[n] = (ev["term"], ev["vote"], ev["commit"])
            d = disk.get(n, (0, 0))
            disk[n] = (ev["commit"], ev["first"] - 1 + len(ev["entries"]) if ev["entries"] else d[1])
            last[n] = disk[n][1]
        elif e in ("wrote", "made", "snap", "restore", "readreq", "read"):
            if e not in ("wrote", "made"):
                c[e] += 1
        elif e in ("ready", "mem"):
            if "snap" in ev:
                c["log replaced by a snapshot"] += 1
            if e == "mem":
                queued[n] += ev.get("w", 0)
                if ev["role"] == "leader" and ev["commit"] > disk.get(n, (0, 0))[1]:
                    c["mem: leader commits what is not on its own disk"] += 1
            t0, v0, c0 = hs.get(n, (0, "", 0))
            r0 = role.get(n, "follower")
            l0 = last.get(n, 0)
            m = pend.get(n) if ev["by"] == "recv" else None
            t1, v1, c1, r1 = ev["term"], ev["vote"], ev["commit"], ev["role"]
            # A node that batches does not say what a follower stored, or
            # where a leader's entries go.
            es = ev.get("entries", [])
            if "first" not in ev:
                ev = dict(ev, first=l0 + 1)
            if m and m["type"] == "timeoutnow" and t1 != t0 and r1 == "candidate":
                c["ready: election started because the leader said so"] += 1
            if m and m["type"] == "prop" and r1 == "leader" and es:
                c["ready: leader appends what a follower passed on"] += 1
            write = (t1, v1, c1) != (t0, v0, c0) or es
            if t1 != t0 and ev["by"] in ("tick", "campaign"):
                c["ready: election started"] += 1
                if r0 == "candidate":
                    c["ready: election started again by a candidate"] += 1
            elif t1 != t0:
                c["ready: later term adopted"] += 1
                if r0 == "leader":
                    c["ready: later term adopted by a leader"] += 1
                if v1:
                    c["ready: term adopted and vote in one write"] += 1
            if v1 and v1 != n and (v1 != v0 or t1 != t0):
                c["ready: vote for another"] += 1
            if r1 == "leader" and r0 != "leader":
                c["ready: becomes leader"] += 1
            if r1 == "follower" and r0 == "candidate":
                c["ready: candidate becomes follower"] += 1
            if r1 == "follower" and r0 == "leader":
                c["ready: leader becomes follower"] += 1
            if es:
                if r1 == "leader":
                    c["ready: leader stores"] += 1
                else:
                    c["ready: follower stores"] += 1
                    if len(es) > 1:
                        c["ready: follower stores several entries"] += 1
                    if ev["first"] <= l0:
                        c["ready: follower deletes a suffix"] += 1
                    if m and ev["first"] > m["index"] + 1:
                        c["ready: follower stores part of a request"] += 1
                last[n] = ev["first"] - 1 + len(es)
            if c1 != c0:
                if r1 == "leader":
                    c["ready: leader commits"] += 1
                elif m and m["type"] == "hb":
                    c["ready: follower commits on a heartbeat"] += 1
                else:
                    c["ready: follower commits on a request"] += 1
                    if not es:
                        c["ready: follower commits on a request it stores nothing of"] += 1
                if es:
                    c["ready: stores and commits in one write"] += 1
            if not write:
                c["ready: role only, no write"] += 1
            hs[n], role[n] = (t1, v1, c1), r1
            wrote[n] = bool(write)
            if e == "ready":
                disk[n] = (c1, last.get(n, 0))
        elif e == "send":
            wrote[n] = False
            s = ev["msg"]
            ty = s["type"]
            if ty == "vote":
                c["send: vote"] += 1
            elif ty == "voteresp":
                if s["reject"]:
                    c["send: vote refused"] += 1
                else:
                    key = (n, s["to"], s["term"])
                    c["send: vote granted again" if key in granted else "send: vote granted"] += 1
                    granted.add(key)
            elif ty == "app":
                c["send: request"] += 1
                if s["index"] + len(s["entries"]) > disk.get(n, (0, 0))[1]:
                    c["send: request for entries not on the leader's disk"] += 1
                if len(s["entries"]) > 1:
                    c["send: request, several entries"] += 1
                if not s["entries"]:
                    c["send: request, no entries"] += 1
            elif ty == "hb":
                c["send: heartbeat"] += 1
                if s["commit"]:
                    c["send: heartbeat with a commit index"] += 1
            elif ty == "appresp":
                m = pend.get(n)
                if s["reject"]:
                    c["send: request refused"] += 1
                elif m and s["index"] != m["index"] + len(m["entries"]):
                    c["send: acknowledgement of the commit index (AckCommitted)"] += 1
                else:
                    c["send: acknowledgement"] += 1
            elif ty == "hbresp":
                c["send: heartbeat answered"] += 1
            else:
                c["send: " + ty] += 1
        elif e == "apply":
            wrote[n] = False
            c["apply"] += 1
            if ev["first"] + len(ev["entries"]) - 1 > disk.get(n, (0, 0))[0]:
                c["apply: before the commit index is on disk"] += 1
            if ev["first"] == 1 and ev["by"] == "boot":
                c["apply: after a restart, from index 1"] += 1
            if len(ev["entries"]) > 1:
                c["apply: several entries"] += 1
        elif e != "conf":
            c["other: %s" % e] += 1
        c["events"] += 1


def main():
    files = []
    for a in sys.argv[1:]:
        if os.path.isdir(a):
            files += sorted(glob.glob(os.path.join(a, "*.ndjson")) + glob.glob(os.path.join(a, "kit", "stream.ndjson"))
                            + glob.glob(os.path.join(a, "*", "stream.ndjson")))
        else:
            files.append(a)
    files = [f for f in dict.fromkeys(files) if not f.endswith("again.ndjson") and os.path.basename(f)[:4] != "raft"]
    if not files:
        sys.exit(__doc__)
    c = collections.Counter()
    for f in files:
        cover(f, c)
    print("%d streams, %d events" % (len(files), c["events"]))
    for r in ROWS + LATER + sorted(k for k in c if k not in ROWS + LATER and k != "events"):
        print("%8d  %s" % (c[r], r))
    zero = [r for r in ROWS if c[r] == 0]
    if zero:
        print("not reached: " + "; ".join(zero))


if __name__ == "__main__":
    main()
