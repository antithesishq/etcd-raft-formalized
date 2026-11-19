#!/usr/bin/env python3
"""Make a non-conforming copy of an accepted stream.

    mutate.py NAME SRC_STREAM DST_STREAM
    mutate.py list

Each mutation is a behaviour the model must not allow; the stream check is
trusted only if it rejects every one (scripts/validator-tests.sh). Prints the
index (from 1) of the first event that differs from the source: the check
must stop there or later, never before. Exits 3 if the source has no place
for the mutation.
"""
import copy
import json
import sys


def find(L, pred, skip=0):
    for k, e in enumerate(L):
        if pred(k, e):
            if skip == 0:
                return k
            skip -= 1
    raise LookupError


def is_ready(e, **kw):
    return e["e"] == "ready" and all(e.get(a) == b for a, b in kw.items())


def is_send(e, ty, **kw):
    return e["e"] == "send" and e["msg"]["type"] == ty and all(e["msg"].get(a) == b for a, b in kw.items())


def track(L):
    """Per event: the node's (term, vote, commit, role, last index) before it."""
    st, out = {}, []
    for e in L:
        n = e["node"]
        s = st.setdefault(n, dict(term=0, vote="", commit=0, role="follower", last=0))
        out.append(dict(s))
        if e["e"] == "boot":
            s.update(term=e["term"], vote=e["vote"], commit=e["commit"], role="follower", last=e["lastIndex"])
        elif e["e"] == "ready":
            s.update(term=e["term"], vote=e["vote"], commit=e["commit"], role=e["role"])
            if e["entries"]:
                s["last"] = e["first"] - 1 + len(e["entries"])
    return out


def follower_store(L, pre):
    """A follower's write of entries that it goes on to acknowledge."""
    return find(L, lambda k, e: is_ready(e, by="recv") and e["role"] == "follower" and e["entries"]
                and k + 1 < len(L) and L[k + 1]["node"] == e["node"] and is_send(L[k + 1], "appresp", reject=False))


def m_commit_ahead(L, pre):
    "A follower commits one entry past what it was told."
    k = find(L, lambda k, e: is_ready(e, role="follower") and e["commit"] > pre[k]["commit"]
             and L[k - 1]["e"] == "recv" and L[k - 1]["msg"]["commit"] == e["commit"])
    L[k]["commit"] += 1
    return k


def m_leader_commits_early(L, pre):
    "A leader commits an entry as it stores it."
    k = find(L, lambda k, e: is_ready(e, role="leader", by="propose") and e["entries"])
    L[k]["commit"] = L[k]["first"]
    return k


def m_term_back(L, pre):
    "A node's term goes down."
    k = find(L, lambda k, e: is_ready(e) and pre[k]["term"] >= 2 and e["term"] == pre[k]["term"], 3)
    L[k]["term"] -= 1
    return k


def m_vote_changed(L, pre):
    "A node that has voted in its term votes for another."
    k = find(L, lambda k, e: is_ready(e) and e["term"] == pre[k]["term"] and pre[k]["vote"] not in ("", e["node"]))
    L[k]["vote"] = L[k]["node"]
    return k


def m_vote_unasked(L, pre):
    "A node votes for a node that did not ask."
    k = find(L, lambda k, e: is_ready(e, by="recv") and e["vote"] not in ("", e["node"]) and
             (e["vote"] != pre[k]["vote"] or e["term"] != pre[k]["term"]))
    others = [x for x in ("raft1", "raft2", "raft3") if x not in (L[k]["node"], L[k]["vote"])]
    L[k]["vote"] = others[0]
    return k


def m_vote_request_altered(L, pre):
    "A node votes on a request for votes that its candidate did not make."
    k = find(L, lambda k, e: is_ready(e, by="recv") and e["vote"] not in ("", e["node"]) and
             (e["vote"] != pre[k]["vote"] or e["term"] != pre[k]["term"]))
    L[k - 1]["msg"]["index"] += 3
    return k - 1


def m_entry_altered(L, pre):
    "A follower stores an entry that is not the one it was sent."
    k = follower_store(L, pre)
    L[k]["entries"][0]["value"] = "ff"
    return k


def m_store_gap(L, pre):
    "A follower stores entries one index too far."
    k = follower_store(L, pre)
    L[k]["first"] += 1
    return k


def m_store_dropped(L, pre):
    "A follower acknowledges entries it did not store."
    k = follower_store(L, pre)
    del L[k]
    return k


def m_leader_entry_old_term(L, pre):
    "A leader stores an entry of another term."
    k = find(L, lambda k, e: is_ready(e, role="leader", by="propose") and e["entries"])
    L[k]["entries"][0]["term"] -= 1
    return k


def m_follower_stores_unsent(L, pre):
    "A node that leads nothing stores entries nobody sent it."
    k = find(L, lambda k, e: is_ready(e, role="leader", by="propose") and e["entries"])
    L[k]["role"] = "follower"
    return k


def m_ack_too_far(L, pre):
    "A follower acknowledges one entry more than the request held."
    k = find(L, lambda k, e: is_send(e, "appresp", reject=False))
    L[k]["msg"]["index"] += 1
    return k


def m_grant_without_vote(L, pre):
    "A node grants a vote it refused."
    k = find(L, lambda k, e: is_send(e, "voteresp", reject=True))
    L[k]["msg"]["reject"] = False
    return k


def m_leader_without_quorum(L, pre):
    "A candidate becomes leader with its own vote only."
    k = find(L, lambda k, e: is_ready(e, role="candidate") and e["by"] in ("tick", "campaign"))
    e = L[k]
    win = dict(e, by="campaign", role="leader", first=pre[k]["last"] + 1,
               entries=[{"term": e["term"], "type": "noop", "value": ""}])
    L.insert(k + 1, win)
    return k + 1


def m_second_leader(L, pre):
    "A second node becomes leader in a term that has one."
    k = find(L, lambda k, e: is_ready(e, role="leader") and pre[k]["role"] != "leader")
    e = L[k]
    other = [x for x in ("raft1", "raft2", "raft3") if x != e["node"]][0]
    j = find(L, lambda j, x: j > k and x["node"] == other and x["e"] in ("ready", "send", "recv"))
    p = track(L)[j]
    if p["term"] > e["term"]:
        raise LookupError
    L.insert(j, {"e": "ready", "node": other, "by": "campaign", "role": "leader", "term": e["term"],
                 "vote": p["vote"] if p["term"] == e["term"] else "", "commit": p["commit"],
                 "first": p["last"] + 1, "entries": [{"term": e["term"], "type": "noop", "value": ""}]})
    return j


def m_send_entry_not_in_log(L, pre):
    "A leader sends an entry it does not hold."
    k = find(L, lambda k, e: is_send(e, "app") and e["msg"]["entries"])
    L[k]["msg"]["entries"][0]["value"] = "ff"
    return k


def m_send_wrong_prev_term(L, pre):
    "A leader sends a request with the wrong term for the entry before it."
    k = find(L, lambda k, e: is_send(e, "app") and e["msg"]["index"] > 0)
    L[k]["msg"]["logTerm"] += 1
    return k


def m_send_commit_ahead(L, pre):
    "A leader sends a commit index nothing has committed."
    k = find(L, lambda k, e: is_send(e, "app") and e["msg"]["entries"])
    L[k]["msg"]["commit"] = L[k]["msg"]["index"] + len(L[k]["msg"]["entries"])
    if L[k]["msg"]["commit"] <= pre[k]["commit"]:
        raise LookupError
    return k


def m_heartbeat_commit_ahead(L, pre):
    "A follower is handed a heartbeat with a commit index nothing has committed."
    k = find(L, lambda k, e: e["e"] == "recv" and e["msg"]["type"] == "hb")
    L[k]["msg"]["commit"] += 40
    return k


def m_request_never_sent(L, pre):
    "A follower is handed a request that is no part of its leader's log."
    k = find(L, lambda k, e: e["e"] == "recv" and e["msg"]["type"] == "app" and e["msg"]["entries"])
    L[k]["msg"]["entries"][0]["value"] = "ff"
    return k


def m_not_leader_sends(L, pre):
    "A node sends a request in a term it does not lead."
    k = find(L, lambda k, e: is_send(e, "hb"))
    other = [x for x in ("raft1", "raft2", "raft3") if x not in (L[k]["node"], L[k]["msg"]["to"])][0]
    L[k]["node"] = L[k]["msg"]["from"] = other
    return k


def m_apply_skips(L, pre):
    "A node passes over an entry when it applies."
    k = find(L, lambda k, e: e["e"] == "apply" and len(e["entries"]) > 1)
    L[k]["first"] += 1
    L[k]["entries"] = L[k]["entries"][1:]
    return k


def m_apply_altered(L, pre):
    "A node applies an entry that is not the one in its log."
    k = find(L, lambda k, e: e["e"] == "apply")
    L[k]["entries"][0] = {"term": L[k]["entries"][0]["term"], "type": "command", "value": "ff"}
    return k


def m_apply_uncommitted(L, pre):
    "A node applies an entry it has not committed."
    k = find(L, lambda k, e: is_ready(e, role="leader", by="propose") and e["entries"]
             and pre[k]["commit"] + 1 == e["first"] and pre[k]["role"] == "leader")
    e = L[k]
    L.insert(k + 1, {"e": "apply", "node": e["node"], "by": "propose", "first": e["first"],
                     "entries": copy.deepcopy(e["entries"])})
    return k + 1


def restart(L, pre, skip=0):
    return find(L, lambda k, e: e["e"] == "boot" and (pre[k]["term"] > 0) and
                (e["term"], e["vote"], e["commit"], e["lastIndex"]) ==
                (pre[k]["term"], pre[k]["vote"], pre[k]["commit"], pre[k]["last"]) and e["lastIndex"] > 1, skip)


def m_boot_lost_entry(L, pre):
    "A restarted node has lost the last entry of its log."
    k = restart(L, pre)
    L[k]["lastIndex"] -= 2
    return k


def m_boot_lost_term(L, pre):
    "A restarted node is in an earlier term."
    k = restart(L, pre)
    L[k]["term"] -= 1
    return k


def m_boot_lost_vote(L, pre):
    "A restarted node has forgotten its vote."
    k = find(L, lambda k, e: e["e"] == "boot" and e["vote"] != "" and
             (e["term"], e["vote"]) == (pre[k]["term"], pre[k]["vote"]))
    L[k]["vote"] = ""
    return k


def m_boot_lost_commit(L, pre):
    "A restarted node's commit index went down."
    k = find(L, lambda k, e: e["e"] == "boot" and e["commit"] > 2 and e["commit"] == pre[k]["commit"])
    L[k]["commit"] -= 2
    return k


def m_gap(L, pre):
    "The stream has a hole."
    k = len(L) // 2
    L.insert(k, {"e": "Gap", "node": L[k]["node"], "expected": 5, "got": 6})
    return k


# Streams of nodes whose writes are made later (`mem`, `write`, `wrote`).

def is_ev(e, name, **kw):
    return e["e"] == name and all(e.get(a) == b for a, b in kw.items())


def later_of(L, k, pred):
    """The first event after k of the same node that satisfies pred, before the node restarts."""
    n = L[k]["node"]
    for j in range(k + 1, len(L)):
        if L[j]["node"] != n:
            continue
        if L[j]["e"] == "boot":
            break
        if pred(L[j]):
            return j
    raise LookupError


def follower_write(L, skip=0):
    """A write of entries a follower was sent, and the acknowledgement that waited for it."""
    def ok(k, e):
        if not (is_ev(e, "write") and e["entries"]):
            return False
        try:
            j = later_of(L, k, lambda x: x["e"] in ("write", "send"))
        except LookupError:
            return False
        return L[j]["e"] == "send" and L[j]["msg"]["type"] == "appresp" and not L[j]["msg"]["reject"] \
            and "cause" in L[j] and L[j]["cause"]
    k = find(L, ok, skip)
    return k, later_of(L, k, lambda x: x["e"] == "send")


def m_write_skipped(L, pre):
    "A node's write is not made, and it goes on as if it was."
    k, _ = follower_write(L)
    j = later_of(L, k, lambda x: x["e"] == "wrote")
    del L[j]
    del L[k]
    return k


def m_write_out_of_order(L, pre):
    "A node makes a later write before an earlier one."
    def ok(k, e):
        if not is_ev(e, "write"):
            return False
        try:
            j = later_of(L, k, lambda x: x["e"] not in ("wrote", "recv"))
        except LookupError:
            return False
        return L[j]["e"] == "write" and any(L[j][f] != e[f] for f in ("term", "vote", "commit", "first", "entries"))
    k = find(L, ok)
    j = later_of(L, k, lambda x: x["e"] == "write")
    for f in ("term", "vote", "commit", "first", "entries"):
        L[k][f], L[j][f] = L[j][f], L[k][f]
    return k


def m_ack_before_write(L, pre):
    "A follower acknowledges entries before it has written them."
    k, j = follower_write(L)
    L.insert(k, L.pop(j))
    return k


def m_vote_request_before_write(L, pre):
    "A candidate asks for votes before its new term is on its disk (patches/README.md, E1)."
    k = find(L, lambda k, e: is_ev(e, "mem", role="candidate", w=1))
    j = later_of(L, k, lambda x: x["e"] == "send" and x["msg"]["type"] == "vote")
    w = later_of(L, k, lambda x: x["e"] == "write")
    if not w < j:
        raise LookupError
    L.insert(k + 1, L.pop(j))
    return k + 1


def m_leader_commits_alone(L, pre):
    "A leader takes an entry for committed as it adds it to its log, before anyone has it on disk."
    k = find(L, lambda k, e: is_ev(e, "mem", role="leader", by="propose") and e["entries"])
    L[k]["commit"] = L[k]["first"]
    return k


def m_apply_before_stored(L, pre):
    "A node hands its state machine an entry that is not on its disk yet."
    def ok(k, e):
        if not (is_ev(e, "write") and e["entries"]):
            return False
        try:
            j = later_of(L, k, lambda x: x["e"] == "apply")
        except LookupError:
            return False
        return L[j]["first"] + len(L[j]["entries"]) - 1 >= e["first"]
    k = find(L, ok)
    j = later_of(L, k, lambda x: x["e"] == "apply")
    L.insert(k, L.pop(j))
    return k


def m_write_altered(L, pre):
    "A write is not of what the node said it would write."
    k, _ = follower_write(L, 1)
    L[k]["entries"][0]["term"] += 1
    return k


def m_write_twice(L, pre):
    "A write that no report said was coming."
    k, _ = follower_write(L)
    j = later_of(L, k, lambda x: x["e"] == "wrote")
    L.insert(j + 1, copy.deepcopy(L[k]))
    return j + 1


# Streams with snapshots and read indexes.

def m_restore_ahead(L, pre):
    "A state machine is replaced by a snapshot of more than the node's log holds."
    k = find(L, lambda k, e: is_ev(e, "restore"))
    L[k]["index"] += 1
    return k


def m_snapshot_of_unapplied(L, pre):
    "A node puts a snapshot in place of entries its state machine has not reached."
    k = find(L, lambda k, e: is_ev(e, "snap"))
    L[k]["index"] += 1000
    return k


def m_snapshot_message_altered(L, pre):
    "A leader sends a snapshot that is not of its log."
    k = find(L, lambda k, e: is_send(e, "snap"))
    L[k]["msg"]["logTerm"] += 1
    return k


def m_read_index_stale(L, pre):
    "A read index that does not cover what was committed when the read was asked for."
    asked = {}
    commit = 0
    def ok(k, e):
        nonlocal commit
        if e["e"] in ("ready", "mem") and e["role"] == "leader":
            commit = max(commit, e["commit"])
        if e["e"] == "readreq":
            asked[(e["node"], e["ctx"])] = commit
        return e["e"] == "read" and asked.get((e["node"], e["ctx"]), 0) >= 2
    k = find(L, ok)
    L[k]["index"] = 1
    return k


# Streams of nodes that take one Ready for several inputs (`mem` after each
# input, then `flush`, `net`, `made`, the messages, `wrote`).

def batch_write(L, pred, skip=0):
    """A `net` that satisfies pred, with the index of its `made`."""
    def ok(k, e):
        if not (is_ev(e, "net") and pred(k, e)):
            return False
        try:
            return L[later_of(L, k, lambda x: True)]["e"] == "made"
        except LookupError:
            return False
    k = find(L, ok, skip)
    return k, later_of(L, k, lambda x: x["e"] == "made")


def m_batch_write_altered(L, pre):
    "A batching node writes an entry that none of its reports said it had."
    k, _ = batch_write(L, lambda k, e: e["entries"], 2)
    L[k]["entries"][0]["term"] += 1
    return k


def m_batch_write_short(L, pre):
    "A batching node writes fewer entries than its reports said it had."
    k, _ = batch_write(L, lambda k, e: len(e["entries"]) >= 2)
    L[k]["entries"].pop()
    return k


def m_batch_write_commit_ahead(L, pre):
    "A batching node writes a commit index beyond what its reports said."
    k, _ = batch_write(L, lambda k, e: True, 5)
    L[k]["commit"] += 1
    return k


def m_batch_flush_missing(L, pre):
    "A batching node leaves a change of term out of its write."
    def ok(k, e):
        if not (is_ev(e, "mem", w=1) and "first" not in e):
            return False
        try:
            j = later_of(L, k, lambda x: x["e"] in ("flush", "net", "mem"))
        except LookupError:
            return False
        return L[j]["e"] == "flush" and e["term"] > pre_term(L, k)
    k = find(L, ok, 3)
    j = later_of(L, k, lambda x: x["e"] == "flush")
    # The flush that follows takes this one's place; the last one is gone.
    n = later_of(L, j, lambda x: x["e"] == "net")
    last = max(i for i in range(j, n) if L[i]["node"] == L[k]["node"] and L[i]["e"] == "flush")
    del L[last]
    return last


def pre_term(L, k):
    n = L[k]["node"]
    for j in range(k - 1, -1, -1):
        if L[j]["node"] == n and L[j]["e"] in ("mem", "ready", "boot", "net"):
            return L[j]["term"]
    return 0


def m_batch_send_before_made(L, pre):
    "A batching node grants a vote before the write that records it is on disk."
    def ok(k, e):
        if not (e["e"] == "send" and "b" in e and e["msg"]["type"] == "voteresp" and not e["msg"]["reject"]):
            return False
        for j in range(k - 1, -1, -1):
            if L[j]["node"] == e["node"]:
                return L[j]["e"] == "made"
        return False
    k = find(L, ok)
    j = max(i for i in range(k) if L[i]["node"] == L[k]["node"])   # its `made`
    L.insert(j, L.pop(k))
    return j


def m_batch_ack_too_far(L, pre):
    "A batching follower acknowledges one entry more than the request held."
    k = find(L, lambda k, e: e["e"] == "send" and "b" in e and e["msg"]["type"] == "appresp"
             and not e["msg"]["reject"] and e["msg"]["index"] > 0, 3)
    L[k]["msg"]["index"] += 1
    return k


def m_batch_vote_unasked(L, pre):
    "A batching node votes for a node that did not ask."
    k = find(L, lambda k, e: is_ev(e, "mem", by="recv", role="follower", w=1) and "first" not in e
             and e["vote"] and L[k - 1]["e"] == "recv" and L[k - 1]["msg"]["type"] == "vote"
             and L[k - 1]["msg"]["from"] == e["vote"])
    others = sorted({x["node"] for x in L} - {L[k]["node"], L[k]["vote"]})
    L[k]["vote"] = others[0]
    return k


def m_batch_append_unreported(L, pre):
    "A batching leader writes an entry that it did not report appending."
    def ok(k, e):
        if not (is_ev(e, "mem", by="propose", role="leader", w=1) and "first" not in e and e["entries"]):
            return False
        try:   # and goes on to write it
            j = later_of(L, k, lambda x: x["e"] == "net")
        except LookupError:
            return False
        return bool(L[j]["entries"])
    k = find(L, ok, 1)
    L[k]["entries"] = []
    return k


def conf_events(L):
    "Indexes of `conf` reports that follow their node's `apply` of the entry directly or soon."
    return [k for k, e in enumerate(L) if e["e"] == "conf"]


def leader_change(L, pred=lambda v: True, skip=0):
    "A leader's report of appending a change of membership: (event index, entry index)."
    def ok(k, e):
        return (e["e"] in ("ready", "mem") and e.get("role") == "leader" and
                any(x["type"] == "conf" and pred(x["value"]) for x in e.get("entries", [])))
    k = find(L, ok, skip)
    j = next(j for j, x in enumerate(L[k]["entries"]) if x["type"] == "conf" and pred(x["value"]))
    return k, j


def m_conf_voters_altered(L, pre):
    "Raft counts with a voter that the change did not add."
    k = find(L, lambda k, e: e["e"] == "conf")
    spare = [x for x in ("raft1", "raft2", "raft3", "raft4", "raft5") if x not in L[k]["voters"]]
    if spare:
        L[k]["voters"] = sorted(L[k]["voters"] + spare[:1])
    else:
        L[k]["voters"] = L[k]["voters"][1:]
    return k


def m_conf_outgoing_dropped(L, pre):
    "After a joint change raft does not count with the voters it had before."
    k = find(L, lambda k, e: e["e"] == "conf" and e["outgoing"])
    L[k]["outgoing"] = []
    return k


def m_conf_wrong_entry(L, pre):
    "Raft is told that an entry that is no change of membership is one."
    k = find(L, lambda k, e: e["e"] == "conf" and L[k - 1]["e"] == "apply" and L[k - 1]["node"] == e["node"]
             and len(L[k - 1]["entries"]) > 1 and L[k - 1]["entries"][0]["type"] != "conf")
    L[k]["index"] = L[k - 1]["first"]
    return k


def m_conf_before_apply(L, pre):
    "Raft is told of a change before the node has handed it to its state machine."
    k = find(L, lambda k, e: e["e"] == "conf" and L[k - 1]["e"] == "apply" and L[k - 1]["node"] == e["node"]
             and L[k - 1]["first"] + len(L[k - 1]["entries"]) - 1 == e["index"])
    L[k - 1], L[k] = L[k], L[k - 1]
    return k - 1


def m_conf_skipped(L, pre):
    "A node applies a second change without having told raft of the first."
    n = {}
    for k, e in enumerate(L):
        if e["e"] == "boot":
            n.pop(e["node"], None)
        elif e["e"] == "conf":
            if e["node"] in n and n[e["node"]][1] < e["index"]:
                del L[n[e["node"]][0]]
                return n[e["node"]][0]
            n[e["node"]] = (k, e["index"])
    raise LookupError


def m_second_change_appended(L, pre):
    "A leader appends a change of membership right after another, which it has not applied."
    k, j = leader_change(L, lambda v: not v["leave"])
    e = L[k]
    e["entries"].insert(j + 1, copy.deepcopy(e["entries"][j]))
    return k


def m_change_of_two_voters(L, pre):
    "A leader appends a change of one step that adds two voters."
    k, j = leader_change(L, lambda v: not v["leave"] and not v["joint"] and len(v["add"]) == 1)
    v = L[k]["entries"][j]["value"]
    other = [x for x in ("raft1", "raft2", "raft3", "raft4", "raft5") if x not in v["add"]]
    v["add"] = sorted(v["add"] + other[-2:])
    return k


def m_leave_not_joint(L, pre):
    "A leader appends a change that leaves a joint configuration it is not in."
    k, j = leader_change(L, lambda v: not v["leave"] and not v["joint"])
    L[k]["entries"][j]["value"] = {"add": [], "remove": [], "joint": False, "leave": True}
    return k


def m_joint_in_joint(L, pre):
    "A leader in a joint configuration appends a change that is not the one that leaves it."
    k, j = leader_change(L, lambda v: v["leave"])
    L[k]["entries"][j]["value"] = {"add": ["raft1"], "remove": [], "joint": True, "leave": False}
    return k


def m_boot_first_voters(L, pre):
    "A node restarts from a snapshot with the voters of the start, not the snapshot's."
    k = find(L, lambda k, e: e["e"] == "boot" and e["applied"] > 0 and e["voters"] != ["raft1", "raft2", "raft3"])
    L[k]["voters"] = ["raft1", "raft2", "raft3"]
    return k


def m_restore_voters_altered(L, pre):
    "A snapshot a leader sent holds voters its entries do not make."
    k = find(L, lambda k, e: e["e"] == "restore" and len(e["voters"]) > 1)
    L[k]["voters"] = L[k]["voters"][1:]
    return k


MUTATIONS = {
    "commit-ahead": m_commit_ahead,
    "leader-commits-early": m_leader_commits_early,
    "term-back": m_term_back,
    "vote-changed": m_vote_changed,
    "vote-unasked": m_vote_unasked,
    "vote-request-altered": m_vote_request_altered,
    "entry-altered": m_entry_altered,
    "store-gap": m_store_gap,
    "store-dropped": m_store_dropped,
    "leader-entry-old-term": m_leader_entry_old_term,
    "follower-stores-unsent": m_follower_stores_unsent,
    "ack-too-far": m_ack_too_far,
    "grant-without-vote": m_grant_without_vote,
    "leader-without-quorum": m_leader_without_quorum,
    "second-leader": m_second_leader,
    "send-entry-not-in-log": m_send_entry_not_in_log,
    "send-wrong-prev-term": m_send_wrong_prev_term,
    "send-commit-ahead": m_send_commit_ahead,
    "heartbeat-commit-ahead": m_heartbeat_commit_ahead,
    "request-never-sent": m_request_never_sent,
    "not-leader-sends": m_not_leader_sends,
    "apply-skips": m_apply_skips,
    "apply-altered": m_apply_altered,
    "apply-uncommitted": m_apply_uncommitted,
    "boot-lost-entry": m_boot_lost_entry,
    "boot-lost-term": m_boot_lost_term,
    "boot-lost-vote": m_boot_lost_vote,
    "boot-lost-commit": m_boot_lost_commit,
    "gap": m_gap,
    "write-skipped": m_write_skipped,
    "write-out-of-order": m_write_out_of_order,
    "ack-before-write": m_ack_before_write,
    "vote-request-before-write": m_vote_request_before_write,
    "leader-commits-alone": m_leader_commits_alone,
    "apply-before-stored": m_apply_before_stored,
    "write-altered": m_write_altered,
    "write-twice": m_write_twice,
    "restore-ahead": m_restore_ahead,
    "snapshot-of-unapplied": m_snapshot_of_unapplied,
    "snapshot-message-altered": m_snapshot_message_altered,
    "read-index-stale": m_read_index_stale,
    "batch-write-altered": m_batch_write_altered,
    "batch-write-short": m_batch_write_short,
    "batch-write-commit-ahead": m_batch_write_commit_ahead,
    "batch-flush-missing": m_batch_flush_missing,
    "batch-send-before-made": m_batch_send_before_made,
    "batch-ack-too-far": m_batch_ack_too_far,
    "batch-vote-unasked": m_batch_vote_unasked,
    "batch-append-unreported": m_batch_append_unreported,
    "conf-voters-altered": m_conf_voters_altered,
    "conf-outgoing-dropped": m_conf_outgoing_dropped,
    "conf-wrong-entry": m_conf_wrong_entry,
    "conf-before-apply": m_conf_before_apply,
    "conf-skipped": m_conf_skipped,
    "second-change-appended": m_second_change_appended,
    "change-of-two-voters": m_change_of_two_voters,
    "leave-not-joint": m_leave_not_joint,
    "joint-in-joint": m_joint_in_joint,
    "boot-first-voters": m_boot_first_voters,
    "restore-voters-altered": m_restore_voters_altered,
}


def main():
    if len(sys.argv) == 2 and sys.argv[1] == "list":
        print("\n".join(MUTATIONS))
        return
    if len(sys.argv) != 4 or sys.argv[1] not in MUTATIONS:
        sys.exit(__doc__)
    L = [json.loads(l) for l in open(sys.argv[2]) if l.strip()]
    try:
        k = MUTATIONS[sys.argv[1]](L, track(L))
    except LookupError:
        sys.exit(3)
    with open(sys.argv[3], "w") as f:
        for e in L:
            f.write(json.dumps(e) + "\n")
    print(k + 1)


if __name__ == "__main__":
    main()
