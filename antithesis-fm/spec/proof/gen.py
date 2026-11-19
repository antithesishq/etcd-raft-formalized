#!/usr/bin/env python3
"""Skeleton generator for per-action step lemmas.
usage: gen.py NAME 'HYPS' 'GOAL' 'USEDEFS' [k=PROOF ...]
Prints LEMMA NAME == ASSUME HYPS, ProtoCases PROVE GOAL with one step per action
(keys a..t of ACTS). A step's proof is BY <1>k DEF Action unless given as k=PROOF.
"""
import sys
ACTS = [
 ('a','NEW i \\in Server','BecomeCandidate(i)','BecomeCandidate'),
 ('b','NEW i \\in Server','BecomeFollower(i)','BecomeFollower'),
 ('c','NEW i \\in Server','BecomeLeader(i)','BecomeLeader'),
 ('d','NEW i \\in Server','StartElection(i)','StartElection'),
 ('e','NEW i \\in Server','Restart(i)','Restart'),
 ('f','NEW i \\in Server','Apply(i)','Apply'),
 ('g','NEW i \\in Server, NEW a \\in 0..Len(log[i])','Restore(i, a)','Restore'),
 ('h','NEW i \\in Server, NEW k \\in 1..Len(log[i])','SwitchConf(i, k)','SwitchConf'),
 ('i','NEW i \\in Server, NEW c \\in commits, NEW a \\in 0..Len(c.entries)','RestoreConf(i, c, a)','RestoreConf'),
 ('j','NEW i \\in Server, NEW e \\in EntryT','LeaderAppend1(i, e)','LeaderAppend1'),
 ('k','NEW i \\in Server, NEW t \\in Nat','AdoptTerm(i, t)','AdoptTerm'),
 ('l','NEW i \\in Server, NEW c \\in Server','CastVote(i, c)','CastVote'),
 ('m','NEW i \\in Server, NEW c \\in Server, NEW t \\in Nat','GrantVote(i, c, t)','GrantVote'),
 ('n','NEW i \\in Server, NEW t \\in Nat, NEW c \\in Nat','LeaderCommit(i, t, c)','LeaderCommit'),
 ('o','NEW i \\in Server, NEW j \\in Server, NEW t \\in Nat, NEW p \\in Nat, NEW n \\in Nat, NEW c \\in Nat','SendAppend(i, j, t, p, n, c)','SendAppend'),
 ('p','NEW j \\in Server, NEW m \\in msgs, m \\in AppendT','Ack(j, m)','Ack'),
 ('q','NEW j \\in Server, NEW m \\in msgs, m \\in AppendT','AckCommitted(j, m)','AckCommitted'),
 ('r','NEW j \\in Server, NEW m \\in msgs, NEW k \\in 1..Len(m.entries), m \\in AppendT','DeleteSuffix(j, m, k)','DeleteSuffix'),
 ('s','NEW j \\in Server, NEW m \\in msgs, NEW k \\in 1..Len(m.entries), m \\in AppendT','StoreEntries(j, m, k)','StoreEntries'),
 ('t','NEW j \\in Server, NEW m \\in msgs, NEW c \\in Nat, m \\in AppendT','FollowerCommit(j, m, c)','FollowerCommit'),
]
def lemma(name, hyps, goal, usedefs, custom=None, lvl=1):
    custom = custom or {}
    out = [f"LEMMA {name} ==", f"  ASSUME {hyps}, ProtoCases", f"  PROVE  {goal}"]
    if usedefs: out.append(f"<{lvl}> USE DEF {usedefs}")
    for k, params, call, d in ACTS:
        st = f"<{lvl}>{k}"
        out.append(f"{st}. ASSUME {params}, {call} PROVE {goal}")
        if k in custom:
            out.append(custom[k].rstrip("\n"))
        else:
            out.append(f"  BY {st} DEF {d}")
    out.append(f"<{lvl}> QED BY " + ", ".join(f"<{lvl}>{k}" for k,_,_,_ in ACTS) + " DEF ProtoCases")
    return "\n".join(out) + "\n"
if __name__ == '__main__':
    name, hyps, goal, defs = sys.argv[1:5]
    custom = {}
    for a in sys.argv[5:]:
        k, v = a.split('=', 1); custom[k] = v
    print(lemma(name, hyps, goal, defs, custom))
