---- MODULE MCEtcd ----
\* Bounded instances of EtcdRaft for model checking. See ../scripts/mc.sh.
EXTENDS EtcdRaft, TLC

CONSTANTS MaxTerm, MaxLog, MaxBatch, MaxMsgs

Bounded ==
    /\ \A i \in Server : currentTerm[i] <= MaxTerm /\ Len(log[i]) <= MaxLog
    /\ \A t \in DOMAIN ledLog : Len(ledLog[t]) <= MaxLog
    /\ \A m \in msgs : m.type = "append" => Len(m.entries) <= MaxBatch
    /\ Cardinality(msgs) <= MaxMsgs

\* Initial voters are interchangeable, and so are the other nodes.
Symmetry == Permutations(InitVoters) \cup Permutations(Server \ InitVoters)

\* Membership changes offered (for ConfChanges): none; or add or remove one
\* voter, replace one jointly, and leave a joint configuration.
NoChanges(N) == {}
Change(a, r, j) == [add |-> a, remove |-> r, joint |-> j, leave |-> FALSE]
SmallChanges(N) ==
    {Change(<<s>>, <<>>, FALSE) : s \in N} \cup {Change(<<>>, <<s>>, FALSE) : s \in N}
    \cup {Change(<<x[1]>>, <<x[2]>>, TRUE) : x \in {y \in N \X N : y[1] # y[2]}}
    \cup {[add |-> <<>>, remove |-> <<>>, joint |-> FALSE, leave |-> TRUE]}
\* Only adding a node that is not an initial voter; the instance Veil's model
\* checker counts too (MCMemCount*.cfg, scripts/veil-count.sh m2).
OneChange(N) == {Change(<<s>>, <<>>, FALSE) : s \in N \ InitVoters}
\* Requests carry as many entries as MaxBatch allows and the highest allowed
\* commit index (a smaller request adds nothing a larger one does not).
MaxCommit(l, t) ==
    LET S == {c \in 0..Len(l) : CommittedIn(l, c, t)} IN CHOOSE c \in S : \A d \in S : d <= c

Sends(i) ==
    \E j \in Server, ld \in leaders :
        /\ ld.server = i
        /\ LET l == ledLog[ld.term] IN
           \E p \in 0..Len(l) :
              SendAppend(i, j, ld.term, p, Min(MaxBatch, Len(l) - p), MaxCommit(l, ld.term))

Receives ==
    \E m \in msgs :
          /\ m.type = "append"
          /\ \/ Ack(m.dst, m) \/ AckCommitted(m.dst, m)
             \/ \E k \in 1..Len(m.entries) : DeleteSuffix(m.dst, m, k) \/ StoreEntries(m.dst, m, k)
             \/ \E c \in 1..m.commit : FollowerCommit(m.dst, m, c)

\* Everything, with the restriction on requests above.
FullProto ==
    \/ \E i \in Server :
          \/ BecomeCandidate(i) \/ BecomeFollower(i) \/ BecomeLeader(i)
          \/ StartElection(i) \/ Restart(i) \/ Apply(i)
          \/ \E a \in 0..Len(log[i]) : Restore(i, a)
          \/ \E k \in 1..Len(log[i]) : SwitchConf(i, k)
          \/ \E c \in commits : \E a \in 0..Len(c.entries) : RestoreConf(i, c, a)
          \/ \E d \in ConfChanges(Server) : LeaderAppend(i, <<Entry(currentTerm[i], "conf", d)>>)
          \/ \E t \in {currentTerm[k] : k \in Server} : AdoptTerm(i, t)
          \/ \E c \in Server : CastVote(i, c)
          \/ \E v \in votes : v.voter = i /\ GrantVote(i, v.cand, v.term)
          \/ \E ty \in {"noop", "config"} : LeaderAppend(i, <<Entry(currentTerm[i], ty, Nil)>>)
          \/ \E v \in Values : LeaderAppend(i, <<Entry(currentTerm[i], "command", v)>>)
          \/ \E l \in leaders : l.server = i /\ \E c \in 1..Len(ledLog[l.term]) : LeaderCommit(i, l.term, c)
          \/ Sends(i)
    \/ Receives
FullNext == FullProto /\ UNCHANGED read
FullSpec == Init /\ [][FullNext]_rvars
\* The same with a read index followed.
FullReadSpec == Init /\ [][FullNext \/ ReadNext]_rvars

\* Without restarts.
QuietProto ==
    \/ \E i \in Server :
          \/ BecomeCandidate(i) \/ BecomeFollower(i) \/ BecomeLeader(i)
          \/ StartElection(i) \/ Apply(i)
          \/ \E a \in 0..Len(log[i]) : Restore(i, a)
          \/ \E k \in 1..Len(log[i]) : SwitchConf(i, k)
          \/ \E c \in commits : \E a \in 0..Len(c.entries) : RestoreConf(i, c, a)
          \/ \E d \in ConfChanges(Server) : LeaderAppend(i, <<Entry(currentTerm[i], "conf", d)>>)
          \/ \E t \in {currentTerm[k] : k \in Server} : AdoptTerm(i, t)
          \/ \E c \in Server : CastVote(i, c)
          \/ \E v \in votes : v.voter = i /\ GrantVote(i, v.cand, v.term)
          \/ \E ty \in {"noop", "config"} : LeaderAppend(i, <<Entry(currentTerm[i], ty, Nil)>>)
          \/ \E v \in Values : LeaderAppend(i, <<Entry(currentTerm[i], "command", v)>>)
          \/ \E l \in leaders : l.server = i /\ \E c \in 1..Len(ledLog[l.term]) : LeaderCommit(i, l.term, c)
          \/ Sends(i)
    \/ Receives
QuietNext == QuietProto /\ UNCHANGED read
QuietSpec == Init /\ [][QuietNext]_rvars

\* EtcdBinding's BootInit, before term 1's facts are forgotten. MCBoot.cfg
\* has TLC reach it.
Booted ==
    /\ \A s \in Server :
          /\ currentTerm[s] = 1 /\ voteTerm[s] = 1 /\ role[s] = Follower
          /\ log[s] = <<Entry(1, "config", Nil)>>
          /\ commitIndex[s] = 0 /\ lastApplied[s] = 0
          /\ confirmed[s] = [term |-> 1, index |-> 1]
    /\ \E f \in Server : /\ \A s \in Server : voteFor[s] = f
                         /\ leaders = {[server |-> f, term |-> 1]}
    /\ ledLog = (1 :> <<Entry(1, "config", Nil)>>)
    /\ commits = {} /\ applied = {}
NotBooted == ~Booted
====

