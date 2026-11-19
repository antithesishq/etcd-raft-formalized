---- MODULE EtcdInv ----
\* The inductive invariant of the TLAPS safety proofs. Definitions only, so
\* TLC can check them too (MCInv.tla).
EXTENDS EtcdRaft

\* a and b have at least k entries and agree on the first k.
Agree(a, b, k) == k <= Len(a) /\ k <= Len(b) /\ \A q \in 1..k : a[q] = b[q]
\* a is a prefix of b, pointwise.
Pre(a, b) == Agree(a, b, Len(a))

----
\* Types.
ETypes == {"noop", "config", "command", "conf"}
Vals == Values \cup {Nil} \cup ConfChanges(Server)
EntryT == {e \in [term : Nat, type : ETypes, value : Vals] :
              e.type = "conf" => e.value \in ConfChanges(Server)}
ConfT == [in : SUBSET Server, out : SUBSET Server]
VoteReqT == [type : {"vote"}, src : Server, term : Nat, lastLogIndex : Nat, lastLogTerm : Nat]
GrantT == [type : {"grant"}, src : Server, dst : Server, term : Nat]
AppendT == [type : {"append"}, src : Server, dst : Server, term : Nat,
            prevLogIndex : Nat, prevLogTerm : Nat, entries : Seq(EntryT), commit : Nat]
AckT == [type : {"ack"}, src : Server, dst : Server, term : Nat, index : Nat]
MsgT == VoteReqT \cup GrantT \cup AppendT \cup AckT
VoteT == [voter : Server, term : Nat, cand : Server]
LeaderT == [server : Server, term : Nat]
CommitT == [server : Server, term : Nat, entries : Seq(EntryT)]
AppliedT == [server : Server, index : Nat, entry : EntryT]
ReadT == [on : BOOLEAN, done : BOOLEAN, term : Nat, index : Nat,
          floor : SUBSET CommitT, msgs : SUBSET MsgT, resp : SUBSET Server]

\* What the proofs need of the constants (from ServerFinite and VotersOK:
\* ConstOKHolds, EtcdSafety.tla).
ConstOK == IsFiniteSet(Server) /\ InitVoters \subseteq Server

TypeOK ==
    /\ ConstOK
    /\ currentTerm \in [Server -> Nat]
    /\ voteTerm \in [Server -> Nat]
    /\ voteFor \in [Server -> Server \cup {Nil}]
    /\ log \in [Server -> Seq(EntryT)]
    /\ commitIndex \in [Server -> Nat]
    /\ lastApplied \in [Server -> Nat]
    /\ role \in [Server -> {Follower, Candidate, Leader}]
    /\ config \in [Server -> ConfT]
    /\ confAt \in [Server -> Nat]
    /\ confirmed \in [Server -> [term : Nat, index : Nat]]
    /\ msgs \subseteq MsgT
    /\ votes \subseteq VoteT
    /\ leaders \subseteq LeaderT
    /\ DOMAIN ledLog \subseteq Nat
    /\ \A t \in DOMAIN ledLog : ledLog[t] \in Seq(EntryT)
    /\ DOMAIN ledConf = DOMAIN ledLog
    /\ DOMAIN ledAt = DOMAIN ledLog
    /\ DOMAIN elAt = DOMAIN ledLog
    /\ \A t \in DOMAIN ledLog : ledConf[t] \in ConfT /\ ledAt[t] \in Nat /\ elAt[t] \in Nat
    /\ commits \subseteq CommitT
    /\ applied \subseteq AppliedT
    /\ read \in ReadT

----
\* Elections.
IsLd(i, t) == [server |-> i, term |-> t] \in leaders
VoteTermBound == \A i \in Server : voteTerm[i] <= currentTerm[i]
VotesBound == \A v \in votes : v.term <= voteTerm[v.voter]
GrantsAreVotes ==
    \A m \in msgs : m.type = "grant" =>
        [voter |-> m.src, term |-> m.term, cand |-> m.dst] \in votes
LeaderSync ==
    \A i \in Server : role[i] = Leader =>
        confAt[i] = ledAt[currentTerm[i]] /\ config[i] = ledConf[currentTerm[i]]
LeaderIsElected == \A i \in Server : role[i] = Leader => IsLd(i, currentTerm[i])
LeadersTermBound == \A ld \in leaders : ld.term <= currentTerm[ld.server]
LedOwner ==
    \A ld \in leaders : ld.term = currentTerm[ld.server] => Pre(log[ld.server], ledLog[ld.term])
LedDom == DOMAIN ledLog = {ld.term : ld \in leaders}
AppendFromLeader == \A m \in msgs : m.type = "append" => IsLd(m.src, m.term)

\* RequestsFromLed, pointwise.
ReqFromLed ==
    \A m \in msgs : m.type = "append" =>
        /\ m.term \in DOMAIN ledLog
        /\ m.prevLogIndex + Len(m.entries) <= Len(ledLog[m.term])
        /\ m.prevLogTerm = TermAt(ledLog[m.term], m.prevLogIndex)
        /\ \A q \in 1..Len(m.entries) : m.entries[q] = ledLog[m.term][m.prevLogIndex + q]
        /\ (m.commit = 0 \/ \E k \in commits : k.term <= m.term /\ Agree(k.entries, ledLog[m.term], m.commit))

\* Every entry of l is, with all entries before it, in the leader log of its term.
FromLed(l) == \A q \in 1..Len(l) : l[q].term \in DOMAIN ledLog /\ Agree(l, ledLog[l[q].term], q)
LogFromLed == \A i \in Server : FromLed(log[i])
LedFromLed == \A t \in DOMAIN ledLog : FromLed(ledLog[t])
TermsPositive == \A t \in DOMAIN ledLog : t >= 1
LogTermsBound == \A i \in Server : \A q \in 1..Len(log[i]) : log[i][q].term <= currentTerm[i]
LedTermsBound == \A t \in DOMAIN ledLog : \A q \in 1..Len(ledLog[t]) : ledLog[t][q].term <= t

\* Vote requests.
ReqOk(u, li, lt) ==
    /\ lt < u
    /\ \/ li = 0 /\ lt = 0
       \/ lt \in DOMAIN ledLog /\ li <= Len(ledLog[lt]) /\ TermAt(ledLog[lt], li) = lt
ReqFacts ==
    \A m \in msgs : m.type = "vote" =>
        m.term <= currentTerm[m.src] /\ ReqOk(m.term, m.lastLogIndex, m.lastLogTerm)
ReqUnique ==
    \A m, n \in msgs : m.type = "vote" /\ n.type = "vote" /\ m.src = n.src /\ m.term = n.term => m = n
VoteHasReq == \A v \in votes : \E m \in msgs : m.type = "vote" /\ m.src = v.cand /\ m.term = v.term
CandLog ==
    \A m \in msgs : m.type = "vote" /\ currentTerm[m.src] = m.term /\ m.term \notin DOMAIN ledLog =>
        Len(log[m.src]) = m.lastLogIndex /\ LastTerm(m.src) = m.lastLogTerm
LedExtendsReq ==
    \A ld \in leaders, m \in msgs : m.type = "vote" /\ m.src = ld.server /\ m.term = ld.term =>
        /\ m.lastLogIndex <= Len(ledLog[ld.term])
        /\ TermAt(ledLog[ld.term], m.lastLogIndex) = m.lastLogTerm

\* Acknowledgements.
AckFacts ==
    \A m \in msgs : m.type = "ack" =>
        IsLd(m.dst, m.term) /\ m.term <= currentTerm[m.src] /\ m.index <= Len(ledLog[m.term])
AckedBy(t, c) ==
    {n \in Server : \E a \in msgs : a.type = "ack" /\ a.src = n /\ a.term = t /\ a.index >= c}
\* A prefix that the leader of t may commit.
Good(t, c) == t \in DOMAIN ledLog /\ c >= 1 /\ c <= Len(ledLog[t]) /\ ledLog[t][c].term = t
\* Some leader log of a term in (lo, hi] does not have the first c entries of ledLog[t].
LostIn(t, c, lo, hi) ==
    \E w \in DOMAIN ledLog : lo < w /\ w <= hi /\ ~Agree(ledLog[t], ledLog[w], c)
AckedHeld ==
    \A n \in Server, t \in DOMAIN ledLog : \A c \in 1..Len(ledLog[t]) :
        Good(t, c) /\ n \in AckedBy(t, c) =>
            Agree(ledLog[t], log[n], c) \/ LostIn(t, c, t, currentTerm[n])
Covers(t, c, li, lt) == c <= li /\ lt \in DOMAIN ledLog /\ Agree(ledLog[t], ledLog[lt], c)
AckVote ==
    \A v \in votes, t \in DOMAIN ledLog : \A c \in 1..Len(ledLog[t]) :
        Good(t, c) /\ v.voter \in AckedBy(t, c) /\ t < v.term =>
            \A m \in msgs : m.type = "vote" /\ m.src = v.cand /\ m.term = v.term =>
                Covers(t, c, m.lastLogIndex, m.lastLogTerm) \/ LostIn(t, c, t, v.term)
Early(n, cand, u) ==
    \A t \in DOMAIN ledLog : \A c \in 1..Len(ledLog[t]) :
        Good(t, c) /\ n \in AckedBy(t, c) /\ t < u =>
            \A m \in msgs : m.type = "vote" /\ m.src = cand /\ m.term = u =>
                Covers(t, c, m.lastLogIndex, m.lastLogTerm) \/ LostIn(t, c, t, u - 1)
EarlyVoters(i, u) ==
    {n \in Server : [voter |-> n, term |-> u, cand |-> i] \in votes /\ Early(n, i, u)}
EarlyQuorum ==
    \A ld \in leaders :
        IsQuorum(EarlyVoters(ld.server, ld.term), ConfOf(ledLog[ld.term], elAt[ld.term]))

\* Commits.
ConfirmedIsLed ==
    \A j \in Server :
        \/ confirmed[j].index = 0
        \/ /\ confirmed[j].term \in DOMAIN ledLog
           /\ Agree(log[j], ledLog[confirmed[j].term], confirmed[j].index)
AtMostOne(l, a, b) == \A p, q \in (a + 1)..b : p < q => ~(IsConf(l[p]) /\ IsConf(l[q]))
Cover(l, d, t) == d = 0 \/ \E k \in commits : k.term <= t /\ Agree(k.entries, l, d)
CoverLt(l, d, t) == d = 0 \/ \E k \in commits : k.term < t /\ Agree(k.entries, l, d)
\* The leader of term t may commit, or has committed, the first c entries of
\* its log, counting with the configuration that the first d entries make.
MRoot(t, c, d) ==
    /\ Good(t, c)
    /\ d <= Len(ledLog[t])
    /\ Cover(ledLog[t], d, t)
    /\ AtMostOne(ledLog[t], d, c)
    /\ IsQuorum(AckedBy(t, c), ConfOf(ledLog[t], d))
Root(r) ==
    /\ r.term \in DOMAIN ledLog
    /\ Pre(r.entries, ledLog[r.term])
    /\ \E d \in 0..Len(ledLog[r.term]) : MRoot(r.term, Len(r.entries), d)
CommitRoot ==
    \A k \in commits :
        /\ k.entries # <<>>
        /\ \E r \in commits : Pre(k.entries, r.entries) /\ Root(r) /\ r.term <= k.term
CommitSafetyP == \A a, b \in commits : Pre(a.entries, b.entries) \/ Pre(b.entries, a.entries)
ConfirmedTermBound == \A i \in Server : confirmed[i].term <= currentTerm[i]
CommitTermBound == \A c \in commits : c.term <= currentTerm[c.server]
CommitKept ==
    \A i \in Server :
        /\ commitIndex[i] <= Len(log[i])
        /\ commitIndex[i] = 0 \/
             \E c \in commits : c.server = i /\ Agree(log[i], c.entries, commitIndex[i])
AppliedCommitted ==
    \A a \in applied : \E k \in commits :
        1 <= a.index /\ a.index <= Len(k.entries) /\ k.entries[a.index] = a.entry

\* Membership.
LeaderConfS ==
    \A t \in DOMAIN ledLog :
        /\ elAt[t] <= ledAt[t] /\ ledAt[t] <= Len(ledLog[t])
        /\ ledConf[t] = ConfOf(ledLog[t], ledAt[t])
        /\ AtMostOne(ledLog[t], ledAt[t], Len(ledLog[t]))
        /\ Cover(ledLog[t], ledAt[t], t)
        /\ CoverLt(ledLog[t], elAt[t], t)
FirstRoot ==
    \A k \in commits : \A p \in 1..Len(k.entries) : IsConf(k.entries[p]) =>
        \E r \in commits :
            /\ r.term <= k.term /\ p <= Len(r.entries)
            /\ r.term \in DOMAIN ledLog
            /\ Pre(r.entries, ledLog[r.term])
            /\ \E d \in 0..(p - 1) : MRoot(r.term, Len(r.entries), d)
LedOld ==
    \A u \in DOMAIN ledLog : \A p, q \in (elAt[u] + 1)..Len(ledLog[u]) :
        p < q /\ IsConf(ledLog[u][p]) /\ IsConf(ledLog[u][q]) =>
            ~(ledLog[u][p].term < u /\ ledLog[u][q].term < u)
LegalChain ==
    \A t \in DOMAIN ledLog : \A p \in 1..Len(ledLog[t]) : IsConf(ledLog[t][p]) =>
        Legal(ConfOf(ledLog[t], p - 1), ledLog[t][p].value)

\* The inductive invariant for the core properties (read indexes apart).
Inv ==
    /\ TypeOK
    /\ ElectionSafety
    /\ VoteTermBound /\ VotesBound /\ GrantsAreVotes /\ LeaderSync
    /\ LeaderIsElected /\ LeadersTermBound /\ LedOwner /\ LedDom /\ AppendFromLeader
    /\ ReqFromLed /\ LogFromLed /\ LedFromLed /\ TermsPositive /\ LogTermsBound /\ LedTermsBound
    /\ ReqFacts /\ ReqUnique /\ VoteHasReq /\ CandLog /\ LedExtendsReq
    /\ AckFacts /\ AckedHeld /\ AckVote /\ EarlyQuorum
    /\ ConfirmedIsLed /\ ConfirmedWithinLog /\ CommitRoot /\ CommitSafetyP
    /\ ConfirmedTermBound /\ CommitTermBound /\ CommitKept /\ AppliedCommitted
    /\ ConfIsCommitted /\ LeaderConfS /\ FirstRoot /\ LedOld /\ LegalChain

\* Leader completeness, for what a leader may commit: a consequence of Inv
\* in one state (theorem LCThm of EtcdLC.tla), not a conjunct of it.
LC ==
    \A t \in DOMAIN ledLog : \A c \in 1..Len(ledLog[t]) : \A d \in 0..Len(ledLog[t]) :
        MRoot(t, c, d) => \A u \in DOMAIN ledLog : t < u => Agree(ledLog[t], ledLog[u], c)
====
