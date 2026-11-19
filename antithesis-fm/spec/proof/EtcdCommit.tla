---- MODULE EtcdCommit ----
\* AckFacts, CommitRoot, FirstRoot, CommitSafetyP, CommitKept and
\* AppliedCommitted are kept by every step of the protocol.
EXTENDS EtcdLog, EtcdLC, EtcdCommitBase

CG == AckFacts /\ CommitRoot /\ FirstRoot /\ CommitSafetyP /\ CommitKept /\ AppliedCommitted

LEMMA InvBasic == ASSUME Inv PROVE Basic /\ TypeOK
BY DEF Inv, Basic

----
\* The steps, by what they do to commits, acknowledgements, logs and applied entries.
Quiet ==
    /\ UNCHANGED <<commits, applied, log, commitIndex>>
    /\ currentTerm' \in [Server -> Nat]
    /\ \A x \in msgs' \ msgs : x.type # "ack"

CommitCases ==
    \/ Quiet
    \/ \E i \in Server : Apply(i)
    \/ \E i \in Server : \E t \in Nat : \E c \in Nat : LeaderCommit(i, t, c)
    \/ \E j \in Server : \E m \in msgs : m \in AppendT /\ Ack(j, m)
    \/ \E j \in Server : \E m \in msgs : m \in AppendT /\ AckCommitted(j, m)
    \/ \E j \in Server : \E m \in msgs : \E k \in 1..Len(m.entries) : m \in AppendT /\ DeleteSuffix(j, m, k)
    \/ \E j \in Server : \E m \in msgs : \E k \in 1..Len(m.entries) : m \in AppendT /\ StoreEntries(j, m, k)
    \/ \E j \in Server : \E m \in msgs : \E c \in Nat : m \in AppendT /\ FollowerCommit(j, m, c)

LEMMA Frame ==
  ASSUME TypeOK, ProtoCases
  PROVE  CommitCases
<1>0. currentTerm \in [Server -> Nat] BY DEF TypeOK
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE Quiet
  BY <1>a, <1>0 DEF BecomeCandidate, Quiet, durable
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE Quiet
  BY <1>b, <1>0 DEF BecomeFollower, Quiet, durable
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE Quiet
  BY <1>c, <1>0 DEF BecomeLeader, Quiet, durable
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE Quiet
  BY <1>d, <1>0 DEF StartElection, Quiet, durable, VoteRequest
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE Quiet
  BY <1>e, <1>0 DEF Restart, Quiet, durable
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE CommitCases
  BY <1>f DEF CommitCases
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE Quiet
  BY <1>g, <1>0 DEF Restore, Quiet, durable
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE Quiet
  BY <1>h, <1>0 DEF SwitchConf, Quiet, durable
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE Quiet
  BY <1>i, <1>0 DEF RestoreConf, Quiet, durable
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE Quiet
  BY <1>j, <1>0 DEF LeaderAppend1, Quiet, durable
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE Quiet
  BY <1>k, <1>0 DEF AdoptTerm, Quiet, durable
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE Quiet
  BY <1>l, <1>0 DEF CastVote, Quiet, durable
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE Quiet
  BY <1>m, <1>0 DEF GrantVote, Quiet, durable
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE CommitCases
  BY <1>n DEF CommitCases
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE Quiet
  BY <1>o, <1>0 DEF SendAppend, Quiet, durable
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE CommitCases
  BY <1>p DEF CommitCases
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE CommitCases
  BY <1>q DEF CommitCases
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE CommitCases
  BY <1>r DEF CommitCases
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE CommitCases
  BY <1>s DEF CommitCases
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE CommitCases
  BY <1>t DEF CommitCases
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases, CommitCases

----
\* Acknowledgements.

LEMMA AckFactsGen ==
  ASSUME TypeOK, LedDom, AckFacts, Grows, currentTerm' \in [Server -> Nat],
         \A a \in msgs' \ msgs : a.type = "ack" =>
            IsLd(a.dst, a.term)' /\ a.term <= currentTerm'[a.src] /\ a.index <= Len(ledLog'[a.term])
  PROVE  AckFacts'
<1> SUFFICES ASSUME NEW m \in msgs', m.type = "ack"
             PROVE IsLd(m.dst, m.term)' /\ m.term <= currentTerm'[m.src] /\ m.index <= Len(ledLog'[m.term])
  BY DEF AckFacts
<1>1. CASE m \notin msgs BY <1>1
<1>2. CASE m \in msgs
  <2>1. IsLd(m.dst, m.term) /\ m.term <= currentTerm[m.src] /\ m.index <= Len(ledLog[m.term])
    BY <1>2 DEF AckFacts
  <2>2. m \in AckT BY <1>2 DEF TypeOK, MsgT, VoteReqT, GrantT, AppendT, AckT
  <2>3. m.term \in DOMAIN ledLog BY <2>1 DEF IsLd, LedDom
  <2>4. ledLog[m.term] \in Seq(EntryT) /\ ledLog'[m.term] \in Seq(EntryT) /\ Pre(ledLog[m.term], ledLog'[m.term])
    BY <2>3, TypeFacts DEF Grows
  <2>5. Len(ledLog[m.term]) <= Len(ledLog'[m.term]) BY <2>4 DEF Pre, Agree
  <2>6. m.src \in Server /\ m.term \in Nat /\ m.index \in Nat BY <2>2 DEF AckT
  <2>7. currentTerm[m.src] \in Nat /\ currentTerm'[m.src] \in Nat /\ currentTerm[m.src] <= currentTerm'[m.src]
    BY <2>6 DEF TypeOK, Grows
  <2>8. IsLd(m.dst, m.term)' BY <2>1 DEF IsLd, Grows
  <2> QED BY <2>1, <2>4, <2>5, <2>6, <2>7, <2>8
<1> QED BY <1>1, <1>2

LEMMA AckFactsStep ==
  ASSUME Inv, ProtoCases
  PROVE  AckFacts'
<1>0. Basic /\ TypeOK /\ Grows /\ LedDom /\ AckFacts BY InvBasic, GrowsStep DEF Inv
<1>1. CommitCases BY <1>0, Frame
<1>2. ASSUME msgs' = msgs, currentTerm' = currentTerm PROVE AckFacts'
  BY <1>2, <1>0, AckFactsGen DEF TypeOK
<1>a. CASE Quiet BY <1>a, <1>0, AckFactsGen DEF Quiet
<1>b. ASSUME NEW i \in Server, Apply(i) PROVE AckFacts'
  BY <1>b, <1>2 DEF Apply, durable
<1>c. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE AckFacts'
  BY <1>c, <1>2 DEF LeaderCommit, durable
<1>d. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE AckFacts'
  <2>0. PICK a : a = [type |-> "ack", src |-> j, dst |-> m.src, term |-> m.term,
                       index |-> m.prevLogIndex + Len(m.entries)]
    OBVIOUS
  <2>1. msgs' = msgs \cup {a} /\ UNCHANGED <<currentTerm, leaders, ledLog>> /\ currentTerm[j] = m.term
    BY <1>d, <2>0 DEF Ack, durable
  <2>2. m.type = "append" BY <1>d DEF AppendT
  <2>3. IsLd(m.src, m.term) BY <2>2 DEF Inv, AppendFromLeader
  <2>4. m.prevLogIndex + Len(m.entries) <= Len(ledLog[m.term]) BY <2>2 DEF Inv, ReqFromLed
  <2>5. currentTerm \in [Server -> Nat] BY <1>0 DEF TypeOK
  <2>6. IsLd(a.dst, a.term)' /\ a.term <= currentTerm'[a.src] /\ a.index <= Len(ledLog'[a.term])
    BY <2>0, <2>1, <2>3, <2>4, <2>5 DEF IsLd
  <2>7. \A x \in msgs' \ msgs : x = a BY <2>1
  <2> QED BY <2>1, <2>5, <2>6, <2>7, <1>0, AckFactsGen
<1>e. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE AckFacts'
  <2>0. PICK a : a = [type |-> "ack", src |-> j, dst |-> m.src, term |-> m.term, index |-> commitIndex[j]]
    OBVIOUS
  <2>1. msgs' = msgs \cup {a} /\ UNCHANGED <<currentTerm, leaders, ledLog>> /\ currentTerm[j] = m.term
    BY <1>e, <2>0 DEF AckCommitted, durable
  <2>2. m.type = "append" BY <1>e DEF AppendT
  <2>3. IsLd(m.src, m.term) BY <2>2 DEF Inv, AppendFromLeader
  <2>4. commitIndex[j] <= Len(ledLog[m.term])
    <3>1. m.term \in DOMAIN ledLog BY <2>2 DEF Inv, ReqFromLed
    <3>2. ledLog[m.term] \in Seq(EntryT) /\ commitIndex[j] \in Nat BY <3>1, <1>0 DEF TypeOK
    <3>3. CASE commitIndex[j] = 0 BY <3>3, <3>2
    <3>4. CASE commitIndex[j] # 0
      <4>1. PICK c0 \in commits : c0.server = j /\ Agree(log[j], c0.entries, commitIndex[j])
        BY <3>4 DEF Inv, CommitKept
      <4>2. c0.term <= currentTerm[j] BY <4>1 DEF Inv, CommitTermBound
      <4>3. Pre(c0.entries, ledLog[m.term]) BY <4>2, <2>1, <3>1, RootInLed
      <4>4. c0.entries \in Seq(EntryT) BY <1>0, TypeFacts
      <4> QED BY <4>1, <4>3, <4>4, <3>2 DEF Pre, Agree
    <3> QED BY <3>3, <3>4
  <2>5. currentTerm \in [Server -> Nat] BY <1>0 DEF TypeOK
  <2>6. IsLd(a.dst, a.term)' /\ a.term <= currentTerm'[a.src] /\ a.index <= Len(ledLog'[a.term])
    BY <2>0, <2>1, <2>3, <2>4, <2>5 DEF IsLd
  <2>7. \A x \in msgs' \ msgs : x = a BY <2>1
  <2> QED BY <2>1, <2>5, <2>6, <2>7, <1>0, AckFactsGen
<1>f. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE AckFacts'
  BY <1>f, <1>2 DEF DeleteSuffix
<1>g. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE AckFacts'
  BY <1>g, <1>2 DEF StoreEntries
<1>h. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE AckFacts'
  BY <1>h, <1>2 DEF FollowerCommit
<1> QED BY <1>1, <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h DEF CommitCases

----
\* What LeaderCommit and FollowerCommit add to commits.

LEMMA LeaderCommitFacts ==
  ASSUME Inv, NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c)
  PROVE  /\ t \in DOMAIN ledLog /\ ledLog[t] \in Seq(EntryT) /\ c >= 1 /\ c <= Len(ledLog[t])
         /\ ledAt[t] \in Nat /\ ledAt[t] <= Len(ledLog[t])
         /\ MRoot(t, c, ledAt[t])
         /\ Cover(ledLog[t], ledAt[t], t)
<1>1. TypeOK /\ LedDom /\ LeaderConfS BY DEF Inv
<1>2. /\ [server |-> i, term |-> t] \in leaders /\ c >= 1 /\ c <= Len(ledLog[t])
      /\ ledLog[t][c].term = t /\ IsQuorum(Acked(i, t, c), ledConf[t])
  BY DEF LeaderCommit
<1>3. t \in DOMAIN ledLog BY <1>1, <1>2 DEF LedDom
<1>4. ledLog[t] \in Seq(EntryT) /\ ledAt[t] \in Nat /\ ledConf[t] \in ConfT /\ ConstOK
  BY <1>1, <1>3 DEF TypeOK
<1>5. /\ ledAt[t] <= Len(ledLog[t]) /\ ledConf[t] = ConfOf(ledLog[t], ledAt[t])
      /\ AtMostOne(ledLog[t], ledAt[t], Len(ledLog[t])) /\ Cover(ledLog[t], ledAt[t], t)
  BY <1>1, <1>3 DEF LeaderConfS
<1>6. Good(t, c) BY <1>2, <1>3 DEF Good
<1>7. AtMostOne(ledLog[t], ledAt[t], c) BY <1>5, <1>2, <1>4 DEF AtMostOne
<1>8. Acked(i, t, c) \subseteq AckedBy(t, c) BY DEF Acked, AckedBy
<1>9. IsQuorum(AckedBy(t, c), ledConf[t]) BY <1>2, <1>4, <1>8, QuorumMono
<1> QED BY <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>9 DEF MRoot

\* The new commit of LeaderCommit, as constants r0 (the commit) and d0 (= ledAt[t]).
LEMMA LeaderCommitNew ==
  ASSUME Inv, Grows, NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c)
  PROVE  \E r0 \in CommitT, d0 \in Nat :
           /\ commits' = commits \cup {r0}
           /\ r0.term = t /\ Len(r0.entries) = c /\ c >= 1
           /\ r0.entries \in Seq(EntryT)
           /\ t \in DOMAIN ledLog /\ ledLog[t] \in Seq(EntryT) /\ ledLog' = ledLog
           /\ Pre(r0.entries, ledLog[t])
           /\ d0 <= Len(ledLog[t])
           /\ MRoot(t, c, d0) /\ MRoot(t, c, d0)'
           /\ Cover(ledLog[t], d0, t)
<1>1. /\ t \in DOMAIN ledLog /\ ledLog[t] \in Seq(EntryT) /\ c >= 1 /\ c <= Len(ledLog[t])
      /\ ledAt[t] \in Nat /\ ledAt[t] <= Len(ledLog[t])
      /\ MRoot(t, c, ledAt[t])
      /\ Cover(ledLog[t], ledAt[t], t)
  BY LeaderCommitFacts
<1>2. PICK E : E = SubSeq(ledLog[t], 1, c) OBVIOUS
<1>3. E \in Seq(EntryT) /\ Len(E) = c /\ \A q \in 1..c : E[q] = ledLog[t][q] BY <1>1, <1>2, SubSeqFacts
<1>4. PICK r0 : r0 = [server |-> i, term |-> t, entries |-> E] OBVIOUS
<1>5. PICK d0 : d0 = ledAt[t] OBVIOUS
<1>6. commits' = commits \cup {r0} /\ ledLog' = ledLog BY <1>2, <1>4 DEF LeaderCommit
<1>7. r0 \in CommitT /\ r0.term = t /\ r0.entries = E BY <1>3, <1>4 DEF CommitT
<1>8. Pre(E, ledLog[t]) BY <1>1, <1>3 DEF Pre, Agree
<1>9. TypeOK BY DEF Inv
<1>10. MRoot(t, c, d0) /\ d0 \in Nat BY <1>1, <1>5
<1>11. MRoot(t, c, d0)' BY <1>1, <1>9, <1>10, MRootMono
<1> QED BY <1>1, <1>3, <1>5, <1>6, <1>7, <1>8, <1>10, <1>11

LEMMA FollowerCommitFacts ==
  ASSUME Inv, NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c)
  PROVE  /\ c >= 1 /\ c <= Len(log[j]) /\ log[j] \in Seq(EntryT) /\ m.term \in Nat
         /\ commitIndex[j] \in Nat /\ c > commitIndex[j]
         /\ \E k \in commits : k.term <= m.term /\ Agree(log[j], k.entries, c)
<1>1. TypeOK /\ ReqFromLed /\ ConfirmedIsLed BY DEF Inv
<1>2. m.type = "append" /\ m.commit \in Nat /\ m.term \in Nat BY DEF AppendT
<1>3. log[j] \in Seq(EntryT) /\ commitIndex[j] \in Nat /\ confirmed[j].index \in Nat /\ confirmed[j].term \in Nat
  BY <1>1 DEF TypeOK
<1>4. m.term = confirmed[j].term /\ c > commitIndex[j] /\ c <= m.commit /\ c <= confirmed[j].index
  BY <1>2, <1>3 DEF FollowerCommit, Min
<1>5. m.term \in DOMAIN ledLog /\ Agree(log[j], ledLog[m.term], confirmed[j].index)
  BY <1>1, <1>3, <1>4 DEF ConfirmedIsLed
<1>6. PICK k \in commits : k.term <= m.term /\ Agree(k.entries, ledLog[m.term], m.commit)
  BY <1>1, <1>2, <1>3, <1>4 DEF ReqFromLed
<1>7. k.entries \in Seq(EntryT) /\ ledLog[m.term] \in Seq(EntryT) BY <1>1, <1>5, TypeFacts
<1>8. Agree(log[j], k.entries, c) BY <1>2, <1>3, <1>4, <1>5, <1>6, <1>7 DEF Agree
<1> QED BY <1>2, <1>3, <1>4, <1>6, <1>8 DEF Agree

\* The new commit of FollowerCommit, as a constant n0, with an old commit k that has its entries.
LEMMA FollowerCommitNew ==
  ASSUME Inv, NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c)
  PROVE  \E n0 \in CommitT, k \in commits :
           /\ commits' = commits \cup {n0}
           /\ commitIndex' = [commitIndex EXCEPT ![j] = c] /\ log' = log
           /\ n0.server = j /\ n0.term = m.term /\ m.term \in Nat /\ Len(n0.entries) = c /\ c >= 1
           /\ n0.entries \in Seq(EntryT) /\ k.entries \in Seq(EntryT) /\ k.term \in Nat
           /\ c <= Len(log[j]) /\ Agree(log[j], n0.entries, c)
           /\ k.term <= m.term /\ Pre(n0.entries, k.entries)
<1>1. /\ c >= 1 /\ c <= Len(log[j]) /\ log[j] \in Seq(EntryT) /\ m.term \in Nat
      /\ commitIndex[j] \in Nat /\ c > commitIndex[j]
      /\ \E k \in commits : k.term <= m.term /\ Agree(log[j], k.entries, c)
  BY FollowerCommitFacts
<1>2. PICK k \in commits : k.term <= m.term /\ Agree(log[j], k.entries, c) BY <1>1
<1>3. PICK E : E = SubSeq(log[j], 1, c) OBVIOUS
<1>4. E \in Seq(EntryT) /\ Len(E) = c /\ \A q \in 1..c : E[q] = log[j][q] BY <1>1, <1>3, SubSeqFacts
<1>5. PICK n0 : n0 = [server |-> j, term |-> m.term, entries |-> E] OBVIOUS
<1>6. commits' = commits \cup {n0} /\ commitIndex' = [commitIndex EXCEPT ![j] = c] /\ log' = log
  BY <1>3, <1>5 DEF FollowerCommit, Committed
<1>7. n0 \in CommitT /\ n0.server = j /\ n0.term = m.term /\ n0.entries = E BY <1>1, <1>4, <1>5 DEF CommitT
<1>8. TypeOK BY DEF Inv
<1>9. k.entries \in Seq(EntryT) /\ k.term \in Nat BY <1>8, TypeFacts
<1>10. Agree(log[j], E, c) /\ Pre(E, k.entries) BY <1>1, <1>2, <1>4, <1>9 DEF Pre, Agree
<1> QED BY <1>1, <1>2, <1>4, <1>6, <1>7, <1>9, <1>10

----
\* CommitRoot.

LEMMA CommitRootKeep ==
  ASSUME TypeOK, Grows, CommitRoot,
         \A k \in commits' \ commits : k.entries # <<>> /\ CRB(k.entries, k.term)'
  PROVE  CommitRoot'
<1> SUFFICES ASSUME NEW k \in commits' PROVE k.entries # <<>> /\ CRB(k.entries, k.term)'
  BY DEF CommitRoot, CRB
<1>1. CASE k \in commits
  <2>1. k.entries # <<>> /\ CRB(k.entries, k.term) BY <1>1 DEF CommitRoot, CRB
  <2> QED BY <2>1, CRBMono
<1> QED BY <1>1

LEMMA CommitRootStep ==
  ASSUME Inv, ProtoCases
  PROVE  CommitRoot'
<1>0. Basic /\ TypeOK /\ Grows /\ CommitRoot BY InvBasic, GrowsStep DEF Inv
<1>1. CommitCases BY <1>0, Frame
<1>2. ASSUME commits' = commits PROVE CommitRoot'
  BY <1>2, <1>0, CommitRootKeep
<1>a. CASE Quiet BY <1>a, <1>2 DEF Quiet
<1>b. ASSUME NEW i \in Server, Apply(i) PROVE CommitRoot'
  BY <1>b, <1>2 DEF Apply
<1>c. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE CommitRoot'
  <2>1. PICK r0 \in CommitT, d0 \in Nat :
           /\ commits' = commits \cup {r0}
           /\ r0.term = t /\ Len(r0.entries) = c /\ c >= 1
           /\ r0.entries \in Seq(EntryT)
           /\ t \in DOMAIN ledLog /\ ledLog[t] \in Seq(EntryT) /\ ledLog' = ledLog
           /\ Pre(r0.entries, ledLog[t])
           /\ d0 <= Len(ledLog[t])
           /\ MRoot(t, c, d0) /\ MRoot(t, c, d0)'
           /\ Cover(ledLog[t], d0, t)
    BY <1>c, <1>0, LeaderCommitNew
  <2>2. MRoot(r0.term, Len(r0.entries), d0)' BY <2>1
  <2>3. d0 \in 0..Len(ledLog'[r0.term]) BY <2>1
  <2>4. Root(r0)' BY <2>1, <2>2, <2>3 DEF Root
  <2>5. Pre(r0.entries, r0.entries) BY <2>1, PreRefl
  <2>6. CRB(r0.entries, r0.term)' BY <2>1, <2>4, <2>5 DEF CRB
  <2>7. r0.entries # <<>> BY <2>1
  <2> QED BY <2>1, <2>6, <2>7, <1>0, CommitRootKeep
<1>d. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE CommitRoot'
  BY <1>d, <1>2 DEF Ack
<1>e. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE CommitRoot'
  BY <1>e, <1>2 DEF AckCommitted
<1>f. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE CommitRoot'
  BY <1>f, <1>2 DEF DeleteSuffix
<1>g. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE CommitRoot'
  BY <1>g, <1>2 DEF StoreEntries
<1>h. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE CommitRoot'
  <2>1. PICK n0 \in CommitT, k \in commits :
           /\ commits' = commits \cup {n0}
           /\ commitIndex' = [commitIndex EXCEPT ![j] = c] /\ log' = log
           /\ n0.server = j /\ n0.term = m.term /\ m.term \in Nat /\ Len(n0.entries) = c /\ c >= 1
           /\ n0.entries \in Seq(EntryT) /\ k.entries \in Seq(EntryT) /\ k.term \in Nat
           /\ c <= Len(log[j]) /\ Agree(log[j], n0.entries, c)
           /\ k.term <= m.term /\ Pre(n0.entries, k.entries)
    BY <1>h, FollowerCommitNew
  <2>2. CRB(k.entries, k.term) BY <1>0 DEF CommitRoot, CRB
  <2>3. CRB(n0.entries, n0.term) BY <2>1, <2>2, <1>0, CRBWeaken
  <2>4. CRB(n0.entries, n0.term)' BY <2>3, <1>0, CRBMono
  <2>5. n0.entries # <<>> BY <2>1
  <2> QED BY <2>1, <2>4, <2>5, <1>0, CommitRootKeep
<1> QED BY <1>1, <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h DEF CommitCases

----
\* FirstRoot.

LEMMA FirstRootKeep ==
  ASSUME TypeOK, Grows, FirstRoot,
         \A k \in commits' \ commits : \A p \in 1..Len(k.entries) :
            IsConf(k.entries[p]) => FRB(k.term, p)'
  PROVE  FirstRoot'
<1> SUFFICES ASSUME NEW k \in commits', NEW p \in 1..Len(k.entries), IsConf(k.entries[p])
             PROVE FRB(k.term, p)'
  BY DEF FirstRoot, FRB
<1>1. CASE k \in commits
  <2>1. FRB(k.term, p) BY <1>1 DEF FirstRoot, FRB
  <2>2. k.entries \in Seq(EntryT) BY <1>1, TypeFacts
  <2>3. p \in Nat BY <2>2
  <2> QED BY <2>1, <2>3, FRBMono
<1> QED BY <1>1

LEMMA FirstRootStep ==
  ASSUME Inv, ProtoCases
  PROVE  FirstRoot'
<1>0. Basic /\ TypeOK /\ Grows /\ FirstRoot BY InvBasic, GrowsStep DEF Inv
<1>1. CommitCases BY <1>0, Frame
<1>2. ASSUME commits' = commits PROVE FirstRoot'
  BY <1>2, <1>0, FirstRootKeep
<1>a. CASE Quiet BY <1>a, <1>2 DEF Quiet
<1>b. ASSUME NEW i \in Server, Apply(i) PROVE FirstRoot'
  BY <1>b, <1>2 DEF Apply
<1>c. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE FirstRoot'
  <2>1. PICK r0 \in CommitT, d0 \in Nat :
           /\ commits' = commits \cup {r0}
           /\ r0.term = t /\ Len(r0.entries) = c /\ c >= 1
           /\ r0.entries \in Seq(EntryT)
           /\ t \in DOMAIN ledLog /\ ledLog[t] \in Seq(EntryT) /\ ledLog' = ledLog
           /\ Pre(r0.entries, ledLog[t])
           /\ d0 <= Len(ledLog[t])
           /\ MRoot(t, c, d0) /\ MRoot(t, c, d0)'
           /\ Cover(ledLog[t], d0, t)
    BY <1>c, <1>0, LeaderCommitNew
  <2>2. ASSUME NEW p \in 1..Len(r0.entries), IsConf(r0.entries[p]) PROVE FRB(r0.term, p)'
    <3>0. p \in Nat /\ p <= c /\ p >= 1 BY <2>1
    <3>1. CASE p > d0
      <4>1. r0 \in commits' BY <2>1
      <4>2. r0.term <= r0.term /\ p <= Len(r0.entries) BY <2>1, <3>0
      <4>3. r0.term \in DOMAIN ledLog' /\ Pre(r0.entries, ledLog'[r0.term]) BY <2>1
      <4>4. d0 \in 0..(p - 1) BY <3>1, <3>0
      <4>5. MRoot(r0.term, Len(r0.entries), d0)' BY <2>1
      <4> QED BY <4>1, <4>2, <4>3, <4>4, <4>5 DEF FRB
    <3>2. CASE p <= d0
      <4>1. PICK k \in commits : k.term <= t /\ Agree(k.entries, ledLog[t], d0)
        BY <2>1, <3>2, <3>0 DEF Cover
      <4>2. k.entries \in Seq(EntryT) /\ k.term \in Nat BY <1>0, TypeFacts
      <4>3. p \in 1..Len(k.entries) /\ k.entries[p] = ledLog[t][p] BY <4>1, <4>2, <3>0, <3>2, <2>1 DEF Agree
      <4>4. r0.entries[p] = ledLog[t][p] BY <2>1, <3>0 DEF Pre, Agree
      <4>5. FRB(k.term, p) BY <4>3, <4>4, <2>2, <1>0 DEF FirstRoot, FRB
      <4>6. FRB(t, p) BY <4>5, <4>1, <4>2, <1>0, FRBWeaken
      <4>7. FRB(t, p)' BY <4>6, <3>0, <1>0, FRBMono
      <4> QED BY <4>7, <2>1
    <3> QED BY <3>1, <3>2, <3>0
  <2> QED BY <2>1, <2>2, <1>0, FirstRootKeep
<1>d. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE FirstRoot'
  BY <1>d, <1>2 DEF Ack
<1>e. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE FirstRoot'
  BY <1>e, <1>2 DEF AckCommitted
<1>f. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE FirstRoot'
  BY <1>f, <1>2 DEF DeleteSuffix
<1>g. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE FirstRoot'
  BY <1>g, <1>2 DEF StoreEntries
<1>h. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE FirstRoot'
  <2>1. PICK n0 \in CommitT, k \in commits :
           /\ commits' = commits \cup {n0}
           /\ commitIndex' = [commitIndex EXCEPT ![j] = c] /\ log' = log
           /\ n0.server = j /\ n0.term = m.term /\ m.term \in Nat /\ Len(n0.entries) = c /\ c >= 1
           /\ n0.entries \in Seq(EntryT) /\ k.entries \in Seq(EntryT) /\ k.term \in Nat
           /\ c <= Len(log[j]) /\ Agree(log[j], n0.entries, c)
           /\ k.term <= m.term /\ Pre(n0.entries, k.entries)
    BY <1>h, FollowerCommitNew
  <2>2. ASSUME NEW p \in 1..Len(n0.entries), IsConf(n0.entries[p]) PROVE FRB(n0.term, p)'
    <3>0. p \in Nat BY <2>1
    <3>1. p \in 1..Len(k.entries) /\ k.entries[p] = n0.entries[p] BY <2>1 DEF Pre, Agree
    <3>2. FRB(k.term, p) BY <3>1, <2>2, <1>0 DEF FirstRoot, FRB
    <3>3. FRB(n0.term, p) BY <3>2, <2>1, <1>0, FRBWeaken
    <3> QED BY <3>3, <3>0, <1>0, FRBMono
  <2> QED BY <2>1, <2>2, <1>0, FirstRootKeep
<1> QED BY <1>1, <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h DEF CommitCases

----
\* CommitSafetyP.

LEMMA CSAdd ==
  ASSUME CommitSafetyP, NEW n, commits' = commits \cup {n}, Pre(n.entries, n.entries),
         \A b \in commits : Pre(n.entries, b.entries) \/ Pre(b.entries, n.entries)
  PROVE  CommitSafetyP'
BY DEF CommitSafetyP

LEMMA CommitSafetyPStep ==
  ASSUME Inv, ProtoCases
  PROVE  CommitSafetyP'
<1>0. Basic /\ TypeOK /\ Grows /\ CommitSafetyP /\ CommitRoot BY InvBasic, GrowsStep DEF Inv
<1>1. CommitCases BY <1>0, Frame
<1>2. ASSUME commits' = commits PROVE CommitSafetyP'
  BY <1>2, <1>0 DEF CommitSafetyP
<1>a. CASE Quiet BY <1>a, <1>2 DEF Quiet
<1>b. ASSUME NEW i \in Server, Apply(i) PROVE CommitSafetyP'
  BY <1>b, <1>2 DEF Apply
<1>c. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE CommitSafetyP'
  <2>1. PICK r0 \in CommitT, d0 \in Nat :
           /\ commits' = commits \cup {r0}
           /\ r0.term = t /\ Len(r0.entries) = c /\ c >= 1
           /\ r0.entries \in Seq(EntryT)
           /\ t \in DOMAIN ledLog /\ ledLog[t] \in Seq(EntryT) /\ ledLog' = ledLog
           /\ Pre(r0.entries, ledLog[t])
           /\ d0 <= Len(ledLog[t])
           /\ MRoot(t, c, d0) /\ MRoot(t, c, d0)'
           /\ Cover(ledLog[t], d0, t)
    BY <1>c, <1>0, LeaderCommitNew
  <2>2. LC BY LCThm
  <2>3. ASSUME NEW b \in commits PROVE Pre(r0.entries, b.entries) \/ Pre(b.entries, r0.entries)
    <3>1. PICK r \in commits : Pre(b.entries, r.entries) /\ Root(r) /\ r.term <= b.term
      BY <1>0 DEF CommitRoot
    <3>2. /\ b.entries \in Seq(EntryT) /\ r.entries \in Seq(EntryT) /\ r.term \in Nat
      BY <1>0, TypeFacts
    <3>3. r.term \in DOMAIN ledLog /\ Pre(r.entries, ledLog[r.term]) BY <3>1 DEF Root
    <3>4. ledLog[r.term] \in Seq(EntryT) BY <3>3, <1>0, TypeFacts
    <3>5. CASE r.term <= t
      <4>1. Pre(r.entries, ledLog[t]) BY <3>5, <2>1, RootInLed
      <4>2. Pre(b.entries, ledLog[t]) BY <4>1, <3>1, <3>2, <2>1, PreTrans
      <4> QED BY <4>2, <2>1, <3>2, PreCmp
    <3>6. CASE r.term > t
      <4>1. c \in 1..Len(ledLog[t]) /\ d0 \in 0..Len(ledLog[t]) BY <2>1 DEF Pre, Agree
      <4>2. Agree(ledLog[t], ledLog[r.term], c) BY <4>1, <2>1, <2>2, <3>3, <3>6, <3>2 DEF LC
      <4>3. Pre(r0.entries, ledLog[r.term]) BY <4>2, <2>1, <3>4 DEF Pre, Agree
      <4>4. Pre(b.entries, ledLog[r.term]) BY <3>1, <3>2, <3>3, <3>4, PreTrans
      <4> QED BY <4>3, <4>4, <2>1, <3>2, <3>4, PreCmp
    <3> QED BY <3>5, <3>6, <3>2
  <2>4. Pre(r0.entries, r0.entries) BY <2>1, PreRefl
  <2> QED BY <2>1, <2>3, <2>4, <1>0, CSAdd
<1>d. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE CommitSafetyP'
  BY <1>d, <1>2 DEF Ack
<1>e. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE CommitSafetyP'
  BY <1>e, <1>2 DEF AckCommitted
<1>f. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE CommitSafetyP'
  BY <1>f, <1>2 DEF DeleteSuffix
<1>g. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE CommitSafetyP'
  BY <1>g, <1>2 DEF StoreEntries
<1>h. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE CommitSafetyP'
  <2>1. PICK n0 \in CommitT, k \in commits :
           /\ commits' = commits \cup {n0}
           /\ commitIndex' = [commitIndex EXCEPT ![j] = c] /\ log' = log
           /\ n0.server = j /\ n0.term = m.term /\ m.term \in Nat /\ Len(n0.entries) = c /\ c >= 1
           /\ n0.entries \in Seq(EntryT) /\ k.entries \in Seq(EntryT) /\ k.term \in Nat
           /\ c <= Len(log[j]) /\ Agree(log[j], n0.entries, c)
           /\ k.term <= m.term /\ Pre(n0.entries, k.entries)
    BY <1>h, FollowerCommitNew
  <2>3. ASSUME NEW b \in commits PROVE Pre(n0.entries, b.entries) \/ Pre(b.entries, n0.entries)
    <3>1. b.entries \in Seq(EntryT) BY <1>0, TypeFacts
    <3>2. CASE Pre(k.entries, b.entries) BY <3>2, <3>1, <2>1, PreTrans
    <3>3. CASE Pre(b.entries, k.entries) BY <3>3, <3>1, <2>1, PreCmp
    <3> QED BY <3>2, <3>3, <1>0 DEF CommitSafetyP
  <2>4. Pre(n0.entries, n0.entries) BY <2>1, PreRefl
  <2> QED BY <2>1, <2>3, <2>4, <1>0, CSAdd
<1> QED BY <1>1, <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h DEF CommitCases

----
\* CommitKept.

LEMMA CKKeep ==
  ASSUME CommitKept, UNCHANGED <<log, commitIndex>>, commits \subseteq commits'
  PROVE  CommitKept'
BY DEF CommitKept

LEMMA CommitKeptStep ==
  ASSUME Inv, ProtoCases
  PROVE  CommitKept'
<1>0. Basic /\ TypeOK /\ Grows /\ CommitKept BY InvBasic, GrowsStep DEF Inv
<1>1. CommitCases BY <1>0, Frame
<1>a. CASE Quiet BY <1>a, <1>0, CKKeep DEF Quiet
<1>b. ASSUME NEW i \in Server, Apply(i) PROVE CommitKept'
  BY <1>b, <1>0, CKKeep DEF Apply, durable
<1>c. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE CommitKept'
  BY <1>c, <1>0, CKKeep DEF LeaderCommit, durable
<1>d. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE CommitKept'
  BY <1>d, <1>0, CKKeep DEF Ack, durable
<1>e. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE CommitKept'
  BY <1>e, <1>0, CKKeep DEF AckCommitted, durable
<1>f. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE CommitKept'
  <2> DEFINE p == m.prevLogIndex
  <2>1. /\ log' = [log EXCEPT ![j] = log'[j]]
        /\ log'[j] \in Seq(EntryT)
        /\ Len(log'[j]) = p + k - 1
        /\ p + k <= Len(log[j])
        /\ \A q \in 1..Len(log'[j]) : log'[j][q] = log[j][q]
    BY <1>f, <1>0, DeleteLog
  <2>2. /\ UNCHANGED <<commitIndex, commits>> /\ m.term = currentTerm[j]
        /\ log[j][p + k].term # m.entries[k].term
    BY <1>f DEF DeleteSuffix
  <2>3. /\ p \in Nat /\ m.entries \in Seq(EntryT) /\ m.type = "append" /\ k \in Nat
        /\ log[j] \in Seq(EntryT) /\ commitIndex[j] \in Nat /\ log \in [Server -> Seq(EntryT)]
    BY <1>f, <1>0 DEF AppendT, TypeOK
  <2>4. m.term \in DOMAIN ledLog /\ m.entries[k] = ledLog[m.term][p + k]
    BY <2>3 DEF Inv, ReqFromLed
  <2>5. commitIndex[j] <= p + k - 1
    <3>1. CASE commitIndex[j] = 0 BY <3>1, <2>3
    <3>2. CASE commitIndex[j] # 0
      <4>1. PICK c0 \in commits : c0.server = j /\ Agree(log[j], c0.entries, commitIndex[j])
        BY <3>2, <1>0 DEF CommitKept
      <4>2. c0.term <= currentTerm[j] BY <4>1 DEF Inv, CommitTermBound
      <4>3. Pre(c0.entries, ledLog[m.term]) BY <4>2, <2>2, <2>4, RootInLed
      <4>4. c0.entries \in Seq(EntryT) /\ ledLog[m.term] \in Seq(EntryT) BY <2>4, <1>0, TypeFacts
      <4>5. \A q \in 1..commitIndex[j] : log[j][q] = ledLog[m.term][q]
        BY <4>1, <4>3, <4>4, <2>3 DEF Pre, Agree
      <4>6. ASSUME p + k <= commitIndex[j] PROVE FALSE
        <5>1. log[j][p + k] = ledLog[m.term][p + k] BY <4>6, <4>5, <2>3
        <5> QED BY <5>1, <2>2, <2>4
      <4> QED BY <4>6, <2>3
    <3> QED BY <3>1, <3>2
  <2> HIDE DEF p
  <2>6. ASSUME NEW s \in Server
        PROVE /\ commitIndex'[s] <= Len(log'[s])
              /\ commitIndex'[s] = 0 \/
                   \E c \in commits' : c.server = s /\ Agree(log'[s], c.entries, commitIndex'[s])
    <3>1. CASE s # j
      <4>1. log'[s] = log[s] BY <3>1, <2>1, <2>3
      <4> QED BY <4>1, <2>2, <1>0 DEF CommitKept
    <3>2. CASE s = j
      <4>1. commitIndex'[j] = commitIndex[j] /\ commits' = commits BY <2>2
      <4>2. commitIndex[j] <= Len(log'[j]) BY <2>1, <2>5
      <4>3. ASSUME NEW c \in commits, Agree(log[j], c.entries, commitIndex[j])
            PROVE Agree(log'[j], c.entries, commitIndex[j])
        BY <4>3, <4>2, <2>1, <2>3 DEF Agree
      <4>4. commitIndex[j] = 0 \/ \E c \in commits : c.server = j /\ Agree(log[j], c.entries, commitIndex[j])
        BY <1>0 DEF CommitKept
      <4> QED BY <3>2, <4>1, <4>2, <4>3, <4>4
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>6 DEF CommitKept
<1>g. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE CommitKept'
  <2> DEFINE p == m.prevLogIndex
  <2>1. /\ log' = [log EXCEPT ![j] = log'[j]]
        /\ log'[j] \in Seq(EntryT)
        /\ Len(log'[j]) = p + Len(m.entries)
        /\ p + k = Len(log[j]) + 1
        /\ \A q \in 1..Len(log[j]) : log'[j][q] = log[j][q]
    BY <1>g, <1>0, StoreLog
  <2>2. UNCHANGED <<commitIndex, commits>> BY <1>g DEF StoreEntries
  <2>3. /\ p \in Nat /\ m.entries \in Seq(EntryT) /\ k \in Nat
        /\ log[j] \in Seq(EntryT) /\ commitIndex[j] \in Nat /\ log \in [Server -> Seq(EntryT)]
    BY <1>g, <1>0 DEF AppendT, TypeOK
  <2>4. Len(log[j]) <= Len(log'[j]) BY <2>1, <2>3
  <2> HIDE DEF p
  <2>6. ASSUME NEW s \in Server
        PROVE /\ commitIndex'[s] <= Len(log'[s])
              /\ commitIndex'[s] = 0 \/
                   \E c \in commits' : c.server = s /\ Agree(log'[s], c.entries, commitIndex'[s])
    <3>1. CASE s # j
      <4>1. log'[s] = log[s] BY <3>1, <2>1, <2>3
      <4> QED BY <4>1, <2>2, <1>0 DEF CommitKept
    <3>2. CASE s = j
      <4>1. commitIndex'[j] = commitIndex[j] /\ commits' = commits BY <2>2
      <4>2. commitIndex[j] <= Len(log[j]) BY <1>0 DEF CommitKept
      <4>3. ASSUME NEW c \in commits, Agree(log[j], c.entries, commitIndex[j])
            PROVE Agree(log'[j], c.entries, commitIndex[j])
        BY <4>3, <4>2, <2>1, <2>3, <2>4 DEF Agree
      <4>4. commitIndex[j] = 0 \/ \E c \in commits : c.server = j /\ Agree(log[j], c.entries, commitIndex[j])
        BY <1>0 DEF CommitKept
      <4>5. commitIndex[j] <= Len(log'[j]) BY <4>2, <2>4, <2>3, <2>1
      <4> QED BY <3>2, <4>1, <4>5, <4>3, <4>4
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>6 DEF CommitKept
<1>h. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE CommitKept'
  <2>1. PICK n0 \in CommitT, k \in commits :
           /\ commits' = commits \cup {n0}
           /\ commitIndex' = [commitIndex EXCEPT ![j] = c] /\ log' = log
           /\ n0.server = j /\ n0.term = m.term /\ m.term \in Nat /\ Len(n0.entries) = c /\ c >= 1
           /\ n0.entries \in Seq(EntryT) /\ k.entries \in Seq(EntryT) /\ k.term \in Nat
           /\ c <= Len(log[j]) /\ Agree(log[j], n0.entries, c)
           /\ k.term <= m.term /\ Pre(n0.entries, k.entries)
    BY <1>h, FollowerCommitNew
  <2>2. commitIndex \in [Server -> Nat] BY <1>0 DEF TypeOK
  <2>6. ASSUME NEW s \in Server
        PROVE /\ commitIndex'[s] <= Len(log'[s])
              /\ commitIndex'[s] = 0 \/
                   \E x \in commits' : x.server = s /\ Agree(log'[s], x.entries, commitIndex'[s])
    <3>1. CASE s # j
      <4>1. commitIndex'[s] = commitIndex[s] /\ log'[s] = log[s] BY <3>1, <2>1, <2>2
      <4> QED BY <4>1, <2>1, <1>0 DEF CommitKept
    <3>2. CASE s = j
      <4>1. commitIndex'[j] = c /\ log'[j] = log[j] /\ n0 \in commits' BY <2>1, <2>2
      <4> QED BY <4>1, <2>1, <3>2
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>6 DEF CommitKept
<1> QED BY <1>1, <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h DEF CommitCases

----
\* AppliedCommitted.

LEMMA ACKeep ==
  ASSUME AppliedCommitted, applied' = applied, commits \subseteq commits'
  PROVE  AppliedCommitted'
BY DEF AppliedCommitted

LEMMA AppliedCommittedStep ==
  ASSUME Inv, ProtoCases
  PROVE  AppliedCommitted'
<1>0. Basic /\ TypeOK /\ Grows /\ AppliedCommitted BY InvBasic, GrowsStep DEF Inv
<1>1. CommitCases BY <1>0, Frame
<1>a. CASE Quiet BY <1>a, <1>0, ACKeep DEF Quiet
<1>b. ASSUME NEW i \in Server, Apply(i) PROVE AppliedCommitted'
  <2> DEFINE k == lastApplied[i] + 1
  <2>1. /\ k <= Len(log[i]) /\ IsCommitted(log[i], k)
        /\ applied' = applied \cup {[server |-> i, index |-> k, entry |-> log[i][k]]}
        /\ commits' = commits
    BY <1>b DEF Apply
  <2>2. log[i] \in Seq(EntryT) /\ k \in Nat /\ k >= 1 BY <1>0 DEF TypeOK
  <2> HIDE DEF k
  <2>3. PICK c \in commits : k <= Len(c.entries) /\ SubSeq(c.entries, 1, k) = SubSeq(log[i], 1, k)
    BY <2>1 DEF IsCommitted
  <2>4. c.entries \in Seq(EntryT) BY <1>0, TypeFacts
  <2>5. Agree(c.entries, log[i], k) BY <2>1, <2>2, <2>3, <2>4, SubSeqAgree
  <2>6. c.entries[k] = log[i][k] BY <2>5, <2>2 DEF Agree
  <2>7. \A a \in applied : \E x \in commits :
           1 <= a.index /\ a.index <= Len(x.entries) /\ x.entries[a.index] = a.entry
    BY <1>0 DEF AppliedCommitted
  <2> QED BY <2>1, <2>2, <2>3, <2>6, <2>7 DEF AppliedCommitted
<1>c. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE AppliedCommitted'
  BY <1>c, <1>0, ACKeep DEF LeaderCommit
<1>d. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE AppliedCommitted'
  BY <1>d, <1>0, ACKeep DEF Ack
<1>e. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE AppliedCommitted'
  BY <1>e, <1>0, ACKeep DEF AckCommitted
<1>f. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE AppliedCommitted'
  BY <1>f, <1>0, ACKeep DEF DeleteSuffix
<1>g. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE AppliedCommitted'
  BY <1>g, <1>0, ACKeep DEF StoreEntries
<1>h. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE AppliedCommitted'
  BY <1>h, <1>0, ACKeep DEF FollowerCommit
<1> QED BY <1>1, <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h DEF CommitCases

----
\* Together.

LEMMA CGInit == ASSUME Init PROVE CG
<1>1. AckFacts BY DEF Init, AckFacts
<1>2. CommitRoot BY DEF Init, CommitRoot
<1>3. FirstRoot BY DEF Init, FirstRoot
<1>4. CommitSafetyP BY DEF Init, CommitSafetyP
<1>5. CommitKept BY DEF Init, CommitKept
<1>6. AppliedCommitted BY DEF Init, AppliedCommitted
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF CG

LEMMA CGUnch == ASSUME CG, UNCHANGED vars PROVE CG'
<1> USE DEF vars, protoVars, durable
<1>1. AckFacts' BY DEF CG, AckFacts, IsLd
<1>2. CommitRoot' BY DEF CG, CommitRoot, Root, MRoot, Good, Cover, AtMostOne, AckedBy, Pre, Agree
<1>3. FirstRoot' BY DEF CG, FirstRoot, MRoot, Good, Cover, AtMostOne, AckedBy, Pre, Agree
<1>4. CommitSafetyP' BY DEF CG, CommitSafetyP
<1>5. CommitKept' BY DEF CG, CommitKept
<1>6. AppliedCommitted' BY DEF CG, AppliedCommitted
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF CG

THEOREM CGStep == ASSUME Inv, ProtoCases PROVE CG'
BY AckFactsStep, CommitRootStep, FirstRootStep, CommitSafetyPStep, CommitKeptStep, AppliedCommittedStep DEF CG
====
