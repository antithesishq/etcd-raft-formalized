---- MODULE EtcdType ----
\* TypeOK, ConfirmedWithinLog, LedDom and LeaderIsElected are inductive together.
EXTENDS EtcdActs

Basic == TypeOK /\ ConfirmedWithinLog /\ LedDom /\ LeaderIsElected

LEMMA BasicInit == ASSUME ConstOK, Init PROVE Basic
<1> USE DEF Init
<1>1. TypeOK
  <2>1. read \in ReadT BY DEF NoRead, ReadT
  <2>2. DOMAIN ledLog = {} /\ DOMAIN ledConf = {} /\ DOMAIN ledAt = {} /\ DOMAIN elAt = {} OBVIOUS
  <2>3. InitConf \in ConfT BY DEF InitConf, ConfT, ConstOK
  <2> QED BY <2>1, <2>2, <2>3 DEF TypeOK, Follower, Candidate, Leader
<1>2. ConfirmedWithinLog BY DEF ConfirmedWithinLog
<1>3. LedDom BY DEF LedDom
<1>4. LeaderIsElected BY DEF LeaderIsElected, Follower, Leader
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF Basic

LEMMA ReadTypeStep == ASSUME TypeOK, [Next]_rvars PROVE read' \in ReadT
<1> USE DEF TypeOK
<1>1. CASE UNCHANGED read BY <1>1
<1>2. ASSUME NEW j \in Server, ReadAck(j) PROVE read' \in ReadT BY <1>2 DEF ReadAck, ReadT
<1>3. ASSUME ReadConfirm PROVE read' \in ReadT BY <1>3 DEF ReadConfirm, ReadT
<1>4. ASSUME NEW i \in Server, currentTerm[i] \in DOMAIN ledLog,
             NEW c \in 0..Len(ledLog[currentTerm[i]]), ReadRequest(i, c)
      PROVE read' \in ReadT
  <2>1. c \in Nat /\ currentTerm[i] \in Nat BY <1>4
  <2> QED BY <1>4, <2>1 DEF ReadRequest, ReadT
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF Next, ReadNext, rvars

\* TypeOK without the read index.
TypeP ==
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

\* The types after a step of the protocol.
LEMMA TypeProto == ASSUME Basic, ProtoCases PROVE TypeP'
<1> USE DEF Basic
<1> USE DEF TypeOK, TypeP
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE TypeP'
  BY <1>a DEF BecomeCandidate, durable, Candidate, Follower, Leader
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE TypeP'
  BY <1>b DEF BecomeFollower, durable, Candidate, Follower, Leader
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE TypeP'
  <2>1. leaders' \subseteq LeaderT BY <1>c DEF BecomeLeader, LeaderT
  <2>2. DOMAIN ledLog' = DOMAIN ledLog \cup {currentTerm[i]} /\ DOMAIN ledConf' = DOMAIN ledLog'
        /\ DOMAIN ledAt' = DOMAIN ledLog' /\ DOMAIN elAt' = DOMAIN ledLog'
    BY <1>c DEF BecomeLeader, WithLed, WithConf, With
  <2>3. \A t \in DOMAIN ledLog' : ledLog'[t] \in Seq(EntryT) /\ ledConf'[t] \in ConfT /\ ledAt'[t] \in Nat /\ elAt'[t] \in Nat
    BY <1>c DEF BecomeLeader, WithLed, WithConf, With
  <2>4. role' \in [Server -> {Follower, Candidate, Leader}] BY <1>c DEF BecomeLeader
  <2> QED BY <1>c, <2>1, <2>2, <2>3, <2>4 DEF BecomeLeader, durable
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE TypeP'
  <2>1. VoteRequest(i, currentTerm[i] + 1) \in MsgT
    BY DEF VoteRequest, MsgT, VoteReqT, LastTerm, TermAt, EntryT
  <2> QED BY <1>d, <2>1 DEF StartElection
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE TypeP'
  <2>1. InitConf \in ConfT BY DEF InitConf, ConfT, ConstOK
  <2> QED BY <1>e, <2>1 DEF Restart, durable, Candidate, Follower, Leader
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE TypeP'
  <2>1. lastApplied[i] + 1 \in 1..Len(log[i]) BY <1>f DEF Apply
  <2>2. [server |-> i, index |-> lastApplied[i] + 1, entry |-> log[i][lastApplied[i] + 1]] \in AppliedT
    BY <2>1 DEF AppliedT
  <2> QED BY <1>f, <2>2 DEF Apply, durable
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE TypeP'
  BY <1>g DEF Restore, durable
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE TypeP'
  <2>1. log[i][k] \in EntryT /\ IsConf(log[i][k]) BY <1>h DEF SwitchConf
  <2>2. NextConf(config[i], log[i][k].value) \in ConfT BY <2>1, EntryChange, NextConfType
  <2>3. role[i] = Leader => currentTerm[i] \in DOMAIN ledLog BY DEF LeaderIsElected, LedDom, IsLd
  <2>4. config' \in [Server -> ConfT] /\ confAt' \in [Server -> Nat] BY <1>h, <2>2 DEF SwitchConf
  <2>5. /\ DOMAIN ledConf' = DOMAIN ledLog /\ DOMAIN ledAt' = DOMAIN ledLog
        /\ \A t \in DOMAIN ledLog : ledConf'[t] \in ConfT /\ ledAt'[t] \in Nat
    <3>1. CASE role[i] # Leader BY <3>1, <1>h DEF SwitchConf
    <3>2. CASE role[i] = Leader
      <4> DEFINE u == currentTerm[i]  C == NextConf(config[i], log[i][k].value)
      <4>1. u \in DOMAIN ledLog BY <3>2, <2>3
      <4>2. ledConf' = [w \in DOMAIN ledConf \cup {u} |-> IF w = u THEN C ELSE ledConf[w]]
        BY <3>2, <1>h DEF SwitchConf, WithConf
      <4>3. ledAt' = [w \in DOMAIN ledAt \cup {u} |-> IF w = u THEN k ELSE ledAt[w]]
        BY <3>2, <1>h DEF SwitchConf, With
      <4>4. C \in ConfT /\ k \in Nat BY <2>2
      <4> HIDE DEF u, C
      <4> QED BY <4>1, <4>2, <4>3, <4>4
    <3> QED BY <3>1, <3>2
  <2> QED BY <1>h, <2>4, <2>5 DEF SwitchConf, durable
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE TypeP'
  <2>1. c.entries \in Seq(EntryT) /\ a \in Nat /\ a <= Len(c.entries) BY DEF CommitT
  <2>2. ConfOf(c.entries, a) \in ConfT BY <2>1, ConfOfType
  <2>3. LastConf(c.entries, a) \in Nat BY <2>1, LastConfFacts
  <2> QED BY <1>i, <2>2, <2>3 DEF RestoreConf, durable
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE TypeP'
  <2>1. DOMAIN ledLog' = DOMAIN ledLog BY <1>j DEF LeaderAppend1, WithLed
  <2>2. \A t \in DOMAIN ledLog : ledLog'[t] \in Seq(EntryT) BY <1>j DEF LeaderAppend1, WithLed
  <2> QED BY <1>j, <2>1, <2>2 DEF LeaderAppend1, durable
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE TypeP'
  BY <1>k DEF AdoptTerm, Candidate, Follower, Leader
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE TypeP'
  BY <1>l DEF CastVote, VoteT
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE TypeP'
  <2>1. [type |-> "grant", src |-> i, dst |-> c, term |-> t] \in MsgT BY DEF MsgT, GrantT
  <2> QED BY <1>m, <2>1 DEF GrantVote, durable
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE TypeP'
  <2>1. t \in DOMAIN ledLog BY <1>n DEF LeaderCommit, LedDom
  <2>2. ledLog[t] \in Seq(EntryT) /\ c <= Len(ledLog[t]) BY <1>n, <2>1 DEF LeaderCommit
  <2>3. SubSeq(ledLog[t], 1, c) \in Seq(EntryT) BY <2>2, SubSeqFacts
  <2>4. [server |-> i, term |-> t, entries |-> SubSeq(ledLog[t], 1, c)] \in CommitT BY <2>3 DEF CommitT
  <2> QED BY <1>n, <2>4 DEF LeaderCommit, durable
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat,
             SendAppend(i, j, t, p, n, c) PROVE TypeP'
  <2>1. t \in DOMAIN ledLog BY <1>o DEF SendAppend, LedDom
  <2>2. ledLog[t] \in Seq(EntryT) /\ p + n <= Len(ledLog[t]) BY <1>o, <2>1 DEF SendAppend
  <2>3. SubSeq(ledLog[t], p + 1, p + n) \in Seq(EntryT) BY <2>2, SubSeqProperties
  <2>4. TermAt(ledLog[t], p) \in Nat BY <2>2 DEF TermAt, EntryT
  <2>5. [type |-> "append", src |-> i, dst |-> j, term |-> t,
         prevLogIndex |-> p, prevLogTerm |-> TermAt(ledLog[t], p),
         entries |-> SubSeq(ledLog[t], p + 1, p + n), commit |-> c] \in MsgT
    BY <2>3, <2>4 DEF MsgT, AppendT
  <2> QED BY <1>o, <2>5 DEF SendAppend, durable
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE TypeP'
  <2> DEFINE last == m.prevLogIndex + Len(m.entries)
  <2>1. last \in Nat BY <1>p DEF AppendT
  <2>2. [type |-> "ack", src |-> j, dst |-> m.src, term |-> m.term, index |-> last] \in MsgT
    BY <1>p, <2>1 DEF MsgT, AckT, AppendT
  <2>3. confirmed' \in [Server -> [term : Nat, index : Nat]]
    BY <1>p, <2>1 DEF Ack, Confirm, Max, AppendT
  <2> HIDE DEF last
  <2> QED BY <1>p, <2>2, <2>3 DEF Ack, durable, last
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE TypeP'
  <2>1. [type |-> "ack", src |-> j, dst |-> m.src, term |-> m.term, index |-> commitIndex[j]] \in MsgT
    BY <1>q DEF MsgT, AckT, AppendT
  <2> QED BY <1>q, <2>1 DEF AckCommitted, durable
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE TypeP'
  <2>1. m.prevLogIndex \in Nat /\ m.term \in Nat /\ m.prevLogIndex + k <= Len(log[j]) BY <1>r DEF AppendT, DeleteSuffix
  <2>2. SubSeq(log[j], 1, m.prevLogIndex + k - 1) \in Seq(EntryT) BY <2>1, SubSeqProperties
  <2>3. log' \in [Server -> Seq(EntryT)] BY <1>r, <2>2 DEF DeleteSuffix
  <2>4. confirmed' \in [Server -> [term : Nat, index : Nat]] BY <1>r, <2>1 DEF DeleteSuffix, Confirm
  <2> QED BY <1>r, <2>3, <2>4 DEF DeleteSuffix
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE TypeP'
  <2>1. m.prevLogIndex \in Nat /\ m.term \in Nat /\ m.entries \in Seq(EntryT) BY <1>s DEF AppendT
  <2>2. SubSeq(m.entries, k, Len(m.entries)) \in Seq(EntryT) BY <2>1, SubSeqProperties
  <2>3. log[j] \o SubSeq(m.entries, k, Len(m.entries)) \in Seq(EntryT) BY <2>2
  <2>4. log' \in [Server -> Seq(EntryT)] BY <1>s, <2>3 DEF StoreEntries
  <2>5. confirmed' \in [Server -> [term : Nat, index : Nat]] BY <1>s, <2>1 DEF StoreEntries, Confirm
  <2> QED BY <1>s, <2>4, <2>5 DEF StoreEntries
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE TypeP'
  <2>1. c <= confirmed[j].index /\ confirmed[j].index <= Len(log[j]) /\ confirmed[j].index \in Nat
    BY <1>t DEF FollowerCommit, Min, ConfirmedWithinLog, AppendT
  <2>2. SubSeq(log[j], 1, c) \in Seq(EntryT) BY <2>1, SubSeqFacts
  <2>3. Committed(j, m.term, c) \in CommitT BY <1>t, <2>2 DEF Committed, CommitT, AppendT
  <2> QED BY <1>t, <2>3 DEF FollowerCommit
<1> HIDE DEF TypeOK, Basic
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n,
           <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases

LEMMA TypeStep == ASSUME Basic, [Next]_rvars PROVE TypeOK'
<1>0. read' \in ReadT BY ReadTypeStep DEF Basic
<1>1. CASE UNCHANGED vars BY <1>0, <1>1 DEF vars, protoVars, durable, TypeOK, Basic
<1>2. CASE ProtoCases
  <2>1. TypeP' BY <1>2, TypeProto
  <2> QED BY <2>1, <1>0 DEF TypeP, TypeOK
<1> QED BY <1>1, <1>2, NextCases DEF Basic

LEMMA CWLStep ==
  ASSUME Basic, ProtoCases
  PROVE  ConfirmedWithinLog'
<1> USE DEF Basic, ConfirmedWithinLog, durable
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE ConfirmedWithinLog'
  BY <1>a DEF BecomeCandidate
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE ConfirmedWithinLog'
  BY <1>b DEF BecomeFollower
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE ConfirmedWithinLog'
  BY <1>c DEF BecomeLeader
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE ConfirmedWithinLog'
  BY <1>d DEF StartElection
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE ConfirmedWithinLog'
  BY <1>e DEF Restart
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE ConfirmedWithinLog'
  BY <1>f DEF Apply
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE ConfirmedWithinLog'
  BY <1>g DEF Restore
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE ConfirmedWithinLog'
  BY <1>h DEF SwitchConf
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE ConfirmedWithinLog'
  BY <1>i DEF RestoreConf
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE ConfirmedWithinLog'
  BY <1>j DEF LeaderAppend1
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE ConfirmedWithinLog'
  BY <1>k DEF AdoptTerm
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE ConfirmedWithinLog'
  BY <1>l DEF CastVote
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE ConfirmedWithinLog'
  BY <1>m DEF GrantVote
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE ConfirmedWithinLog'
  BY <1>n DEF LeaderCommit
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE ConfirmedWithinLog'
  BY <1>o DEF SendAppend
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE ConfirmedWithinLog'
  <2>1. m.prevLogIndex \in Nat /\ m.entries \in Seq(EntryT) /\ log[j] \in Seq(EntryT) /\ confirmed[j].index \in Nat
    BY <1>p DEF TypeOK, AppendT
  <2>2. m.prevLogIndex + Len(m.entries) <= Len(log[j])
    BY <1>p, <2>1 DEF Ack, PrevOk, HasFirst
  <2> QED BY <1>p, <2>1, <2>2 DEF Ack, Confirm, Max, TypeOK
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE ConfirmedWithinLog'
  BY <1>q DEF AckCommitted
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE ConfirmedWithinLog'
  <2>1. m.prevLogIndex \in Nat /\ log[j] \in Seq(EntryT) /\ m.prevLogIndex + k <= Len(log[j])
    BY <1>r DEF TypeOK, AppendT, DeleteSuffix
  <2>2. Len(SubSeq(log[j], 1, m.prevLogIndex + k - 1)) = m.prevLogIndex + k - 1 BY <2>1, SubSeqProperties
  <2> QED BY <1>r, <2>1, <2>2 DEF DeleteSuffix, Confirm, TypeOK
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE ConfirmedWithinLog'
  <2>1. m.prevLogIndex \in Nat /\ log[j] \in Seq(EntryT) /\ m.entries \in Seq(EntryT)
    BY <1>s DEF TypeOK, AppendT
  <2>2. SubSeq(m.entries, k, Len(m.entries)) \in Seq(EntryT) /\ Len(SubSeq(m.entries, k, Len(m.entries))) = Len(m.entries) - k + 1
    BY <2>1, SubSeqProperties
  <2>3. Len(log[j] \o SubSeq(m.entries, k, Len(m.entries))) = Len(log[j]) + Len(m.entries) - k + 1 BY <2>1, <2>2
  <2> QED BY <1>s, <2>1, <2>3 DEF StoreEntries, Confirm, TypeOK
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE ConfirmedWithinLog'
  BY <1>t DEF FollowerCommit
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases

LEMMA LedDomStep ==
  ASSUME Basic, ProtoCases
  PROVE  LedDom'
<1> USE DEF Basic, LedDom, durable
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE LedDom'
  BY <1>a DEF BecomeCandidate
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE LedDom'
  BY <1>b DEF BecomeFollower
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE LedDom'
  <2>1. DOMAIN ledLog' = DOMAIN ledLog \cup {currentTerm[i]} BY <1>c DEF BecomeLeader, WithLed
  <2>2. leaders' = leaders \cup {[server |-> i, term |-> currentTerm[i]]} BY <1>c DEF BecomeLeader
  <2> QED BY <2>1, <2>2
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE LedDom'
  BY <1>d DEF StartElection
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE LedDom'
  BY <1>e DEF Restart
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE LedDom'
  BY <1>f DEF Apply
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE LedDom'
  BY <1>g DEF Restore
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE LedDom'
  BY <1>h DEF SwitchConf
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE LedDom'
  BY <1>i DEF RestoreConf
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE LedDom'
  <2>1. DOMAIN ledLog' = DOMAIN ledLog BY <1>j DEF LeaderAppend1, WithLed
  <2> QED BY <1>j, <2>1 DEF LeaderAppend1
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE LedDom'
  BY <1>k DEF AdoptTerm
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE LedDom'
  BY <1>l DEF CastVote
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE LedDom'
  BY <1>m DEF GrantVote
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE LedDom'
  BY <1>n DEF LeaderCommit
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE LedDom'
  BY <1>o DEF SendAppend
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE LedDom'
  BY <1>p DEF Ack
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE LedDom'
  BY <1>q DEF AckCommitted
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE LedDom'
  BY <1>r DEF DeleteSuffix
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE LedDom'
  BY <1>s DEF StoreEntries
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE LedDom'
  BY <1>t DEF FollowerCommit
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases

LEMMA LIEStep ==
  ASSUME Basic, ProtoCases
  PROVE  LeaderIsElected'
<1> USE DEF Basic, LeaderIsElected, IsLd, durable, Leader, Follower, Candidate
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE LeaderIsElected'
  BY <1>a DEF BecomeCandidate, TypeOK
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE LeaderIsElected'
  BY <1>b DEF BecomeFollower, TypeOK
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE LeaderIsElected'
  BY <1>c DEF BecomeLeader, TypeOK
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE LeaderIsElected'
  BY <1>d DEF StartElection, TypeOK
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE LeaderIsElected'
  BY <1>e DEF Restart, TypeOK
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE LeaderIsElected'
  BY <1>f DEF Apply
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE LeaderIsElected'
  BY <1>g DEF Restore
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE LeaderIsElected'
  BY <1>h DEF SwitchConf
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE LeaderIsElected'
  BY <1>i DEF RestoreConf
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE LeaderIsElected'
  BY <1>j DEF LeaderAppend1
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE LeaderIsElected'
  BY <1>k DEF AdoptTerm, TypeOK
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE LeaderIsElected'
  BY <1>l DEF CastVote
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE LeaderIsElected'
  BY <1>m DEF GrantVote
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE LeaderIsElected'
  BY <1>n DEF LeaderCommit
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE LeaderIsElected'
  BY <1>o DEF SendAppend
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE LeaderIsElected'
  BY <1>p DEF Ack
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE LeaderIsElected'
  BY <1>q DEF AckCommitted
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE LeaderIsElected'
  BY <1>r DEF DeleteSuffix
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE LeaderIsElected'
  BY <1>s DEF StoreEntries
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE LeaderIsElected'
  BY <1>t DEF FollowerCommit
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases

THEOREM BasicStep == ASSUME Basic, [Next]_rvars PROVE Basic'
<1>1. TypeOK' BY TypeStep
<1>2. CASE UNCHANGED vars
  BY <1>1, <1>2 DEF vars, protoVars, durable, Basic, ConfirmedWithinLog, LedDom, LeaderIsElected, IsLd
<1>3. CASE ProtoCases BY <1>1, <1>3, CWLStep, LedDomStep, LIEStep DEF Basic
<1> QED BY <1>2, <1>3, NextCases DEF Basic
====
