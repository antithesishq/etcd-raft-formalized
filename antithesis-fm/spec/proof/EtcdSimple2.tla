---- MODULE EtcdSimple2 ----
\* Invariants about logs and leader logs.
EXTENDS EtcdSimple1, EtcdLog

S2 == /\ LedOwner /\ ReqFromLed /\ LogFromLed /\ LedFromLed /\ LogTermsBound /\ LedTermsBound
      /\ ConfirmedIsLed

LEMMA S2Init == ASSUME Init PROVE S2
BY DEF Init, S2, LedOwner, ReqFromLed, LogFromLed, LedFromLed, LogTermsBound, LedTermsBound,
       ConfirmedIsLed, FromLed

LEMMA S2Unch == ASSUME S2, UNCHANGED vars PROVE S2'
BY DEF vars, protoVars, durable, S2, LedOwner, ReqFromLed, LogFromLed, LedFromLed, LogTermsBound,
       LedTermsBound, ConfirmedIsLed, FromLed, Agree, Pre, TermAt

\* ---- LedOwner
LEMMA LedOwnerKeep ==
  ASSUME TypeOK, LedOwner, Grows, UNCHANGED <<leaders, currentTerm, log>>, LedDom
  PROVE  LedOwner'
<1> SUFFICES ASSUME NEW ld \in leaders, ld.term = currentTerm[ld.server]
             PROVE Pre(log[ld.server], ledLog'[ld.term])
  BY DEF LedOwner
<1>1. ld.term \in DOMAIN ledLog /\ ld.server \in Server BY DEF LedDom, TypeOK, LeaderT
<1>2. Pre(log[ld.server], ledLog[ld.term]) BY DEF LedOwner
<1>3. Pre(ledLog[ld.term], ledLog'[ld.term]) /\ ledLog'[ld.term] \in Seq(EntryT) BY <1>1 DEF Grows
<1>4. log[ld.server] \in Seq(EntryT) /\ ledLog[ld.term] \in Seq(EntryT) BY <1>1 DEF TypeOK
<1> QED BY <1>2, <1>3, <1>4, PreTrans

LEMMA LedOwnerStep ==
  ASSUME Basic, S1, S2, ProtoCases
  PROVE  LedOwner'
<1>G. Grows BY GrowsStep
<1>T. TypeOK BY DEF Basic
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE LedOwner'
  BY <1>a, <1>G, <1>T, LedOwnerKeep DEF BecomeCandidate, durable, Basic, S2
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE LedOwner'
  BY <1>b, <1>G, <1>T, LedOwnerKeep DEF BecomeFollower, durable, Basic, S2
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE LedOwner'
  <2> DEFINE u == currentTerm[i]
  <2>1. /\ u \notin DOMAIN ledLog /\ ledLog'[u] = log[i]
        /\ \A t \in DOMAIN ledLog : ledLog'[t] = ledLog[t]
        /\ leaders' = leaders \cup {[server |-> i, term |-> u]}
        /\ UNCHANGED <<currentTerm, log>>
    BY <1>c, BecomeLeaderLed DEF durable
  <2>2. log \in [Server -> Seq(EntryT)] BY <1>T DEF TypeOK
  <2> SUFFICES ASSUME NEW ld \in leaders', ld.term = currentTerm[ld.server]
               PROVE Pre(log[ld.server], ledLog'[ld.term])
    BY <2>1 DEF LedOwner
  <2>3. CASE ld \in leaders
    <3>1. ld.term \in DOMAIN ledLog BY <2>3 DEF Basic, LedDom
    <3>2. Pre(log[ld.server], ledLog[ld.term]) BY <2>3 DEF S2, LedOwner
    <3> QED BY <3>1, <3>2, <2>1
  <2>4. CASE ld = [server |-> i, term |-> u]
    <3>1. ld.server = i /\ ld.term = u BY <2>4
    <3>2. Pre(log[i], log[i]) BY <2>2 DEF Pre, Agree
    <3> QED BY <3>1, <3>2, <2>1
  <2> QED BY <2>3, <2>4, <2>1
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE LedOwner'
  <2>1. \A ld \in leaders : ld.server \in Server /\ ld.term \in Nat /\ ld.term <= currentTerm[ld.server]
    BY <1>T DEF TypeOK, LeaderT, S1, LeadersTermBound
  <2>2. currentTerm \in [Server -> Nat] BY <1>T DEF TypeOK
  <2> QED BY <1>d, <2>1, <2>2 DEF StartElection, S2, LedOwner
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE LedOwner'
  BY <1>e, <1>G, <1>T, LedOwnerKeep DEF Restart, durable, Basic, S2
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE LedOwner'
  BY <1>f, <1>G, <1>T, LedOwnerKeep DEF Apply, durable, Basic, S2
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE LedOwner'
  BY <1>g, <1>G, <1>T, LedOwnerKeep DEF Restore, durable, Basic, S2
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE LedOwner'
  BY <1>h, <1>G, <1>T, LedOwnerKeep DEF SwitchConf, durable, Basic, S2
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE LedOwner'
  BY <1>i, <1>G, <1>T, LedOwnerKeep DEF RestoreConf, durable, Basic, S2
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE LedOwner'
  BY <1>j, <1>G, <1>T, LedOwnerKeep DEF LeaderAppend1, durable, Basic, S2
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE LedOwner'
  <2>1. \A ld \in leaders : ld.server \in Server /\ ld.term \in Nat /\ ld.term <= currentTerm[ld.server]
    BY <1>T DEF TypeOK, LeaderT, S1, LeadersTermBound
  <2>2. currentTerm \in [Server -> Nat] BY <1>T DEF TypeOK
  <2> QED BY <1>k, <2>1, <2>2 DEF AdoptTerm, S2, LedOwner
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE LedOwner'
  BY <1>l, <1>G, <1>T, LedOwnerKeep DEF CastVote, durable, Basic, S2
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE LedOwner'
  BY <1>m, <1>G, <1>T, LedOwnerKeep DEF GrantVote, durable, Basic, S2
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE LedOwner'
  BY <1>n, <1>G, <1>T, LedOwnerKeep DEF LeaderCommit, durable, Basic, S2
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE LedOwner'
  BY <1>o, <1>G, <1>T, LedOwnerKeep DEF SendAppend, durable, Basic, S2
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE LedOwner'
  BY <1>p, <1>G, <1>T, LedOwnerKeep DEF Ack, durable, Basic, S2
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE LedOwner'
  BY <1>q, <1>G, <1>T, LedOwnerKeep DEF AckCommitted, durable, Basic, S2
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE LedOwner'
  <2>1. /\ log' = [log EXCEPT ![j] = log'[j]] /\ log'[j] \in Seq(EntryT) /\ Pre(log'[j], log[j])
    BY <1>r, <1>T, DeleteLog, DeleteAgree DEF S2
  <2>2. log \in [Server -> Seq(EntryT)] BY <1>T DEF TypeOK
  <2> SUFFICES ASSUME NEW ld \in leaders, ld.term = currentTerm[ld.server]
               PROVE Pre(log'[ld.server], ledLog[ld.term])
    BY <1>r DEF LedOwner, DeleteSuffix
  <2>3. ld.term \in DOMAIN ledLog /\ ld.server \in Server BY <1>T DEF Basic, LedDom, TypeOK, LeaderT
  <2>4. Pre(log[ld.server], ledLog[ld.term]) /\ ledLog[ld.term] \in Seq(EntryT) BY <2>3, <1>T DEF S2, LedOwner, TypeOK
  <2>5. CASE ld.server # j BY <2>5, <2>1, <2>3, <2>4, <2>2
  <2>6. CASE ld.server = j BY <2>6, <2>1, <2>2, <2>4, PreTrans
  <2> QED BY <2>5, <2>6
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE LedOwner'
  <2>1. /\ log' = [log EXCEPT ![j] = log'[j]] /\ m.term \in DOMAIN ledLog /\ Pre(log'[j], ledLog[m.term])
    BY <1>s, <1>T, StoreLog, StoreAgree DEF S2
  <2>2. log \in [Server -> Seq(EntryT)] BY <1>T DEF TypeOK
  <2> SUFFICES ASSUME NEW ld \in leaders, ld.term = currentTerm[ld.server]
               PROVE Pre(log'[ld.server], ledLog[ld.term])
    BY <1>s DEF LedOwner, StoreEntries
  <2>3. ld.term \in DOMAIN ledLog /\ ld.server \in Server BY <1>T DEF Basic, LedDom, TypeOK, LeaderT
  <2>4. Pre(log[ld.server], ledLog[ld.term]) BY DEF S2, LedOwner
  <2>5. CASE ld.server # j BY <2>5, <2>1, <2>3, <2>4, <2>2
  <2>6. CASE ld.server = j
    <3>1. m.term = ld.term BY <2>6, <1>s DEF StoreEntries
    <3> QED BY <3>1, <2>6, <2>1
  <2> QED BY <2>5, <2>6
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE LedOwner'
  BY <1>t, <1>G, <1>T, LedOwnerKeep DEF FollowerCommit, durable, Basic, S2
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases


\* ---- ReqFromLed
LEMMA ReqFromLedKeep ==
  ASSUME TypeOK, ReqFromLed, Grows, msgs' \subseteq MsgT, \A m \in msgs' \ msgs : m.type # "append"
  PROVE  ReqFromLed'
<1> SUFFICES ASSUME NEW m \in msgs', m.type = "append"
             PROVE /\ m.term \in DOMAIN ledLog'
                   /\ m.prevLogIndex + Len(m.entries) <= Len(ledLog'[m.term])
                   /\ m.prevLogTerm = TermAt(ledLog'[m.term], m.prevLogIndex)
                   /\ \A q \in 1..Len(m.entries) : m.entries[q] = ledLog'[m.term][m.prevLogIndex + q]
                   /\ (m.commit = 0 \/ \E k \in commits' : k.term <= m.term /\ Agree(k.entries, ledLog'[m.term], m.commit))
  BY DEF ReqFromLed
<1>1. m \in msgs /\ m \in AppendT BY AppendMsgType DEF TypeOK
<1> DEFINE p == m.prevLogIndex  L == ledLog[m.term]  L2 == ledLog'[m.term]
<1>2. /\ m.term \in DOMAIN ledLog
      /\ p + Len(m.entries) <= Len(L)
      /\ m.prevLogTerm = TermAt(L, p)
      /\ \A q \in 1..Len(m.entries) : m.entries[q] = L[p + q]
      /\ (m.commit = 0 \/ \E k \in commits : k.term <= m.term /\ Agree(k.entries, L, m.commit))
  BY <1>1 DEF ReqFromLed
<1>3. p \in Nat /\ m.entries \in Seq(EntryT) /\ m.commit \in Nat BY <1>1 DEF AppendT
<1>4. L \in Seq(EntryT) /\ L2 \in Seq(EntryT) /\ Pre(L, L2) /\ m.term \in DOMAIN ledLog'
  BY <1>2 DEF TypeOK, Grows
<1>5. p + Len(m.entries) <= Len(L2) BY <1>2, <1>3, <1>4 DEF Pre, Agree
<1>6. TermAt(L2, p) = TermAt(L, p) BY <1>2, <1>3, <1>4 DEF Pre, Agree, TermAt
<1>7. \A q \in 1..Len(m.entries) : m.entries[q] = L2[p + q] BY <1>2, <1>3, <1>4 DEF Pre, Agree
<1>8. m.commit = 0 \/ \E k \in commits' : k.term <= m.term /\ Agree(k.entries, L2, m.commit)
  <2>1. CASE m.commit = 0 BY <2>1
  <2>2. CASE m.commit # 0
    <3>1. PICK k \in commits : k.term <= m.term /\ Agree(k.entries, L, m.commit) BY <2>2, <1>2
    <3>2. k.entries \in Seq(EntryT) BY DEF TypeOK, CommitT
    <3>3. Agree(k.entries, L2, m.commit) BY <3>1, <3>2, <1>2, <1>3, AgreeGrowL
    <3>4. k \in commits' BY DEF Grows
    <3> QED BY <3>1, <3>3, <3>4
  <2> QED BY <2>1, <2>2
<1> QED BY <1>4, <1>5, <1>6, <1>7, <1>8, <1>2

LEMMA ReqFromLedStep ==
  ASSUME Basic, S1, S2, ProtoCases
  PROVE  ReqFromLed'
<1>G. Grows BY GrowsStep
<1>T. TypeOK BY DEF Basic
<1>T2. msgs' \subseteq MsgT BY TypeProto DEF TypeP
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE ReqFromLed'
  BY <1>a, <1>G, <1>T, <1>T2, ReqFromLedKeep DEF BecomeCandidate, durable, S2
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE ReqFromLed'
  BY <1>b, <1>G, <1>T, <1>T2, ReqFromLedKeep DEF BecomeFollower, durable, S2
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE ReqFromLed'
  BY <1>c, <1>G, <1>T, <1>T2, ReqFromLedKeep DEF BecomeLeader, durable, S2
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE ReqFromLed'
  BY <1>d, <1>G, <1>T, <1>T2, ReqFromLedKeep DEF StartElection, durable, S2, VoteRequest
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE ReqFromLed'
  BY <1>e, <1>G, <1>T, <1>T2, ReqFromLedKeep DEF Restart, durable, S2
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE ReqFromLed'
  BY <1>f, <1>G, <1>T, <1>T2, ReqFromLedKeep DEF Apply, durable, S2
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE ReqFromLed'
  BY <1>g, <1>G, <1>T, <1>T2, ReqFromLedKeep DEF Restore, durable, S2
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE ReqFromLed'
  BY <1>h, <1>G, <1>T, <1>T2, ReqFromLedKeep DEF SwitchConf, durable, S2
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE ReqFromLed'
  BY <1>i, <1>G, <1>T, <1>T2, ReqFromLedKeep DEF RestoreConf, durable, S2
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE ReqFromLed'
  BY <1>j, <1>G, <1>T, <1>T2, ReqFromLedKeep DEF LeaderAppend1, durable, S2
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE ReqFromLed'
  BY <1>k, <1>G, <1>T, <1>T2, ReqFromLedKeep DEF AdoptTerm, durable, S2
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE ReqFromLed'
  BY <1>l, <1>G, <1>T, <1>T2, ReqFromLedKeep DEF CastVote, durable, S2
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE ReqFromLed'
  BY <1>m, <1>G, <1>T, <1>T2, ReqFromLedKeep DEF GrantVote, durable, S2
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE ReqFromLed'
  BY <1>n, <1>G, <1>T, <1>T2, ReqFromLedKeep DEF LeaderCommit, durable, S2
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE ReqFromLed'
  <2> DEFINE L == ledLog[t]
           mm == [type |-> "append", src |-> i, dst |-> j, term |-> t,
                  prevLogIndex |-> p, prevLogTerm |-> TermAt(L, p),
                  entries |-> SubSeq(L, p + 1, p + n), commit |-> c]
  <2>1. t \in DOMAIN ledLog /\ p + n <= Len(L) /\ CommittedIn(L, c, t) /\ msgs' = msgs \cup {mm}
        /\ UNCHANGED <<ledLog, commits>>
    BY <1>o DEF SendAppend, Basic, LedDom
  <2>2. L \in Seq(EntryT) BY <2>1, <1>T DEF TypeOK
  <2>3. Len(SubSeq(L, p + 1, p + n)) = n /\ \A q \in 1..n : SubSeq(L, p + 1, p + n)[q] = L[p + q]
    BY <2>1, <2>2, SubSeqProperties
  <2>4. c = 0 \/ \E k \in commits : k.term <= t /\ Agree(k.entries, L, c)
    <3>1. CASE c = 0 BY <3>1
    <3>2. CASE c # 0
      <4>1. c <= Len(L) BY <3>2, <2>1 DEF CommittedIn
      <4>2. PICK k \in commits : k.term <= t /\ c <= Len(k.entries) /\ SubSeq(k.entries, 1, c) = SubSeq(L, 1, c)
        BY <3>2, <2>1 DEF CommittedIn, KnownIn
      <4>3. k.entries \in Seq(EntryT) BY <1>T DEF TypeOK, CommitT
      <4>4. Agree(k.entries, L, c) BY <4>1, <4>2, <4>3, <2>2, SubSeqAgree
      <4> QED BY <4>2, <4>4
    <3> QED BY <3>1, <3>2
  <2>5. /\ mm.term \in DOMAIN ledLog
        /\ mm.prevLogIndex + Len(mm.entries) <= Len(ledLog[mm.term])
        /\ mm.prevLogTerm = TermAt(ledLog[mm.term], mm.prevLogIndex)
        /\ \A q \in 1..Len(mm.entries) : mm.entries[q] = ledLog[mm.term][mm.prevLogIndex + q]
        /\ (mm.commit = 0 \/ \E k \in commits : k.term <= mm.term /\ Agree(k.entries, ledLog[mm.term], mm.commit))
    BY <2>1, <2>3, <2>4
  <2> HIDE DEF mm, L
  <2> QED BY <2>1, <2>5 DEF S2, ReqFromLed
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE ReqFromLed'
  BY <1>p, <1>G, <1>T, <1>T2, ReqFromLedKeep DEF Ack, durable, S2
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE ReqFromLed'
  BY <1>q, <1>G, <1>T, <1>T2, ReqFromLedKeep DEF AckCommitted, durable, S2
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE ReqFromLed'
  BY <1>r, <1>G, <1>T, <1>T2, ReqFromLedKeep DEF DeleteSuffix, durable, S2
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE ReqFromLed'
  BY <1>s, <1>G, <1>T, <1>T2, ReqFromLedKeep DEF StoreEntries, durable, S2
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE ReqFromLed'
  BY <1>t, <1>G, <1>T, <1>T2, ReqFromLedKeep DEF FollowerCommit, durable, S2
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases


\* ---- LogFromLed
LEMMA LogFromLedKeep ==
  ASSUME TypeOK, LogFromLed, Grows, UNCHANGED log
  PROVE  LogFromLed'
<1> SUFFICES ASSUME NEW i \in Server PROVE FromLed(log[i])' BY DEF LogFromLed
<1>1. log[i] \in Seq(EntryT) /\ FromLed(log[i]) BY DEF TypeOK, LogFromLed
<1>2. FromLed(log[i])' = (\A q \in 1..Len(log[i]) : log[i][q].term \in DOMAIN ledLog' /\ Agree(log[i], ledLog'[log[i][q].term], q))
  BY DEF FromLed
<1>3. \A q \in 1..Len(log[i]) : log[i][q].term \in DOMAIN ledLog /\ Agree(log[i], ledLog[log[i][q].term], q)
  BY <1>1 DEF FromLed
<1>4. \A q \in 1..Len(log[i]) : Agree(log[i], ledLog'[log[i][q].term], q)
  BY <1>1, <1>3, AgreeGrowL
<1> QED BY <1>2, <1>3, <1>4 DEF Grows

\* FromLed of a constant sequence, after a step that leaves ledLog alone.
LEMMA LogFromLedSet ==
  ASSUME TypeOK, LogFromLed, UNCHANGED ledLog, NEW j \in Server, NEW l \in Seq(EntryT),
         log' = [log EXCEPT ![j] = l], FromLed(l)
  PROVE  LogFromLed'
<1> SUFFICES ASSUME NEW i \in Server
             PROVE \A q \in 1..Len(log'[i]) : log'[i][q].term \in DOMAIN ledLog /\ Agree(log'[i], ledLog[log'[i][q].term], q)
  BY DEF LogFromLed, FromLed
<1>1. log \in [Server -> Seq(EntryT)] BY DEF TypeOK
<1>2. CASE i = j BY <1>2, <1>1 DEF FromLed
<1>3. CASE i # j
  <2>1. log'[i] = log[i] BY <1>3, <1>1
  <2> QED BY <2>1 DEF LogFromLed, FromLed
<1> QED BY <1>2, <1>3

LEMMA LogFromLedStep ==
  ASSUME Basic, S1, S2, ProtoCases
  PROVE  LogFromLed'
<1>G. Grows BY GrowsStep
<1>T. TypeOK BY DEF Basic
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE LogFromLed'
  BY <1>a, <1>G, <1>T, LogFromLedKeep DEF BecomeCandidate, durable, S2
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE LogFromLed'
  BY <1>b, <1>G, <1>T, LogFromLedKeep DEF BecomeFollower, durable, S2
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE LogFromLed'
  BY <1>c, <1>G, <1>T, LogFromLedKeep DEF BecomeLeader, durable, S2
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE LogFromLed'
  BY <1>d, <1>G, <1>T, LogFromLedKeep DEF StartElection, durable, S2
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE LogFromLed'
  BY <1>e, <1>G, <1>T, LogFromLedKeep DEF Restart, durable, S2
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE LogFromLed'
  BY <1>f, <1>G, <1>T, LogFromLedKeep DEF Apply, durable, S2
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE LogFromLed'
  BY <1>g, <1>G, <1>T, LogFromLedKeep DEF Restore, durable, S2
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE LogFromLed'
  BY <1>h, <1>G, <1>T, LogFromLedKeep DEF SwitchConf, durable, S2
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE LogFromLed'
  BY <1>i, <1>G, <1>T, LogFromLedKeep DEF RestoreConf, durable, S2
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE LogFromLed'
  BY <1>j, <1>G, <1>T, LogFromLedKeep DEF LeaderAppend1, durable, S2
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE LogFromLed'
  BY <1>k, <1>G, <1>T, LogFromLedKeep DEF AdoptTerm, durable, S2
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE LogFromLed'
  BY <1>l, <1>G, <1>T, LogFromLedKeep DEF CastVote, durable, S2
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE LogFromLed'
  BY <1>m, <1>G, <1>T, LogFromLedKeep DEF GrantVote, durable, S2
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE LogFromLed'
  BY <1>n, <1>G, <1>T, LogFromLedKeep DEF LeaderCommit, durable, S2
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE LogFromLed'
  BY <1>o, <1>G, <1>T, LogFromLedKeep DEF SendAppend, durable, S2
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE LogFromLed'
  BY <1>p, <1>G, <1>T, LogFromLedKeep DEF Ack, durable, S2
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE LogFromLed'
  BY <1>q, <1>G, <1>T, LogFromLedKeep DEF AckCommitted, durable, S2
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE LogFromLed'
  <2>1. /\ log' = [log EXCEPT ![j] = log'[j]] /\ log'[j] \in Seq(EntryT) /\ Pre(log'[j], log[j])
    BY <1>r, <1>T, DeleteLog, DeleteAgree DEF S2
  <2>2. log[j] \in Seq(EntryT) /\ FromLed(log[j]) BY <1>T DEF TypeOK, S2, LogFromLed
  <2>3. FromLed(log'[j]) BY <2>1, <2>2, FromLedPrefix
  <2> QED BY <1>r, <1>T, <2>1, <2>3, LogFromLedSet DEF DeleteSuffix, S2
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE LogFromLed'
  <2>1. /\ log' = [log EXCEPT ![j] = log'[j]] /\ log'[j] \in Seq(EntryT)
        /\ m.term \in DOMAIN ledLog /\ Pre(log'[j], ledLog[m.term])
    BY <1>s, <1>T, StoreLog, StoreAgree DEF S2
  <2>2. ledLog[m.term] \in Seq(EntryT) /\ FromLed(ledLog[m.term]) BY <2>1, <1>T DEF TypeOK, S2, LedFromLed
  <2>3. FromLed(log'[j]) BY <2>1, <2>2, FromLedPrefix
  <2> QED BY <1>s, <1>T, <2>1, <2>3, LogFromLedSet DEF StoreEntries, S2
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE LogFromLed'
  BY <1>t, <1>G, <1>T, LogFromLedKeep DEF FollowerCommit, durable, S2
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases


\* ---- LedFromLed
LEMMA LedFromLedSame ==
  ASSUME LedFromLed, UNCHANGED ledLog PROVE LedFromLed'
BY DEF LedFromLed, FromLed

LEMMA LedFromLedStep ==
  ASSUME Basic, S1, S2, ProtoCases
  PROVE  LedFromLed'
<1>G. Grows BY GrowsStep
<1>T. TypeOK BY DEF Basic
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE LedFromLed'
  BY <1>a, LedFromLedSame DEF BecomeCandidate, durable, S2
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE LedFromLed'
  BY <1>b, LedFromLedSame DEF BecomeFollower, durable, S2
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE LedFromLed'
  <2> DEFINE u == currentTerm[i]
  <2>1. /\ DOMAIN ledLog' = DOMAIN ledLog \cup {u} /\ ledLog'[u] = log[i]
        /\ \A t \in DOMAIN ledLog : ledLog'[t] = ledLog[t]
    BY <1>c, BecomeLeaderLed
  <2>2. log[i] \in Seq(EntryT) /\ FromLedIn(log[i], ledLog) BY <1>T DEF TypeOK, S2, LogFromLed, FromLed, FromLedIn
  <2>3. FromLedIn(log[i], ledLog') BY <2>2, <1>G, <1>T, FromLedGrow2
  <2>5. \A q \in 1..Len(log[i]) : log[i][q].term \in DOMAIN ledLog' /\ Agree(log[i], ledLog'[log[i][q].term], q)
    BY <2>3 DEF FromLedIn
  <2>6. ASSUME NEW t \in DOMAIN ledLog
        PROVE \A q \in 1..Len(ledLog[t]) : ledLog[t][q].term \in DOMAIN ledLog' /\ Agree(ledLog[t], ledLog'[ledLog[t][q].term], q)
    <3>1. ledLog[t] \in Seq(EntryT) /\ FromLedIn(ledLog[t], ledLog) BY <1>T DEF TypeOK, S2, LedFromLed, FromLed, FromLedIn
    <3>2. FromLedIn(ledLog[t], ledLog') BY <3>1, <1>G, <1>T, FromLedGrow2
    <3> QED BY <3>2 DEF FromLedIn
  <2> SUFFICES ASSUME NEW t \in DOMAIN ledLog'
               PROVE \A q \in 1..Len(ledLog'[t]) : ledLog'[t][q].term \in DOMAIN ledLog' /\ Agree(ledLog'[t], ledLog'[ledLog'[t][q].term], q)
    BY DEF LedFromLed, FromLed
  <2>7. CASE t = u BY <2>7, <2>1, <2>5
  <2>8. CASE t \in DOMAIN ledLog BY <2>8, <2>1, <2>6
  <2> QED BY <2>7, <2>8, <2>1
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE LedFromLed'
  BY <1>d, LedFromLedSame DEF StartElection, durable, S2
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE LedFromLed'
  BY <1>e, LedFromLedSame DEF Restart, durable, S2
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE LedFromLed'
  BY <1>f, LedFromLedSame DEF Apply, durable, S2
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE LedFromLed'
  BY <1>g, LedFromLedSame DEF Restore, durable, S2
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE LedFromLed'
  BY <1>h, LedFromLedSame DEF SwitchConf, durable, S2
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE LedFromLed'
  BY <1>i, LedFromLedSame DEF RestoreConf, durable, S2
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE LedFromLed'
  <2> DEFINE u == currentTerm[i]  L == ledLog[u]  L2 == ledLog'[u]
  <2>1. /\ u \in DOMAIN ledLog /\ e.term = u /\ DOMAIN ledLog' = DOMAIN ledLog
        /\ L \in Seq(EntryT) /\ L2 \in Seq(EntryT) /\ Len(L2) = Len(L) + 1 /\ L2[Len(L) + 1] = e
        /\ \A q \in 1..Len(L) : L2[q] = L[q]
        /\ \A t \in DOMAIN ledLog : t # u => ledLog'[t] = ledLog[t]
    BY <1>j, AppendLed
  <2>4. ASSUME NEW t \in DOMAIN ledLog
        PROVE \A q \in 1..Len(ledLog[t]) : ledLog[t][q].term \in DOMAIN ledLog' /\ Agree(ledLog[t], ledLog'[ledLog[t][q].term], q)
    <3>1. ledLog[t] \in Seq(EntryT) /\ FromLedIn(ledLog[t], ledLog) BY <1>T DEF TypeOK, S2, LedFromLed, FromLed, FromLedIn
    <3>2. FromLedIn(ledLog[t], ledLog') BY <3>1, <1>G, <1>T, FromLedGrow2
    <3> QED BY <3>2 DEF FromLedIn
  <2> SUFFICES ASSUME NEW t \in DOMAIN ledLog, NEW q \in 1..Len(ledLog'[t])
               PROVE ledLog'[t][q].term \in DOMAIN ledLog' /\ Agree(ledLog'[t], ledLog'[ledLog'[t][q].term], q)
    BY <2>1 DEF LedFromLed, FromLed
  <2>5. CASE t # u BY <2>5, <2>1, <2>4
  <2>6. CASE t = u /\ q <= Len(L)
    <3>1. L[q].term \in DOMAIN ledLog' /\ Agree(L, ledLog'[L[q].term], q) BY <2>6, <2>1, <2>4
    <3>2. L2[q] = L[q] BY <2>6, <2>1
    <3>3. Agree(L2, ledLog'[L[q].term], q) BY <3>1, <2>6, <2>1 DEF Agree
    <3> QED BY <3>1, <3>2, <3>3, <2>6
  <2>7. CASE t = u /\ q = Len(L) + 1
    <3>1. L2[q].term = u BY <2>7, <2>1
    <3>2. Agree(L2, L2, q) BY <2>7, <2>1 DEF Agree
    <3> QED BY <3>1, <3>2, <2>7, <2>1
  <2> QED BY <2>5, <2>6, <2>7, <2>1
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE LedFromLed'
  BY <1>k, LedFromLedSame DEF AdoptTerm, durable, S2
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE LedFromLed'
  BY <1>l, LedFromLedSame DEF CastVote, durable, S2
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE LedFromLed'
  BY <1>m, LedFromLedSame DEF GrantVote, durable, S2
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE LedFromLed'
  BY <1>n, LedFromLedSame DEF LeaderCommit, durable, S2
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE LedFromLed'
  BY <1>o, LedFromLedSame DEF SendAppend, durable, S2
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE LedFromLed'
  BY <1>p, LedFromLedSame DEF Ack, durable, S2
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE LedFromLed'
  BY <1>q, LedFromLedSame DEF AckCommitted, durable, S2
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE LedFromLed'
  BY <1>r, LedFromLedSame DEF DeleteSuffix, durable, S2
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE LedFromLed'
  BY <1>s, LedFromLedSame DEF StoreEntries, durable, S2
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE LedFromLed'
  BY <1>t, LedFromLedSame DEF FollowerCommit, durable, S2
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases


\* ---- LogTermsBound
LEMMA LogTermsBoundStep ==
  ASSUME Basic, S1, S2, ProtoCases
  PROVE  LogTermsBound'
<1>G. Grows BY GrowsStep
<1>T. TypeOK BY DEF Basic
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE LogTermsBound'
  BY <1>a DEF BecomeCandidate, durable, S2, LogTermsBound
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE LogTermsBound'
  BY <1>b DEF BecomeFollower, durable, S2, LogTermsBound
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE LogTermsBound'
  BY <1>c DEF BecomeLeader, durable, S2, LogTermsBound
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE LogTermsBound'
  <2>1. currentTerm \in [Server -> Nat] /\ log \in [Server -> Seq(EntryT)] BY <1>T DEF TypeOK
  <2>2. \A s \in Server : \A q \in 1..Len(log[s]) : log[s][q].term \in Nat BY <2>1 DEF EntryT
  <2> QED BY <1>d, <2>1, <2>2 DEF StartElection, S2, LogTermsBound
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE LogTermsBound'
  BY <1>e DEF Restart, durable, S2, LogTermsBound
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE LogTermsBound'
  BY <1>f DEF Apply, durable, S2, LogTermsBound
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE LogTermsBound'
  BY <1>g DEF Restore, durable, S2, LogTermsBound
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE LogTermsBound'
  BY <1>h DEF SwitchConf, durable, S2, LogTermsBound
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE LogTermsBound'
  BY <1>i DEF RestoreConf, durable, S2, LogTermsBound
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE LogTermsBound'
  BY <1>j DEF LeaderAppend1, durable, S2, LogTermsBound
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE LogTermsBound'
  <2>1. currentTerm \in [Server -> Nat] /\ log \in [Server -> Seq(EntryT)] BY <1>T DEF TypeOK
  <2>2. \A s \in Server : \A q \in 1..Len(log[s]) : log[s][q].term \in Nat BY <2>1 DEF EntryT
  <2> QED BY <1>k, <2>1, <2>2 DEF AdoptTerm, S2, LogTermsBound
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE LogTermsBound'
  BY <1>l DEF CastVote, durable, S2, LogTermsBound
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE LogTermsBound'
  BY <1>m DEF GrantVote, durable, S2, LogTermsBound
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE LogTermsBound'
  BY <1>n DEF LeaderCommit, durable, S2, LogTermsBound
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE LogTermsBound'
  BY <1>o DEF SendAppend, durable, S2, LogTermsBound
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE LogTermsBound'
  BY <1>p DEF Ack, durable, S2, LogTermsBound
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE LogTermsBound'
  BY <1>q DEF AckCommitted, durable, S2, LogTermsBound
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE LogTermsBound'
  <2>1. /\ log' = [log EXCEPT ![j] = log'[j]] /\ log'[j] \in Seq(EntryT) /\ Pre(log'[j], log[j])
    BY <1>r, <1>T, DeleteLog, DeleteAgree DEF S2
  <2>2. log \in [Server -> Seq(EntryT)] BY <1>T DEF TypeOK
  <2>3. \A q \in 1..Len(log'[j]) : q \in 1..Len(log[j]) /\ log'[j][q] = log[j][q] BY <2>1, <2>2 DEF Pre, Agree
  <2> QED BY <1>r, <2>1, <2>2, <2>3 DEF DeleteSuffix, S2, LogTermsBound
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE LogTermsBound'
  <2>1. /\ log' = [log EXCEPT ![j] = log'[j]] /\ log'[j] \in Seq(EntryT)
        /\ m.term \in DOMAIN ledLog /\ Pre(log'[j], ledLog[m.term])
    BY <1>s, <1>T, StoreLog, StoreAgree DEF S2
  <2>2. log \in [Server -> Seq(EntryT)] /\ ledLog[m.term] \in Seq(EntryT) BY <2>1, <1>T DEF TypeOK
  <2>3. \A q \in 1..Len(log'[j]) : q \in 1..Len(ledLog[m.term]) /\ log'[j][q] = ledLog[m.term][q] BY <2>1, <2>2 DEF Pre, Agree
  <2>4. \A q \in 1..Len(ledLog[m.term]) : ledLog[m.term][q].term <= m.term BY <2>1 DEF S2, LedTermsBound
  <2>5. m.term = currentTerm[j] BY <1>s DEF StoreEntries
  <2> QED BY <1>s, <2>1, <2>2, <2>3, <2>4, <2>5 DEF StoreEntries, S2, LogTermsBound
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE LogTermsBound'
  BY <1>t DEF FollowerCommit, durable, S2, LogTermsBound
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases


\* ---- LedTermsBound
LEMMA LedTermsBoundStep ==
  ASSUME Basic, S1, S2, ProtoCases
  PROVE  LedTermsBound'
<1>G. Grows BY GrowsStep
<1>T. TypeOK BY DEF Basic
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE LedTermsBound'
  BY <1>a DEF BecomeCandidate, durable, S2, LedTermsBound
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE LedTermsBound'
  BY <1>b DEF BecomeFollower, durable, S2, LedTermsBound
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE LedTermsBound'
  <2> DEFINE u == currentTerm[i]
  <2>1. /\ DOMAIN ledLog' = DOMAIN ledLog \cup {u} /\ ledLog'[u] = log[i]
        /\ \A t \in DOMAIN ledLog : ledLog'[t] = ledLog[t]
    BY <1>c, BecomeLeaderLed
  <2>2. \A q \in 1..Len(log[i]) : log[i][q].term <= u BY DEF S2, LogTermsBound
  <2> HIDE DEF u
  <2> QED BY <2>1, <2>2 DEF S2, LedTermsBound
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE LedTermsBound'
  BY <1>d DEF StartElection, durable, S2, LedTermsBound
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE LedTermsBound'
  BY <1>e DEF Restart, durable, S2, LedTermsBound
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE LedTermsBound'
  BY <1>f DEF Apply, durable, S2, LedTermsBound
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE LedTermsBound'
  BY <1>g DEF Restore, durable, S2, LedTermsBound
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE LedTermsBound'
  BY <1>h DEF SwitchConf, durable, S2, LedTermsBound
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE LedTermsBound'
  BY <1>i DEF RestoreConf, durable, S2, LedTermsBound
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE LedTermsBound'
  <2> DEFINE u == currentTerm[i]  L == ledLog[u]  L2 == ledLog'[u]
  <2>1. /\ u \in DOMAIN ledLog /\ e.term = u /\ DOMAIN ledLog' = DOMAIN ledLog
        /\ L \in Seq(EntryT) /\ L2 \in Seq(EntryT) /\ Len(L2) = Len(L) + 1 /\ L2[Len(L) + 1] = e
        /\ \A q \in 1..Len(L) : L2[q] = L[q]
        /\ \A t \in DOMAIN ledLog : t # u => ledLog'[t] = ledLog[t]
    BY <1>j, AppendLed
  <2>2. \A q \in 1..Len(L) : L[q].term <= u BY <2>1 DEF S2, LedTermsBound
  <2>2a. u \in Nat BY <1>T DEF TypeOK
  <2>3. \A q \in 1..Len(L2) : L2[q].term <= u
    <3> TAKE q \in 1..Len(L2)
    <3>1. CASE q <= Len(L) BY <3>1, <2>1, <2>2
    <3>2. CASE q = Len(L) + 1 BY <3>2, <2>1, <2>2a
    <3> QED BY <3>1, <3>2, <2>1
  <2> HIDE DEF u, L, L2
  <2> QED BY <2>1, <2>3 DEF S2, LedTermsBound, L, L2
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE LedTermsBound'
  BY <1>k DEF AdoptTerm, durable, S2, LedTermsBound
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE LedTermsBound'
  BY <1>l DEF CastVote, durable, S2, LedTermsBound
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE LedTermsBound'
  BY <1>m DEF GrantVote, durable, S2, LedTermsBound
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE LedTermsBound'
  BY <1>n DEF LeaderCommit, durable, S2, LedTermsBound
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE LedTermsBound'
  BY <1>o DEF SendAppend, durable, S2, LedTermsBound
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE LedTermsBound'
  BY <1>p DEF Ack, durable, S2, LedTermsBound
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE LedTermsBound'
  BY <1>q DEF AckCommitted, durable, S2, LedTermsBound
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE LedTermsBound'
  BY <1>r DEF DeleteSuffix, durable, S2, LedTermsBound
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE LedTermsBound'
  BY <1>s DEF StoreEntries, durable, S2, LedTermsBound
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE LedTermsBound'
  BY <1>t DEF FollowerCommit, durable, S2, LedTermsBound
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases


\* ---- ConfirmedIsLed
LEMMA ConfirmedIsLedKeep ==
  ASSUME TypeOK, ConfirmedIsLed, Grows, UNCHANGED <<confirmed, log>>
  PROVE  ConfirmedIsLed'
<1> SUFFICES ASSUME NEW j \in Server, confirmed[j].index # 0
             PROVE confirmed[j].term \in DOMAIN ledLog' /\ Agree(log[j], ledLog'[confirmed[j].term], confirmed[j].index)
  BY DEF ConfirmedIsLed
<1>1. confirmed[j].term \in DOMAIN ledLog /\ Agree(log[j], ledLog[confirmed[j].term], confirmed[j].index)
  BY DEF ConfirmedIsLed
<1>2. log[j] \in Seq(EntryT) /\ confirmed[j].index \in Nat BY DEF TypeOK
<1> QED BY <1>1, <1>2, AgreeGrowL DEF Grows

\* One node's confirmed mark and log are set; leader logs are left alone.
LEMMA ConfirmedIsLedSet ==
  ASSUME TypeOK, ConfirmedIsLed, UNCHANGED ledLog, NEW j \in Server,
         \A i \in Server : i # j => confirmed'[i] = confirmed[i] /\ log'[i] = log[i],
         confirmed'[j].index = 0 \/
           (confirmed'[j].term \in DOMAIN ledLog /\ Agree(log'[j], ledLog[confirmed'[j].term], confirmed'[j].index))
  PROVE  ConfirmedIsLed'
BY DEF ConfirmedIsLed

LEMMA ConfirmedIsLedStep ==
  ASSUME Basic, S1, S2, ProtoCases
  PROVE  ConfirmedIsLed'
<1>G. Grows BY GrowsStep
<1>T. TypeOK BY DEF Basic
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE ConfirmedIsLed'
  BY <1>a, <1>G, <1>T, ConfirmedIsLedKeep DEF BecomeCandidate, durable, S2
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE ConfirmedIsLed'
  BY <1>b, <1>G, <1>T, ConfirmedIsLedKeep DEF BecomeFollower, durable, S2
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE ConfirmedIsLed'
  BY <1>c, <1>G, <1>T, ConfirmedIsLedKeep DEF BecomeLeader, durable, S2
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE ConfirmedIsLed'
  BY <1>d, <1>G, <1>T, ConfirmedIsLedKeep DEF StartElection, durable, S2
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE ConfirmedIsLed'
  BY <1>e, <1>G, <1>T, ConfirmedIsLedKeep DEF Restart, durable, S2
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE ConfirmedIsLed'
  BY <1>f, <1>G, <1>T, ConfirmedIsLedKeep DEF Apply, durable, S2
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE ConfirmedIsLed'
  BY <1>g, <1>G, <1>T, ConfirmedIsLedKeep DEF Restore, durable, S2
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE ConfirmedIsLed'
  BY <1>h, <1>G, <1>T, ConfirmedIsLedKeep DEF SwitchConf, durable, S2
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE ConfirmedIsLed'
  BY <1>i, <1>G, <1>T, ConfirmedIsLedKeep DEF RestoreConf, durable, S2
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE ConfirmedIsLed'
  BY <1>j, <1>G, <1>T, ConfirmedIsLedKeep DEF LeaderAppend1, durable, S2
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE ConfirmedIsLed'
  BY <1>k, <1>G, <1>T, ConfirmedIsLedKeep DEF AdoptTerm, durable, S2
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE ConfirmedIsLed'
  BY <1>l, <1>G, <1>T, ConfirmedIsLedKeep DEF CastVote, durable, S2
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE ConfirmedIsLed'
  BY <1>m, <1>G, <1>T, ConfirmedIsLedKeep DEF GrantVote, durable, S2
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE ConfirmedIsLed'
  BY <1>n, <1>G, <1>T, ConfirmedIsLedKeep DEF LeaderCommit, durable, S2
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE ConfirmedIsLed'
  BY <1>o, <1>G, <1>T, ConfirmedIsLedKeep DEF SendAppend, durable, S2
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE ConfirmedIsLed'
  <2> DEFINE last == m.prevLogIndex + Len(m.entries)
  <2>1. PrevOk(j, m) /\ HasFirst(j, m, Len(m.entries)) /\ UNCHANGED <<ledLog, log>>
        /\ confirmed' = [confirmed EXCEPT ![j] = [term |-> m.term, index |-> IF confirmed[j].term = m.term THEN Max(confirmed[j].index, last) ELSE last]]
    BY <1>p DEF Ack, Confirm, durable
  <2>2. m.entries \in Seq(EntryT) /\ m.type = "append" /\ m.prevLogIndex \in Nat BY <1>p DEF AppendT
  <2>3. Agree(log[j], ledLog[m.term], last) BY <2>1, <2>2, <1>T, <1>p, CheckedPrefix DEF S2
  <2>4. m.term \in DOMAIN ledLog BY <2>2 DEF S2, ReqFromLed
  <2>5. confirmed \in [Server -> [term : Nat, index : Nat]] BY <1>T DEF TypeOK
  <2>6. confirmed'[j].term = m.term /\ (confirmed'[j].index = last \/ (confirmed[j].term = m.term /\ confirmed'[j].index = confirmed[j].index))
    BY <2>1, <2>5 DEF Max
  <2>7. confirmed[j].index = 0 \/ (confirmed[j].term \in DOMAIN ledLog /\ Agree(log[j], ledLog[confirmed[j].term], confirmed[j].index))
    BY DEF S2, ConfirmedIsLed
  <2>8. confirmed'[j].index = 0 \/ (confirmed'[j].term \in DOMAIN ledLog /\ Agree(log'[j], ledLog[confirmed'[j].term], confirmed'[j].index))
    BY <2>1, <2>3, <2>4, <2>6, <2>7
  <2>9. \A s \in Server : s # j => confirmed'[s] = confirmed[s] /\ log'[s] = log[s] BY <2>1, <2>5
  <2> HIDE DEF last
  <2> QED BY <2>1, <2>8, <2>9, <1>T, ConfirmedIsLedSet DEF S2
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE ConfirmedIsLed'
  BY <1>q, <1>G, <1>T, ConfirmedIsLedKeep DEF AckCommitted, durable, S2
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE ConfirmedIsLed'
  <2>1. /\ log' = [log EXCEPT ![j] = log'[j]] /\ log'[j] \in Seq(EntryT)
        /\ Len(log'[j]) = m.prevLogIndex + k - 1
        /\ m.term \in DOMAIN ledLog /\ Pre(log'[j], ledLog[m.term])
    BY <1>r, <1>T, DeleteLog, DeleteAgree DEF S2
  <2>2. confirmed' = [confirmed EXCEPT ![j] = [term |-> m.term, index |-> m.prevLogIndex + k - 1]] /\ UNCHANGED ledLog
    BY <1>r DEF DeleteSuffix, Confirm
  <2>3. confirmed \in [Server -> [term : Nat, index : Nat]] /\ log \in [Server -> Seq(EntryT)] BY <1>T DEF TypeOK
  <2>4. confirmed'[j].term = m.term /\ confirmed'[j].index = Len(log'[j]) BY <2>1, <2>2, <2>3
  <2>5. Agree(log'[j], ledLog[confirmed'[j].term], confirmed'[j].index) BY <2>1, <2>4 DEF Pre
  <2>6. \A s \in Server : s # j => confirmed'[s] = confirmed[s] /\ log'[s] = log[s] BY <2>1, <2>2, <2>3
  <2> QED BY <2>1, <2>2, <2>4, <2>5, <2>6, <1>T, ConfirmedIsLedSet DEF S2
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE ConfirmedIsLed'
  <2>1. /\ log' = [log EXCEPT ![j] = log'[j]] /\ log'[j] \in Seq(EntryT)
        /\ Len(log'[j]) = m.prevLogIndex + Len(m.entries)
        /\ m.term \in DOMAIN ledLog /\ Pre(log'[j], ledLog[m.term])
    BY <1>s, <1>T, StoreLog, StoreAgree DEF S2
  <2>2. confirmed' = [confirmed EXCEPT ![j] = [term |-> m.term, index |-> m.prevLogIndex + Len(m.entries)]] /\ UNCHANGED ledLog
    BY <1>s DEF StoreEntries, Confirm
  <2>3. confirmed \in [Server -> [term : Nat, index : Nat]] /\ log \in [Server -> Seq(EntryT)] BY <1>T DEF TypeOK
  <2>4. confirmed'[j].term = m.term /\ confirmed'[j].index = Len(log'[j]) BY <2>1, <2>2, <2>3
  <2>5. Agree(log'[j], ledLog[confirmed'[j].term], confirmed'[j].index) BY <2>1, <2>4 DEF Pre
  <2>6. \A s \in Server : s # j => confirmed'[s] = confirmed[s] /\ log'[s] = log[s] BY <2>1, <2>2, <2>3
  <2> QED BY <2>1, <2>2, <2>4, <2>5, <2>6, <1>T, ConfirmedIsLedSet DEF S2
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE ConfirmedIsLed'
  BY <1>t, <1>G, <1>T, ConfirmedIsLedKeep DEF FollowerCommit, durable, S2
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases


THEOREM S2Step == ASSUME Basic, S1, S2, ProtoCases PROVE S2'
BY LedOwnerStep, ReqFromLedStep, LogFromLedStep, LedFromLedStep, LogTermsBoundStep, LedTermsBoundStep,
   ConfirmedIsLedStep DEF S2
====
