---- MODULE EtcdSimple3 ----
\* Invariants about vote requests, and LeaderSync, TermsPositive.
EXTENDS EtcdSimple2

S3 == /\ TermsPositive /\ ReqFacts /\ ReqUnique /\ VoteHasReq /\ CandLog /\ LedExtendsReq /\ LeaderSync

LEMMA S3Init == ASSUME Init PROVE S3
BY DEF Init, S3, TermsPositive, ReqFacts, ReqUnique, VoteHasReq, CandLog, LedExtendsReq, LeaderSync,
       Follower, Leader

LEMMA S3Unch == ASSUME S3, UNCHANGED vars PROVE S3'
BY DEF vars, protoVars, durable, S3, TermsPositive, ReqFacts, ReqUnique, VoteHasReq, CandLog,
       LedExtendsReq, LeaderSync, ReqOk, TermAt, LastTerm

\* Who is counted in Granted(i) has voted for i in i's term.
LEMMA GrantedVoted ==
  ASSUME GrantsAreVotes, NEW i \in Server, NEW n \in Granted(i)
  PROVE  [voter |-> n, term |-> currentTerm[i], cand |-> i] \in votes
<1>1. CASE n \in {j \in Server \ {i} : [type |-> "grant", src |-> j, dst |-> i, term |-> currentTerm[i]] \in msgs}
  <2> DEFINE g == [type |-> "grant", src |-> n, dst |-> i, term |-> currentTerm[i]]
  <2>1. g \in msgs /\ g.type = "grant" BY <1>1
  <2>2. [voter |-> g.src, term |-> g.term, cand |-> g.dst] \in votes BY <2>1 DEF GrantsAreVotes
  <2> QED BY <2>2
<1>2. CASE n \in (IF [voter |-> i, term |-> currentTerm[i], cand |-> i] \in votes THEN {i} ELSE {})
  BY <1>2
<1> QED BY <1>1, <1>2 DEF Granted

\* ---- TermsPositive
LEMMA TermsPositiveStep ==
  ASSUME Basic, S1, S2, S3, ProtoCases
  PROVE  TermsPositive'
<1>G. Grows BY GrowsStep
<1>T. TypeOK BY DEF Basic
<1>TP. TypeP' BY TypeProto
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE TermsPositive'
  BY <1>a DEF BecomeCandidate, durable, S3, TermsPositive
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE TermsPositive'
  BY <1>b DEF BecomeFollower, durable, S3, TermsPositive
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE TermsPositive'
  <2> DEFINE u == currentTerm[i]
  <2>1. /\ u \in Nat /\ DOMAIN ledLog' = DOMAIN ledLog \cup {u} /\ IsQuorum(Granted(i), config[i])
    BY <1>c, BecomeLeaderLed
  <2>2. config[i] \in ConfT /\ ConstOK BY <1>T DEF TypeOK
  <2>3. PICK n \in Server : n \in Granted(i) BY <2>1, <2>2, QuorumNonEmpty
  <2>4. [voter |-> n, term |-> u, cand |-> i] \in votes BY <2>3, GrantedVoted DEF S1
  <2>5. PICK m \in msgs : m.type = "vote" /\ m.src = i /\ m.term = u BY <2>4 DEF S3, VoteHasReq
  <2>6. m.lastLogTerm < u BY <2>5 DEF S3, ReqFacts, ReqOk
  <2>7. m \in VoteReqT BY <2>5, <1>T DEF TypeOK, MsgT, VoteReqT, GrantT, AppendT, AckT
  <2>8. u >= 1 BY <2>1, <2>6, <2>7 DEF VoteReqT
  <2> HIDE DEF u
  <2> QED BY <2>1, <2>8 DEF S3, TermsPositive
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE TermsPositive'
  BY <1>d DEF StartElection, durable, S3, TermsPositive
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE TermsPositive'
  BY <1>e DEF Restart, durable, S3, TermsPositive
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE TermsPositive'
  BY <1>f DEF Apply, durable, S3, TermsPositive
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE TermsPositive'
  BY <1>g DEF Restore, durable, S3, TermsPositive
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE TermsPositive'
  BY <1>h DEF SwitchConf, durable, S3, TermsPositive
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE TermsPositive'
  BY <1>i DEF RestoreConf, durable, S3, TermsPositive
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE TermsPositive'
  <2>1. DOMAIN ledLog' = DOMAIN ledLog BY <1>j, AppendLed
  <2> QED BY <2>1 DEF S3, TermsPositive
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE TermsPositive'
  BY <1>k DEF AdoptTerm, durable, S3, TermsPositive
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE TermsPositive'
  BY <1>l DEF CastVote, durable, S3, TermsPositive
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE TermsPositive'
  BY <1>m DEF GrantVote, durable, S3, TermsPositive
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE TermsPositive'
  BY <1>n DEF LeaderCommit, durable, S3, TermsPositive
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE TermsPositive'
  BY <1>o DEF SendAppend, durable, S3, TermsPositive
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE TermsPositive'
  BY <1>p DEF Ack, durable, S3, TermsPositive
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE TermsPositive'
  BY <1>q DEF AckCommitted, durable, S3, TermsPositive
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE TermsPositive'
  BY <1>r DEF DeleteSuffix, durable, S3, TermsPositive
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE TermsPositive'
  BY <1>s DEF StoreEntries, durable, S3, TermsPositive
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE TermsPositive'
  BY <1>t DEF FollowerCommit, durable, S3, TermsPositive
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases


\* ---- ReqFacts
LEMMA VoteMsgType ==
  ASSUME NEW m \in MsgT, m.type = "vote" PROVE m \in VoteReqT
BY DEF MsgT, VoteReqT, GrantT, AppendT, AckT

LEMMA ReqOkGrow ==
  ASSUME TypeOK, Grows, NEW u \in Nat, NEW li \in Nat, NEW lt \in Nat, ReqOk(u, li, lt)
  PROVE  ReqOk(u, li, lt)'
<1>1. CASE li = 0 /\ lt = 0 BY <1>1 DEF ReqOk
<1>2. CASE lt \in DOMAIN ledLog /\ li <= Len(ledLog[lt]) /\ TermAt(ledLog[lt], li) = lt
  <2>1. ledLog[lt] \in Seq(EntryT) /\ ledLog'[lt] \in Seq(EntryT) /\ Pre(ledLog[lt], ledLog'[lt]) /\ lt \in DOMAIN ledLog'
    BY <1>2 DEF TypeOK, Grows
  <2>2. li <= Len(ledLog'[lt]) /\ TermAt(ledLog'[lt], li) = TermAt(ledLog[lt], li)
    BY <1>2, <2>1 DEF Pre, Agree, TermAt
  <2> QED BY <1>2, <2>1, <2>2 DEF ReqOk
<1> QED BY <1>1, <1>2 DEF ReqOk

LEMMA ReqFactsKeep ==
  ASSUME TypeOK, ReqFacts, Grows, currentTerm' \in [Server -> Nat], \A m \in msgs' \ msgs : m.type # "vote"
  PROVE  ReqFacts'
<1> SUFFICES ASSUME NEW m \in msgs', m.type = "vote"
             PROVE m.term <= currentTerm'[m.src] /\ ReqOk(m.term, m.lastLogIndex, m.lastLogTerm)'
  BY DEF ReqFacts
<1>1. m \in msgs /\ m \in VoteReqT BY VoteMsgType DEF TypeOK
<1>2. m.term <= currentTerm[m.src] /\ ReqOk(m.term, m.lastLogIndex, m.lastLogTerm) BY <1>1 DEF ReqFacts
<1>3. m.src \in Server /\ m.term \in Nat /\ m.lastLogIndex \in Nat /\ m.lastLogTerm \in Nat BY <1>1 DEF VoteReqT
<1>4. currentTerm[m.src] <= currentTerm'[m.src] /\ currentTerm[m.src] \in Nat /\ currentTerm'[m.src] \in Nat
  BY <1>3 DEF Grows, TypeOK
<1>5. ReqOk(m.term, m.lastLogIndex, m.lastLogTerm)' BY <1>2, <1>3, ReqOkGrow
<1> QED BY <1>2, <1>3, <1>4, <1>5

LEMMA ReqFactsStep ==
  ASSUME Basic, S1, S2, S3, ProtoCases
  PROVE  ReqFacts'
<1>G. Grows BY GrowsStep
<1>T. TypeOK BY DEF Basic
<1>TP. TypeP' BY TypeProto
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE ReqFacts'
  BY <1>a, <1>G, <1>T, <1>TP, ReqFactsKeep DEF BecomeCandidate, durable, S3, TypeP
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE ReqFacts'
  BY <1>b, <1>G, <1>T, <1>TP, ReqFactsKeep DEF BecomeFollower, durable, S3, TypeP
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE ReqFacts'
  BY <1>c, <1>G, <1>T, <1>TP, ReqFactsKeep DEF BecomeLeader, durable, S3, TypeP
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE ReqFacts'
  <2> DEFINE u == currentTerm[i] + 1  li == Len(log[i])  lt == LastTerm(i)
           nm == VoteRequest(i, u)
  <2>1. msgs' = msgs \cup {nm} /\ currentTerm' = [currentTerm EXCEPT ![i] = u] /\ UNCHANGED ledLog
    BY <1>d DEF StartElection
  <2>2. currentTerm \in [Server -> Nat] /\ log[i] \in Seq(EntryT) BY <1>T DEF TypeOK
  <2>3. nm.type = "vote" /\ nm.src = i /\ nm.term = u /\ nm.lastLogIndex = li /\ nm.lastLogTerm = lt
    BY DEF VoteRequest
  <2>4. ReqOk(u, li, lt)
    <3>1. CASE li = 0 BY <3>1, <2>2 DEF ReqOk, LastTerm, TermAt
    <3>2. CASE li # 0
      <4>1. li \in 1..Len(log[i]) /\ lt = log[i][li].term BY <3>2, <2>2 DEF LastTerm, TermAt
      <4>2. lt <= currentTerm[i] BY <4>1 DEF S2, LogTermsBound
      <4>3. lt \in DOMAIN ledLog /\ Agree(log[i], ledLog[lt], li) BY <4>1 DEF S2, LogFromLed, FromLed
      <4>4. ledLog[lt] \in Seq(EntryT) /\ lt \in Nat BY <4>3, <1>T DEF TypeOK
      <4>5. li <= Len(ledLog[lt]) /\ ledLog[lt][li] = log[i][li] BY <4>1, <4>3 DEF Agree
      <4>6. TermAt(ledLog[lt], li) = lt BY <4>1, <4>4, <4>5 DEF TermAt
      <4> QED BY <4>2, <4>3, <4>4, <4>5, <4>6, <2>2 DEF ReqOk
    <3> QED BY <3>1, <3>2
  <2> HIDE DEF nm, li, lt
  <2> SUFFICES ASSUME NEW m \in msgs', m.type = "vote"
               PROVE m.term <= currentTerm'[m.src] /\ ReqOk(m.term, m.lastLogIndex, m.lastLogTerm)
    BY <2>1 DEF ReqFacts, ReqOk
  <2>5. CASE m = nm BY <2>5, <2>3, <2>4, <2>1, <2>2
  <2>6. CASE m \in msgs
    <3>1. m \in VoteReqT BY <2>6, <1>T, VoteMsgType DEF TypeOK
    <3>2. m.term <= currentTerm[m.src] /\ ReqOk(m.term, m.lastLogIndex, m.lastLogTerm) BY <2>6 DEF S3, ReqFacts
    <3>3. m.src \in Server /\ m.term \in Nat BY <3>1 DEF VoteReqT
    <3> QED BY <3>2, <3>3, <2>1, <2>2
  <2> QED BY <2>5, <2>6, <2>1
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE ReqFacts'
  BY <1>e, <1>G, <1>T, <1>TP, ReqFactsKeep DEF Restart, durable, S3, TypeP
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE ReqFacts'
  BY <1>f, <1>G, <1>T, <1>TP, ReqFactsKeep DEF Apply, durable, S3, TypeP
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE ReqFacts'
  BY <1>g, <1>G, <1>T, <1>TP, ReqFactsKeep DEF Restore, durable, S3, TypeP
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE ReqFacts'
  BY <1>h, <1>G, <1>T, <1>TP, ReqFactsKeep DEF SwitchConf, durable, S3, TypeP
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE ReqFacts'
  BY <1>i, <1>G, <1>T, <1>TP, ReqFactsKeep DEF RestoreConf, durable, S3, TypeP
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE ReqFacts'
  BY <1>j, <1>G, <1>T, <1>TP, ReqFactsKeep DEF LeaderAppend1, durable, S3, TypeP
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE ReqFacts'
  BY <1>k, <1>G, <1>T, <1>TP, ReqFactsKeep DEF AdoptTerm, durable, S3, TypeP
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE ReqFacts'
  BY <1>l, <1>G, <1>T, <1>TP, ReqFactsKeep DEF CastVote, durable, S3, TypeP
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE ReqFacts'
  BY <1>m, <1>G, <1>T, <1>TP, ReqFactsKeep DEF GrantVote, durable, S3, TypeP
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE ReqFacts'
  BY <1>n, <1>G, <1>T, <1>TP, ReqFactsKeep DEF LeaderCommit, durable, S3, TypeP
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE ReqFacts'
  BY <1>o, <1>G, <1>T, <1>TP, ReqFactsKeep DEF SendAppend, durable, S3, TypeP
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE ReqFacts'
  BY <1>p, <1>G, <1>T, <1>TP, ReqFactsKeep DEF Ack, durable, S3, TypeP
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE ReqFacts'
  BY <1>q, <1>G, <1>T, <1>TP, ReqFactsKeep DEF AckCommitted, durable, S3, TypeP
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE ReqFacts'
  BY <1>r, <1>G, <1>T, <1>TP, ReqFactsKeep DEF DeleteSuffix, durable, S3, TypeP
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE ReqFacts'
  BY <1>s, <1>G, <1>T, <1>TP, ReqFactsKeep DEF StoreEntries, durable, S3, TypeP
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE ReqFacts'
  BY <1>t, <1>G, <1>T, <1>TP, ReqFactsKeep DEF FollowerCommit, durable, S3, TypeP
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases


\* ---- ReqUnique
LEMMA ReqUniqueStep ==
  ASSUME Basic, S1, S2, S3, ProtoCases
  PROVE  ReqUnique'
<1>G. Grows BY GrowsStep
<1>T. TypeOK BY DEF Basic
<1>TP. TypeP' BY TypeProto
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE ReqUnique'
  BY <1>a DEF BecomeCandidate, durable, S3, ReqUnique
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE ReqUnique'
  BY <1>b DEF BecomeFollower, durable, S3, ReqUnique
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE ReqUnique'
  BY <1>c DEF BecomeLeader, durable, S3, ReqUnique
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE ReqUnique'
  <2> DEFINE nm == VoteRequest(i, currentTerm[i] + 1)
  <2>1. msgs' = msgs \cup {nm} BY <1>d DEF StartElection
  <2>2. nm.type = "vote" /\ nm.src = i /\ nm.term = currentTerm[i] + 1 BY DEF VoteRequest
  <2>3. currentTerm \in [Server -> Nat] BY <1>T DEF TypeOK
  <2>4. \A m \in msgs : m.type = "vote" /\ m.src = i => m.term # currentTerm[i] + 1
    <3> TAKE m \in msgs
    <3> SUFFICES ASSUME m.type = "vote", m.src = i PROVE m.term # currentTerm[i] + 1 OBVIOUS
    <3>1. m \in VoteReqT BY <1>T, VoteMsgType DEF TypeOK
    <3>2. m.term <= currentTerm[i] /\ m.term \in Nat BY <3>1 DEF S3, ReqFacts, VoteReqT
    <3> QED BY <3>2, <2>3
  <2> HIDE DEF nm
  <2> QED BY <2>1, <2>2, <2>4 DEF S3, ReqUnique
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE ReqUnique'
  BY <1>e DEF Restart, durable, S3, ReqUnique
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE ReqUnique'
  BY <1>f DEF Apply, durable, S3, ReqUnique
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE ReqUnique'
  BY <1>g DEF Restore, durable, S3, ReqUnique
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE ReqUnique'
  BY <1>h DEF SwitchConf, durable, S3, ReqUnique
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE ReqUnique'
  BY <1>i DEF RestoreConf, durable, S3, ReqUnique
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE ReqUnique'
  BY <1>j DEF LeaderAppend1, durable, S3, ReqUnique
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE ReqUnique'
  BY <1>k DEF AdoptTerm, durable, S3, ReqUnique
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE ReqUnique'
  BY <1>l DEF CastVote, durable, S3, ReqUnique
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE ReqUnique'
  BY <1>m DEF GrantVote, durable, S3, ReqUnique
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE ReqUnique'
  BY <1>n DEF LeaderCommit, durable, S3, ReqUnique
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE ReqUnique'
  BY <1>o DEF SendAppend, durable, S3, ReqUnique
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE ReqUnique'
  BY <1>p DEF Ack, durable, S3, ReqUnique
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE ReqUnique'
  BY <1>q DEF AckCommitted, durable, S3, ReqUnique
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE ReqUnique'
  BY <1>r DEF DeleteSuffix, durable, S3, ReqUnique
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE ReqUnique'
  BY <1>s DEF StoreEntries, durable, S3, ReqUnique
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE ReqUnique'
  BY <1>t DEF FollowerCommit, durable, S3, ReqUnique
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases


\* ---- VoteHasReq
LEMMA VoteHasReqStep ==
  ASSUME Basic, S1, S2, S3, ProtoCases
  PROVE  VoteHasReq'
<1>G. Grows BY GrowsStep
<1>T. TypeOK BY DEF Basic
<1>TP. TypeP' BY TypeProto
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE VoteHasReq'
  BY <1>a DEF BecomeCandidate, durable, S3, VoteHasReq
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE VoteHasReq'
  BY <1>b DEF BecomeFollower, durable, S3, VoteHasReq
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE VoteHasReq'
  BY <1>c DEF BecomeLeader, durable, S3, VoteHasReq
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE VoteHasReq'
  BY <1>d DEF StartElection, durable, S3, VoteHasReq
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE VoteHasReq'
  BY <1>e DEF Restart, durable, S3, VoteHasReq
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE VoteHasReq'
  BY <1>f DEF Apply, durable, S3, VoteHasReq
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE VoteHasReq'
  BY <1>g DEF Restore, durable, S3, VoteHasReq
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE VoteHasReq'
  BY <1>h DEF SwitchConf, durable, S3, VoteHasReq
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE VoteHasReq'
  BY <1>i DEF RestoreConf, durable, S3, VoteHasReq
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE VoteHasReq'
  BY <1>j DEF LeaderAppend1, durable, S3, VoteHasReq
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE VoteHasReq'
  BY <1>k DEF AdoptTerm, durable, S3, VoteHasReq
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE VoteHasReq'
  <2>1. \E mm \in msgs : mm.type = "vote" /\ mm.src = c /\ mm.term = currentTerm[i]
    BY <1>l DEF CastVote, MayVote
  <2>2. votes' = votes \cup {[voter |-> i, term |-> currentTerm[i], cand |-> c]} /\ UNCHANGED msgs
    BY <1>l DEF CastVote
  <2> QED BY <2>1, <2>2 DEF S3, VoteHasReq
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE VoteHasReq'
  BY <1>m DEF GrantVote, durable, S3, VoteHasReq
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE VoteHasReq'
  BY <1>n DEF LeaderCommit, durable, S3, VoteHasReq
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE VoteHasReq'
  BY <1>o DEF SendAppend, durable, S3, VoteHasReq
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE VoteHasReq'
  BY <1>p DEF Ack, durable, S3, VoteHasReq
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE VoteHasReq'
  BY <1>q DEF AckCommitted, durable, S3, VoteHasReq
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE VoteHasReq'
  BY <1>r DEF DeleteSuffix, durable, S3, VoteHasReq
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE VoteHasReq'
  BY <1>s DEF StoreEntries, durable, S3, VoteHasReq
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE VoteHasReq'
  BY <1>t DEF FollowerCommit, durable, S3, VoteHasReq
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases


\* ---- CandLog
LEMMA CandLogKeep ==
  ASSUME CandLog, UNCHANGED <<currentTerm, log>>, DOMAIN ledLog \subseteq DOMAIN ledLog',
         \A m \in msgs' \ msgs : m.type # "vote"
  PROVE  CandLog'
BY DEF CandLog, LastTerm

LEMMA CandLogStep ==
  ASSUME Basic, S1, S2, S3, ProtoCases
  PROVE  CandLog'
<1>G. Grows BY GrowsStep
<1>T. TypeOK BY DEF Basic
<1>TP. TypeP' BY TypeProto
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE CandLog'
  BY <1>a, <1>G, CandLogKeep DEF BecomeCandidate, durable, S3, Grows
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE CandLog'
  BY <1>b, <1>G, CandLogKeep DEF BecomeFollower, durable, S3, Grows
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE CandLog'
  BY <1>c, <1>G, CandLogKeep DEF BecomeLeader, durable, S3, Grows
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE CandLog'
  <2> DEFINE nm == VoteRequest(i, currentTerm[i] + 1)
  <2>1. msgs' = msgs \cup {nm} /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1] /\ UNCHANGED <<log, ledLog>>
    BY <1>d DEF StartElection
  <2>2. nm.type = "vote" /\ nm.src = i /\ nm.term = currentTerm[i] + 1
        /\ nm.lastLogIndex = Len(log[i]) /\ nm.lastLogTerm = LastTerm(i)
    BY DEF VoteRequest
  <2>3. currentTerm \in [Server -> Nat] BY <1>T DEF TypeOK
  <2> HIDE DEF nm
  <2> SUFFICES ASSUME NEW m \in msgs', m.type = "vote", currentTerm'[m.src] = m.term, m.term \notin DOMAIN ledLog
               PROVE Len(log[m.src]) = m.lastLogIndex /\ LastTerm(m.src) = m.lastLogTerm
    BY <2>1 DEF CandLog, LastTerm
  <2>4. CASE m = nm BY <2>4, <2>2
  <2>5. CASE m \in msgs
    <3>1. m \in VoteReqT BY <2>5, <1>T, VoteMsgType DEF TypeOK
    <3>2. m.term <= currentTerm[m.src] /\ m.term \in Nat /\ m.src \in Server BY <2>5, <3>1 DEF S3, ReqFacts, VoteReqT
    <3>3. m.src # i BY <3>2, <2>1, <2>3
    <3>4. currentTerm[m.src] = m.term BY <3>3, <3>2, <2>1, <2>3
    <3> QED BY <3>4, <2>5 DEF S3, CandLog
  <2> QED BY <2>4, <2>5, <2>1
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE CandLog'
  BY <1>e, <1>G, CandLogKeep DEF Restart, durable, S3, Grows
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE CandLog'
  BY <1>f, <1>G, CandLogKeep DEF Apply, durable, S3, Grows
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE CandLog'
  BY <1>g, <1>G, CandLogKeep DEF Restore, durable, S3, Grows
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE CandLog'
  BY <1>h, <1>G, CandLogKeep DEF SwitchConf, durable, S3, Grows
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE CandLog'
  BY <1>i, <1>G, CandLogKeep DEF RestoreConf, durable, S3, Grows
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE CandLog'
  BY <1>j, <1>G, CandLogKeep DEF LeaderAppend1, durable, S3, Grows
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE CandLog'
  <2>1. currentTerm' = [currentTerm EXCEPT ![i] = t] /\ t > currentTerm[i] /\ UNCHANGED <<log, ledLog, msgs>>
    BY <1>k DEF AdoptTerm
  <2>3. currentTerm \in [Server -> Nat] BY <1>T DEF TypeOK
  <2> SUFFICES ASSUME NEW m \in msgs, m.type = "vote", currentTerm'[m.src] = m.term, m.term \notin DOMAIN ledLog
               PROVE Len(log[m.src]) = m.lastLogIndex /\ LastTerm(m.src) = m.lastLogTerm
    BY <2>1 DEF CandLog, LastTerm
  <2>4. m \in VoteReqT BY <1>T, VoteMsgType DEF TypeOK
  <2>5. m.term <= currentTerm[m.src] /\ m.term \in Nat /\ m.src \in Server BY <2>4 DEF S3, ReqFacts, VoteReqT
  <2>6. m.src # i BY <2>5, <2>1, <2>3
  <2>7. currentTerm[m.src] = m.term BY <2>6, <2>5, <2>1, <2>3
  <2> QED BY <2>7 DEF S3, CandLog
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE CandLog'
  BY <1>l, <1>G, CandLogKeep DEF CastVote, durable, S3, Grows
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE CandLog'
  BY <1>m, <1>G, CandLogKeep DEF GrantVote, durable, S3, Grows
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE CandLog'
  BY <1>n, <1>G, CandLogKeep DEF LeaderCommit, durable, S3, Grows
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE CandLog'
  BY <1>o, <1>G, CandLogKeep DEF SendAppend, durable, S3, Grows
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE CandLog'
  BY <1>p, <1>G, CandLogKeep DEF Ack, durable, S3, Grows
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE CandLog'
  BY <1>q, <1>G, CandLogKeep DEF AckCommitted, durable, S3, Grows
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE CandLog'
  <2>1. log' = [log EXCEPT ![j] = log'[j]] BY <1>r, <1>T, DeleteLog
  <2>2. m.term = currentTerm[j] /\ UNCHANGED <<currentTerm, ledLog, msgs>> BY <1>r DEF DeleteSuffix
  <2>3. m.term \in DOMAIN ledLog BY <1>r DEF S2, ReqFromLed, AppendT
  <2>4. log \in [Server -> Seq(EntryT)] BY <1>T DEF TypeOK
  <2> SUFFICES ASSUME NEW vm \in msgs, vm.type = "vote", currentTerm[vm.src] = vm.term, vm.term \notin DOMAIN ledLog
               PROVE Len(log'[vm.src]) = vm.lastLogIndex /\ LastTerm(vm.src)' = vm.lastLogTerm
    BY <2>2 DEF CandLog
  <2>5. vm.src # j BY <2>2, <2>3
  <2>6. vm \in VoteReqT BY <1>T, VoteMsgType DEF TypeOK
  <2>7. log'[vm.src] = log[vm.src] BY <2>5, <2>6, <2>1, <2>4 DEF VoteReqT
  <2>8. Len(log[vm.src]) = vm.lastLogIndex /\ LastTerm(vm.src) = vm.lastLogTerm BY DEF S3, CandLog
  <2> QED BY <2>7, <2>8 DEF LastTerm
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE CandLog'
  <2>1. log' = [log EXCEPT ![j] = log'[j]] BY <1>s, <1>T, StoreLog
  <2>2. m.term = currentTerm[j] /\ UNCHANGED <<currentTerm, ledLog, msgs>> BY <1>s DEF StoreEntries
  <2>3. m.term \in DOMAIN ledLog BY <1>s DEF S2, ReqFromLed, AppendT
  <2>4. log \in [Server -> Seq(EntryT)] BY <1>T DEF TypeOK
  <2> SUFFICES ASSUME NEW vm \in msgs, vm.type = "vote", currentTerm[vm.src] = vm.term, vm.term \notin DOMAIN ledLog
               PROVE Len(log'[vm.src]) = vm.lastLogIndex /\ LastTerm(vm.src)' = vm.lastLogTerm
    BY <2>2 DEF CandLog
  <2>5. vm.src # j BY <2>2, <2>3
  <2>6. vm \in VoteReqT BY <1>T, VoteMsgType DEF TypeOK
  <2>7. log'[vm.src] = log[vm.src] BY <2>5, <2>6, <2>1, <2>4 DEF VoteReqT
  <2>8. Len(log[vm.src]) = vm.lastLogIndex /\ LastTerm(vm.src) = vm.lastLogTerm BY DEF S3, CandLog
  <2> QED BY <2>7, <2>8 DEF LastTerm
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE CandLog'
  BY <1>t, <1>G, CandLogKeep DEF FollowerCommit, durable, S3, Grows
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases


\* ---- LedExtendsReq
LEMMA LedExtendsReqKeep ==
  ASSUME TypeOK, LedDom, LedExtendsReq, Grows, UNCHANGED leaders, \A m \in msgs' \ msgs : m.type # "vote"
  PROVE  LedExtendsReq'
<1> SUFFICES ASSUME NEW ld \in leaders, NEW m \in msgs', m.type = "vote", m.src = ld.server, m.term = ld.term
             PROVE m.lastLogIndex <= Len(ledLog'[ld.term]) /\ TermAt(ledLog'[ld.term], m.lastLogIndex) = m.lastLogTerm
  BY DEF LedExtendsReq
<1>1. m \in msgs /\ m \in VoteReqT BY VoteMsgType DEF TypeOK
<1>2. ld.term \in DOMAIN ledLog BY DEF LedDom
<1>3. m.lastLogIndex <= Len(ledLog[ld.term]) /\ TermAt(ledLog[ld.term], m.lastLogIndex) = m.lastLogTerm
  BY <1>1 DEF LedExtendsReq
<1>4. ledLog[ld.term] \in Seq(EntryT) /\ ledLog'[ld.term] \in Seq(EntryT) /\ Pre(ledLog[ld.term], ledLog'[ld.term])
  BY <1>2 DEF TypeOK, Grows
<1>5. m.lastLogIndex \in Nat BY <1>1 DEF VoteReqT
<1> QED BY <1>3, <1>4, <1>5 DEF Pre, Agree, TermAt

LEMMA LedExtendsReqStep ==
  ASSUME Basic, S1, S2, S3, ProtoCases
  PROVE  LedExtendsReq'
<1>G. Grows BY GrowsStep
<1>T. TypeOK BY DEF Basic
<1>TP. TypeP' BY TypeProto
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE LedExtendsReq'
  BY <1>a, <1>G, <1>T, LedExtendsReqKeep DEF BecomeCandidate, durable, S3, Basic
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE LedExtendsReq'
  BY <1>b, <1>G, <1>T, LedExtendsReqKeep DEF BecomeFollower, durable, S3, Basic
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE LedExtendsReq'
  <2> DEFINE u == currentTerm[i]
  <2>1. /\ u \notin DOMAIN ledLog /\ ledLog'[u] = log[i]
        /\ \A t \in DOMAIN ledLog : ledLog'[t] = ledLog[t]
        /\ leaders' = leaders \cup {[server |-> i, term |-> u]}
        /\ UNCHANGED <<currentTerm, log, msgs>>
    BY <1>c, BecomeLeaderLed DEF durable
  <2> SUFFICES ASSUME NEW ld \in leaders', NEW m \in msgs, m.type = "vote", m.src = ld.server, m.term = ld.term
               PROVE m.lastLogIndex <= Len(ledLog'[ld.term]) /\ TermAt(ledLog'[ld.term], m.lastLogIndex) = m.lastLogTerm
    BY <2>1 DEF LedExtendsReq
  <2>2. CASE ld \in leaders
    <3>1. ld.term \in DOMAIN ledLog BY <2>2 DEF Basic, LedDom
    <3> QED BY <3>1, <2>1, <2>2 DEF S3, LedExtendsReq
  <2>3. CASE ld = [server |-> i, term |-> u]
    <3>1. m.src = i /\ m.term = u /\ ld.term = u BY <2>3
    <3>2. Len(log[i]) = m.lastLogIndex /\ LastTerm(i) = m.lastLogTerm BY <3>1, <2>1 DEF S3, CandLog
    <3>3. log[i] \in Seq(EntryT) BY <1>T DEF TypeOK
    <3> QED BY <3>1, <3>2, <3>3, <2>1 DEF LastTerm
  <2> QED BY <2>2, <2>3, <2>1
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE LedExtendsReq'
  <2> DEFINE nm == VoteRequest(i, currentTerm[i] + 1)
  <2>1. msgs' = msgs \cup {nm} /\ UNCHANGED <<leaders, ledLog>> BY <1>d DEF StartElection
  <2>2. nm.type = "vote" /\ nm.src = i /\ nm.term = currentTerm[i] + 1 BY DEF VoteRequest
  <2>3. currentTerm \in [Server -> Nat] BY <1>T DEF TypeOK
  <2>4. \A ld \in leaders : ld.server = i => ld.term # currentTerm[i] + 1
    <3> TAKE ld \in leaders
    <3>1. ld.term <= currentTerm[ld.server] /\ ld.term \in Nat BY <1>T DEF S1, LeadersTermBound, TypeOK, LeaderT
    <3> QED BY <3>1, <2>3
  <2> HIDE DEF nm
  <2> QED BY <2>1, <2>2, <2>4 DEF S3, LedExtendsReq
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE LedExtendsReq'
  BY <1>e, <1>G, <1>T, LedExtendsReqKeep DEF Restart, durable, S3, Basic
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE LedExtendsReq'
  BY <1>f, <1>G, <1>T, LedExtendsReqKeep DEF Apply, durable, S3, Basic
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE LedExtendsReq'
  BY <1>g, <1>G, <1>T, LedExtendsReqKeep DEF Restore, durable, S3, Basic
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE LedExtendsReq'
  BY <1>h, <1>G, <1>T, LedExtendsReqKeep DEF SwitchConf, durable, S3, Basic
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE LedExtendsReq'
  BY <1>i, <1>G, <1>T, LedExtendsReqKeep DEF RestoreConf, durable, S3, Basic
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE LedExtendsReq'
  BY <1>j, <1>G, <1>T, LedExtendsReqKeep DEF LeaderAppend1, durable, S3, Basic
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE LedExtendsReq'
  BY <1>k, <1>G, <1>T, LedExtendsReqKeep DEF AdoptTerm, durable, S3, Basic
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE LedExtendsReq'
  BY <1>l, <1>G, <1>T, LedExtendsReqKeep DEF CastVote, durable, S3, Basic
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE LedExtendsReq'
  BY <1>m, <1>G, <1>T, LedExtendsReqKeep DEF GrantVote, durable, S3, Basic
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE LedExtendsReq'
  BY <1>n, <1>G, <1>T, LedExtendsReqKeep DEF LeaderCommit, durable, S3, Basic
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE LedExtendsReq'
  BY <1>o, <1>G, <1>T, LedExtendsReqKeep DEF SendAppend, durable, S3, Basic
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE LedExtendsReq'
  BY <1>p, <1>G, <1>T, LedExtendsReqKeep DEF Ack, durable, S3, Basic
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE LedExtendsReq'
  BY <1>q, <1>G, <1>T, LedExtendsReqKeep DEF AckCommitted, durable, S3, Basic
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE LedExtendsReq'
  BY <1>r, <1>G, <1>T, LedExtendsReqKeep DEF DeleteSuffix, durable, S3, Basic
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE LedExtendsReq'
  BY <1>s, <1>G, <1>T, LedExtendsReqKeep DEF StoreEntries, durable, S3, Basic
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE LedExtendsReq'
  BY <1>t, <1>G, <1>T, LedExtendsReqKeep DEF FollowerCommit, durable, S3, Basic
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases


\* ---- LeaderSync
LEMMA LeaderSyncStep ==
  ASSUME Basic, S1, S2, S3, ProtoCases
  PROVE  LeaderSync'
<1>G. Grows BY GrowsStep
<1>T. TypeOK BY DEF Basic
<1>TP. TypeP' BY TypeProto
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE LeaderSync'
  BY <1>a, <1>T DEF BecomeCandidate, durable, S3, LeaderSync, TypeOK, Leader, Follower, Candidate
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE LeaderSync'
  BY <1>b, <1>T DEF BecomeFollower, durable, S3, LeaderSync, TypeOK, Leader, Follower, Candidate
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE LeaderSync'
  <2> DEFINE u == currentTerm[i]
  <2>1. /\ u \notin DOMAIN ledLog /\ ledAt'[u] = confAt[i] /\ ledConf'[u] = config[i]
        /\ \A t \in DOMAIN ledLog : ledAt'[t] = ledAt[t] /\ ledConf'[t] = ledConf[t]
        /\ role' = [role EXCEPT ![i] = Leader]
        /\ UNCHANGED <<currentTerm, config, confAt>>
    BY <1>c, BecomeLeaderLed DEF durable
  <2>2. role \in [Server -> {Follower, Candidate, Leader}] BY <1>T DEF TypeOK
  <2> SUFFICES ASSUME NEW s \in Server, role'[s] = Leader
               PROVE confAt[s] = ledAt'[currentTerm[s]] /\ config[s] = ledConf'[currentTerm[s]]
    BY <2>1 DEF LeaderSync
  <2>3. CASE s = i BY <2>3, <2>1
  <2>4. CASE s # i
    <3>1. role[s] = Leader BY <2>4, <2>1, <2>2
    <3>2. currentTerm[s] \in DOMAIN ledLog BY <3>1 DEF Basic, LeaderIsElected, LedDom, IsLd
    <3> QED BY <3>1, <3>2, <2>1 DEF S3, LeaderSync
  <2> QED BY <2>3, <2>4
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE LeaderSync'
  BY <1>d, <1>T DEF StartElection, durable, S3, LeaderSync, TypeOK, Leader, Follower, Candidate
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE LeaderSync'
  BY <1>e, <1>T DEF Restart, durable, S3, LeaderSync, TypeOK, Leader, Follower, Candidate
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE LeaderSync'
  BY <1>f, <1>T DEF Apply, durable, S3, LeaderSync, TypeOK, Leader, Follower, Candidate
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE LeaderSync'
  BY <1>g, <1>T DEF Restore, durable, S3, LeaderSync, TypeOK, Leader, Follower, Candidate
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE LeaderSync'
  <2> DEFINE u == currentTerm[i]  C == NextConf(config[i], log[i][k].value)
  <2>1. /\ config' = [config EXCEPT ![i] = C] /\ confAt' = [confAt EXCEPT ![i] = k]
        /\ ledConf' = IF role[i] = Leader THEN WithConf(u, C) ELSE ledConf
        /\ ledAt' = IF role[i] = Leader THEN With(ledAt, u, k) ELSE ledAt
        /\ UNCHANGED <<currentTerm, role>>
    BY <1>h DEF SwitchConf, durable
  <2>2. config \in [Server -> ConfT] /\ confAt \in [Server -> Nat] /\ DOMAIN ledConf = DOMAIN ledLog /\ DOMAIN ledAt = DOMAIN ledLog
    BY <1>T DEF TypeOK
  <2> HIDE DEF C
  <2> SUFFICES ASSUME NEW s \in Server, role[s] = Leader
               PROVE confAt'[s] = ledAt'[currentTerm[s]] /\ config'[s] = ledConf'[currentTerm[s]]
    BY <2>1 DEF LeaderSync
  <2>3. currentTerm[s] \in DOMAIN ledLog /\ IsLd(s, currentTerm[s]) BY DEF Basic, LeaderIsElected, LedDom, IsLd
  <2>4. confAt[s] = ledAt[currentTerm[s]] /\ config[s] = ledConf[currentTerm[s]] BY DEF S3, LeaderSync
  <2>5. CASE role[i] # Leader BY <2>5, <2>1, <2>2, <2>4
  <2>6. CASE role[i] = Leader
    <3>1. IsLd(i, u) BY <2>6 DEF Basic, LeaderIsElected
    <3>2. currentTerm[s] = u => s = i BY <3>1, <2>3 DEF S1, ElectionSafety, IsLd
    <3>3. ledConf' = [w \in DOMAIN ledConf \cup {u} |-> IF w = u THEN C ELSE ledConf[w]]
          /\ ledAt' = [w \in DOMAIN ledAt \cup {u} |-> IF w = u THEN k ELSE ledAt[w]]
      BY <2>6, <2>1 DEF WithConf, With
    <3>4. CASE s = i BY <3>4, <3>3, <2>1, <2>2
    <3>5. CASE s # i
      <4>1. currentTerm[s] # u BY <3>5, <3>2
      <4> QED BY <4>1, <3>5, <3>3, <2>1, <2>2, <2>3, <2>4
    <3> QED BY <3>4, <3>5
  <2> QED BY <2>5, <2>6
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE LeaderSync'
  BY <1>i, <1>T DEF RestoreConf, durable, S3, LeaderSync, TypeOK, Leader, Follower, Candidate
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE LeaderSync'
  BY <1>j, <1>T DEF LeaderAppend1, durable, S3, LeaderSync, TypeOK, Leader, Follower, Candidate
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE LeaderSync'
  BY <1>k, <1>T DEF AdoptTerm, durable, S3, LeaderSync, TypeOK, Leader, Follower, Candidate
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE LeaderSync'
  BY <1>l, <1>T DEF CastVote, durable, S3, LeaderSync, TypeOK, Leader, Follower, Candidate
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE LeaderSync'
  BY <1>m, <1>T DEF GrantVote, durable, S3, LeaderSync, TypeOK, Leader, Follower, Candidate
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE LeaderSync'
  BY <1>n, <1>T DEF LeaderCommit, durable, S3, LeaderSync, TypeOK, Leader, Follower, Candidate
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE LeaderSync'
  BY <1>o, <1>T DEF SendAppend, durable, S3, LeaderSync, TypeOK, Leader, Follower, Candidate
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE LeaderSync'
  BY <1>p, <1>T DEF Ack, durable, S3, LeaderSync, TypeOK, Leader, Follower, Candidate
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE LeaderSync'
  BY <1>q, <1>T DEF AckCommitted, durable, S3, LeaderSync, TypeOK, Leader, Follower, Candidate
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE LeaderSync'
  BY <1>r, <1>T DEF DeleteSuffix, durable, S3, LeaderSync, TypeOK, Leader, Follower, Candidate
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE LeaderSync'
  BY <1>s, <1>T DEF StoreEntries, durable, S3, LeaderSync, TypeOK, Leader, Follower, Candidate
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE LeaderSync'
  BY <1>t, <1>T DEF FollowerCommit, durable, S3, LeaderSync, TypeOK, Leader, Follower, Candidate
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases


THEOREM S3Step == ASSUME Basic, S1, S2, S3, ProtoCases PROVE S3'
BY TermsPositiveStep, ReqFactsStep, ReqUniqueStep, VoteHasReqStep, CandLogStep, LedExtendsReqStep,
   LeaderSyncStep DEF S3
====
