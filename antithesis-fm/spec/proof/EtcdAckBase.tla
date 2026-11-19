---- MODULE EtcdAckBase ----
\* State-level facts, and what a step keeps of Good, Covers, LostIn and
\* acknowledgements; used by EtcdAck.tla.
EXTENDS EtcdLog, EtcdLC

LEMMA AInvBasic == ASSUME Inv PROVE Basic /\ TypeOK
BY DEF Inv, Basic

\* Terms do not decrease along a log that is from leader logs.
LEMMA SortedLed ==
  ASSUME TypeOK, LedTermsBound, NEW l \in Seq(EntryT), FromLed(l),
         NEW p \in 1..Len(l), NEW q \in 1..Len(l), p <= q
  PROVE  l[p].term <= l[q].term
<1> DEFINE w == l[q].term
<1>1. w \in DOMAIN ledLog /\ Agree(l, ledLog[w], q) BY DEF FromLed
<1>2. ledLog[w] \in Seq(EntryT) BY <1>1 DEF TypeOK
<1>3. p \in 1..Len(ledLog[w]) /\ l[p] = ledLog[w][p] BY <1>1, <1>2 DEF Agree
<1>4. ledLog[w][p].term <= w BY <1>1, <1>3 DEF LedTermsBound
<1> QED BY <1>3, <1>4

\* What is committed in a term is in the leader log of every term from it on.
LEMMA ARootInLed ==
  ASSUME Inv, NEW k \in commits, NEW u \in DOMAIN ledLog, k.term <= u
  PROVE  Pre(k.entries, ledLog[u])
<1>0. TypeOK /\ CommitRoot BY DEF Inv
<1>1. PICK r \in commits : Pre(k.entries, r.entries) /\ Root(r) /\ r.term <= k.term
  BY <1>0 DEF CommitRoot
<1>2. /\ k.entries \in Seq(EntryT) /\ r.entries \in Seq(EntryT) /\ k.term \in Nat /\ r.term \in Nat
      /\ u \in Nat /\ ledLog[u] \in Seq(EntryT)
  BY <1>0, TypeFacts
<1>3. r.term \in DOMAIN ledLog /\ Pre(r.entries, ledLog[r.term]) BY <1>1 DEF Root
<1>4. ledLog[r.term] \in Seq(EntryT) BY <1>0, <1>3, TypeFacts
<1>5. Pre(r.entries, ledLog[u])
  <2>1. CASE r.term = u BY <2>1, <1>3
  <2>2. CASE r.term < u
    <3>1. PICK d \in 0..Len(ledLog[r.term]) : MRoot(r.term, Len(r.entries), d) BY <1>1 DEF Root
    <3>2. Len(r.entries) \in 1..Len(ledLog[r.term]) BY <3>1, <1>2, <1>4 DEF MRoot, Good
    <3>3. LC BY LCThm
    <3>4. Agree(ledLog[r.term], ledLog[u], Len(r.entries)) BY <3>1, <3>2, <3>3, <2>2, <1>3 DEF LC
    <3> QED BY <1>2, <1>3, <1>4, <3>4 DEF Pre, Agree
  <2> QED BY <2>1, <2>2, <1>1, <1>2
<1> QED BY <1>1, <1>2, <1>5, PreTrans

----
\* What a step keeps.

LEMMA GoodOld ==
  ASSUME TypeOK, Grows, NEW t \in DOMAIN ledLog, NEW c \in Nat, c <= Len(ledLog[t])
  PROVE  Good(t, c)' <=> Good(t, c)
<1>1. ledLog[t] \in Seq(EntryT) BY DEF TypeOK
<1>2. ledLog'[t] \in Seq(EntryT) /\ Pre(ledLog[t], ledLog'[t]) /\ t \in DOMAIN ledLog' BY DEF Grows
<1>3. c >= 1 => ledLog'[t][c] = ledLog[t][c] /\ c <= Len(ledLog'[t]) BY <1>1, <1>2 DEF Pre, Agree
<1> QED BY <1>1, <1>2, <1>3 DEF Good

LEMMA GoodKeep ==
  ASSUME TypeOK, Grows, NEW t \in DOMAIN ledLog, NEW c \in Nat, Good(t, c)
  PROVE  Good(t, c)'
BY GoodOld DEF Good

\* A leader log of a later term that lacks the first c entries of ledLog[t]
\* lacks them for ever: what it gets later is of its own term.
LEMMA LostKeep ==
  ASSUME TypeOK, Grows, NEW t \in DOMAIN ledLog, NEW c \in Nat, Good(t, c),
         NEW w \in DOMAIN ledLog, t < w, ~Agree(ledLog[t], ledLog[w], c)
  PROVE  w \in DOMAIN ledLog' /\ ~Agree(ledLog'[t], ledLog'[w], c)
<1>1. ledLog[t] \in Seq(EntryT) /\ ledLog[w] \in Seq(EntryT) /\ t \in Nat /\ w \in Nat BY DEF TypeOK
<1>2. ledLog'[t] \in Seq(EntryT) /\ Pre(ledLog[t], ledLog'[t]) BY DEF Grows
<1>3. /\ ledLog'[w] \in Seq(EntryT) /\ Pre(ledLog[w], ledLog'[w]) /\ w \in DOMAIN ledLog'
      /\ \A q \in (Len(ledLog[w]) + 1)..Len(ledLog'[w]) : ledLog'[w][q].term = w
  BY DEF Grows
<1>4. c >= 1 /\ c <= Len(ledLog[t]) /\ ledLog[t][c].term = t BY DEF Good
<1>5. \A q \in 1..c : ledLog'[t][q] = ledLog[t][q] BY <1>1, <1>2, <1>4 DEF Pre, Agree
<1>6. ASSUME Agree(ledLog'[t], ledLog'[w], c) PROVE FALSE
  <2>1. c <= Len(ledLog'[w]) /\ \A q \in 1..c : ledLog'[t][q] = ledLog'[w][q] BY <1>6 DEF Agree
  <2>2. CASE c <= Len(ledLog[w])
    <3>1. \A q \in 1..c : ledLog'[w][q] = ledLog[w][q] BY <2>2, <1>1, <1>3 DEF Pre, Agree
    <3> QED BY <3>1, <2>1, <2>2, <1>4, <1>5 DEF Agree
  <2>3. CASE c > Len(ledLog[w])
    <3>1. c \in (Len(ledLog[w]) + 1)..Len(ledLog'[w]) /\ c \in 1..c BY <2>3, <2>1, <1>1, <1>3, <1>4
    <3>2. ledLog'[w][c].term = w BY <3>1, <1>3
    <3>3. ledLog'[w][c] = ledLog[t][c] BY <3>1, <2>1, <1>5
    <3> QED BY <3>2, <3>3, <1>4, <1>1
  <2> QED BY <2>2, <2>3, <1>1
<1> QED BY <1>3, <1>6

LEMMA LostGrow ==
  ASSUME TypeOK, Grows, NEW t \in DOMAIN ledLog, NEW c \in Nat, Good(t, c),
         NEW lo \in Nat, NEW hi \in Nat, t <= lo, LostIn(t, c, lo, hi)
  PROVE  \E w \in DOMAIN ledLog :
            /\ w \in Nat /\ w \in DOMAIN ledLog' /\ lo < w /\ w <= hi
            /\ ~Agree(ledLog'[t], ledLog'[w], c)
<1>1. PICK w \in DOMAIN ledLog : lo < w /\ w <= hi /\ ~Agree(ledLog[t], ledLog[w], c) BY DEF LostIn
<1>2. t \in Nat /\ w \in Nat BY DEF TypeOK
<1>3. t < w BY <1>1, <1>2
<1>4. w \in DOMAIN ledLog' /\ ~Agree(ledLog'[t], ledLog'[w], c) BY <1>1, <1>3, LostKeep
<1> QED BY <1>1, <1>2, <1>4

LEMMA CoversKeep ==
  ASSUME TypeOK, Grows, NEW t \in DOMAIN ledLog, NEW c \in Nat, NEW li, NEW lt, Covers(t, c, li, lt)
  PROVE  Covers(t, c, li, lt)'
<1>1. lt \in DOMAIN ledLog /\ Agree(ledLog[t], ledLog[lt], c) /\ c <= li BY DEF Covers
<1>2. Agree(ledLog'[t], ledLog'[lt], c) BY <1>1, AgreeGrow
<1> QED BY <1>1, <1>2 DEF Covers, Grows

\* An acknowledgement that was there before the step, for a prefix that is
\* good after it: the prefix was good before.
LEMMA OldAck ==
  ASSUME TypeOK, AckFacts, LedDom, Grows,
         NEW t, NEW c \in Nat, Good(t, c)',
         NEW a \in msgs, a.type = "ack", a.term = t, a.index >= c
  PROVE  /\ t \in DOMAIN ledLog /\ c \in 1..Len(ledLog[t]) /\ Good(t, c)
         /\ a.src \in Server /\ a.src \in AckedBy(t, c)
<1>1. a \in AckT BY DEF TypeOK, MsgT, VoteReqT, GrantT, AppendT, AckT
<1>2. a.src \in Server /\ a.index \in Nat BY <1>1 DEF AckT
<1>3. IsLd(a.dst, t) /\ a.index <= Len(ledLog[t]) BY DEF AckFacts
<1>4. t \in DOMAIN ledLog BY <1>3 DEF IsLd, LedDom
<1>5. ledLog[t] \in Seq(EntryT) BY <1>4 DEF TypeOK
<1>6. c <= Len(ledLog[t]) BY <1>2, <1>3, <1>5
<1>7. Good(t, c) BY <1>4, <1>6, GoodOld
<1>8. c >= 1 BY <1>7 DEF Good
<1> QED BY <1>2, <1>4, <1>5, <1>6, <1>7, <1>8 DEF AckedBy

----
\* What the new messages of a step are like.
NewAckOk ==
    \A a \in msgs' \ msgs : a.type = "ack" =>
        /\ a.src \in Server /\ a.index \in Nat /\ a.term \in DOMAIN ledLog
        /\ a.term = currentTerm[a.src]
        /\ Agree(log[a.src], ledLog[a.term], a.index)
NewReqFresh ==
    \A a \in msgs' \ msgs : a.type = "vote" => a.src \in Server /\ a.term > currentTerm[a.src]
StepOK0 == Grows /\ NewAckOk /\ NewReqFresh /\ currentTerm' \in [Server -> Nat]

LEMMA StepOK0Same ==
  ASSUME Grows, msgs' = msgs, currentTerm' \in [Server -> Nat]
  PROVE  StepOK0
BY DEF StepOK0, NewAckOk, NewReqFresh

LEMMA StepOK0Other ==
  ASSUME Grows, NEW x, msgs' = msgs \cup {x}, x.type \notin {"ack", "vote"}, currentTerm' \in [Server -> Nat]
  PROVE  StepOK0
BY DEF StepOK0, NewAckOk, NewReqFresh

LEMMA StepOK0Step ==
  ASSUME Inv, ProtoCases
  PROVE  StepOK0
<1>0. TypeOK /\ Grows /\ currentTerm \in [Server -> Nat] /\ commitIndex \in [Server -> Nat] /\ log \in [Server -> Seq(EntryT)]
  BY AInvBasic, GrowsStep DEF TypeOK
<1>1. ReqFromLed /\ LogFromLed /\ LedFromLed BY DEF Inv
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE StepOK0
  BY <1>a, <1>0, StepOK0Same DEF BecomeCandidate, durable
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE StepOK0
  BY <1>b, <1>0, StepOK0Same DEF BecomeFollower, durable
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE StepOK0
  BY <1>c, <1>0, StepOK0Same DEF BecomeLeader, durable
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE StepOK0
  <2>1. msgs' = msgs \cup {VoteRequest(i, currentTerm[i] + 1)} /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    BY <1>d DEF StartElection
  <2>2. currentTerm' \in [Server -> Nat] BY <2>1, <1>0
  <2>3. NewAckOk BY <2>1 DEF NewAckOk, VoteRequest
  <2>4. NewReqFresh BY <2>1, <1>0 DEF NewReqFresh, VoteRequest
  <2> QED BY <1>0, <2>2, <2>3, <2>4 DEF StepOK0
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE StepOK0
  BY <1>e, <1>0, StepOK0Same DEF Restart, durable
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE StepOK0
  BY <1>f, <1>0, StepOK0Same DEF Apply, durable
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE StepOK0
  BY <1>g, <1>0, StepOK0Same DEF Restore, durable
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE StepOK0
  BY <1>h, <1>0, StepOK0Same DEF SwitchConf, durable
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE StepOK0
  BY <1>i, <1>0, StepOK0Same DEF RestoreConf, durable
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE StepOK0
  BY <1>j, <1>0, StepOK0Same DEF LeaderAppend1, durable
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE StepOK0
  <2>1. msgs' = msgs /\ currentTerm' = [currentTerm EXCEPT ![i] = t] BY <1>k DEF AdoptTerm
  <2>2. currentTerm' \in [Server -> Nat] BY <2>1, <1>0
  <2> QED BY <1>0, <2>1, <2>2, StepOK0Same
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE StepOK0
  BY <1>l, <1>0, StepOK0Same DEF CastVote, durable
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE StepOK0
  <2>1. msgs' = msgs \cup {[type |-> "grant", src |-> i, dst |-> c, term |-> t]} /\ currentTerm' = currentTerm
    BY <1>m DEF GrantVote, durable
  <2> QED BY <1>0, <2>1, StepOK0Other
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE StepOK0
  BY <1>n, <1>0, StepOK0Same DEF LeaderCommit, durable
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE StepOK0
  <2> DEFINE x == [type |-> "append", src |-> i, dst |-> j, term |-> t,
                           prevLogIndex |-> p, prevLogTerm |-> TermAt(ledLog[t], p),
                           entries |-> SubSeq(ledLog[t], p + 1, p + n), commit |-> c]
  <2>1. msgs' = msgs \cup {x} /\ currentTerm' = currentTerm
    BY <1>o DEF SendAppend, durable
  <2>2. x.type \notin {"ack", "vote"} OBVIOUS
  <2> HIDE DEF x
  <2> QED BY <1>0, <2>1, <2>2, StepOK0Other
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE StepOK0
  <2> DEFINE last == m.prevLogIndex + Len(m.entries)
              x == [type |-> "ack", src |-> j, dst |-> m.src, term |-> m.term, index |-> last]
  <2>1. msgs' = msgs \cup {x} /\ currentTerm' = currentTerm /\ currentTerm[j] = m.term
        /\ PrevOk(j, m) /\ HasFirst(j, m, Len(m.entries))
    BY <1>p DEF Ack, durable
  <2>2. m.prevLogIndex \in Nat /\ m.entries \in Seq(EntryT) /\ m.type = "append" BY <1>p DEF AppendT
  <2>3. Len(m.entries) \in 0..Len(m.entries) /\ last \in Nat BY <2>2
  <2>4. Agree(log[j], ledLog[m.term], last) BY <1>p, <1>0, <1>1, <2>1, <2>3, CheckedPrefix
  <2>5. m.term \in DOMAIN ledLog BY <1>1, <2>2 DEF ReqFromLed
  <2>6. NewAckOk BY <2>1, <2>3, <2>4, <2>5 DEF NewAckOk
  <2>7. NewReqFresh BY <2>1 DEF NewReqFresh
  <2> QED BY <1>0, <2>1, <2>6, <2>7 DEF StepOK0
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE StepOK0
  <2> DEFINE ci == commitIndex[j]
              x == [type |-> "ack", src |-> j, dst |-> m.src, term |-> m.term, index |-> ci]
  <2>1. msgs' = msgs \cup {x} /\ currentTerm' = currentTerm /\ currentTerm[j] = m.term
        /\ m.prevLogIndex < ci
    BY <1>q DEF AckCommitted, durable
  <2>2. m.prevLogIndex \in Nat /\ m.type = "append" BY <1>q DEF AppendT
  <2>3. ci \in Nat /\ log[j] \in Seq(EntryT) BY <1>0
  <2>4. m.term \in DOMAIN ledLog BY <1>1, <2>2 DEF ReqFromLed
  <2>5. ci <= Len(log[j]) /\ \E k \in commits : k.server = j /\ Agree(log[j], k.entries, ci)
    BY <2>1, <2>2, <2>3 DEF Inv, CommitKept
  <2>6. PICK k \in commits : k.server = j /\ Agree(log[j], k.entries, ci) BY <2>5
  <2>7. k.term <= m.term BY <2>6, <2>1 DEF Inv, CommitTermBound
  <2>8. Pre(k.entries, ledLog[m.term]) BY <2>4, <2>7, ARootInLed
  <2>9. k.entries \in Seq(EntryT) /\ ledLog[m.term] \in Seq(EntryT) BY <1>0, <2>4, TypeFacts
  <2>10. Agree(log[j], ledLog[m.term], ci) BY <2>3, <2>6, <2>8, <2>9 DEF Pre, Agree
  <2>11. NewAckOk BY <2>1, <2>3, <2>4, <2>10 DEF NewAckOk
  <2>12. NewReqFresh BY <2>1 DEF NewReqFresh
  <2> QED BY <1>0, <2>1, <2>11, <2>12 DEF StepOK0
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE StepOK0
  BY <1>r, <1>0, StepOK0Same DEF DeleteSuffix, durable
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE StepOK0
  BY <1>s, <1>0, StepOK0Same DEF StoreEntries, durable
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE StepOK0
  BY <1>t, <1>0, StepOK0Same DEF FollowerCommit, durable
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases

LedT == \A t \in DOMAIN ledLog : ledLog[t] \in Seq(EntryT)
LEMMA LedTStep ==
  ASSUME Inv, ProtoCases
  PROVE  LedT'
<1>0. \A t \in DOMAIN ledLog : ledLog[t] \in Seq(EntryT) BY AInvBasic DEF TypeOK
<1>1. Basic /\ log \in [Server -> Seq(EntryT)] BY AInvBasic DEF TypeOK
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE LedT'
  BY <1>a, <1>0 DEF BecomeCandidate, LedT
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE LedT'
  BY <1>b, <1>0 DEF BecomeFollower, LedT
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE LedT'
  BY <1>c, <1>0, <1>1, BecomeLeaderLed DEF LedT
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE LedT'
  BY <1>d, <1>0 DEF StartElection, LedT
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE LedT'
  BY <1>e, <1>0 DEF Restart, LedT
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE LedT'
  BY <1>f, <1>0 DEF Apply, LedT
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE LedT'
  BY <1>g, <1>0 DEF Restore, LedT
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE LedT'
  BY <1>h, <1>0 DEF SwitchConf, LedT
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE LedT'
  BY <1>i, <1>0 DEF RestoreConf, LedT
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE LedT'
  BY <1>j, <1>0, <1>1, AppendLed DEF LedT
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE LedT'
  BY <1>k, <1>0 DEF AdoptTerm, LedT
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE LedT'
  BY <1>l, <1>0 DEF CastVote, LedT
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE LedT'
  BY <1>m, <1>0 DEF GrantVote, LedT
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE LedT'
  BY <1>n, <1>0 DEF LeaderCommit, LedT
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE LedT'
  BY <1>o, <1>0 DEF SendAppend, LedT
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE LedT'
  BY <1>p, <1>0 DEF Ack, LedT
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE LedT'
  BY <1>q, <1>0 DEF AckCommitted, LedT
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE LedT'
  BY <1>r, <1>0 DEF DeleteSuffix, LedT
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE LedT'
  BY <1>s, <1>0 DEF StoreEntries, LedT
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE LedT'
  BY <1>t, <1>0 DEF FollowerCommit, LedT
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases

StepOK == StepOK0 /\ LedT'
LEMMA StepOKStep == ASSUME Inv, ProtoCases PROVE StepOK
BY StepOK0Step, LedTStep DEF StepOK
====
