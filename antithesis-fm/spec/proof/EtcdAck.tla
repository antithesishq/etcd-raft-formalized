---- MODULE EtcdAck ----
\* AckedHeld, AckVote and EarlyQuorum are kept by every step of the protocol.
EXTENDS EtcdAckBase

AG == AckedHeld /\ AckVote /\ EarlyQuorum

LEMMA AGInit == ASSUME Init PROVE AG
<1>1. DOMAIN ledLog = {} /\ leaders = {} /\ votes = {} BY DEF Init
<1> QED BY <1>1 DEF AG, AckedHeld, AckVote, EarlyQuorum

LEMMA AGUnch == ASSUME AG, UNCHANGED vars PROVE AG'
<1>1. UNCHANGED <<ledLog, log, currentTerm, msgs, votes, leaders, elAt>> BY DEF vars, protoVars, durable
<1>2. AckedHeld' BY <1>1 DEF AG, AckedHeld, Good, AckedBy, LostIn, Agree
<1>3. AckVote' BY <1>1 DEF AG, AckVote, Good, AckedBy, LostIn, Covers, Agree
<1>4. EarlyQuorum' BY <1>1 DEF AG, EarlyQuorum, EarlyVoters, Early, Good, AckedBy, LostIn, Covers, Agree
<1> QED BY <1>2, <1>3, <1>4 DEF AG

----
\* An acknowledgement of a node that has voted in a later term is not new.
LEMMA VoterAckOld ==
  ASSUME Inv, StepOK, NEW v \in votes,
         NEW t, NEW c \in Nat, Good(t, c)', v.voter \in AckedBy(t, c)', t < v.term
  PROVE  t \in DOMAIN ledLog /\ c \in 1..Len(ledLog[t]) /\ Good(t, c) /\ v.voter \in AckedBy(t, c)
<1>0. TypeOK /\ AckFacts /\ LedDom /\ VotesBound /\ VoteTermBound /\ Grows BY DEF Inv, StepOK, StepOK0
<1>1. PICK a \in msgs' : a.type = "ack" /\ a.src = v.voter /\ a.term = t /\ a.index >= c BY DEF AckedBy
<1>2. v.voter \in Server /\ v.term \in Nat /\ voteTerm[v.voter] \in Nat /\ currentTerm[v.voter] \in Nat
  BY <1>0 DEF TypeOK, VoteT
<1>3. v.term <= voteTerm[v.voter] /\ voteTerm[v.voter] <= currentTerm[v.voter]
  BY <1>0, <1>2 DEF VotesBound, VoteTermBound
<1>4. a \in msgs
  <2>1. ASSUME a \notin msgs PROVE FALSE
    <3>1. t = currentTerm[v.voter] BY <2>1, <1>1 DEF StepOK, StepOK0, NewAckOk
    <3> QED BY <3>1, <1>2, <1>3
  <2> QED BY <2>1
<1> QED BY <1>0, <1>1, <1>4, OldAck

\* A request for the votes of an election in which a vote exists is not new.
LEMMA ReqOld ==
  ASSUME Inv, StepOK, NEW v \in votes, NEW m \in msgs', m.type = "vote", m.src = v.cand, m.term = v.term
  PROVE  m \in msgs
<1>0. TypeOK /\ VoteHasReq /\ ReqFacts BY DEF Inv
<1>1. PICK m2 \in msgs : m2.type = "vote" /\ m2.src = v.cand /\ m2.term = v.term BY <1>0 DEF VoteHasReq
<1>2. v.term <= currentTerm[v.cand] BY <1>0, <1>1 DEF ReqFacts
<1>3. v.cand \in Server /\ v.term \in Nat /\ currentTerm[v.cand] \in Nat BY <1>0 DEF TypeOK, VoteT
<1>4. ASSUME m \notin msgs PROVE FALSE
  <2>1. m.term > currentTerm[m.src] BY <1>4 DEF StepOK, StepOK0, NewReqFresh
  <2> QED BY <2>1, <1>2, <1>3
<1> QED BY <1>4

----
\* AckedHeld.

LEMMA AHOld ==
  ASSUME Inv, StepOK, NEW n \in Server, log'[n] = log[n],
         NEW t \in DOMAIN ledLog', NEW c \in 1..Len(ledLog'[t]), Good(t, c)', n \in AckedBy(t, c)'
  PROVE  Agree(ledLog'[t], log'[n], c) \/ LostIn(t, c, t, currentTerm[n])'
<1>0. TypeOK /\ Grows /\ AckFacts /\ LedDom /\ AckedHeld /\ LedT' BY DEF Inv, StepOK, StepOK0
<1>1. c \in Nat /\ ledLog'[t] \in Seq(EntryT) BY <1>0 DEF LedT
<1>2. PICK a \in msgs' : a.type = "ack" /\ a.src = n /\ a.term = t /\ a.index >= c BY DEF AckedBy
<1>3. /\ log[n] \in Seq(EntryT) /\ currentTerm[n] \in Nat /\ currentTerm'[n] \in Nat
      /\ currentTerm[n] <= currentTerm'[n]
  BY <1>0 DEF TypeOK, StepOK, StepOK0, Grows
<1>4. CASE a \in msgs
  <2>1. t \in DOMAIN ledLog /\ c \in 1..Len(ledLog[t]) /\ Good(t, c) /\ n \in AckedBy(t, c)
    BY <1>0, <1>1, <1>2, <1>4, OldAck
  <2>2. Agree(ledLog[t], log[n], c) \/ LostIn(t, c, t, currentTerm[n]) BY <1>0, <2>1 DEF AckedHeld
  <2>3. t \in Nat /\ ledLog[t] \in Seq(EntryT) /\ Pre(ledLog[t], ledLog'[t]) BY <1>0, <2>1 DEF TypeOK, Grows
  <2>4. CASE Agree(ledLog[t], log[n], c) BY <2>4, <2>3, <1>1, <1>3 DEF Pre, Agree
  <2>5. CASE LostIn(t, c, t, currentTerm[n])
    <3>1. PICK w \in DOMAIN ledLog :
            /\ w \in Nat /\ w \in DOMAIN ledLog' /\ t < w /\ w <= currentTerm[n]
            /\ ~Agree(ledLog'[t], ledLog'[w], c)
      BY <2>5, <1>0, <2>1, <2>3, <1>1, <1>3, LostGrow
    <3>2. w <= currentTerm'[n] BY <3>1, <1>3
    <3> QED BY <3>1, <3>2 DEF LostIn
  <2> QED BY <2>2, <2>4, <2>5
<1>5. CASE a \notin msgs
  <2>1. a.index \in Nat /\ t \in DOMAIN ledLog /\ Agree(log[n], ledLog[t], a.index)
    BY <1>2, <1>5 DEF StepOK, StepOK0, NewAckOk
  <2>2. ledLog[t] \in Seq(EntryT) /\ Pre(ledLog[t], ledLog'[t]) BY <1>0, <2>1 DEF TypeOK, Grows
  <2>3. Agree(ledLog'[t], log[n], c) BY <2>1, <2>2, <1>1, <1>2, <1>3 DEF Pre, Agree
  <2> QED BY <2>3
<1> QED BY <1>4, <1>5

LEMMA AHSame ==
  ASSUME Inv, StepOK, log' = log
  PROVE  AckedHeld'
<1> SUFFICES ASSUME NEW n \in Server, NEW t \in DOMAIN ledLog', NEW c \in 1..Len(ledLog'[t]),
                    Good(t, c)', n \in AckedBy(t, c)'
             PROVE  Agree(ledLog'[t], log'[n], c) \/ LostIn(t, c, t, currentTerm[n])'
  BY DEF AckedHeld
<1> QED BY AHOld

\* The node whose log a step changes: common part.
LEMMA AHLogStep ==
  ASSUME Inv, StepOK, NEW j \in Server, UNCHANGED <<msgs, ledLog, currentTerm>>,
         NEW t \in DOMAIN ledLog', NEW c \in 1..Len(ledLog'[t]), Good(t, c)', j \in AckedBy(t, c)'
  PROVE  /\ t \in DOMAIN ledLog /\ c \in 1..Len(ledLog[t]) /\ Good(t, c) /\ c \in Nat /\ t \in Nat
         /\ ledLog[t] \in Seq(EntryT) /\ log[j] \in Seq(EntryT)
         /\ t <= currentTerm[j] /\ currentTerm[j] \in Nat
         /\ Agree(ledLog[t], log[j], c) \/ LostIn(t, c, t, currentTerm[j])
<1>0. TypeOK /\ AckFacts /\ LedDom /\ AckedHeld /\ Grows BY DEF Inv, StepOK, StepOK0
<1>1. t \in DOMAIN ledLog /\ ledLog[t] \in Seq(EntryT) /\ t \in Nat /\ c \in Nat /\ c \in 1..Len(ledLog[t])
  BY <1>0 DEF TypeOK
<1>2. PICK a \in msgs : a.type = "ack" /\ a.src = j /\ a.term = t /\ a.index >= c BY DEF AckedBy
<1>3. Good(t, c) /\ j \in AckedBy(t, c) BY <1>0, <1>1, <1>2, OldAck
<1>4. t <= currentTerm[j] BY <1>0, <1>2 DEF AckFacts
<1>5. log[j] \in Seq(EntryT) /\ currentTerm[j] \in Nat BY <1>0 DEF TypeOK
<1>6. Agree(ledLog[t], log[j], c) \/ LostIn(t, c, t, currentTerm[j]) BY <1>0, <1>1, <1>3 DEF AckedHeld
<1> QED BY <1>1, <1>3, <1>4, <1>5, <1>6

LEMMA AHStore ==
  ASSUME Inv, StepOK, NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT,
         StoreEntries(j, m, k)
  PROVE  AckedHeld'
<1> SUFFICES ASSUME NEW n \in Server, NEW t \in DOMAIN ledLog', NEW c \in 1..Len(ledLog'[t]),
                    Good(t, c)', n \in AckedBy(t, c)'
             PROVE  Agree(ledLog'[t], log'[n], c) \/ LostIn(t, c, t, currentTerm[n])'
  BY DEF AckedHeld
<1>0. TypeOK BY DEF Inv
<1>1. UNCHANGED <<msgs, ledLog, currentTerm>> BY DEF StoreEntries
<1>2. /\ log' = [log EXCEPT ![j] = log'[j]]
      /\ log'[j] \in Seq(EntryT)
      /\ Len(log'[j]) = m.prevLogIndex + Len(m.entries)
      /\ m.prevLogIndex + k = Len(log[j]) + 1
      /\ \A q \in 1..Len(log[j]) : log'[j][q] = log[j][q]
  BY <1>0, StoreLog
<1>3. CASE n # j
  <2>1. log'[n] = log[n] BY <1>2, <1>3, <1>0 DEF TypeOK
  <2> QED BY <2>1, AHOld
<1>4. CASE n = j
  <2>1. /\ t \in DOMAIN ledLog /\ c \in 1..Len(ledLog[t]) /\ Good(t, c) /\ c \in Nat /\ t \in Nat
        /\ ledLog[t] \in Seq(EntryT) /\ log[j] \in Seq(EntryT)
        /\ t <= currentTerm[j] /\ currentTerm[j] \in Nat
        /\ Agree(ledLog[t], log[j], c) \/ LostIn(t, c, t, currentTerm[j])
    BY <1>1, <1>4, AHLogStep
  <2>2. CASE LostIn(t, c, t, currentTerm[j]) BY <2>2, <1>1, <1>4 DEF LostIn
  <2>3. CASE Agree(ledLog[t], log[j], c)
    <3>1. m.prevLogIndex \in Nat /\ m.entries \in Seq(EntryT) BY DEF AppendT
    <3>2. Len(log[j]) <= Len(log'[j]) BY <3>1, <1>2, <2>1
    <3>3. Agree(ledLog[t], log'[j], c) BY <2>3, <2>1, <3>2, <1>2 DEF Agree
    <3> QED BY <3>3, <1>1, <1>4
  <2> QED BY <2>1, <2>2, <2>3
<1> QED BY <1>3, <1>4

LEMMA AHDelete ==
  ASSUME Inv, StepOK, NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT,
         DeleteSuffix(j, m, k)
  PROVE  AckedHeld'
<1> SUFFICES ASSUME NEW n \in Server, NEW t \in DOMAIN ledLog', NEW c \in 1..Len(ledLog'[t]),
                    Good(t, c)', n \in AckedBy(t, c)'
             PROVE  Agree(ledLog'[t], log'[n], c) \/ LostIn(t, c, t, currentTerm[n])'
  BY DEF AckedHeld
<1> DEFINE p == m.prevLogIndex
<1>0. TypeOK /\ ReqFromLed BY DEF Inv
<1>1. UNCHANGED <<msgs, ledLog, currentTerm>> BY DEF DeleteSuffix
<1>2. /\ log' = [log EXCEPT ![j] = log'[j]]
      /\ log'[j] \in Seq(EntryT)
      /\ Len(log'[j]) = p + k - 1
      /\ p + k <= Len(log[j])
      /\ \A q \in 1..Len(log'[j]) : log'[j][q] = log[j][q]
  BY <1>0, DeleteLog
<1>3. CASE n # j
  <2>1. log'[n] = log[n] BY <1>2, <1>3, <1>0 DEF TypeOK
  <2> QED BY <2>1, AHOld
<1>4. CASE n = j
  <2>1. /\ t \in DOMAIN ledLog /\ c \in 1..Len(ledLog[t]) /\ Good(t, c) /\ c \in Nat /\ t \in Nat
        /\ ledLog[t] \in Seq(EntryT) /\ log[j] \in Seq(EntryT)
        /\ t <= currentTerm[j] /\ currentTerm[j] \in Nat
        /\ Agree(ledLog[t], log[j], c) \/ LostIn(t, c, t, currentTerm[j])
    BY <1>1, <1>4, AHLogStep
  <2>2. CASE LostIn(t, c, t, currentTerm[j]) BY <2>2, <1>1, <1>4 DEF LostIn
  <2>3. CASE Agree(ledLog[t], log[j], c)
    <3>1. p \in Nat /\ m.entries \in Seq(EntryT) /\ m.type = "append" /\ k \in Nat /\ k >= 1 BY DEF AppendT
    <3>2. CASE c <= p + k - 1
      <4>1. Agree(ledLog[t], log'[j], c) BY <2>3, <2>1, <3>1, <3>2, <1>2 DEF Agree
      <4> QED BY <4>1, <1>1, <1>4
    <3>3. CASE c >= p + k
      <4>1. /\ m.term \in DOMAIN ledLog /\ m.entries[k] = ledLog[m.term][p + k]
        BY <1>0, <3>1 DEF ReqFromLed
      <4>2. log[j][p + k].term # m.entries[k].term /\ m.term = currentTerm[j] BY DEF DeleteSuffix
      <4>3. p + k \in 1..c BY <3>1, <3>3, <2>1
      <4>4. ledLog[t][p + k] = log[j][p + k] BY <4>3, <2>3 DEF Agree
      <4>5. ~Agree(ledLog[t], ledLog[m.term], c) BY <4>1, <4>2, <4>3, <4>4 DEF Agree
      <4>6. Agree(ledLog[t], ledLog[t], c) BY <2>1 DEF Agree
      <4>7. t # m.term BY <4>5, <4>6
      <4>8. t < m.term /\ m.term <= currentTerm[j] BY <4>7, <4>2, <2>1
      <4>9. LostIn(t, c, t, currentTerm[j]) BY <4>1, <4>5, <4>8 DEF LostIn
      <4> QED BY <4>9, <1>1, <1>4 DEF LostIn
    <3> QED BY <3>1, <3>2, <3>3, <2>1
  <2> QED BY <2>1, <2>2, <2>3
<1> QED BY <1>3, <1>4

LEMMA AHStep ==
  ASSUME Inv, StepOK, ProtoCases
  PROVE  AckedHeld'
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE AckedHeld'
  BY <1>a, AHSame DEF BecomeCandidate, durable
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE AckedHeld'
  BY <1>b, AHSame DEF BecomeFollower, durable
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE AckedHeld'
  BY <1>c, AHSame DEF BecomeLeader, durable
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE AckedHeld'
  BY <1>d, AHSame DEF StartElection, durable
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE AckedHeld'
  BY <1>e, AHSame DEF Restart, durable
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE AckedHeld'
  BY <1>f, AHSame DEF Apply, durable
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE AckedHeld'
  BY <1>g, AHSame DEF Restore, durable
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE AckedHeld'
  BY <1>h, AHSame DEF SwitchConf, durable
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE AckedHeld'
  BY <1>i, AHSame DEF RestoreConf, durable
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE AckedHeld'
  BY <1>j, AHSame DEF LeaderAppend1, durable
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE AckedHeld'
  BY <1>k, AHSame DEF AdoptTerm, durable
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE AckedHeld'
  BY <1>l, AHSame DEF CastVote, durable
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE AckedHeld'
  BY <1>m, AHSame DEF GrantVote, durable
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE AckedHeld'
  BY <1>n, AHSame DEF LeaderCommit, durable
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE AckedHeld'
  BY <1>o, AHSame DEF SendAppend, durable
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE AckedHeld'
  BY <1>p, AHSame DEF Ack, durable
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE AckedHeld'
  BY <1>q, AHSame DEF AckCommitted, durable
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE AckedHeld'
  BY <1>r, AHDelete
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE AckedHeld'
  BY <1>s, AHStore
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE AckedHeld'
  BY <1>t, AHSame DEF FollowerCommit, durable
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases

----
\* AckVote.

LEMMA AVOld ==
  ASSUME Inv, StepOK, NEW v \in votes,
         NEW t, NEW c \in Nat, Good(t, c)', v.voter \in AckedBy(t, c)', t < v.term,
         NEW m \in msgs', m.type = "vote", m.src = v.cand, m.term = v.term
  PROVE  Covers(t, c, m.lastLogIndex, m.lastLogTerm)' \/ LostIn(t, c, t, v.term)'
<1>0. TypeOK /\ Grows /\ AckVote BY DEF Inv, StepOK, StepOK0
<1>1. t \in DOMAIN ledLog /\ c \in 1..Len(ledLog[t]) /\ Good(t, c) /\ v.voter \in AckedBy(t, c)
  BY VoterAckOld
<1>2. m \in msgs BY ReqOld
<1>3. Covers(t, c, m.lastLogIndex, m.lastLogTerm) \/ LostIn(t, c, t, v.term)
  BY <1>0, <1>1, <1>2 DEF AckVote
<1>4. t \in Nat /\ v.term \in Nat BY <1>0, <1>1 DEF TypeOK, VoteT
<1>5. CASE Covers(t, c, m.lastLogIndex, m.lastLogTerm) BY <1>5, <1>0, <1>1, CoversKeep
<1>6. CASE LostIn(t, c, t, v.term)
  <2>1. PICK w \in DOMAIN ledLog :
            /\ w \in Nat /\ w \in DOMAIN ledLog' /\ t < w /\ w <= v.term
            /\ ~Agree(ledLog'[t], ledLog'[w], c)
    BY <1>6, <1>0, <1>1, <1>4, LostGrow
  <2> QED BY <2>1 DEF LostIn
<1> QED BY <1>3, <1>5, <1>6

LEMMA AVSame ==
  ASSUME Inv, StepOK, votes' = votes
  PROVE  AckVote'
<1> SUFFICES ASSUME NEW v \in votes', NEW t \in DOMAIN ledLog', NEW c \in 1..Len(ledLog'[t]),
                    Good(t, c)', v.voter \in AckedBy(t, c)', t < v.term,
                    NEW m \in msgs', m.type = "vote", m.src = v.cand, m.term = v.term
             PROVE  Covers(t, c, m.lastLogIndex, m.lastLogTerm)' \/ LostIn(t, c, t, v.term)'
  BY DEF AckVote
<1>1. c \in Nat BY DEF StepOK, LedT
<1> QED BY <1>1, AVOld

\* The request that gets a vote is at least as far as what the voter has acknowledged.
LEMMA VoteCover ==
  ASSUME Inv, NEW i \in Server, NEW m \in msgs, m.type = "vote", m.term = currentTerm[i], UpToDate(m, i),
         NEW t \in DOMAIN ledLog, NEW c \in 1..Len(ledLog[t]), Good(t, c), i \in AckedBy(t, c),
         t < currentTerm[i]
  PROVE  Covers(t, c, m.lastLogIndex, m.lastLogTerm) \/ LostIn(t, c, t, currentTerm[i])
<1>0. TypeOK /\ AckedHeld /\ LogFromLed /\ LedFromLed /\ LedTermsBound /\ TermsPositive /\ ReqFacts
  BY DEF Inv
<1> DEFINE u == currentTerm[i]  L == Len(log[i])  T == log[i][L].term
           li == m.lastLogIndex  lt == m.lastLogTerm
<1>1. /\ log[i] \in Seq(EntryT) /\ u \in Nat /\ t \in Nat /\ ledLog[t] \in Seq(EntryT) /\ c \in Nat
      /\ t >= 1 /\ L \in Nat
  BY <1>0 DEF TypeOK, TermsPositive
<1>2. li \in Nat /\ lt \in Nat BY <1>0 DEF TypeOK, MsgT, VoteReqT, GrantT, AppendT, AckT
<1>3. ReqOk(u, li, lt) BY <1>0 DEF ReqFacts
<1>4. Agree(ledLog[t], log[i], c) \/ LostIn(t, c, t, u) BY <1>0 DEF AckedHeld
<1>5. CASE Agree(ledLog[t], log[i], c)
  <2>1. c <= L /\ L \in 1..L /\ c \in 1..L /\ log[i][c] = ledLog[t][c] /\ log[i][c].term = t
    BY <1>5, <1>1 DEF Agree, Good
  <2>2. LastTerm(i) = T BY <2>1, <1>1 DEF LastTerm, TermAt
  <2>3. FromLed(log[i]) BY <1>0 DEF LogFromLed
  <2>4. log[i][c].term <= log[i][L].term BY <1>0, <1>1, <2>1, <2>3, SortedLed
  <2>5. T \in DOMAIN ledLog /\ Agree(log[i], ledLog[T], L) BY <2>1, <2>3 DEF FromLed
  <2>6. T \in Nat /\ ledLog[T] \in Seq(EntryT) /\ t <= T BY <2>5, <2>4, <2>1, <1>0 DEF TypeOK
  <2>7. lt > T \/ (lt = T /\ li >= L) BY <2>2 DEF UpToDate
  <2>8. CASE lt = T /\ li >= L
    <3>0. c <= Len(ledLog[t]) /\ c <= Len(ledLog[T]) /\ L <= Len(ledLog[T])
      BY <1>5, <2>5, <2>6, <2>1, <1>1 DEF Agree
    <3>a. ASSUME NEW q \in 1..c PROVE ledLog[t][q] = ledLog[T][q]
      <4>1. q \in 1..L BY <2>1, <1>1
      <4>2. ledLog[t][q] = log[i][q] BY <1>5 DEF Agree
      <4>3. log[i][q] = ledLog[T][q] BY <4>1, <2>5 DEF Agree
      <4> QED BY <4>2, <4>3
    <3>1. Agree(ledLog[t], ledLog[T], c) BY <3>0, <3>a DEF Agree
    <3>2. c <= li BY <2>8, <2>1, <1>1, <1>2
    <3> QED BY <3>1, <3>2, <2>5, <2>8 DEF Covers
  <2>9. CASE lt > T
    <3>1. lt \in DOMAIN ledLog /\ li <= Len(ledLog[lt]) /\ TermAt(ledLog[lt], li) = lt /\ lt < u
      BY <1>3, <2>9, <2>6, <1>1, <1>2 DEF ReqOk
    <3>2. ledLog[lt] \in Seq(EntryT) BY <3>1, <1>0 DEF TypeOK
    <3>3. li >= 1 /\ ledLog[lt][li].term = lt BY <3>1, <2>9, <2>6, <1>1, <1>2 DEF TermAt
    <3>4. CASE ~Agree(ledLog[t], ledLog[lt], c)
      <4>1. t < lt /\ lt <= u BY <3>1, <2>9, <2>6, <1>1, <1>2
      <4> QED BY <4>1, <3>1, <3>4 DEF LostIn
    <3>5. CASE Agree(ledLog[t], ledLog[lt], c)
      <4>1. c <= Len(ledLog[lt]) /\ ledLog[lt][c].term = t BY <3>5, <1>1 DEF Agree, Good
      <4>2. FromLed(ledLog[lt]) BY <3>1, <1>0 DEF LedFromLed
      <4>3. ASSUME li < c PROVE FALSE
        <5>1. li \in 1..Len(ledLog[lt]) /\ c \in 1..Len(ledLog[lt]) /\ li <= c
          BY <4>3, <4>1, <3>1, <3>2, <3>3, <1>1, <1>2
        <5>2. ledLog[lt][li].term <= ledLog[lt][c].term BY <5>1, <4>2, <3>2, <1>0, SortedLed
        <5> QED BY <5>2, <4>1, <3>3, <2>9, <2>6, <1>1, <1>2
      <4>4. c <= li BY <4>3, <1>1, <1>2
      <4> QED BY <4>4, <3>1, <3>5 DEF Covers
    <3> QED BY <3>4, <3>5
  <2> QED BY <2>7, <2>8, <2>9
<1> QED BY <1>4, <1>5

LEMMA AVCast ==
  ASSUME Inv, StepOK, NEW i \in Server, NEW cd \in Server, CastVote(i, cd)
  PROVE  AckVote'
<1>0. TypeOK /\ ReqUnique BY DEF Inv
<1>1. /\ msgs' = msgs /\ ledLog' = ledLog
      /\ votes' = votes \cup {[voter |-> i, term |-> currentTerm[i], cand |-> cd]}
      /\ MayVote(i, cd)
  BY DEF CastVote
<1> SUFFICES ASSUME NEW v \in votes', NEW t \in DOMAIN ledLog', NEW c \in 1..Len(ledLog'[t]),
                    Good(t, c)', v.voter \in AckedBy(t, c)', t < v.term,
                    NEW m \in msgs', m.type = "vote", m.src = v.cand, m.term = v.term
             PROVE  Covers(t, c, m.lastLogIndex, m.lastLogTerm)' \/ LostIn(t, c, t, v.term)'
  BY DEF AckVote
<1>2. c \in Nat BY DEF StepOK, LedT
<1>3. CASE v \in votes BY <1>3, <1>2, AVOld
<1>4. CASE v \notin votes
  <2>1. v.voter = i /\ v.term = currentTerm[i] /\ v.cand = cd BY <1>4, <1>1
  <2>2. PICK m0 \in msgs : m0.type = "vote" /\ m0.src = cd /\ m0.term = currentTerm[i] /\ UpToDate(m0, i)
    BY <1>1 DEF MayVote
  <2>3. m = m0 BY <2>1, <2>2, <1>0, <1>1 DEF ReqUnique
  <2>4. t \in DOMAIN ledLog /\ c \in 1..Len(ledLog[t]) /\ Good(t, c) /\ i \in AckedBy(t, c)
    BY <2>1, <1>1 DEF Good, AckedBy
  <2>5. Covers(t, c, m.lastLogIndex, m.lastLogTerm) \/ LostIn(t, c, t, currentTerm[i])
    BY <2>1, <2>2, <2>3, <2>4, VoteCover
  <2> QED BY <2>5, <2>1, <1>1 DEF Covers, LostIn
<1> QED BY <1>3, <1>4

LEMMA AVStep ==
  ASSUME Inv, StepOK, ProtoCases
  PROVE  AckVote'
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE AckVote'
  BY <1>a, AVSame DEF BecomeCandidate, durable
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE AckVote'
  BY <1>b, AVSame DEF BecomeFollower, durable
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE AckVote'
  BY <1>c, AVSame DEF BecomeLeader, durable
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE AckVote'
  BY <1>d, AVSame DEF StartElection, durable
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE AckVote'
  BY <1>e, AVSame DEF Restart, durable
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE AckVote'
  BY <1>f, AVSame DEF Apply, durable
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE AckVote'
  BY <1>g, AVSame DEF Restore, durable
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE AckVote'
  BY <1>h, AVSame DEF SwitchConf, durable
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE AckVote'
  BY <1>i, AVSame DEF RestoreConf, durable
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE AckVote'
  BY <1>j, AVSame DEF LeaderAppend1, durable
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE AckVote'
  BY <1>k, AVSame DEF AdoptTerm, durable
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE AckVote'
  BY <1>l, AVCast
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE AckVote'
  BY <1>m, AVSame DEF GrantVote, durable
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE AckVote'
  BY <1>n, AVSame DEF LeaderCommit, durable
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE AckVote'
  BY <1>o, AVSame DEF SendAppend, durable
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE AckVote'
  BY <1>p, AVSame DEF Ack, durable
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE AckVote'
  BY <1>q, AVSame DEF AckCommitted, durable
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE AckVote'
  BY <1>r, AVSame DEF DeleteSuffix, durable
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE AckVote'
  BY <1>s, AVSame DEF StoreEntries, durable
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE AckVote'
  BY <1>t, AVSame DEF FollowerCommit, durable
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases

----
\* EarlyQuorum.

LEMMA EarlyKeep ==
  ASSUME Inv, StepOK, NEW v \in votes, Early(v.voter, v.cand, v.term)
  PROVE  Early(v.voter, v.cand, v.term)'
<1>0. TypeOK /\ Grows /\ LedT' BY DEF Inv, StepOK, StepOK0
<1> SUFFICES ASSUME NEW t \in DOMAIN ledLog', NEW c \in 1..Len(ledLog'[t]),
                    Good(t, c)', v.voter \in AckedBy(t, c)', t < v.term,
                    NEW m \in msgs', m.type = "vote", m.src = v.cand, m.term = v.term
             PROVE  Covers(t, c, m.lastLogIndex, m.lastLogTerm)' \/ LostIn(t, c, t, v.term - 1)'
  BY DEF Early
<1>1. c \in Nat BY <1>0 DEF LedT
<1>2. t \in DOMAIN ledLog /\ c \in 1..Len(ledLog[t]) /\ Good(t, c) /\ v.voter \in AckedBy(t, c)
  BY <1>1, VoterAckOld
<1>3. m \in msgs BY ReqOld
<1>4. Covers(t, c, m.lastLogIndex, m.lastLogTerm) \/ LostIn(t, c, t, v.term - 1)
  BY <1>2, <1>3 DEF Early
<1>5. t \in Nat /\ v.term \in Nat /\ v.term - 1 \in Nat BY <1>0, <1>2 DEF TypeOK, VoteT
<1>6. CASE Covers(t, c, m.lastLogIndex, m.lastLogTerm) BY <1>6, <1>0, <1>1, <1>2, CoversKeep
<1>7. CASE LostIn(t, c, t, v.term - 1)
  <2>1. PICK w \in DOMAIN ledLog :
            /\ w \in Nat /\ w \in DOMAIN ledLog' /\ t < w /\ w <= v.term - 1
            /\ ~Agree(ledLog'[t], ledLog'[w], c)
    BY <1>7, <1>0, <1>1, <1>2, <1>5, LostGrow
  <2> QED BY <2>1 DEF LostIn
<1> QED BY <1>4, <1>6, <1>7

LEMMA EQOld ==
  ASSUME Inv, StepOK, NEW ld \in leaders
  PROVE  IsQuorum(EarlyVoters(ld.server, ld.term)', ConfOf(ledLog'[ld.term], elAt'[ld.term]))
<1> DEFINE s == ld.server  u == ld.term
<1>0. TypeOK /\ Grows /\ LedDom /\ LeaderConfS /\ EarlyQuorum /\ ConstOK
  BY TypeFacts DEF Inv, StepOK, StepOK0
<1>1. u \in DOMAIN ledLog BY <1>0 DEF LedDom
<1>2. ledLog[u] \in Seq(EntryT) /\ elAt[u] \in Nat /\ ledAt[u] \in Nat BY <1>0, <1>1 DEF TypeOK
<1>3. elAt[u] <= Len(ledLog[u]) BY <1>0, <1>1, <1>2 DEF LeaderConfS
<1>4. elAt'[u] = elAt[u] /\ Pre(ledLog[u], ledLog'[u]) BY <1>0, <1>1 DEF Grows
<1>5. \A q \in 1..elAt[u] : ledLog'[u][q] = ledLog[u][q] BY <1>2, <1>3, <1>4 DEF Pre, Agree
<1>6. ConfOf(ledLog'[u], elAt[u]) = ConfOf(ledLog[u], elAt[u]) BY <1>2, <1>5, ConfOfCongr
<1>7. ConfOf(ledLog[u], elAt[u]) \in ConfT BY <1>0, <1>2, <1>3, ConfOfType
<1>8. IsQuorum(EarlyVoters(s, u), ConfOf(ledLog[u], elAt[u])) BY <1>0 DEF EarlyQuorum
<1>9. EarlyVoters(s, u) \subseteq EarlyVoters(s, u)'
  <2> SUFFICES ASSUME NEW n \in EarlyVoters(s, u) PROVE n \in EarlyVoters(s, u)' OBVIOUS
  <2> DEFINE v == [voter |-> n, term |-> u, cand |-> s]
  <2>1. n \in Server /\ v \in votes /\ Early(n, s, u) BY DEF EarlyVoters
  <2>2. v \in votes' BY <2>1, <1>0 DEF Grows
  <2>3. v.voter = n /\ v.cand = s /\ v.term = u OBVIOUS
  <2> HIDE DEF v
  <2>4. Early(v.voter, v.cand, v.term)' BY <2>1, <2>3, EarlyKeep
  <2>5. Early(n, s, u)' BY <2>3, <2>4
  <2> QED BY <2>1, <2>2, <2>5 DEF EarlyVoters, v
<1> HIDE DEF s, u
<1> QED BY <1>0, <1>4, <1>6, <1>7, <1>8, <1>9, QuorumMono DEF s, u

LEMMA EQSame ==
  ASSUME Inv, StepOK, leaders' = leaders
  PROVE  EarlyQuorum'
<1> SUFFICES ASSUME NEW ld \in leaders'
             PROVE  IsQuorum(EarlyVoters(ld.server, ld.term)', ConfOf(ledLog'[ld.term], elAt'[ld.term]))
  BY DEF EarlyQuorum
<1> QED BY EQOld

\* The configuration a candidate counts votes with is the one its log makes.
LEMMA ElectConf ==
  ASSUME Inv, NEW i \in Server, CommittedBefore(log[i], confAt[i], currentTerm[i])
  PROVE  config[i] = ConfOf(log[i], confAt[i])
<1>0. TypeOK /\ ConfIsCommitted /\ CommitSafetyP BY DEF Inv
<1> DEFINE a == confAt[i]
<1>1. a \in Nat /\ log[i] \in Seq(EntryT) BY <1>0 DEF TypeOK
<1>2. CASE a = 0
  <2>1. config[i] = InitConf \/ \E c \in commits : config[i] = ConfOf(c.entries, 0)
    BY <1>0, <1>2 DEF ConfIsCommitted
  <2>2. \A l : ConfOf(l, 0) = InitConf BY ConfOf0
  <2> QED BY <2>1, <2>2, <1>2
<1>3. CASE a # 0
  <2>1. PICK c \in commits : a <= Len(c.entries) /\ config[i] = ConfOf(c.entries, a)
    BY <1>0, <1>3 DEF ConfIsCommitted
  <2>2. a <= Len(log[i]) /\ \E k \in commits : a <= Len(k.entries) /\ SubSeq(k.entries, 1, a) = SubSeq(log[i], 1, a)
    BY <1>3 DEF CommittedBefore
  <2>3. PICK k \in commits : a <= Len(k.entries) /\ SubSeq(k.entries, 1, a) = SubSeq(log[i], 1, a)
    BY <2>2
  <2>4. c.entries \in Seq(EntryT) /\ k.entries \in Seq(EntryT) BY <1>0, TypeFacts
  <2>5. Agree(k.entries, log[i], a) BY <1>1, <2>2, <2>3, <2>4, SubSeqAgree
  <2>6. Pre(c.entries, k.entries) \/ Pre(k.entries, c.entries) BY <1>0 DEF CommitSafetyP
  <2>7. \A q \in 1..a : c.entries[q] = log[i][q] BY <1>1, <2>1, <2>3, <2>4, <2>5, <2>6 DEF Pre, Agree
  <2>8. ConfOf(c.entries, a) = ConfOf(log[i], a) BY <1>1, <2>7, ConfOfCongr
  <2> QED BY <2>1, <2>8
<1> QED BY <1>2, <1>3

\* The nodes that elect a leader are early voters of its election.
LEMMA EQNew ==
  ASSUME Inv, StepOK, NEW i \in Server, BecomeLeader(i), NEW u, u = currentTerm[i]
  PROVE  IsQuorum(EarlyVoters(i, u)', ConfOf(ledLog'[u], elAt'[u]))
<1>0. TypeOK /\ Basic /\ Grows /\ ConstOK /\ GrantsAreVotes /\ AckVote /\ LedT'
  BY AInvBasic, TypeFacts DEF Inv, StepOK, StepOK0
<1>1. /\ u \in Nat /\ u \notin DOMAIN ledLog
      /\ ledLog'[u] = log[i] /\ elAt'[u] = confAt[i]
      /\ IsQuorum(Granted(i), config[i])
      /\ msgs' = msgs /\ votes' = votes
  BY <1>0, BecomeLeaderLed
<1>2. CommittedBefore(log[i], confAt[i], currentTerm[i]) BY DEF BecomeLeader
<1>3. config[i] = ConfOf(log[i], confAt[i]) BY <1>2, ElectConf
<1>4. config[i] \in ConfT BY <1>0 DEF TypeOK
<1>5. Granted(i) \subseteq EarlyVoters(i, u)'
  <2> SUFFICES ASSUME NEW n \in Granted(i) PROVE n \in EarlyVoters(i, u)' OBVIOUS
  <2> DEFINE v == [voter |-> n, term |-> u, cand |-> i]
  <2>1. n \in Server /\ v \in votes
    <3>1. CASE n = i BY <3>1 DEF Granted
    <3>2. CASE n # i
      <4> DEFINE g == [type |-> "grant", src |-> n, dst |-> i, term |-> u]
      <4>1. n \in Server /\ g \in msgs BY <3>2 DEF Granted
      <4>2. g.type = "grant" /\ g.src = n /\ g.dst = i /\ g.term = u OBVIOUS
      <4> HIDE DEF g
      <4> QED BY <4>1, <4>2, <1>0 DEF GrantsAreVotes
    <3> QED BY <3>1, <3>2
  <2>2. v.voter = n /\ v.cand = i /\ v.term = u OBVIOUS
  <2> HIDE DEF v
  <2>3. Early(n, i, u)'
    <3> SUFFICES ASSUME NEW t \in DOMAIN ledLog', NEW c \in 1..Len(ledLog'[t]),
                        Good(t, c)', n \in AckedBy(t, c)', t < u,
                        NEW m \in msgs', m.type = "vote", m.src = i, m.term = u
                 PROVE  Covers(t, c, m.lastLogIndex, m.lastLogTerm)' \/ LostIn(t, c, t, u - 1)'
      BY DEF Early
    <3>1. c \in Nat BY <1>0 DEF LedT
    <3>2. t \in DOMAIN ledLog /\ c \in 1..Len(ledLog[t]) /\ Good(t, c) /\ v.voter \in AckedBy(t, c)
      BY <3>1, <2>1, <2>2, VoterAckOld
    <3>3. m \in msgs BY <1>1
    <3>4. Covers(t, c, m.lastLogIndex, m.lastLogTerm) \/ LostIn(t, c, t, u)
      BY <3>2, <3>3, <2>1, <2>2, <1>0 DEF AckVote
    <3>5. t \in Nat /\ u - 1 \in Nat BY <1>0, <1>1, <3>2 DEF TypeOK
    <3>6. CASE Covers(t, c, m.lastLogIndex, m.lastLogTerm) BY <3>6, <1>0, <3>1, <3>2, CoversKeep
    <3>7. CASE LostIn(t, c, t, u)
      <4>1. PICK w0 \in DOMAIN ledLog : t < w0 /\ w0 <= u /\ ~Agree(ledLog[t], ledLog[w0], c)
        BY <3>7 DEF LostIn
      <4>2. w0 \in Nat /\ w0 # u BY <4>1, <1>1, <1>0 DEF TypeOK
      <4>3. LostIn(t, c, t, u - 1) BY <4>1, <4>2, <1>1, <3>5 DEF LostIn
      <4>4. PICK w \in DOMAIN ledLog :
              /\ w \in Nat /\ w \in DOMAIN ledLog' /\ t < w /\ w <= u - 1
              /\ ~Agree(ledLog'[t], ledLog'[w], c)
        BY <4>3, <1>0, <3>1, <3>2, <3>5, LostGrow
      <4> QED BY <4>4 DEF LostIn
    <3> QED BY <3>4, <3>6, <3>7
  <2> QED BY <2>1, <2>3, <1>1 DEF EarlyVoters, v
<1>6. IsQuorum(EarlyVoters(i, u)', config[i]) BY <1>0, <1>1, <1>4, <1>5, QuorumMono
<1> QED BY <1>1, <1>3, <1>6

LEMMA EQBecome ==
  ASSUME Inv, StepOK, NEW i \in Server, BecomeLeader(i)
  PROVE  EarlyQuorum'
<1> SUFFICES ASSUME NEW ld \in leaders'
             PROVE  IsQuorum(EarlyVoters(ld.server, ld.term)', ConfOf(ledLog'[ld.term], elAt'[ld.term]))
  BY DEF EarlyQuorum
<1>1. leaders' = leaders \cup {[server |-> i, term |-> currentTerm[i]]} BY DEF BecomeLeader
<1>2. CASE ld \in leaders BY <1>2, EQOld
<1>3. CASE ld \notin leaders
  <2>1. ld.server = i /\ ld.term = currentTerm[i] BY <1>1, <1>3
  <2> QED BY <2>1, EQNew
<1> QED BY <1>2, <1>3

LEMMA EQStep ==
  ASSUME Inv, StepOK, ProtoCases
  PROVE  EarlyQuorum'
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE EarlyQuorum'
  BY <1>a, EQSame DEF BecomeCandidate, durable
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE EarlyQuorum'
  BY <1>b, EQSame DEF BecomeFollower, durable
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE EarlyQuorum'
  BY <1>c, EQBecome
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE EarlyQuorum'
  BY <1>d, EQSame DEF StartElection, durable
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE EarlyQuorum'
  BY <1>e, EQSame DEF Restart, durable
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE EarlyQuorum'
  BY <1>f, EQSame DEF Apply, durable
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE EarlyQuorum'
  BY <1>g, EQSame DEF Restore, durable
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE EarlyQuorum'
  BY <1>h, EQSame DEF SwitchConf, durable
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE EarlyQuorum'
  BY <1>i, EQSame DEF RestoreConf, durable
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE EarlyQuorum'
  BY <1>j, EQSame DEF LeaderAppend1, durable
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE EarlyQuorum'
  BY <1>k, EQSame DEF AdoptTerm, durable
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE EarlyQuorum'
  BY <1>l, EQSame DEF CastVote, durable
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE EarlyQuorum'
  BY <1>m, EQSame DEF GrantVote, durable
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE EarlyQuorum'
  BY <1>n, EQSame DEF LeaderCommit, durable
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE EarlyQuorum'
  BY <1>o, EQSame DEF SendAppend, durable
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE EarlyQuorum'
  BY <1>p, EQSame DEF Ack, durable
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE EarlyQuorum'
  BY <1>q, EQSame DEF AckCommitted, durable
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE EarlyQuorum'
  BY <1>r, EQSame DEF DeleteSuffix, durable
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE EarlyQuorum'
  BY <1>s, EQSame DEF StoreEntries, durable
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE EarlyQuorum'
  BY <1>t, EQSame DEF FollowerCommit, durable
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases

THEOREM AGStep == ASSUME Inv, ProtoCases PROVE AG'
<1>1. StepOK BY StepOKStep
<1> QED BY <1>1, AHStep, AVStep, EQStep DEF AG
====
