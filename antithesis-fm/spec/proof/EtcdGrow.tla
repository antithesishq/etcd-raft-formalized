---- MODULE EtcdGrow ----
\* What every step of the protocol does to the facts: they only grow.
EXTENDS EtcdType

Grows ==
    /\ msgs \subseteq msgs' /\ commits \subseteq commits'
    /\ votes \subseteq votes' /\ leaders \subseteq leaders'
    /\ DOMAIN ledLog \subseteq DOMAIN ledLog'
    /\ \A t \in DOMAIN ledLog :
          /\ ledLog'[t] \in Seq(EntryT)
          /\ Pre(ledLog[t], ledLog'[t])
          /\ \A q \in (Len(ledLog[t]) + 1)..Len(ledLog'[t]) : ledLog'[t][q].term = t
          /\ elAt'[t] = elAt[t]
    /\ \A i \in Server : currentTerm[i] <= currentTerm'[i]

LEMMA GrowsSame ==
  ASSUME TypeOK, UNCHANGED <<msgs, commits, votes, leaders, ledLog, elAt, currentTerm>>
  PROVE  Grows
BY DEF Grows, Pre, Agree, TypeOK

LEMMA GrowsFacts ==
  ASSUME TypeOK, msgs \subseteq msgs', commits \subseteq commits', votes \subseteq votes',
         UNCHANGED <<leaders, ledLog, elAt, currentTerm>>
  PROVE  Grows
BY DEF Grows, Pre, Agree, TypeOK

LEMMA GrowsStep ==
  ASSUME Basic, ProtoCases
  PROVE  Grows
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE Grows
  BY <1>a, GrowsSame DEF BecomeCandidate, Basic, durable
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE Grows
  BY <1>b, GrowsSame DEF BecomeFollower, Basic, durable
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE Grows
  <2> DEFINE u == currentTerm[i]
  <2>1. u \notin DOMAIN ledLog /\ ledLog' = [w \in DOMAIN ledLog \cup {u} |-> IF w = u THEN log[i] ELSE ledLog[w]]
    BY <1>c DEF BecomeLeader, WithLed
  <2>2. elAt' = [w \in DOMAIN elAt \cup {u} |-> IF w = u THEN confAt[i] ELSE elAt[w]]
    BY <1>c DEF BecomeLeader, With
  <2>3. DOMAIN elAt = DOMAIN ledLog /\ \A t \in DOMAIN ledLog : ledLog[t] \in Seq(EntryT) BY DEF Basic, TypeOK
  <2>4. \A t \in DOMAIN ledLog : ledLog'[t] = ledLog[t] /\ elAt'[t] = elAt[t] BY <2>1, <2>2, <2>3
  <2>5. \A t \in DOMAIN ledLog : Pre(ledLog[t], ledLog'[t]) BY <2>3, <2>4 DEF Pre, Agree
  <2>6. currentTerm \in [Server -> Nat] BY DEF Basic, TypeOK
  <2> HIDE DEF u
  <2> QED BY <1>c, <2>1, <2>3, <2>4, <2>5, <2>6 DEF BecomeLeader, Grows, durable
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE Grows
  <2>1. currentTerm \in [Server -> Nat] /\ \A t \in DOMAIN ledLog : ledLog[t] \in Seq(EntryT) BY DEF Basic, TypeOK
  <2> QED BY <1>d, <2>1 DEF StartElection, Grows, Pre, Agree
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE Grows
  BY <1>e, GrowsSame DEF Restart, Basic, durable
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE Grows
  BY <1>f, GrowsSame DEF Apply, Basic, durable
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE Grows
  BY <1>g, GrowsSame DEF Restore, Basic, durable
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE Grows
  BY <1>h, GrowsSame DEF SwitchConf, Basic, durable
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE Grows
  BY <1>i, GrowsSame DEF RestoreConf, Basic, durable
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE Grows
  <2> DEFINE u == currentTerm[i]
  <2>1. u \in DOMAIN ledLog /\ ledLog' = [w \in DOMAIN ledLog \cup {u} |-> IF w = u THEN Append(ledLog[u], e) ELSE ledLog[w]]
    BY <1>j DEF LeaderAppend1, WithLed
  <2>2. \A t \in DOMAIN ledLog : ledLog[t] \in Seq(EntryT) BY DEF Basic, TypeOK
  <2>3. e.term = u BY <1>j DEF LeaderAppend1
  <2>4. \A t \in DOMAIN ledLog : /\ ledLog'[t] \in Seq(EntryT)
                                  /\ Pre(ledLog[t], ledLog'[t])
                                  /\ \A q \in (Len(ledLog[t]) + 1)..Len(ledLog'[t]) : ledLog'[t][q].term = t
    <3> TAKE t \in DOMAIN ledLog
    <3>1. CASE t # u BY <3>1, <2>1, <2>2 DEF Pre, Agree
    <3>2. CASE t = u
      <4>1. ledLog'[t] = Append(ledLog[u], e) BY <3>2, <2>1
      <4>2. ledLog[u] \in Seq(EntryT) BY <2>1, <2>2
      <4> HIDE DEF u
      <4> QED BY <4>1, <4>2, <2>3, <3>2 DEF Pre, Agree
    <3> QED BY <3>1, <3>2
  <2>5. currentTerm \in [Server -> Nat] BY DEF Basic, TypeOK
  <2> HIDE DEF u
  <2> QED BY <1>j, <2>1, <2>4, <2>5 DEF LeaderAppend1, Grows, durable
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE Grows
  <2>1. currentTerm \in [Server -> Nat] /\ \A t \in DOMAIN ledLog : ledLog[t] \in Seq(EntryT) BY DEF Basic, TypeOK
  <2> QED BY <1>k, <2>1 DEF AdoptTerm, Grows, Pre, Agree
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE Grows
  BY <1>l, GrowsFacts DEF CastVote, Basic, durable
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE Grows
  BY <1>m, GrowsFacts DEF GrantVote, Basic, durable
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE Grows
  BY <1>n, GrowsFacts DEF LeaderCommit, Basic, durable
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE Grows
  BY <1>o, GrowsFacts DEF SendAppend, Basic, durable
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE Grows
  BY <1>p, GrowsFacts DEF Ack, Basic, durable
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE Grows
  BY <1>q, GrowsFacts DEF AckCommitted, Basic, durable
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE Grows
  BY <1>r, GrowsSame DEF DeleteSuffix, Basic, durable
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE Grows
  BY <1>s, GrowsSame DEF StoreEntries, Basic, durable
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE Grows
  BY <1>t, GrowsFacts DEF FollowerCommit, Basic, durable
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases
====
