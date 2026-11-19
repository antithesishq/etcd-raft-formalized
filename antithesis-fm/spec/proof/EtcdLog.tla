---- MODULE EtcdLog ----
\* Lemmas about logs: what StoreEntries and DeleteSuffix make of a log, what a
\* request that was checked says, and how the facts about logs grow.
EXTENDS EtcdGrow

\* The log after StoreEntries(j, m, k).
LEMMA StoreLog ==
  ASSUME TypeOK, NEW j \in Server, NEW m \in msgs, m \in AppendT,
         NEW k \in 1..Len(m.entries), StoreEntries(j, m, k)
  PROVE  /\ log' = [log EXCEPT ![j] = log'[j]]
         /\ log'[j] \in Seq(EntryT)
         /\ Len(log'[j]) = m.prevLogIndex + Len(m.entries)
         /\ m.prevLogIndex + k = Len(log[j]) + 1
         /\ \A q \in 1..Len(log[j]) : log'[j][q] = log[j][q]
         /\ \A q \in (Len(log[j]) + 1)..Len(log'[j]) : log'[j][q] = m.entries[q - m.prevLogIndex]
<1> DEFINE p == m.prevLogIndex  s == SubSeq(m.entries, k, Len(m.entries))
<1>1. p \in Nat /\ m.entries \in Seq(EntryT) /\ log[j] \in Seq(EntryT) /\ log \in [Server -> Seq(EntryT)]
  BY DEF TypeOK, AppendT
<1>2. s \in Seq(EntryT) /\ Len(s) = Len(m.entries) - k + 1 /\ \A q \in 1..Len(s) : s[q] = m.entries[k + q - 1]
  BY <1>1, SubSeqProperties
<1>3. log'[j] = log[j] \o s /\ p + k = Len(log[j]) + 1 /\ log' = [log EXCEPT ![j] = log[j] \o s]
  BY <1>1 DEF StoreEntries
<1>4. log[j] \o s \in Seq(EntryT) /\ Len(log[j] \o s) = Len(log[j]) + Len(s)
      /\ \A q \in 1..(Len(log[j]) + Len(s)) : (log[j] \o s)[q] = IF q <= Len(log[j]) THEN log[j][q] ELSE s[q - Len(log[j])]
  BY <1>1, <1>2, ConcatProperties
<1> HIDE DEF s
<1>5. \A q \in (Len(log[j]) + 1)..Len(log'[j]) : log'[j][q] = m.entries[q - p]
  <2> TAKE q \in (Len(log[j]) + 1)..Len(log'[j])
  <2>1. log'[j][q] = s[q - Len(log[j])] /\ q - Len(log[j]) \in 1..Len(s) BY <1>1, <1>2, <1>3, <1>4
  <2> QED BY <2>1, <1>1, <1>2, <1>3
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5

\* The log after DeleteSuffix(j, m, k).
LEMMA DeleteLog ==
  ASSUME TypeOK, NEW j \in Server, NEW m \in msgs, m \in AppendT,
         NEW k \in 1..Len(m.entries), DeleteSuffix(j, m, k)
  PROVE  /\ log' = [log EXCEPT ![j] = log'[j]]
         /\ log'[j] \in Seq(EntryT)
         /\ Len(log'[j]) = m.prevLogIndex + k - 1
         /\ m.prevLogIndex + k <= Len(log[j])
         /\ \A q \in 1..Len(log'[j]) : log'[j][q] = log[j][q]
<1> DEFINE p == m.prevLogIndex
<1>1. p \in Nat /\ log[j] \in Seq(EntryT) /\ log \in [Server -> Seq(EntryT)] /\ p + k <= Len(log[j])
  BY DEF TypeOK, AppendT, DeleteSuffix
<1>2. log'[j] = SubSeq(log[j], 1, p + k - 1) /\ log' = [log EXCEPT ![j] = SubSeq(log[j], 1, p + k - 1)]
  BY <1>1 DEF DeleteSuffix
<1>3. p + k - 1 \in Nat /\ p + k - 1 <= Len(log[j]) BY <1>1
<1>4. /\ SubSeq(log[j], 1, p + k - 1) \in Seq(EntryT)
      /\ Len(SubSeq(log[j], 1, p + k - 1)) = p + k - 1
      /\ \A q \in 1..(p + k - 1) : SubSeq(log[j], 1, p + k - 1)[q] = log[j][q]
  BY <1>1, <1>3, SubSeqFacts
<1> QED BY <1>1, <1>2, <1>4

\* A request whose previous entry and first n entries are in j's log, by
\* their terms: j's log is the leader log of the request's term up to there.
LEMMA CheckedPrefix ==
  ASSUME TypeOK, ReqFromLed, LogFromLed, LedFromLed,
         NEW j \in Server, NEW m \in msgs, m \in AppendT, PrevOk(j, m),
         NEW n \in 0..Len(m.entries), HasFirst(j, m, n)
  PROVE  Agree(log[j], ledLog[m.term], m.prevLogIndex + n)
<1> DEFINE p == m.prevLogIndex  L == ledLog[m.term]  l == log[j]  x == p + n
<1>1. p \in Nat /\ m.entries \in Seq(EntryT) /\ l \in Seq(EntryT) /\ m.type = "append"
  BY DEF TypeOK, AppendT
<1>2. /\ m.term \in DOMAIN ledLog
      /\ p + Len(m.entries) <= Len(L)
      /\ m.prevLogTerm = TermAt(L, p)
      /\ \A q \in 1..Len(m.entries) : m.entries[q] = L[p + q]
  BY <1>1 DEF ReqFromLed
<1>3. L \in Seq(EntryT) BY <1>2 DEF TypeOK
<1>4. CASE x = 0 BY <1>4, <1>1, <1>3 DEF Agree
<1>5. CASE x > 0
  <2>1. x \in 1..Len(l) /\ x \in 1..Len(L) /\ l[x].term = L[x].term
    <3>1. CASE n = 0
      BY <3>1, <1>5, <1>1, <1>2, <1>3 DEF PrevOk, TermAt
    <3>2. CASE n > 0
      <4>0. n \in 1..Len(m.entries) /\ n \in Nat /\ Len(m.entries) \in Nat BY <3>2, <1>1
      <4>1. p + n <= Len(l) /\ l[p + n].term = m.entries[n].term BY <4>0, <1>1 DEF HasFirst
      <4>2. m.entries[n] = L[p + n] BY <4>0, <1>2
      <4>3. p + n <= Len(L) /\ p + n >= 1 BY <4>0, <1>1, <1>2, <1>3
      <4> QED BY <4>1, <4>2, <4>3, <1>1, <1>3
    <3> QED BY <3>1, <3>2
  <2> DEFINE tx == l[x].term
  <2>2. tx \in DOMAIN ledLog /\ Agree(l, ledLog[tx], x) BY <2>1 DEF LogFromLed, FromLed
  <2>3. Agree(L, ledLog[tx], x) BY <2>1, <1>2 DEF LedFromLed, FromLed
  <2> HIDE DEF tx
  <2> QED BY <2>2, <2>3 DEF Agree
<1> QED BY <1>4, <1>5, <1>1

\* Agreement of leader logs survives a step.
LEMMA AgreeGrow ==
  ASSUME TypeOK, Grows, NEW t \in DOMAIN ledLog, NEW w \in DOMAIN ledLog, NEW c \in Nat,
         Agree(ledLog[t], ledLog[w], c)
  PROVE  Agree(ledLog'[t], ledLog'[w], c)
<1>1. ledLog[t] \in Seq(EntryT) /\ ledLog[w] \in Seq(EntryT) BY DEF TypeOK
<1>2. Pre(ledLog[t], ledLog'[t]) /\ Pre(ledLog[w], ledLog'[w]) BY DEF Grows
<1>3. ledLog'[t] \in Seq(EntryT) /\ ledLog'[w] \in Seq(EntryT) BY DEF Grows
<1> QED BY <1>1, <1>2, <1>3 DEF Pre, Agree

LEMMA AgreeGrowL ==
  ASSUME TypeOK, Grows, NEW l \in Seq(EntryT), NEW w \in DOMAIN ledLog, NEW c \in Nat,
         Agree(l, ledLog[w], c)
  PROVE  Agree(l, ledLog'[w], c)
<1>1. ledLog[w] \in Seq(EntryT) /\ ledLog'[w] \in Seq(EntryT) BY DEF TypeOK, Grows
<1>2. Pre(ledLog[w], ledLog'[w]) BY DEF Grows
<1> QED BY <1>1, <1>2 DEF Pre, Agree

LEMMA FromLedGrow ==
  ASSUME TypeOK, Grows, NEW l \in Seq(EntryT), FromLed(l)
  PROVE  FromLed(l)'
<1> SUFFICES ASSUME NEW q \in 1..Len(l)
             PROVE l[q].term \in DOMAIN ledLog' /\ Agree(l, ledLog'[l[q].term], q)
  BY DEF FromLed
<1>1. l[q].term \in DOMAIN ledLog /\ Agree(l, ledLog[l[q].term], q) BY DEF FromLed
<1>2. Agree(l, ledLog'[l[q].term], q) BY <1>1, AgreeGrowL
<1> QED BY <1>1, <1>2 DEF Grows

\* FromLed with the leader logs as a parameter (to speak of them after a step).
FromLedIn(l, led) == \A q \in 1..Len(l) : l[q].term \in DOMAIN led /\ Agree(l, led[l[q].term], q)

LEMMA FromLedGrow2 ==
  ASSUME TypeOK, Grows, NEW l \in Seq(EntryT), FromLedIn(l, ledLog)
  PROVE  FromLedIn(l, ledLog')
<1> SUFFICES ASSUME NEW q \in 1..Len(l)
             PROVE l[q].term \in DOMAIN ledLog' /\ Agree(l, ledLog'[l[q].term], q)
  BY DEF FromLedIn
<1>1. l[q].term \in DOMAIN ledLog /\ Agree(l, ledLog[l[q].term], q) BY DEF FromLedIn
<1>2. Agree(l, ledLog'[l[q].term], q) BY <1>1, AgreeGrowL
<1> QED BY <1>1, <1>2 DEF Grows

\* A prefix of a log that is from leader logs is so too.
LEMMA FromLedPrefix ==
  ASSUME NEW L \in Seq(EntryT), NEW l \in Seq(EntryT), FromLed(L), Pre(l, L)
  PROVE  FromLed(l)
<1> SUFFICES ASSUME NEW q \in 1..Len(l)
             PROVE l[q].term \in DOMAIN ledLog /\ Agree(l, ledLog[l[q].term], q)
  BY DEF FromLed
<1>1. q \in 1..Len(L) /\ l[q] = L[q] BY DEF Pre, Agree
<1>2. L[q].term \in DOMAIN ledLog /\ Agree(L, ledLog[L[q].term], q) BY <1>1 DEF FromLed
<1> QED BY <1>1, <1>2 DEF Pre, Agree

LEMMA QuorumNonEmpty ==
  ASSUME ConstOK, NEW C \in ConfT, NEW P, IsQuorum(P, C)
  PROVE  \E s \in Server : s \in P
<1>1. IsFiniteSet(C.in) /\ C.in \subseteq Server BY FS_Subset DEF ConfT, ConstOK
<1>2. IsFiniteSet(P \cap C.in) BY <1>1, FS_Subset
<1>3. Cardinality(P \cap C.in) \in Nat /\ Cardinality(C.in) \in Nat BY <1>1, <1>2, FS_CardinalityType
<1>4. Cardinality(P \cap C.in) # 0 BY <1>3 DEF IsQuorum, Majority
<1>5. P \cap C.in # {} BY <1>4, <1>2, FS_EmptySet
<1> QED BY <1>5, <1>1

\* What BecomeLeader and LeaderAppend1 do, spelled out.
LEMMA BecomeLeaderLed ==
  ASSUME Basic, NEW i \in Server, BecomeLeader(i)
  PROVE  LET u == currentTerm[i] IN
         /\ u \in Nat /\ u \notin DOMAIN ledLog
         /\ DOMAIN ledLog' = DOMAIN ledLog \cup {u}
         /\ ledLog'[u] = log[i] /\ elAt'[u] = confAt[i] /\ ledAt'[u] = confAt[i] /\ ledConf'[u] = config[i]
         /\ \A t \in DOMAIN ledLog : /\ ledLog'[t] = ledLog[t] /\ elAt'[t] = elAt[t]
                                     /\ ledAt'[t] = ledAt[t] /\ ledConf'[t] = ledConf[t]
         /\ leaders' = leaders \cup {[server |-> i, term |-> u]}
         /\ role' = [role EXCEPT ![i] = Leader]
         /\ role[i] = Candidate
         /\ IsQuorum(Granted(i), config[i])
         /\ UNCHANGED <<durable, lastApplied, config, confAt, confirmed, msgs, votes, commits, applied>>
<1> DEFINE u == currentTerm[i]
<1>1. u \in Nat /\ DOMAIN ledConf = DOMAIN ledLog /\ DOMAIN ledAt = DOMAIN ledLog /\ DOMAIN elAt = DOMAIN ledLog
  BY DEF Basic, TypeOK
<1>2. /\ ledLog' = [w \in DOMAIN ledLog \cup {u} |-> IF w = u THEN log[i] ELSE ledLog[w]]
      /\ ledConf' = [w \in DOMAIN ledConf \cup {u} |-> IF w = u THEN config[i] ELSE ledConf[w]]
      /\ ledAt' = [w \in DOMAIN ledAt \cup {u} |-> IF w = u THEN confAt[i] ELSE ledAt[w]]
      /\ elAt' = [w \in DOMAIN elAt \cup {u} |-> IF w = u THEN confAt[i] ELSE elAt[w]]
      /\ u \notin DOMAIN ledLog
  BY DEF BecomeLeader, WithLed, WithConf, With
<1>3. /\ leaders' = leaders \cup {[server |-> i, term |-> u]}
      /\ role' = [role EXCEPT ![i] = Leader] /\ role[i] = Candidate
      /\ IsQuorum(Granted(i), config[i])
      /\ UNCHANGED <<durable, lastApplied, config, confAt, confirmed, msgs, votes, commits, applied>>
  BY DEF BecomeLeader
<1> HIDE DEF u
<1>4. /\ DOMAIN ledLog' = DOMAIN ledLog \cup {u}
      /\ ledLog'[u] = log[i] /\ elAt'[u] = confAt[i] /\ ledAt'[u] = confAt[i] /\ ledConf'[u] = config[i]
      /\ \A t \in DOMAIN ledLog : /\ ledLog'[t] = ledLog[t] /\ elAt'[t] = elAt[t]
                                  /\ ledAt'[t] = ledAt[t] /\ ledConf'[t] = ledConf[t]
  BY <1>1, <1>2
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF u

LEMMA AppendLed ==
  ASSUME Basic, NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e)
  PROVE  LET u == currentTerm[i] IN
         /\ u \in DOMAIN ledLog /\ e.term = u /\ role[i] = Leader
         /\ DOMAIN ledLog' = DOMAIN ledLog
         /\ ledLog[u] \in Seq(EntryT)
         /\ ledLog'[u] \in Seq(EntryT)
         /\ Len(ledLog'[u]) = Len(ledLog[u]) + 1
         /\ ledLog'[u][Len(ledLog[u]) + 1] = e
         /\ \A q \in 1..Len(ledLog[u]) : ledLog'[u][q] = ledLog[u][q]
         /\ \A t \in DOMAIN ledLog : t # u => ledLog'[t] = ledLog[t]
         /\ IsConf(e) => AllSwitched(i, ledLog[u]) /\ Legal(config[i], e.value)
         /\ UNCHANGED <<durable, role, lastApplied, config, confAt, confirmed, msgs, votes, leaders, ledConf, ledAt, elAt, commits, applied>>
<1> DEFINE u == currentTerm[i]
<1>1. u \in DOMAIN ledLog /\ e.term = u /\ role[i] = Leader
      /\ ledLog' = [w \in DOMAIN ledLog \cup {u} |-> IF w = u THEN Append(ledLog[u], e) ELSE ledLog[w]]
      /\ (IsConf(e) => AllSwitched(i, ledLog[u]) /\ Legal(config[i], e.value))
      /\ UNCHANGED <<durable, role, lastApplied, config, confAt, confirmed, msgs, votes, leaders, ledConf, ledAt, elAt, commits, applied>>
  BY DEF LeaderAppend1, WithLed
<1>2. ledLog[u] \in Seq(EntryT) BY <1>1 DEF Basic, TypeOK
<1>3. Append(ledLog[u], e) \in Seq(EntryT) /\ Len(Append(ledLog[u], e)) = Len(ledLog[u]) + 1
      /\ Append(ledLog[u], e)[Len(ledLog[u]) + 1] = e
      /\ \A q \in 1..Len(ledLog[u]) : Append(ledLog[u], e)[q] = ledLog[u][q]
  BY <1>2, AppendProperties
<1> HIDE DEF u
<1>4. DOMAIN ledLog' = DOMAIN ledLog /\ ledLog'[u] = Append(ledLog[u], e)
      /\ \A t \in DOMAIN ledLog : t # u => ledLog'[t] = ledLog[t]
  BY <1>1
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF u

LEMMA PreTrans ==
  ASSUME NEW a \in Seq(EntryT), NEW b \in Seq(EntryT), NEW c \in Seq(EntryT), Pre(a, b), Pre(b, c)
  PROVE  Pre(a, c)
BY DEF Pre, Agree

\* After StoreEntries, j's log is a prefix of the leader log of the request's term.
LEMMA StoreAgree ==
  ASSUME TypeOK, ReqFromLed, LogFromLed, LedFromLed,
         NEW j \in Server, NEW m \in msgs, m \in AppendT,
         NEW k \in 1..Len(m.entries), StoreEntries(j, m, k)
  PROVE  /\ m.term \in DOMAIN ledLog
         /\ Pre(log'[j], ledLog[m.term])
<1> DEFINE p == m.prevLogIndex  L == ledLog[m.term]
<1>1. p \in Nat /\ m.entries \in Seq(EntryT) /\ log[j] \in Seq(EntryT) /\ m.type = "append"
  BY DEF TypeOK, AppendT
<1>2. /\ m.term \in DOMAIN ledLog
      /\ p + Len(m.entries) <= Len(L)
      /\ \A q \in 1..Len(m.entries) : m.entries[q] = L[p + q]
  BY <1>1 DEF ReqFromLed
<1>3. L \in Seq(EntryT) BY <1>2 DEF TypeOK
<1>4. /\ log'[j] \in Seq(EntryT)
      /\ Len(log'[j]) = p + Len(m.entries)
      /\ p + k = Len(log[j]) + 1
      /\ \A q \in 1..Len(log[j]) : log'[j][q] = log[j][q]
      /\ \A q \in (Len(log[j]) + 1)..Len(log'[j]) : log'[j][q] = m.entries[q - p]
  BY StoreLog
<1>5. PrevOk(j, m) /\ HasFirst(j, m, k - 1) BY DEF StoreEntries
<1>6. Agree(log[j], L, p + (k - 1)) BY <1>5, <1>1, CheckedPrefix
<1>7. \A q \in 1..Len(log'[j]) : log'[j][q] = L[q]
  <2> TAKE q \in 1..Len(log'[j])
  <2>1. CASE q <= Len(log[j]) BY <2>1, <1>1, <1>4, <1>6 DEF Agree
  <2>2. CASE q > Len(log[j])
    <3>1. q - p \in 1..Len(m.entries) /\ log'[j][q] = m.entries[q - p] BY <2>2, <1>1, <1>4
    <3>2. m.entries[q - p] = L[p + (q - p)] BY <3>1, <1>2
    <3> QED BY <3>1, <3>2, <1>1
  <2> QED BY <2>1, <2>2, <1>1
<1> QED BY <1>2, <1>3, <1>4, <1>7 DEF Pre, Agree

LEMMA DeleteAgree ==
  ASSUME TypeOK, ReqFromLed, LogFromLed, LedFromLed,
         NEW j \in Server, NEW m \in msgs, m \in AppendT,
         NEW k \in 1..Len(m.entries), DeleteSuffix(j, m, k)
  PROVE  /\ m.term \in DOMAIN ledLog
         /\ Pre(log'[j], ledLog[m.term])
         /\ Pre(log'[j], log[j])
<1> DEFINE p == m.prevLogIndex  L == ledLog[m.term]
<1>1. p \in Nat /\ m.entries \in Seq(EntryT) /\ log[j] \in Seq(EntryT) /\ m.type = "append"
  BY DEF TypeOK, AppendT
<1>2. m.term \in DOMAIN ledLog BY <1>1 DEF ReqFromLed
<1>3. L \in Seq(EntryT) BY <1>2 DEF TypeOK
<1>4. /\ log'[j] \in Seq(EntryT)
      /\ Len(log'[j]) = p + k - 1
      /\ p + k <= Len(log[j])
      /\ \A q \in 1..Len(log'[j]) : log'[j][q] = log[j][q]
  BY DeleteLog
<1>5. PrevOk(j, m) /\ HasFirst(j, m, k - 1) BY DEF DeleteSuffix
<1>6. Agree(log[j], L, p + (k - 1)) BY <1>5, <1>1, CheckedPrefix
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>6 DEF Pre, Agree
====
