---- MODULE EtcdActs ----
\* The steps of the protocol, as one disjunction with typed parameters.
EXTENDS EtcdBase

\* LeaderAppend(i, <<e>>), said for one entry.
LeaderAppend1(i, e) ==
    /\ role[i] = Leader
    /\ currentTerm[i] \in DOMAIN ledLog
    /\ e.term = currentTerm[i]
    /\ IsConf(e) => AllSwitched(i, ledLog[currentTerm[i]]) /\ Legal(config[i], e.value)
    /\ ledLog' = WithLed(currentTerm[i], Append(ledLog[currentTerm[i]], e))
    /\ UNCHANGED <<durable, role, lastApplied, config, confAt, confirmed, msgs, votes, leaders, ledConf, ledAt, elAt, commits, applied>>

ProtoCases ==
    \/ \E i \in Server : BecomeCandidate(i)
    \/ \E i \in Server : BecomeFollower(i)
    \/ \E i \in Server : BecomeLeader(i)
    \/ \E i \in Server : StartElection(i)
    \/ \E i \in Server : Restart(i)
    \/ \E i \in Server : Apply(i)
    \/ \E i \in Server : \E a \in 0..Len(log[i]) : Restore(i, a)
    \/ \E i \in Server : \E k \in 1..Len(log[i]) : SwitchConf(i, k)
    \/ \E i \in Server : \E c \in commits : \E a \in 0..Len(c.entries) : RestoreConf(i, c, a)
    \/ \E i \in Server : \E e \in EntryT : LeaderAppend1(i, e)
    \/ \E i \in Server : \E t \in Nat : AdoptTerm(i, t)
    \/ \E i \in Server : \E c \in Server : CastVote(i, c)
    \/ \E i \in Server : \E c \in Server : \E t \in Nat : GrantVote(i, c, t)
    \/ \E i \in Server : \E t \in Nat : \E c \in Nat : LeaderCommit(i, t, c)
    \/ \E i \in Server : \E j \in Server : \E t \in Nat : \E p \in Nat : \E n \in Nat : \E c \in Nat :
          SendAppend(i, j, t, p, n, c)
    \/ \E j \in Server : \E m \in msgs : m \in AppendT /\ Ack(j, m)
    \/ \E j \in Server : \E m \in msgs : m \in AppendT /\ AckCommitted(j, m)
    \/ \E j \in Server : \E m \in msgs : \E k \in 1..Len(m.entries) : m \in AppendT /\ DeleteSuffix(j, m, k)
    \/ \E j \in Server : \E m \in msgs : \E k \in 1..Len(m.entries) : m \in AppendT /\ StoreEntries(j, m, k)
    \/ \E j \in Server : \E m \in msgs : \E c \in Nat : m \in AppendT /\ FollowerCommit(j, m, c)

LEMMA AppendOne ==
  ASSUME TypeOK, NEW i \in Server, NEW e \in EntryT, LeaderAppend(i, <<e>>)
  PROVE  LeaderAppend1(i, e)
<1>1. Len(<<e>>) = 1 /\ <<e>>[1] = e OBVIOUS
<1>2. currentTerm[i] \in DOMAIN ledLog BY DEF LeaderAppend
<1>3. ledLog[currentTerm[i]] \in Seq(EntryT) BY <1>2 DEF TypeOK
<1>4. ledLog[currentTerm[i]] \o <<e>> = Append(ledLog[currentTerm[i]], e) BY <1>3, AppendIsConcat
<1> HIDE DEF IsConf, AllSwitched, Legal, WithLed
<1> QED BY <1>1, <1>4 DEF LeaderAppend, LeaderAppend1

LEMMA AppendMsgType ==
  ASSUME NEW m \in MsgT, m.type = "append" PROVE m \in AppendT
BY DEF MsgT, VoteReqT, GrantT, AppendT, AckT

LEMMA ProtoNextCases ==
  ASSUME TypeOK, LedDom, ProtoNext
  PROVE  ProtoCases
<1> USE DEF TypeOK
<1>1. ASSUME NEW i \in Server, NEW d \in ConfChanges(Server), LeaderAppend(i, <<Entry(currentTerm[i], "conf", d)>>)
      PROVE \E e \in EntryT : LeaderAppend1(i, e)
  <2>1. Entry(currentTerm[i], "conf", d) \in EntryT BY DEF Entry, EntryT, ETypes, Vals
  <2> QED BY <2>1, <1>1, AppendOne
<1>2. ASSUME NEW i \in Server, NEW ty \in {"noop", "config"}, LeaderAppend(i, <<Entry(currentTerm[i], ty, Nil)>>)
      PROVE \E e \in EntryT : LeaderAppend1(i, e)
  <2>1. Entry(currentTerm[i], ty, Nil) \in EntryT BY DEF Entry, EntryT, ETypes, Vals
  <2> QED BY <2>1, <1>2, AppendOne
<1>3. ASSUME NEW i \in Server, NEW v \in Values, LeaderAppend(i, <<Entry(currentTerm[i], "command", v)>>)
      PROVE \E e \in EntryT : LeaderAppend1(i, e)
  <2>1. Entry(currentTerm[i], "command", v) \in EntryT BY DEF Entry, EntryT, ETypes, Vals
  <2> QED BY <2>1, <1>3, AppendOne
<1>4. ASSUME NEW l \in leaders PROVE l.term \in Nat /\ Len(ledLog[l.term]) \in Nat
  <2>1. l.term \in DOMAIN ledLog BY DEF LedDom
  <2>2. ledLog[l.term] \in Seq(EntryT) BY <2>1
  <2> QED BY <2>2 DEF LeaderT
<1>5. ASSUME NEW i \in Server, NEW l \in leaders, NEW j \in Server,
             \E p, n, c \in 0..Len(ledLog[l.term]) : SendAppend(i, j, l.term, p, n, c)
      PROVE \E t \in Nat : \E p \in Nat : \E n \in Nat : \E c \in Nat : SendAppend(i, j, t, p, n, c)
  <2>1. l.term \in Nat /\ Len(ledLog[l.term]) \in Nat BY <1>4
  <2>2. PICK p, n, c \in 0..Len(ledLog[l.term]) : SendAppend(i, j, l.term, p, n, c) BY <1>5
  <2>3. p \in Nat /\ n \in Nat /\ c \in Nat BY <2>1
  <2> HIDE DEF TypeOK
  <2> QED BY <2>1, <2>2, <2>3
<1>6. ASSUME NEW i \in Server, NEW l \in leaders,
             \E c \in 1..Len(ledLog[l.term]) : LeaderCommit(i, l.term, c)
      PROVE \E t \in Nat : \E c \in Nat : LeaderCommit(i, t, c)
  BY <1>4, <1>6
<1>7. ASSUME NEW i \in Server, NEW v \in votes, GrantVote(i, v.cand, v.term)
      PROVE \E c \in Server : \E t \in Nat : GrantVote(i, c, t)
  BY <1>7 DEF VoteT
<1>8. ASSUME NEW i \in Server, NEW t \in {currentTerm[k] : k \in Server}, AdoptTerm(i, t)
      PROVE \E u \in Nat : AdoptTerm(i, u)
  BY <1>8
<1>9. ASSUME NEW m \in msgs, m.type = "append"
      PROVE m \in AppendT /\ m.dst \in Server /\ m.commit \in Nat
  BY <1>9, AppendMsgType DEF AppendT
<1>10. ASSUME NEW m \in msgs, m.type = "append", NEW c \in 1..m.commit, FollowerCommit(m.dst, m, c)
       PROVE \E j \in Server : \E mm \in msgs : \E cc \in Nat : mm \in AppendT /\ FollowerCommit(j, mm, cc)
  BY <1>9, <1>10
<1>11. CASE \E i \in Server :
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
          \/ \E j \in Server, l \in leaders :
                /\ l.server = i
                /\ \E p, n, c \in 0..Len(ledLog[l.term]) : SendAppend(i, j, l.term, p, n, c)
  <2> HIDE DEF TypeOK
  <2> QED BY <1>11, <1>1, <1>2, <1>3, <1>5, <1>6, <1>7, <1>8 DEF ProtoCases
<1>12. CASE \E m \in msgs :
          /\ m.type = "append"
          /\ \/ Ack(m.dst, m) \/ AckCommitted(m.dst, m)
             \/ \E k \in 1..Len(m.entries) : DeleteSuffix(m.dst, m, k) \/ StoreEntries(m.dst, m, k)
             \/ \E c \in 1..m.commit : FollowerCommit(m.dst, m, c)
  <2> HIDE DEF TypeOK
  <2> QED BY <1>12, <1>9, <1>10 DEF ProtoCases
<1> QED BY <1>11, <1>12 DEF ProtoNext

LEMMA NextCases ==
  ASSUME TypeOK, LedDom, [Next]_rvars
  PROVE  UNCHANGED vars \/ (ProtoCases /\ UNCHANGED read)
<1>1. ReadNext => UNCHANGED vars BY DEF ReadNext, ReadAck, ReadRequest, ReadConfirm
<1>2. UNCHANGED rvars => UNCHANGED vars BY DEF rvars
<1> QED BY <1>1, <1>2, ProtoNextCases DEF Next
====
