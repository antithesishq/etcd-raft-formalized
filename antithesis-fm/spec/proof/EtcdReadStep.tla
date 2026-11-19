---- MODULE EtcdReadStep ----
\* The read-index invariants RInv are inductive (given Inv, and ReadSafeP for ReadConfirm).
EXTENDS EtcdMember, EtcdReadInv

ReadCases ==
    \/ \E j \in Server : ReadAck(j)
    \/ ReadConfirm
    \/ \E i \in Server : \E c \in Nat : ReadRequest(i, c)

LEMMA NextCasesR ==
  ASSUME TypeOK, LedDom, [Next]_rvars
  PROVE  \/ UNCHANGED rvars
         \/ ProtoCases /\ UNCHANGED read
         \/ ReadCases /\ UNCHANGED vars
<1>1. ASSUME NEW i \in Server, currentTerm[i] \in DOMAIN ledLog,
             NEW c \in 0..Len(ledLog[currentTerm[i]]), ReadRequest(i, c)
      PROVE  c \in Nat
  <2>1. ledLog[currentTerm[i]] \in Seq(EntryT) BY <1>1 DEF TypeOK
  <2> QED BY <2>1
<1>2. ReadNext => ReadCases /\ UNCHANGED vars
  BY <1>1 DEF ReadNext, ReadCases, ReadAck, ReadRequest, ReadConfirm
<1> QED BY <1>2, ProtoNextCases DEF Next

LEMMA RInit == ASSUME Init PROVE RInv
BY DEF Init, NoRead, RInv, ReadMsgsOld, ReadFloorOld, ReadFloorBound, ReadIndexSafety,
       ReadTermLed, ReadFloorRooted, ReadFirstRoot, ReadRespBound

LEMMA RUnch == ASSUME RInv, UNCHANGED rvars PROVE RInv'
BY DEF rvars, vars, protoVars, durable, RInv, ReadMsgsOld, ReadFloorOld, ReadFloorBound, ReadIndexSafety,
       ReadTermLed, ReadFloorRooted, ReadFirstRoot, ReadRespBound, MRootS, AckedByS, CoverS, Good,
       AtMostOne, Pre, Agree

\* What MRootS says, after a step of the protocol (M and K fixed).
MRootS2(M, K, t, c, d) ==
    /\ t \in DOMAIN ledLog' /\ c >= 1 /\ c <= Len(ledLog'[t]) /\ ledLog'[t][c].term = t
    /\ d <= Len(ledLog'[t])
    /\ CoverS(K, ledLog'[t], d, t)
    /\ AtMostOne(ledLog'[t], d, c)
    /\ IsQuorum(AckedByS(M, t, c), ConfOf(ledLog'[t], d))

LEMMA MRootSGrow ==
  ASSUME TypeOK, Grows, NEW M, NEW K \in SUBSET CommitT, NEW t \in DOMAIN ledLog,
         NEW c \in Nat, NEW d \in Nat, MRootS(M, K, t, c, d)
  PROVE  MRootS2(M, K, t, c, d)
<1> DEFINE L == ledLog[t]  L2 == ledLog'[t]
<1>1. L \in Seq(EntryT) /\ L2 \in Seq(EntryT) /\ Pre(L, L2) /\ t \in DOMAIN ledLog'
  BY DEF TypeOK, Grows
<1>2. c >= 1 /\ c <= Len(L) /\ L[c].term = t /\ d <= Len(L) /\ CoverS(K, L, d, t) /\ AtMostOne(L, d, c)
      /\ IsQuorum(AckedByS(M, t, c), ConfOf(L, d))
  BY DEF MRootS, Good
<1>3. Len(L) <= Len(L2) /\ \A q \in 1..Len(L) : L2[q] = L[q] BY <1>1 DEF Pre, Agree
<1>4. CoverS(K, L2, d, t)
  <2>1. CASE d = 0 BY <2>1 DEF CoverS
  <2>2. CASE d # 0
    <3>1. PICK k \in K : k.term <= t /\ Agree(k.entries, L, d) BY <2>2, <1>2 DEF CoverS
    <3>2. k.entries \in Seq(EntryT) BY DEF CommitT
    <3>3. Agree(k.entries, L2, d) BY <3>1, <3>2, AgreeGrowL
    <3> QED BY <3>1, <3>3 DEF CoverS
  <2> QED BY <2>1, <2>2
<1>5. AtMostOne(L2, d, c)
  <2>1. \A q \in (d + 1)..c : L2[q] = L[q] BY <1>1, <1>2, <1>3
  <2> QED BY <2>1, <1>2 DEF AtMostOne
<1>6. ConfOf(L2, d) = ConfOf(L, d)
  <2>1. \A q \in 1..d : L2[q] = L[q] BY <1>1, <1>2, <1>3
  <2> QED BY <2>1, ConfOfCongr
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF MRootS2

LEMMA RProto ==
  ASSUME Inv, RInv, ProtoCases, UNCHANGED read
  PROVE  RInv'
<1>B. Basic /\ S1 /\ S2 /\ S3 /\ MG /\ CommitSafetyP BY InvParts
<1>G. Grows BY <1>B, GrowsStep
<1>T. TypeOK BY <1>B DEF Basic
<1>R. read \in ReadT /\ read.floor \in SUBSET CommitT /\ read' = read BY <1>T DEF TypeOK, ReadT
<1>1. ReadMsgsOld' BY <1>G DEF RInv, ReadMsgsOld, Grows
<1>2. ReadFloorOld' BY <1>G DEF RInv, ReadFloorOld, Grows
<1>3. ReadFloorBound' BY DEF RInv, ReadFloorBound
<1>4. ReadIndexSafety' BY DEF RInv, ReadIndexSafety
<1>5. ReadTermLed' BY <1>G DEF RInv, ReadTermLed, Grows
<1>6. ReadRespBound' BY DEF RInv, ReadRespBound
<1>7. ASSUME NEW r \in read.floor, r.term \in DOMAIN ledLog, Pre(r.entries, ledLog[r.term]),
             NEW d \in 0..Len(ledLog[r.term]), MRootS(read.msgs, read.floor, r.term, Len(r.entries), d)
      PROVE  /\ r.term \in DOMAIN ledLog' /\ Pre(r.entries, ledLog'[r.term])
             /\ d \in 0..Len(ledLog'[r.term]) /\ MRootS2(read.msgs, read.floor, r.term, Len(r.entries), d)
  <2>1. r.entries \in Seq(EntryT) BY <1>R DEF CommitT
  <2>2. ledLog[r.term] \in Seq(EntryT) /\ ledLog'[r.term] \in Seq(EntryT) /\ Pre(ledLog[r.term], ledLog'[r.term])
        /\ r.term \in DOMAIN ledLog'
    BY <1>7, <1>G, <1>T DEF TypeOK, Grows
  <2>3. Pre(r.entries, ledLog'[r.term]) BY <1>7, <2>1, <2>2, PreTrans
  <2>4. d \in Nat /\ d \in 0..Len(ledLog'[r.term]) BY <2>2 DEF Pre, Agree
  <2>5. MRootS2(read.msgs, read.floor, r.term, Len(r.entries), d) BY <1>7, <1>G, <1>T, <1>R, <2>1, <2>4, MRootSGrow
  <2> QED BY <2>2, <2>3, <2>4, <2>5
<1>8. ReadFloorRooted'
  <2> SUFFICES ASSUME read.on, NEW k \in read.floor
               PROVE \E r \in read.floor :
                        /\ Pre(k.entries, r.entries)
                        /\ r.term \in DOMAIN ledLog'
                        /\ Pre(r.entries, ledLog'[r.term])
                        /\ \E d \in 0..Len(ledLog'[r.term]) : MRootS2(read.msgs, read.floor, r.term, Len(r.entries), d)
    BY <1>R DEF ReadFloorRooted, MRootS, MRootS2, Good
  <2>1. PICK r \in read.floor :
            /\ Pre(k.entries, r.entries) /\ r.term \in DOMAIN ledLog /\ Pre(r.entries, ledLog[r.term])
            /\ \E d \in 0..Len(ledLog[r.term]) : MRootS(read.msgs, read.floor, r.term, Len(r.entries), d)
    BY DEF RInv, ReadFloorRooted
  <2> QED BY <2>1, <1>7
<1>9. ReadFirstRoot'
  <2> SUFFICES ASSUME read.on, NEW k \in read.floor, NEW p \in 1..Len(k.entries), IsConf(k.entries[p])
               PROVE \E r \in read.floor :
                        /\ r.term <= k.term /\ p <= Len(r.entries)
                        /\ r.term \in DOMAIN ledLog'
                        /\ Pre(r.entries, ledLog'[r.term])
                        /\ \E d \in 0..(p - 1) : MRootS2(read.msgs, read.floor, r.term, Len(r.entries), d)
    BY <1>R DEF ReadFirstRoot, MRootS, MRootS2, Good
  <2>1. PICK r \in read.floor :
            /\ r.term <= k.term /\ p <= Len(r.entries) /\ r.term \in DOMAIN ledLog /\ Pre(r.entries, ledLog[r.term])
            /\ \E d \in 0..(p - 1) : MRootS(read.msgs, read.floor, r.term, Len(r.entries), d)
    BY DEF RInv, ReadFirstRoot
  <2>2. PICK d \in 0..(p - 1) : MRootS(read.msgs, read.floor, r.term, Len(r.entries), d) BY <2>1
  <2>3. d \in 0..Len(ledLog[r.term]) BY <2>2 DEF MRootS
  <2> QED BY <2>1, <2>2, <2>3, <1>7
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>8, <1>9 DEF RInv

LEMMA RRead ==
  ASSUME Inv, RInv, ReadSafeP, ReadCases, UNCHANGED vars
  PROVE  RInv'
<1>T. TypeOK /\ read \in ReadT BY DEF Inv, TypeOK
<1>U. UNCHANGED <<msgs, commits, ledLog, currentTerm, ledConf>> BY DEF vars, protoVars, durable
<1>1. ASSUME NEW j \in Server, ReadAck(j) PROVE RInv'
  <2>1. read.on /\ currentTerm[j] <= read.term /\ read' = [read EXCEPT !.resp = @ \cup {j}]
    BY <1>1 DEF ReadAck
  <2>2. /\ read'.on = read.on /\ read'.done = read.done /\ read'.term = read.term /\ read'.index = read.index
        /\ read'.floor = read.floor /\ read'.msgs = read.msgs /\ read'.resp = read.resp \cup {j}
    BY <2>1, <1>T DEF ReadT
  <2>3. ReadRespBound'
    <3> SUFFICES ASSUME NEW n \in read.resp \cup {j}, NEW m \in read.msgs, m.type = "ack", m.src = n
                 PROVE m.term <= read.term
      BY <2>2 DEF ReadRespBound
    <3>1. CASE n \in read.resp BY <3>1, <2>1 DEF RInv, ReadRespBound
    <3>2. CASE n = j
      <4>1. m \in msgs BY <2>1 DEF RInv, ReadMsgsOld
      <4>2. m.term <= currentTerm[j] BY <4>1, <3>2 DEF Inv, AckFacts
      <4>3. m.term \in Nat BY <4>1, <1>T DEF TypeOK, MsgT, VoteReqT, GrantT, AppendT, AckT
      <4>4. currentTerm[j] \in Nat /\ read.term \in Nat BY <1>T DEF TypeOK, ReadT
      <4> QED BY <4>2, <4>3, <4>4, <2>1
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>2, <2>3, <1>U DEF RInv, ReadMsgsOld, ReadFloorOld, ReadFloorBound, ReadIndexSafety,
       ReadTermLed, ReadFloorRooted, ReadFirstRoot, MRootS, AckedByS, CoverS, Good
<1>2. ASSUME ReadConfirm PROVE RInv'
  <2>1. read.on /\ IsQuorum(read.resp, ledConf[read.term]) /\ read' = [read EXCEPT !.done = TRUE]
    BY <1>2 DEF ReadConfirm
  <2>2. /\ read'.on = read.on /\ read'.done = TRUE /\ read'.term = read.term /\ read'.index = read.index
        /\ read'.floor = read.floor /\ read'.msgs = read.msgs /\ read'.resp = read.resp
    BY <2>1, <1>T DEF ReadT
  <2>3. ReadIndexSafety' BY <2>1, <2>2 DEF ReadSafeP, ReadIndexSafety
  <2> QED BY <2>2, <2>3, <1>U DEF RInv, ReadMsgsOld, ReadFloorOld, ReadFloorBound,
       ReadTermLed, ReadFloorRooted, ReadFirstRoot, ReadRespBound, MRootS, AckedByS, CoverS, Good
<1>3. ASSUME NEW i \in Server, NEW c \in Nat, ReadRequest(i, c) PROVE RInv'
  <2> DEFINE t == currentTerm[i]
  <2>1. /\ t \in DOMAIN ledLog
        /\ \A k \in commits : k.term <= t => Len(k.entries) <= c
        /\ read' = [on |-> TRUE, done |-> FALSE, term |-> t, index |-> c,
                    floor |-> commits, msgs |-> msgs, resp |-> {}]
    BY <1>3 DEF ReadRequest
  <2>2. /\ read'.on = TRUE /\ read'.done = FALSE /\ read'.term = t /\ read'.index = c
        /\ read'.floor = commits /\ read'.msgs = msgs /\ read'.resp = {}
    BY <2>1
  <2>3. ReadMsgsOld' /\ ReadFloorOld' /\ ReadFloorBound' /\ ReadIndexSafety' /\ ReadTermLed' /\ ReadRespBound'
    BY <2>1, <2>2, <1>U DEF ReadMsgsOld, ReadFloorOld, ReadFloorBound, ReadIndexSafety, ReadTermLed, ReadRespBound
  <2>4. ReadFloorRooted'
    <3> SUFFICES ASSUME NEW k \in commits
                 PROVE \E r \in commits :
                          /\ Pre(k.entries, r.entries)
                          /\ r.term \in DOMAIN ledLog
                          /\ Pre(r.entries, ledLog[r.term])
                          /\ \E d \in 0..Len(ledLog[r.term]) : MRootS(msgs, commits, r.term, Len(r.entries), d)
      BY <2>2, <1>U DEF ReadFloorRooted, MRootS, AckedByS, CoverS, Good
    <3>1. PICK r \in commits : Pre(k.entries, r.entries) /\ Root(r) BY DEF Inv, CommitRoot
    <3>2. PICK d \in 0..Len(ledLog[r.term]) : MRoot(r.term, Len(r.entries), d) BY <3>1 DEF Root
    <3>3. MRootS(msgs, commits, r.term, Len(r.entries), d) BY <3>2 DEF MRoot, MRootS, AckedBy, AckedByS, Cover, CoverS
    <3> QED BY <3>1, <3>2, <3>3 DEF Root
  <2>5. ReadFirstRoot'
    <3> SUFFICES ASSUME NEW k \in commits, NEW p \in 1..Len(k.entries), IsConf(k.entries[p])
                 PROVE \E r \in commits :
                          /\ r.term <= k.term /\ p <= Len(r.entries)
                          /\ r.term \in DOMAIN ledLog
                          /\ Pre(r.entries, ledLog[r.term])
                          /\ \E d \in 0..(p - 1) : MRootS(msgs, commits, r.term, Len(r.entries), d)
      BY <2>2, <1>U DEF ReadFirstRoot, MRootS, AckedByS, CoverS, Good
    <3>1. PICK r \in commits :
              /\ r.term <= k.term /\ p <= Len(r.entries) /\ r.term \in DOMAIN ledLog
              /\ Pre(r.entries, ledLog[r.term])
              /\ \E d \in 0..(p - 1) : MRoot(r.term, Len(r.entries), d)
      BY DEF Inv, FirstRoot
    <3>2. PICK d \in 0..(p - 1) : MRoot(r.term, Len(r.entries), d) BY <3>1
    <3>3. MRootS(msgs, commits, r.term, Len(r.entries), d) BY <3>2 DEF MRoot, MRootS, AckedBy, AckedByS, Cover, CoverS
    <3> QED BY <3>1, <3>3
  <2> QED BY <2>3, <2>4, <2>5 DEF RInv
<1> QED BY <1>1, <1>2, <1>3 DEF ReadCases
====
