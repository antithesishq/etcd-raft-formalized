---- MODULE EtcdReadCore ----
\* What ReadConfirm needs: once a quorum of the reader's leader's configuration
\* has answered, the read index covers every prefix committed at the request.
\* From Inv and RInv in one state; argument as in EtcdRaftVeil.lean
\* (MemberCore.read_core, read_safe).
EXTENDS EtcdLC, EtcdReadInv

----
\* No node of R had acknowledged anything, in M, in a term after T.
RNone(M, R, T) ==
  \A n \in R : \A m \in M : m.type = "ack" /\ m.src = n => m.term <= T

\* FirstRoot for the messages M and the committed prefixes K.
FirstRootS(M, K) ==
  \A k \in K : \A p \in 1..Len(k.entries) : IsConf(k.entries[p]) =>
    \E r \in K :
      /\ r.term <= k.term /\ p <= Len(r.entries)
      /\ r.term \in DOMAIN ledLog
      /\ Pre(r.entries, ledLog[r.term])
      /\ \E d \in 0..(p - 1) : MRootS(M, K, r.term, Len(r.entries), d)

\* The reader: the leader of term T counts with the configuration that the
\* first e entries of its log make, and the nodes R have answered it.
Reader(M, R, T, e) ==
  /\ T \in DOMAIN ledLog /\ e \in Nat /\ e <= Len(ledLog[T])
  /\ Cover(ledLog[T], e, T)
  /\ AtMostOne(ledLog[T], e, Len(ledLog[T]))
  /\ IsQuorum(R, ConfOf(ledLog[T], e))
  /\ RNone(M, R, T)

----
\* What was acknowledged and committed then is acknowledged and committed now.
LEMMA Up ==
  ASSUME TypeOK, NEW M, M \subseteq msgs, NEW K, K \subseteq commits,
         NEW t \in DOMAIN ledLog, NEW c \in Nat, NEW d \in Nat, MRootS(M, K, t, c, d)
  PROVE  MRoot(t, c, d)
<1>1. ConstOK /\ ledLog[t] \in Seq(EntryT) BY TypeFacts
<1>2. d <= Len(ledLog[t]) BY DEF MRootS
<1>3. ConfOf(ledLog[t], d) \in ConfT BY <1>1, <1>2, ConfOfType
<1>4. AckedByS(M, t, c) \subseteq AckedBy(t, c) BY DEF AckedByS, AckedBy
<1>5. IsQuorum(AckedByS(M, t, c), ConfOf(ledLog[t], d)) BY DEF MRootS
<1>6. IsQuorum(AckedBy(t, c), ConfOf(ledLog[t], d)) BY <1>1, <1>3, <1>4, <1>5, QuorumMono
<1>7. Cover(ledLog[t], d, t) BY DEF MRootS, CoverS, Cover
<1> QED BY <1>2, <1>6, <1>7 DEF MRootS, MRoot

LEMMA NoAck ==
  ASSUME NEW M, NEW R, NEW T \in Nat, RNone(M, R, T), NEW t \in Nat, T < t, NEW c,
         NEW n \in R, n \in AckedByS(M, t, c)
  PROVE  FALSE
BY DEF RNone, AckedByS

LEMMA SameS ==
  ASSUME ConstOK, NEW M, NEW R, NEW T \in Nat, RNone(M, R, T), NEW t \in Nat, T < t, NEW c,
         NEW C \in ConfT, IsQuorum(AckedByS(M, t, c), C), IsQuorum(R, C)
  PROVE  FALSE
<1>1. PICK s \in Server : s \in AckedByS(M, t, c) /\ s \in R BY QuorumInter
<1> QED BY <1>1, NoAck

LEMMA NextS ==
  ASSUME ConstOK, NEW M, NEW R, NEW T \in Nat, RNone(M, R, T), NEW t \in Nat, T < t, NEW c,
         NEW C \in ConfT, NEW x, ChangeOK(x), Legal(C, x),
         \/ IsQuorum(AckedByS(M, t, c), C) /\ IsQuorum(R, NextConf(C, x))
         \/ IsQuorum(R, C) /\ IsQuorum(AckedByS(M, t, c), NextConf(C, x))
  PROVE  FALSE
<1>1. PICK s \in Server : s \in AckedByS(M, t, c) /\ s \in R BY QuorumInterNext
<1> QED BY <1>1, NoAck

\* A committed prefix has no entry of a term after the one it was committed in.
LEMMA CommitTerms ==
  ASSUME TypeOK, CommitRoot, LedTermsBound, NEW k \in commits
  PROVE  \A q \in 1..Len(k.entries) : k.entries[q].term <= k.term
<1>1. PICK r \in commits : Pre(k.entries, r.entries) /\ Root(r) /\ r.term <= k.term
  BY DEF CommitRoot
<1>2. r.term \in DOMAIN ledLog /\ Pre(r.entries, ledLog[r.term]) BY <1>1 DEF Root
<1>3. /\ k.entries \in Seq(EntryT) /\ r.entries \in Seq(EntryT) /\ ledLog[r.term] \in Seq(EntryT)
      /\ k.term \in Nat /\ r.term \in Nat
  BY <1>2, TypeFacts
<1> TAKE q \in 1..Len(k.entries)
<1>4. q \in 1..Len(ledLog[r.term]) /\ k.entries[q] = ledLog[r.term][q]
  BY <1>1, <1>2, <1>3 DEF Pre, Agree
<1>5. ledLog[r.term][q].term <= r.term BY <1>2, <1>4 DEF LedTermsBound
<1>6. ledLog[r.term][q].term \in Nat BY <1>3, <1>4 DEF EntryT
<1> QED BY <1>1, <1>3, <1>4, <1>5, <1>6

\* A committed prefix is in the leader log of every later term.
LEMMA CommitInLater ==
  ASSUME TypeOK, CommitRoot, LC, NEW k \in commits, NEW u \in DOMAIN ledLog, k.term < u
  PROVE  Pre(k.entries, ledLog[u])
<1>1. PICK r \in commits : Pre(k.entries, r.entries) /\ Root(r) /\ r.term <= k.term
  BY DEF CommitRoot
<1> DEFINE t0 == r.term
<1>2. t0 \in DOMAIN ledLog /\ Pre(r.entries, ledLog[t0]) BY <1>1 DEF Root
<1>3. PICK d0 \in 0..Len(ledLog[t0]) : MRoot(t0, Len(r.entries), d0) BY <1>1 DEF Root
<1>4. /\ k.entries \in Seq(EntryT) /\ r.entries \in Seq(EntryT) /\ ledLog[t0] \in Seq(EntryT)
      /\ ledLog[u] \in Seq(EntryT)
      /\ k.term \in Nat /\ t0 \in Nat /\ u \in Nat
  BY <1>2, TypeFacts
<1>5. Len(r.entries) \in 1..Len(ledLog[t0]) BY <1>3, <1>4 DEF MRoot, Good
<1>6. t0 < u BY <1>1, <1>4
<1>7. Agree(ledLog[t0], ledLog[u], Len(r.entries)) BY <1>2, <1>3, <1>5, <1>6 DEF LC
<1> HIDE DEF t0
<1> QED BY <1>1, <1>2, <1>4, <1>7 DEF Pre, Agree

\* The log of a later leader has what made the reader's configuration.
LEMMA ReaderPrefix ==
  ASSUME TypeOK, CommitRoot, LC,
         NEW T \in DOMAIN ledLog, NEW e \in Nat, e <= Len(ledLog[T]), Cover(ledLog[T], e, T),
         NEW t \in DOMAIN ledLog, T < t
  PROVE  /\ Agree(ledLog[t], ledLog[T], e)
         /\ e = 0 \/ \E k \in commits : k.term <= T /\ e <= Len(k.entries) /\ Pre(k.entries, ledLog[t])
<1>0. ledLog[t] \in Seq(EntryT) /\ ledLog[T] \in Seq(EntryT) /\ t \in Nat /\ T \in Nat BY TypeFacts
<1>1. CASE e = 0 BY <1>1, <1>0 DEF Agree
<1>2. CASE e # 0
  <2>1. PICK k \in commits : k.term <= T /\ Agree(k.entries, ledLog[T], e) BY <1>2 DEF Cover
  <2>2. k.entries \in Seq(EntryT) /\ k.term \in Nat BY TypeFacts
  <2>3. k.term < t BY <2>1, <2>2, <1>0
  <2>4. Pre(k.entries, ledLog[t]) BY <2>3, CommitInLater
  <2>5. Agree(ledLog[t], ledLog[T], e) BY <2>1, <2>2, <2>4, <1>0 DEF Pre, Agree
  <2>6. e <= Len(k.entries) BY <2>1 DEF Agree
  <2> QED BY <2>1, <2>4, <2>5, <2>6
<1> QED BY <1>1, <1>2

\* A change in a prefix committed then was first committed, then, by a
\* leader that did not count with it yet; l is a log that has the prefix.
LEMMA FirstRootUseS ==
  ASSUME TypeOK, CommitSafetyP, NEW M, NEW K, K \subseteq commits, FirstRootS(M, K),
         NEW k \in K, NEW l \in Seq(EntryT), NEW a \in Nat, Agree(k.entries, l, a),
         NEW p \in 1..a, IsConf(l[p])
  PROVE  \E t1 \in DOMAIN ledLog, c1 \in Nat, d1 \in Nat :
           /\ t1 <= k.term /\ p <= c1 /\ d1 < p /\ MRootS(M, K, t1, c1, d1)
           /\ Agree(ledLog[t1], l, p)
<1>0. k \in commits /\ k.entries \in Seq(EntryT) BY TypeFacts
<1>1. p \in 1..Len(k.entries) /\ IsConf(k.entries[p]) BY <1>0 DEF Agree
<1>2. PICK r \in K :
        /\ r.term <= k.term /\ p <= Len(r.entries)
        /\ r.term \in DOMAIN ledLog
        /\ Pre(r.entries, ledLog[r.term])
        /\ \E d \in 0..(p - 1) : MRootS(M, K, r.term, Len(r.entries), d)
  BY <1>1 DEF FirstRootS
<1>3. PICK d1 \in 0..(p - 1) : MRootS(M, K, r.term, Len(r.entries), d1) BY <1>2
<1>4. r \in commits /\ r.entries \in Seq(EntryT) /\ ledLog[r.term] \in Seq(EntryT) BY <1>2, TypeFacts
<1>5. Pre(r.entries, k.entries) \/ Pre(k.entries, r.entries) BY <1>0, <1>4 DEF CommitSafetyP
<1>6. Agree(r.entries, ledLog[r.term], Len(r.entries)) BY <1>2 DEF Pre
<1>7. Agree(ledLog[r.term], l, p)
  BY <1>0, <1>2, <1>4, <1>5, <1>6, AgreeVia
<1>8. Len(r.entries) \in Nat /\ d1 \in Nat /\ d1 < p BY <1>4
<1> QED BY <1>2, <1>3, <1>7, <1>8

LEMMA RootFactsS ==
  ASSUME TypeOK, NEW M, NEW K, NEW t \in DOMAIN ledLog, NEW c \in Nat, NEW d \in Nat,
         MRootS(M, K, t, c, d)
  PROVE  /\ Good(t, c) /\ 1 <= c /\ c <= Len(ledLog[t]) /\ d <= Len(ledLog[t])
         /\ ledLog[t] \in Seq(EntryT) /\ t \in Nat
         /\ IsQuorum(AckedByS(M, t, c), ConfOf(ledLog[t], d))
         /\ ConfOf(ledLog[t], d) \in ConfT
         /\ ledLog[t][c].term = t
<1>1. ledLog[t] \in Seq(EntryT) /\ t \in Nat /\ ConstOK BY TypeFacts
<1>2. d <= Len(ledLog[t]) BY DEF MRootS
<1>3. ConfOf(ledLog[t], d) \in ConfT BY <1>1, <1>2, ConfOfType
<1> QED BY <1>1, <1>3 DEF MRootS, Good

----
\* The later leader's configuration is the later one.
LEMMA ReadLater ==
  ASSUME TypeOK, CommitSafetyP, LegalChain, CommitRoot, LC,
         NEW M, M \subseteq msgs, NEW K, K \subseteq commits, FirstRootS(M, K),
         NEW R, NEW T, NEW e, Reader(M, R, T, e),
         NEW t \in DOMAIN ledLog, NEW c \in Nat, NEW d \in Nat, MRootS(M, K, t, c, d), T < t,
         e < d
  PROVE  FALSE
<1> DEFINE A == ledLog[t]
           AT == ledLog[T]
<1>a. /\ T \in DOMAIN ledLog /\ e \in Nat /\ e <= Len(AT) /\ Cover(AT, e, T)
      /\ IsQuorum(R, ConfOf(AT, e)) /\ RNone(M, R, T)
  BY DEF Reader
<1>b. ConstOK /\ A \in Seq(EntryT) /\ AT \in Seq(EntryT) /\ T \in Nat /\ t \in Nat
  BY <1>a, TypeFacts
<1>c. /\ 1 <= c /\ c <= Len(A) /\ d <= Len(A)
      /\ IsQuorum(AckedByS(M, t, c), ConfOf(A, d))
  BY RootFactsS
<1>d. ConfOf(AT, e) \in ConfT BY <1>a, <1>b, ConfOfType
<1>1. PICK kD \in K : kD.term <= t /\ Agree(kD.entries, A, d)
  BY <1>a DEF MRootS, CoverS
<1>2. kD \in commits /\ kD.entries \in Seq(EntryT) /\ kD.term \in Nat BY TypeFacts
<1>3. Agree(A, AT, e) BY <1>a, ReaderPrefix
<1>4. ConfOf(A, e) = ConfOf(AT, e) BY <1>3, <1>a, ConfOfCongr DEF Agree
<1>5. CASE NoC(A, e, d)
  <2>1. ConfOf(A, d) = ConfOf(A, e) BY <1>5, <1>a, ConfOfSkip DEF NoC
  <2>2. IsQuorum(AckedByS(M, t, c), ConfOf(AT, e)) BY <2>1, <1>4, <1>c
  <2> QED BY <2>2, <1>a, <1>b, <1>d, SameS
<1>6. ASSUME NEW p1 \in (e + 1)..d, IsConf(A[p1]), NoC(A, e, p1 - 1)
      PROVE  FALSE
  <2>1. Legal(ConfOf(A, p1 - 1), A[p1].value) BY <1>6, <1>a, <1>b, <1>c DEF LegalChain
  <2>2. ConfOf(A, p1 - 1) = ConfOf(A, e) BY <1>6, <1>a, ConfOfSkip DEF NoC
  <2>3. Legal(ConfOf(AT, e), A[p1].value) BY <2>1, <2>2, <1>4
  <2>4. A[p1] \in EntryT BY <1>a, <1>b, <1>c
  <2>5. ChangeOK(A[p1].value) BY <2>4, <1>6, EntryChange
  <2>6. CASE NoC(A, p1, d)
    <3>1. ConfOf(A, d) = NextConf(ConfOf(A, e), A[p1].value)
      BY <2>6, <1>6, <1>a, ConfOfOne
    <3>2. IsQuorum(AckedByS(M, t, c), NextConf(ConfOf(AT, e), A[p1].value)) BY <3>1, <1>4, <1>c
    <3> QED BY <3>2, <2>3, <2>5, <1>a, <1>b, <1>d, NextS
  <2>7. ASSUME NEW p2 \in (p1 + 1)..d, IsConf(A[p2]), NoC(A, p1, p2 - 1)
        PROVE  FALSE
    <3>1. PICK t1 \in DOMAIN ledLog, c1 \in Nat, d1 \in Nat :
             /\ t1 <= kD.term /\ p2 <= c1 /\ d1 < p2 /\ MRootS(M, K, t1, c1, d1)
             /\ Agree(ledLog[t1], A, p2)
      <4>1. p2 \in 1..d BY <1>a
      <4> QED BY <4>1, <2>7, <1>1, <1>b, FirstRootUseS
    <3> DEFINE A1 == ledLog[t1]
    <3>2. /\ A1 \in Seq(EntryT) /\ t1 \in Nat /\ c1 <= Len(A1) /\ d1 <= Len(A1)
          /\ IsQuorum(AckedByS(M, t1, c1), ConfOf(A1, d1))
      BY <3>1, RootFactsS
    <3>3. A1[p1] = A[p1] /\ A1[p2] = A[p2] BY <3>1, <1>a DEF Agree
    <3>m. MRoot(t1, c1, d1) BY <3>1, Up
    <3>4. p1 <= d1
      <4>1. IsConf(A1[p1]) /\ IsConf(A1[p2]) BY <3>3, <1>6, <2>7
      <4>2. p1 \in Nat /\ p2 \in Nat /\ p1 < p2 /\ p2 <= c1 BY <3>1, <1>a
      <4> QED BY <4>1, <4>2, <3>m, TwoConf
    <3>5. CASE T < t1
      <4>1. ConfOf(A1, d1) = ConfOf(A, d1) BY <3>1, <1>a, ConfOfCongr DEF Agree
      <4>2. ConfOf(A, d1) = NextConf(ConfOf(A, e), A[p1].value)
        <5>1. NoC(A, p1, d1) BY <2>7, <3>1, <1>a DEF NoC
        <5> QED BY <5>1, <3>4, <1>6, <1>a, ConfOfOne
      <4>3. IsQuorum(AckedByS(M, t1, c1), NextConf(ConfOf(AT, e), A[p1].value))
        BY <3>2, <4>1, <4>2, <1>4
      <4> QED BY <4>3, <3>5, <3>2, <2>3, <2>5, <1>a, <1>b, <1>d, NextS
    <3>6. CASE t1 <= T
      <4>1. Agree(A1, AT, c1)
        <5>1. CASE t1 = T BY <5>1, <3>2 DEF Agree
        <5>2. CASE t1 < T
          <6>1. c1 \in 1..Len(A1) /\ d1 \in 0..Len(A1) BY <3>2, <3>1, <1>a
          <6> QED BY <6>1, <5>2, <3>m, <1>a DEF LC
        <5> QED BY <5>1, <5>2, <3>6, <3>2, <1>b
      <4>2. AT[p1] = A1[p1] /\ AT[p2] = A1[p2] /\ p2 <= Len(AT)
        BY <4>1, <3>1, <3>2, <1>a, <1>b DEF Agree
      <4>3. /\ p1 \in (e + 1)..Len(AT) /\ p2 \in (e + 1)..Len(AT) /\ p1 < p2
            /\ IsConf(AT[p1]) /\ IsConf(AT[p2])
        BY <4>2, <3>3, <1>6, <2>7, <1>a, <1>b
      <4>4. AtMostOne(AT, e, Len(AT)) BY DEF Reader
      <4> QED BY <4>3, <4>4 DEF AtMostOne
    <3> QED BY <3>5, <3>6, <3>2, <1>b
  <2>8. NoC(A, p1, d) \/ \E p \in (p1 + 1)..d : IsConf(A[p]) /\ NoC(A, p1, p - 1)
    BY <1>a, FirstChange
  <2> QED BY <2>6, <2>7, <2>8
<1>7. NoC(A, e, d) \/ \E p \in (e + 1)..d : IsConf(A[p]) /\ NoC(A, e, p - 1)
  BY <1>a, FirstChange
<1> QED BY <1>5, <1>6, <1>7

\* The reader's configuration is the later one, or they are the same.
LEMMA ReadEarlier ==
  ASSUME TypeOK, LegalChain, CommitRoot, LedTermsBound, LC,
         NEW M, NEW K, NEW R, NEW T, NEW e, Reader(M, R, T, e),
         NEW t \in DOMAIN ledLog, NEW c \in Nat, NEW d \in Nat, MRootS(M, K, t, c, d), T < t,
         d <= e
  PROVE  FALSE
<1> DEFINE A == ledLog[t]
           AT == ledLog[T]
<1>a. /\ T \in DOMAIN ledLog /\ e \in Nat /\ e <= Len(AT) /\ Cover(AT, e, T)
      /\ IsQuorum(R, ConfOf(AT, e)) /\ RNone(M, R, T)
  BY DEF Reader
<1>b. ConstOK /\ A \in Seq(EntryT) /\ AT \in Seq(EntryT) /\ T \in Nat /\ t \in Nat
  BY <1>a, TypeFacts
<1>c. /\ 1 <= c /\ c <= Len(A) /\ d <= Len(A)
      /\ IsQuorum(AckedByS(M, t, c), ConfOf(A, d))
      /\ ConfOf(A, d) \in ConfT
      /\ A[c].term = t
  BY RootFactsS
<1>3. /\ Agree(A, AT, e)
      /\ e = 0 \/ \E k \in commits : k.term <= T /\ e <= Len(k.entries) /\ Pre(k.entries, A)
  BY <1>a, ReaderPrefix
<1>4. ConfOf(A, e) = ConfOf(AT, e) BY <1>3, <1>a, ConfOfCongr DEF Agree
<1>e. IsQuorum(R, ConfOf(A, e)) BY <1>4, <1>a
<1>5. CASE NoC(A, d, e)
  <2>1. ConfOf(A, e) = ConfOf(A, d) BY <1>5, <1>a, ConfOfSkip DEF NoC
  <2>2. IsQuorum(R, ConfOf(A, d)) BY <2>1, <1>e
  <2> QED BY <2>2, <1>a, <1>b, <1>c, SameS
<1>6. ASSUME NEW p1 \in (d + 1)..e, IsConf(A[p1]), NoC(A, d, p1 - 1)
      PROVE  FALSE
  <2>0. e <= Len(A) BY <1>3 DEF Agree
  <2>6. CASE NoC(A, p1, e)
    <3>1. Legal(ConfOf(A, p1 - 1), A[p1].value) BY <1>6, <1>a, <1>b, <2>0 DEF LegalChain
    <3>2. ConfOf(A, p1 - 1) = ConfOf(A, d) BY <1>6, <1>a, ConfOfSkip DEF NoC
    <3>3. Legal(ConfOf(A, d), A[p1].value) BY <3>1, <3>2
    <3>4. A[p1] \in EntryT BY <1>a, <1>b, <2>0
    <3>5. ChangeOK(A[p1].value) BY <3>4, <1>6, EntryChange
    <3>6. ConfOf(A, e) = NextConf(ConfOf(A, d), A[p1].value)
      BY <2>6, <1>6, <1>a, ConfOfOne
    <3>7. IsQuorum(R, NextConf(ConfOf(A, d), A[p1].value)) BY <3>6, <1>e
    <3> QED BY <3>7, <3>3, <3>5, <1>a, <1>b, <1>c, NextS
  <2>7. ASSUME NEW p2 \in (p1 + 1)..e, IsConf(A[p2]), NoC(A, p1, p2 - 1)
        PROVE  FALSE
    <3>1. c < p2
      <4>1. ASSUME p2 <= c PROVE FALSE
        <5>1. p1 \in (d + 1)..c /\ p2 \in (d + 1)..c /\ p1 < p2 BY <4>1, <1>a
        <5>2. AtMostOne(A, d, c) BY DEF MRootS
        <5> QED BY <5>1, <5>2, <1>6, <2>7 DEF AtMostOne
      <4> QED BY <4>1, <1>a
    <3>2. PICK k \in commits : k.term <= T /\ e <= Len(k.entries) /\ Pre(k.entries, A)
      BY <1>3, <1>a
    <3>3. k.entries \in Seq(EntryT) /\ k.term \in Nat BY TypeFacts
    <3>4. c \in 1..Len(k.entries) BY <3>1, <3>2, <3>3, <1>a, <1>c
    <3>5. k.entries[c] = A[c] BY <3>2, <3>4 DEF Pre, Agree
    <3>6. k.entries[c].term <= k.term BY <3>4, CommitTerms
    <3> QED BY <3>5, <3>6, <3>2, <3>3, <1>c, <1>b
  <2>8. NoC(A, p1, e) \/ \E p \in (p1 + 1)..e : IsConf(A[p]) /\ NoC(A, p1, p - 1)
    BY <1>a, FirstChange
  <2> QED BY <2>6, <2>7, <2>8
<1>7. NoC(A, d, e) \/ \E p \in (d + 1)..e : IsConf(A[p]) /\ NoC(A, d, p - 1)
  BY <1>a, FirstChange
<1> QED BY <1>5, <1>6, <1>7

\* A leader that had, then, a quorum of acknowledgements for a prefix it
\* might commit is of the reader's term or of an earlier one.
LEMMA ReadCore ==
  ASSUME TypeOK, CommitSafetyP, LegalChain, CommitRoot, LedTermsBound, LC,
         NEW M, M \subseteq msgs, NEW K, K \subseteq commits, FirstRootS(M, K),
         NEW R, NEW T, NEW e, Reader(M, R, T, e),
         NEW t \in DOMAIN ledLog, NEW c \in Nat, NEW d \in Nat, MRootS(M, K, t, c, d)
  PROVE  t <= T
<1>0. T \in Nat /\ t \in Nat /\ e \in Nat BY TypeFacts DEF Reader
<1>1. ASSUME T < t PROVE FALSE
  <2>1. CASE e < d BY <1>1, <2>1, ReadLater
  <2>2. CASE d <= e BY <1>1, <2>2, ReadEarlier
  <2> QED BY <2>1, <2>2, <1>0
<1> QED BY <1>0, <1>1

----
THEOREM ReadSafe == ASSUME Inv, RInv PROVE ReadSafeP
<1>1. /\ TypeOK /\ CommitSafetyP /\ LegalChain /\ CommitRoot /\ LedTermsBound /\ LeaderConfS
  BY DEF Inv
<1>2. LC BY LCThm
<1> DEFINE T == read.term
           M == read.msgs
           K == read.floor
           R == read.resp
           e == ledAt[T]
<1> SUFFICES ASSUME read.on, IsQuorum(R, ledConf[T]), NEW k \in K
             PROVE  Len(k.entries) <= read.index
  BY DEF ReadSafeP
<1>3. /\ M \subseteq msgs /\ K \subseteq commits /\ T \in DOMAIN ledLog
  BY DEF RInv, ReadMsgsOld, ReadFloorOld, ReadTermLed
<1>4. FirstRootS(M, K) BY DEF RInv, ReadFirstRoot, FirstRootS
<1>5. RNone(M, R, T) BY DEF RInv, ReadRespBound, RNone
<1>6. /\ e <= Len(ledLog[T])
      /\ ledConf[T] = ConfOf(ledLog[T], e)
      /\ AtMostOne(ledLog[T], e, Len(ledLog[T]))
      /\ Cover(ledLog[T], e, T)
  BY <1>1, <1>3 DEF LeaderConfS
<1>7. e \in Nat BY <1>1, <1>3 DEF TypeOK
<1>8. Reader(M, R, T, e) BY <1>3, <1>5, <1>6, <1>7 DEF Reader
<1>9. PICK r \in K :
        /\ Pre(k.entries, r.entries)
        /\ r.term \in DOMAIN ledLog
        /\ \E d \in 0..Len(ledLog[r.term]) : MRootS(M, K, r.term, Len(r.entries), d)
  BY DEF RInv, ReadFloorRooted
<1>10. PICK d \in 0..Len(ledLog[r.term]) : MRootS(M, K, r.term, Len(r.entries), d) BY <1>9
<1>11. /\ k \in commits /\ r \in commits /\ k.entries \in Seq(EntryT) /\ r.entries \in Seq(EntryT)
       /\ ledLog[r.term] \in Seq(EntryT)
  BY <1>1, <1>3, <1>9, TypeFacts
<1>12. Len(r.entries) \in Nat /\ d \in Nat BY <1>11
<1> HIDE DEF T, M, K, R, e
<1>13. r.term <= T BY <1>1, <1>2, <1>3, <1>4, <1>8, <1>9, <1>10, <1>12, ReadCore
<1>14. Len(r.entries) <= read.index
  <2>1. ReadFloorBound /\ read.on BY DEF RInv
  <2> QED BY <2>1, <1>13 DEF ReadFloorBound, T, K
<1>15. Len(k.entries) <= Len(r.entries) BY <1>9 DEF Pre, Agree
<1>16. read.index \in Nat BY <1>1 DEF TypeOK, ReadT
<1> QED BY <1>11, <1>12, <1>14, <1>15, <1>16
====
