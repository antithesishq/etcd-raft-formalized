---- MODULE EtcdLC ----
\* LC of EtcdInv.tla (leader completeness for what a leader may commit) from
\* Inv in one state; argument as in EtcdRaftVeil.lean (MemberCore.core,
\* leader_complete).
EXTENDS EtcdBase

----
\* Sequences and configurations.

\* No change of membership at the positions in (a, b].
NoC(l, a, b) == \A p \in (a + 1)..b : ~IsConf(l[p])

LEMMA FirstChange ==
  ASSUME NEW l, NEW a \in Nat, NEW b \in Nat
  PROVE  NoC(l, a, b) \/ \E p \in (a + 1)..b : IsConf(l[p]) /\ NoC(l, a, p - 1)
<1> DEFINE P(n) == NoC(l, a, n) \/ \E p \in (a + 1)..n : IsConf(l[p]) /\ NoC(l, a, p - 1)
<1>1. P(0) BY DEF NoC
<1>2. ASSUME NEW n \in Nat, P(n) PROVE P(n + 1)
  <2>1. CASE \E p \in (a + 1)..n : IsConf(l[p]) /\ NoC(l, a, p - 1)
    BY <2>1
  <2>2. CASE NoC(l, a, n) /\ ~(a < n + 1 /\ IsConf(l[n + 1]))
    <3>1. NoC(l, a, n + 1) BY <2>2 DEF NoC
    <3> QED BY <3>1
  <2>3. CASE NoC(l, a, n) /\ a < n + 1 /\ IsConf(l[n + 1])
    <3>1. n + 1 \in (a + 1)..(n + 1) /\ NoC(l, a, (n + 1) - 1) BY <2>3
    <3> QED BY <3>1, <2>3
  <2> QED BY <1>2, <2>1, <2>2, <2>3
<1> HIDE DEF P
<1>3. \A n \in Nat : P(n) BY <1>1, <1>2, NatInduction
<1> QED BY <1>3 DEF P

\* The configuration at d when the only change in (a, d] is the one at p.
LEMMA ConfOfOne ==
  ASSUME NEW l, NEW a \in Nat, NEW p \in Nat, NEW d \in Nat, a < p, p <= d,
         NoC(l, a, p - 1), IsConf(l[p]), NoC(l, p, d)
  PROVE  ConfOf(l, d) = NextConf(ConfOf(l, a), l[p].value)
<1>1. ConfOf(l, d) = ConfOf(l, p) BY ConfOfSkip DEF NoC
<1>2. ConfOf(l, p) = NextConf(ConfOf(l, p - 1), l[p].value) BY ConfOfStep
<1>3. ConfOf(l, p - 1) = ConfOf(l, a) BY ConfOfSkip DEF NoC
<1> QED BY <1>1, <1>2, <1>3

\* Two sequences whose first d and first e entries are those of comparable
\* sequences agree on their first m entries, for m up to d and e.
LEMMA AgreeVia ==
  ASSUME NEW S, NEW A \in Seq(S), NEW B \in Seq(S), NEW kD \in Seq(S), NEW kE \in Seq(S),
         NEW d \in Nat, NEW e \in Nat, NEW m \in Nat,
         Agree(kD, A, d), Agree(kE, B, e), Pre(kD, kE) \/ Pre(kE, kD), m <= d, m <= e
  PROVE  Agree(A, B, m)
BY DEF Agree, Pre

LEMMA AgreeTrans ==
  ASSUME NEW S, NEW A \in Seq(S), NEW B \in Seq(S), NEW C \in Seq(S),
         NEW j \in Nat, NEW k \in Nat, NEW m \in Nat,
         Agree(A, B, j), Agree(B, C, k), m <= j, m <= k
  PROVE  Agree(A, C, m) /\ Agree(C, A, m)
BY DEF Agree

----
\* The state.

LEMMA TypeFacts ==
  ASSUME TypeOK
  PROVE  /\ ConstOK
         /\ DOMAIN ledLog \subseteq Nat
         /\ \A t \in DOMAIN ledLog : ledLog[t] \in Seq(EntryT) /\ elAt[t] \in Nat
         /\ \A k \in commits : k.entries \in Seq(EntryT) /\ k.term \in Nat
BY DEF TypeOK, CommitT

\* Leader completeness for the terms before u.
Before(u) ==
  \A w \in DOMAIN ledLog : w < u =>
    \A t \in DOMAIN ledLog : \A c \in Nat, d \in Nat :
      MRoot(t, c, d) /\ t < w => Agree(ledLog[t], ledLog[w], c)

\* A voter in V that had acknowledged entries in an earlier term: the leader
\* log of u has them, or a leader log in between does not.
TEarly(u, V) ==
  \A n \in V : \A t \in DOMAIN ledLog : \A c \in Nat :
    Good(t, c) /\ n \in AckedBy(t, c) /\ t < u =>
      Agree(ledLog[t], ledLog[u], c) \/ LostIn(t, c, t, u - 1)

\* What Core asks of the leader log of term u, elected by the nodes V.
Tgt(u, V) ==
  /\ u \in DOMAIN ledLog
  /\ elAt[u] <= Len(ledLog[u])
  /\ CoverLt(ledLog[u], elAt[u], u)
  /\ IsQuorum(V, ConfOf(ledLog[u], elAt[u]))
  /\ TEarly(u, V)
  /\ Before(u)

LEMMA RootFacts ==
  ASSUME TypeOK, NEW t \in DOMAIN ledLog, NEW c \in Nat, NEW d \in Nat, MRoot(t, c, d)
  PROVE  /\ Good(t, c) /\ 1 <= c /\ c <= Len(ledLog[t]) /\ d <= Len(ledLog[t])
         /\ ledLog[t] \in Seq(EntryT) /\ t \in Nat
         /\ IsQuorum(AckedBy(t, c), ConfOf(ledLog[t], d))
         /\ ConfOf(ledLog[t], d) \in ConfT
<1>1. ledLog[t] \in Seq(EntryT) /\ t \in Nat /\ ConstOK BY TypeFacts
<1>2. d <= Len(ledLog[t]) BY DEF MRoot
<1>3. ConfOf(ledLog[t], d) \in ConfT BY <1>1, <1>2, ConfOfType
<1> QED BY <1>1, <1>3 DEF MRoot, Good

\* A voter of the election had acknowledged the entries.
LEMMA Near ==
  ASSUME TypeOK, NEW u \in DOMAIN ledLog, NEW V, TEarly(u, V), Before(u),
         NEW t \in DOMAIN ledLog, NEW c \in Nat, NEW d \in Nat, MRoot(t, c, d), t < u,
         NEW n \in V, n \in AckedBy(t, c)
  PROVE  Agree(ledLog[t], ledLog[u], c)
<1>1. Good(t, c) BY DEF MRoot
<1>2. Agree(ledLog[t], ledLog[u], c) \/ LostIn(t, c, t, u - 1) BY <1>1 DEF TEarly
<1>3. ASSUME LostIn(t, c, t, u - 1) PROVE FALSE
  <2>1. PICK w \in DOMAIN ledLog : t < w /\ w <= u - 1 /\ ~Agree(ledLog[t], ledLog[w], c)
    BY <1>3 DEF LostIn
  <2>2. w \in Nat /\ u \in Nat BY TypeFacts
  <2>3. w < u BY <2>1, <2>2
  <2> QED BY <2>1, <2>3 DEF Before
<1> QED BY <1>2, <1>3

\* A root and the electors share a node when a quorum of the root's
\* configuration and one of the electors' do.
LEMMA NearSame ==
  ASSUME TypeOK, NEW u \in DOMAIN ledLog, NEW V, TEarly(u, V), Before(u),
         NEW t \in DOMAIN ledLog, NEW c \in Nat, NEW d \in Nat, MRoot(t, c, d), t < u,
         NEW C \in ConfT, IsQuorum(AckedBy(t, c), C), IsQuorum(V, C)
  PROVE  Agree(ledLog[t], ledLog[u], c)
<1>1. ConstOK BY TypeFacts
<1>2. PICK s \in Server : s \in AckedBy(t, c) /\ s \in V BY <1>1, QuorumInter
<1> QED BY <1>2, Near

LEMMA NearNext ==
  ASSUME TypeOK, NEW u \in DOMAIN ledLog, NEW V, TEarly(u, V), Before(u),
         NEW t \in DOMAIN ledLog, NEW c \in Nat, NEW d \in Nat, MRoot(t, c, d), t < u,
         NEW C \in ConfT, NEW x, ChangeOK(x), Legal(C, x),
         \/ IsQuorum(AckedBy(t, c), C) /\ IsQuorum(V, NextConf(C, x))
         \/ IsQuorum(V, C) /\ IsQuorum(AckedBy(t, c), NextConf(C, x))
  PROVE  Agree(ledLog[t], ledLog[u], c)
<1>1. ConstOK BY TypeFacts
<1>2. PICK s \in Server : s \in AckedBy(t, c) /\ s \in V BY <1>1, QuorumInterNext
<1> QED BY <1>2, Near

\* A change in a committed prefix was first committed by a leader that did
\* not count with it yet; l is a log that has the prefix.
LEMMA FirstRootUse ==
  ASSUME TypeOK, CommitSafetyP, FirstRoot,
         NEW k \in commits, NEW l \in Seq(EntryT), NEW a \in Nat, Agree(k.entries, l, a),
         NEW p \in 1..a, IsConf(l[p])
  PROVE  \E t1 \in DOMAIN ledLog, c1 \in Nat, d1 \in Nat :
           /\ t1 <= k.term /\ p <= c1 /\ d1 < p /\ MRoot(t1, c1, d1)
           /\ Agree(ledLog[t1], l, p)
<1>0. k.entries \in Seq(EntryT) BY TypeFacts
<1>1. p \in 1..Len(k.entries) /\ IsConf(k.entries[p]) BY <1>0 DEF Agree
<1>2. PICK r \in commits :
        /\ r.term <= k.term /\ p <= Len(r.entries)
        /\ r.term \in DOMAIN ledLog
        /\ Pre(r.entries, ledLog[r.term])
        /\ \E d \in 0..(p - 1) : MRoot(r.term, Len(r.entries), d)
  BY <1>1 DEF FirstRoot
<1>3. PICK d1 \in 0..(p - 1) : MRoot(r.term, Len(r.entries), d1) BY <1>2
<1>4. r.entries \in Seq(EntryT) /\ ledLog[r.term] \in Seq(EntryT) BY <1>2, TypeFacts
<1>5. Pre(r.entries, k.entries) \/ Pre(k.entries, r.entries) BY DEF CommitSafetyP
<1>6. Agree(r.entries, ledLog[r.term], Len(r.entries)) BY <1>2 DEF Pre
<1>7. Agree(ledLog[r.term], l, p)
  BY <1>0, <1>2, <1>4, <1>5, <1>6, AgreeVia
<1>8. Len(r.entries) \in Nat /\ d1 \in Nat /\ d1 < p BY <1>4
<1> QED BY <1>2, <1>3, <1>7, <1>8

\* Two changes within what a root's leader may commit: the leader counts
\* with the first.
LEMMA TwoConf ==
  ASSUME NEW t, NEW c \in Nat, NEW d \in Nat, MRoot(t, c, d),
         NEW p \in Nat, NEW q \in Nat, p < q, q <= c,
         IsConf(ledLog[t][p]), IsConf(ledLog[t][q])
  PROVE  p <= d
BY DEF MRoot, AtMostOne

----
\* The committing leader's configuration is the later one.
LEMMA Later ==
  ASSUME TypeOK, CommitSafetyP, FirstRoot, LegalChain, LedTermsBound, LedOld,
         NEW u, NEW V, Tgt(u, V),
         NEW t \in DOMAIN ledLog, NEW c \in Nat, NEW d \in Nat, MRoot(t, c, d), t < u,
         elAt[u] < d
  PROVE  Agree(ledLog[t], ledLog[u], c)
<1> DEFINE A == ledLog[t]
           B == ledLog[u]
           e == elAt[u]
<1>a. u \in DOMAIN ledLog /\ TEarly(u, V) /\ Before(u) /\ e <= Len(B)
      /\ IsQuorum(V, ConfOf(B, e)) BY DEF Tgt
<1>b. ConstOK /\ A \in Seq(EntryT) /\ B \in Seq(EntryT) /\ e \in Nat /\ u \in Nat /\ t \in Nat
  BY <1>a, TypeFacts
<1>c. /\ 1 <= c /\ c <= Len(A) /\ d <= Len(A)
      /\ IsQuorum(AckedBy(t, c), ConfOf(A, d))
  BY RootFacts
<1>d. ConfOf(B, e) \in ConfT BY <1>a, <1>b, ConfOfType
<1>1. PICK kD \in commits : kD.term <= t /\ Agree(kD.entries, A, d)
  BY <1>b DEF MRoot, Cover
<1>2. kD.entries \in Seq(EntryT) /\ kD.term \in Nat BY TypeFacts
<1>3. Agree(A, B, e)
  <2>1. CASE e = 0 BY <2>1, <1>b DEF Agree
  <2>2. CASE e # 0
    <3>1. PICK kE \in commits : kE.term < u /\ Agree(kE.entries, B, e)
      BY <2>2 DEF Tgt, CoverLt
    <3>2. kE.entries \in Seq(EntryT) BY TypeFacts
    <3>3. Pre(kD.entries, kE.entries) \/ Pre(kE.entries, kD.entries) BY DEF CommitSafetyP
    <3> QED BY <1>1, <1>2, <1>b, <3>1, <3>2, <3>3, AgreeVia
  <2> QED BY <2>1, <2>2
<1>4. ConfOf(A, e) = ConfOf(B, e) BY <1>3, <1>b, ConfOfCongr DEF Agree
<1>5. CASE NoC(A, e, d)
  <2>1. ConfOf(A, d) = ConfOf(A, e) BY <1>5, <1>b, ConfOfSkip DEF NoC
  <2> QED BY <2>1, <1>4, <1>a, <1>c, <1>d, NearSame
<1>6. ASSUME NEW p1 \in (e + 1)..d, IsConf(A[p1]), NoC(A, e, p1 - 1)
      PROVE  Agree(A, B, c)
  <2>1. Legal(ConfOf(A, p1 - 1), A[p1].value) BY <1>6, <1>b, <1>c DEF LegalChain
  <2>2. ConfOf(A, p1 - 1) = ConfOf(A, e) BY <1>6, <1>b, ConfOfSkip DEF NoC
  <2>3. Legal(ConfOf(B, e), A[p1].value) BY <2>1, <2>2, <1>4
  <2>4. A[p1] \in EntryT BY <1>b, <1>c
  <2>5. ChangeOK(A[p1].value) BY <2>4, <1>6, EntryChange
  <2>6. CASE NoC(A, p1, d)
    <3>1. ConfOf(A, d) = NextConf(ConfOf(A, e), A[p1].value)
      BY <2>6, <1>6, <1>b, ConfOfOne
    <3>2. IsQuorum(AckedBy(t, c), NextConf(ConfOf(B, e), A[p1].value)) BY <3>1, <1>4, <1>c
    <3> QED BY <3>2, <2>3, <2>5, <1>a, <1>d, NearNext
  <2>7. ASSUME NEW p2 \in (p1 + 1)..d, IsConf(A[p2]), NoC(A, p1, p2 - 1)
        PROVE  FALSE
    <3>1. PICK t1 \in DOMAIN ledLog, c1 \in Nat, d1 \in Nat :
             /\ t1 <= kD.term /\ p2 <= c1 /\ d1 < p2 /\ MRoot(t1, c1, d1)
             /\ Agree(ledLog[t1], A, p2)
      <4>1. p2 \in 1..d BY <1>b
      <4> QED BY <4>1, <2>7, <1>1, <1>b, FirstRootUse
    <3> DEFINE A1 == ledLog[t1]
    <3>2. A1 \in Seq(EntryT) /\ t1 \in Nat /\ t1 < u /\ c1 <= Len(A1)
      BY <3>1, <1>1, <1>2, <1>b, RootFacts
    <3>3. A1[p1] = A[p1] /\ A1[p2] = A[p2] BY <3>1, <1>b DEF Agree
    <3>4. p1 <= d1
      <4>1. IsConf(A1[p1]) /\ IsConf(A1[p2]) BY <3>3, <1>6, <2>7
      <4>2. p1 \in Nat /\ p2 \in Nat /\ p1 < p2 /\ p2 <= c1 BY <3>1, <1>b
      <4> QED BY <4>1, <4>2, <3>1, TwoConf
    <3>5. ConfOf(A1, d1) = ConfOf(A, d1) BY <3>1, <1>b, ConfOfCongr DEF Agree
    <3>6. ConfOf(A, d1) = NextConf(ConfOf(A, e), A[p1].value)
      <4>1. NoC(A, p1, d1) BY <2>7, <3>1, <1>b DEF NoC
      <4> QED BY <4>1, <3>4, <1>6, <1>b, ConfOfOne
    <3>7. IsQuorum(AckedBy(t1, c1), NextConf(ConfOf(B, e), A[p1].value))
      BY <3>1, <3>5, <3>6, <1>4, RootFacts
    <3>8. Agree(A1, B, c1) BY <3>7, <3>1, <3>2, <2>3, <2>5, <1>a, <1>d, NearNext
    <3>9. B[p1] = A1[p1] /\ B[p2] = A1[p2] /\ p2 <= Len(B) /\ p2 <= Len(A1)
      BY <3>8, <3>1, <3>2, <1>b DEF Agree
    <3>10. A1[p1].term <= t1 /\ A1[p2].term <= t1
      <4>1. p1 \in 1..Len(A1) /\ p2 \in 1..Len(A1) BY <3>9, <3>2, <1>b
      <4>2. \A q \in 1..Len(A1) : A1[q].term <= t1 BY DEF LedTermsBound
      <4> QED BY <4>1, <4>2
    <3>11. A1[p1].term \in Nat /\ A1[p2].term \in Nat BY <3>2, <3>9, <1>b DEF EntryT
    <3>12. /\ p1 \in (e + 1)..Len(B) /\ p2 \in (e + 1)..Len(B) /\ p1 < p2
           /\ IsConf(B[p1]) /\ IsConf(B[p2])
           /\ B[p1].term < u /\ B[p2].term < u
      BY <3>9, <3>10, <3>11, <3>2, <3>3, <1>6, <2>7, <1>b
    <3> QED BY <3>12, <1>a DEF LedOld
  <2>8. NoC(A, p1, d) \/ \E p \in (p1 + 1)..d : IsConf(A[p]) /\ NoC(A, p1, p - 1)
    BY <1>b, FirstChange
  <2> QED BY <2>6, <2>7, <2>8
<1>7. NoC(A, e, d) \/ \E p \in (e + 1)..d : IsConf(A[p]) /\ NoC(A, e, p - 1)
  BY <1>b, FirstChange
<1> QED BY <1>5, <1>6, <1>7

\* The elected node's configuration is the later one, or they are the same:
\* one step of the induction on elAt[u] - d.
LEMMA EarlierStep ==
  ASSUME TypeOK, CommitSafetyP, FirstRoot, LegalChain,
         NEW u, NEW V, Tgt(u, V),
         NEW t \in DOMAIN ledLog, NEW c \in Nat, NEW d \in Nat, MRoot(t, c, d), t < u,
         d <= elAt[u],
         \A t2 \in DOMAIN ledLog : \A c2 \in Nat, d2 \in Nat :
            MRoot(t2, c2, d2) /\ t2 < u /\ d < d2 /\ d2 <= elAt[u]
              => Agree(ledLog[t2], ledLog[u], c2)
  PROVE  Agree(ledLog[t], ledLog[u], c)
<1> DEFINE A == ledLog[t]
           B == ledLog[u]
           e == elAt[u]
<1>a. u \in DOMAIN ledLog /\ TEarly(u, V) /\ Before(u) /\ e <= Len(B)
      /\ IsQuorum(V, ConfOf(B, e)) BY DEF Tgt
<1>b. ConstOK /\ A \in Seq(EntryT) /\ B \in Seq(EntryT) /\ e \in Nat /\ u \in Nat /\ t \in Nat
  BY <1>a, TypeFacts
<1>c. /\ 1 <= c /\ c <= Len(A) /\ d <= Len(A)
      /\ IsQuorum(AckedBy(t, c), ConfOf(A, d))
      /\ ConfOf(A, d) \in ConfT
  BY RootFacts
<1>1. Agree(A, B, d)
  <2>1. CASE d = 0 BY <2>1, <1>b DEF Agree
  <2>2. CASE d # 0
    <3>1. PICK kD \in commits : kD.term <= t /\ Agree(kD.entries, A, d)
      BY <2>2 DEF MRoot, Cover
    <3>2. PICK kE \in commits : kE.term < u /\ Agree(kE.entries, B, e)
      BY <2>2, <1>b DEF Tgt, CoverLt
    <3>3. kD.entries \in Seq(EntryT) /\ kE.entries \in Seq(EntryT) BY TypeFacts
    <3>4. Pre(kD.entries, kE.entries) \/ Pre(kE.entries, kD.entries) BY DEF CommitSafetyP
    <3> QED BY <1>b, <3>1, <3>2, <3>3, <3>4, AgreeVia
  <2> QED BY <2>1, <2>2
<1>2. ConfOf(A, d) = ConfOf(B, d) BY <1>1, ConfOfCongr DEF Agree
<1>3. CASE NoC(B, d, e)
  <2>1. ConfOf(B, e) = ConfOf(B, d) BY <1>3, <1>b, ConfOfSkip DEF NoC
  <2> QED BY <2>1, <1>2, <1>a, <1>c, NearSame
<1>4. ASSUME NEW p1 \in (d + 1)..e, IsConf(B[p1]), NoC(B, d, p1 - 1)
      PROVE  Agree(A, B, c)
  <2>6. CASE NoC(B, p1, e)
    <3>1. Legal(ConfOf(B, p1 - 1), B[p1].value) BY <1>4, <1>a, <1>b DEF LegalChain
    <3>2. ConfOf(B, p1 - 1) = ConfOf(B, d) BY <1>4, <1>b, ConfOfSkip DEF NoC
    <3>3. Legal(ConfOf(A, d), B[p1].value) BY <3>1, <3>2, <1>2
    <3>4. B[p1] \in EntryT BY <1>a, <1>b
    <3>5. ChangeOK(B[p1].value) BY <3>4, <1>4, EntryChange
    <3>6. ConfOf(B, e) = NextConf(ConfOf(B, d), B[p1].value)
      BY <2>6, <1>4, <1>b, ConfOfOne
    <3>7. IsQuorum(V, NextConf(ConfOf(A, d), B[p1].value)) BY <3>6, <1>2, <1>a
    <3> QED BY <3>7, <3>3, <3>5, <1>a, <1>c, NearNext
  <2>7. ASSUME NEW p2 \in (p1 + 1)..e, IsConf(B[p2]), NoC(B, p1, p2 - 1)
        PROVE  Agree(A, B, c)
    <3>0. PICK kE \in commits : kE.term < u /\ Agree(kE.entries, B, e)
      BY <1>b DEF Tgt, CoverLt
    <3>1. PICK t2 \in DOMAIN ledLog, c2 \in Nat, d2 \in Nat :
             /\ t2 <= kE.term /\ p2 <= c2 /\ d2 < p2 /\ MRoot(t2, c2, d2)
             /\ Agree(ledLog[t2], B, p2)
      <4>1. p2 \in 1..e BY <1>b
      <4> QED BY <4>1, <2>7, <3>0, <1>b, FirstRootUse
    <3> DEFINE A2 == ledLog[t2]
    <3>2. A2 \in Seq(EntryT) /\ t2 \in Nat /\ t2 < u /\ c2 <= Len(A2)
      <4>1. kE.term \in Nat BY TypeFacts
      <4> QED BY <4>1, <3>0, <3>1, <1>b, RootFacts
    <3>3. A2[p1] = B[p1] /\ A2[p2] = B[p2] BY <3>1, <1>b DEF Agree
    <3>4. p1 <= d2
      <4>1. IsConf(A2[p1]) /\ IsConf(A2[p2]) BY <3>3, <1>4, <2>7
      <4>2. p1 \in Nat /\ p2 \in Nat /\ p1 < p2 /\ p2 <= c2 BY <3>1, <1>b
      <4> QED BY <4>1, <4>2, <3>1, TwoConf
    <3>5. Agree(A2, B, c2) BY <3>1, <3>2, <3>4, <1>b
    \* the two leader logs agree on what both may commit
    <3>6. \A k \in Nat : k <= c /\ k <= c2 => Agree(A, A2, k)
      <4>1. CASE t < t2
        <5>1. Agree(A, A2, c) BY <4>1, <3>2, <3>1, <1>a DEF Before
        <5> QED BY <5>1, <1>b, <3>2 DEF Agree
      <4>2. CASE t = t2
        BY <4>2, <1>b, <1>c, <3>2 DEF Agree
      <4>3. CASE t2 < t
        <5>1. Agree(A2, A, c2) BY <4>3, <3>1, <1>a DEF Before
        <5> QED BY <5>1, <1>b, <3>2 DEF Agree
      <4> QED BY <4>1, <4>2, <4>3, <1>b, <3>2
    <3>7. c < p2
      <4>1. ASSUME p2 <= c PROVE FALSE
        <5>1. Agree(A, A2, p2) BY <4>1, <3>1, <3>6, <1>b
        <5>2. A[p1] = A2[p1] /\ A[p2] = A2[p2] BY <5>1, <1>b DEF Agree
        <5>3. IsConf(A[p1]) /\ IsConf(A[p2]) BY <5>2, <3>3, <1>4, <2>7
        <5>4. p1 \in Nat /\ p2 \in Nat /\ p1 < p2 BY <1>b
        <5>5. p1 <= d BY <5>3, <5>4, <4>1, TwoConf
        <5> QED BY <5>5, <1>b
      <4> QED BY <4>1, <1>b
    <3>8. Agree(A, A2, c) BY <3>6, <3>7, <3>1, <1>b
    <3> QED BY <3>8, <3>5, <3>7, <3>1, <3>2, <1>b DEF Agree
  <2>8. NoC(B, p1, e) \/ \E p \in (p1 + 1)..e : IsConf(B[p]) /\ NoC(B, p1, p - 1)
    BY <1>b, FirstChange
  <2> QED BY <2>6, <2>7, <2>8
<1>5. NoC(B, d, e) \/ \E p \in (d + 1)..e : IsConf(B[p]) /\ NoC(B, d, p - 1)
  BY <1>b, FirstChange
<1> QED BY <1>3, <1>4, <1>5

LEMMA Earlier ==
  ASSUME TypeOK, CommitSafetyP, FirstRoot, LegalChain,
         NEW u, NEW V, Tgt(u, V)
  PROVE  \A t \in DOMAIN ledLog : \A c \in Nat, d \in Nat :
           MRoot(t, c, d) /\ t < u /\ d <= elAt[u] => Agree(ledLog[t], ledLog[u], c)
<1> DEFINE Q(m) == \A t \in DOMAIN ledLog : \A c \in Nat, d \in Nat :
                     MRoot(t, c, d) /\ t < u /\ d <= elAt[u] /\ elAt[u] - d = m
                       => Agree(ledLog[t], ledLog[u], c)
<1>0. u \in DOMAIN ledLog /\ elAt[u] \in Nat BY TypeFacts DEF Tgt
<1>1. ASSUME NEW m \in Nat, \A k \in 0..(m - 1) : Q(k) PROVE Q(m)
  <2> SUFFICES ASSUME NEW t \in DOMAIN ledLog, NEW c \in Nat, NEW d \in Nat,
                      MRoot(t, c, d), t < u, d <= elAt[u], elAt[u] - d = m
               PROVE  Agree(ledLog[t], ledLog[u], c)
    OBVIOUS
  <2>1. ASSUME NEW t2 \in DOMAIN ledLog, NEW c2 \in Nat, NEW d2 \in Nat,
               MRoot(t2, c2, d2), t2 < u, d < d2, d2 <= elAt[u]
        PROVE  Agree(ledLog[t2], ledLog[u], c2)
    <3>1. elAt[u] - d2 \in 0..(m - 1) BY <2>1, <1>0
    <3>2. Q(elAt[u] - d2) BY <3>1, <1>1
    <3> QED BY <3>2, <2>1
  <2> HIDE DEF Q
  <2> QED BY <2>1, EarlierStep
<1> HIDE DEF Q
<1>2. \A m \in Nat : Q(m) BY <1>1, GeneralNatInduction
<1>3. ASSUME NEW t \in DOMAIN ledLog, NEW c \in Nat, NEW d \in Nat,
             MRoot(t, c, d), t < u, d <= elAt[u]
      PROVE  Agree(ledLog[t], ledLog[u], c)
  <2>1. elAt[u] - d \in Nat BY <1>3, <1>0
  <2>2. Q(elAt[u] - d) BY <2>1, <1>2
  <2> QED BY <2>2, <1>3 DEF Q
<1> QED BY <1>3

\* Leader completeness with membership changes: the leader log of u has
\* every prefix that a leader of an earlier term may commit.
LEMMA Core ==
  ASSUME TypeOK, CommitSafetyP, FirstRoot, LegalChain, LedTermsBound, LedOld,
         NEW u, NEW V, Tgt(u, V)
  PROVE  \A t \in DOMAIN ledLog : \A c \in Nat, d \in Nat :
           MRoot(t, c, d) /\ t < u => Agree(ledLog[t], ledLog[u], c)
<1> SUFFICES ASSUME NEW t \in DOMAIN ledLog, NEW c \in Nat, NEW d \in Nat, MRoot(t, c, d), t < u
             PROVE  Agree(ledLog[t], ledLog[u], c)
  OBVIOUS
<1>0. elAt[u] \in Nat BY TypeFacts DEF Tgt
<1>1. CASE elAt[u] < d BY <1>1, Later
<1>2. CASE d <= elAt[u] BY <1>2, Earlier
<1> QED BY <1>0, <1>1, <1>2

----
\* The target of Core, from the invariants.

LEMMA TEarlyInv ==
  ASSUME TypeOK, VoteHasReq, LedExtendsReq, LedFromLed,
         NEW ld \in leaders, ld.term \in DOMAIN ledLog
  PROVE  TEarly(ld.term, EarlyVoters(ld.server, ld.term))
<1> DEFINE u == ld.term
           i == ld.server
           B == ledLog[u]
<1> SUFFICES ASSUME NEW n \in EarlyVoters(i, u), NEW t \in DOMAIN ledLog, NEW c \in Nat,
                    Good(t, c), n \in AckedBy(t, c), t < u,
                    ~LostIn(t, c, t, u - 1)
             PROVE  Agree(ledLog[t], B, c)
  BY DEF TEarly
<1>1. [voter |-> n, term |-> u, cand |-> i] \in votes /\ Early(n, i, u) BY DEF EarlyVoters
<1>2. PICK m \in msgs : m.type = "vote" /\ m.src = i /\ m.term = u
  BY <1>1 DEF VoteHasReq
<1>3. c \in 1..Len(ledLog[t]) BY TypeFacts DEF Good
<1>4. Covers(t, c, m.lastLogIndex, m.lastLogTerm) BY <1>1, <1>2, <1>3 DEF Early
<1> DEFINE li == m.lastLogIndex
           lt == m.lastLogTerm
<1>5. c <= li /\ lt \in DOMAIN ledLog /\ Agree(ledLog[t], ledLog[lt], c) BY <1>4 DEF Covers
<1>6. li <= Len(B) /\ TermAt(B, li) = lt BY <1>2 DEF LedExtendsReq
<1>7. li \in Nat BY <1>2 DEF TypeOK, MsgT, VoteReqT, GrantT, AppendT, AckT
<1>8. B \in Seq(EntryT) /\ ledLog[t] \in Seq(EntryT) /\ ledLog[lt] \in Seq(EntryT) BY <1>5, TypeFacts
<1>9. li \in 1..Len(B) /\ B[li].term = lt BY <1>3, <1>5, <1>6, <1>7, <1>8 DEF TermAt
<1>10. Agree(B, ledLog[lt], li) BY <1>9 DEF LedFromLed, FromLed
<1> HIDE DEF B, li, lt
<1> QED BY <1>5, <1>7, <1>8, <1>10 DEF Agree

LEMMA TgtInv ==
  ASSUME Inv, NEW u \in DOMAIN ledLog, Before(u)
  PROVE  \E V : Tgt(u, V)
<1>1. /\ TypeOK /\ LedDom /\ EarlyQuorum /\ LeaderConfS
      /\ VoteHasReq /\ LedExtendsReq /\ LedFromLed
  BY DEF Inv
<1>2. PICK ld \in leaders : ld.term = u BY <1>1 DEF LedDom
<1> DEFINE V == EarlyVoters(ld.server, u)
<1>3. TEarly(u, V) BY <1>1, <1>2, TEarlyInv
<1>4. IsQuorum(V, ConfOf(ledLog[u], elAt[u])) BY <1>1, <1>2 DEF EarlyQuorum
<1>5. elAt[u] <= ledAt[u] /\ ledAt[u] <= Len(ledLog[u]) /\ CoverLt(ledLog[u], elAt[u], u)
  BY <1>1 DEF LeaderConfS
<1>6. elAt[u] \in Nat /\ ledAt[u] \in Nat /\ ledLog[u] \in Seq(EntryT) BY <1>1 DEF TypeOK
<1>7. elAt[u] <= Len(ledLog[u]) BY <1>5, <1>6
<1> HIDE DEF V
<1>8. Tgt(u, V) BY <1>3, <1>4, <1>5, <1>7 DEF Tgt
<1> QED BY <1>8

----
THEOREM LCThm == ASSUME Inv PROVE LC
<1>1. /\ TypeOK /\ CommitSafetyP /\ FirstRoot /\ LegalChain /\ LedTermsBound /\ LedOld
  BY DEF Inv
<1> DEFINE P(u) == u \in DOMAIN ledLog =>
                     \A t \in DOMAIN ledLog : \A c \in Nat, d \in Nat :
                       MRoot(t, c, d) /\ t < u => Agree(ledLog[t], ledLog[u], c)
<1>2. ASSUME NEW u \in Nat, \A w \in 0..(u - 1) : P(w) PROVE P(u)
  <2> SUFFICES ASSUME u \in DOMAIN ledLog
               PROVE  \A t \in DOMAIN ledLog : \A c \in Nat, d \in Nat :
                        MRoot(t, c, d) /\ t < u => Agree(ledLog[t], ledLog[u], c)
    OBVIOUS
  <2>1. Before(u)
    <3> SUFFICES ASSUME NEW w \in DOMAIN ledLog, w < u
                 PROVE  \A t \in DOMAIN ledLog : \A c \in Nat, d \in Nat :
                          MRoot(t, c, d) /\ t < w => Agree(ledLog[t], ledLog[w], c)
      BY DEF Before
    <3>1. w \in 0..(u - 1) BY <1>1, TypeFacts
    <3>2. P(w) BY <3>1, <1>2
    <3> QED BY <3>2
  <2> HIDE DEF P
  <2>2. PICK V : Tgt(u, V) BY <2>1, TgtInv
  <2> QED BY <2>2, <1>1, Core
<1> HIDE DEF P
<1>3. \A u \in Nat : P(u) BY <1>2, GeneralNatInduction
<1>4. DOMAIN ledLog \subseteq Nat /\ \A t \in DOMAIN ledLog : ledLog[t] \in Seq(EntryT)
  BY <1>1, TypeFacts
<1> SUFFICES ASSUME NEW t \in DOMAIN ledLog, NEW c \in 1..Len(ledLog[t]),
                    NEW d \in 0..Len(ledLog[t]), MRoot(t, c, d),
                    NEW u \in DOMAIN ledLog, t < u
             PROVE  Agree(ledLog[t], ledLog[u], c)
  BY DEF LC
<1>5. u \in Nat /\ c \in Nat /\ d \in Nat BY <1>4
<1>6. P(u) BY <1>3, <1>5
<1> QED BY <1>5, <1>6 DEF P
====
