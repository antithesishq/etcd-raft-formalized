---- MODULE EtcdBase ----
\* Constant-level lemmas: sequences, quorums, configurations.
EXTENDS EtcdChange, EtcdRec, FiniteSetTheorems, SequenceTheorems, NaturalsInduction

----
\* Sequences.

LEMMA SubSeqEq ==
  ASSUME NEW S, NEW a \in Seq(S), NEW b \in Seq(S), NEW k \in Nat, k <= Len(a), k <= Len(b)
  PROVE  (SubSeq(a, 1, k) = SubSeq(b, 1, k)) <=> (\A q \in 1..k : a[q] = b[q])
<1>1. ASSUME SubSeq(a, 1, k) = SubSeq(b, 1, k) PROVE \A q \in 1..k : a[q] = b[q]
  <2> TAKE q \in 1..k
  <2>1. SubSeq(a, 1, k)[q] = a[q] OBVIOUS
  <2>2. SubSeq(b, 1, k)[q] = b[q] OBVIOUS
  <2> QED BY <1>1, <2>1, <2>2
<1>2. ASSUME \A q \in 1..k : a[q] = b[q] PROVE SubSeq(a, 1, k) = SubSeq(b, 1, k)
  <2>1. SubSeq(a, 1, k) \in Seq(S) /\ Len(SubSeq(a, 1, k)) = k OBVIOUS
  <2>2. SubSeq(b, 1, k) \in Seq(S) /\ Len(SubSeq(b, 1, k)) = k OBVIOUS
  <2>3. \A q \in 1..k : SubSeq(a, 1, k)[q] = SubSeq(b, 1, k)[q] BY <1>2
  <2> QED BY <2>1, <2>2, <2>3, SeqEqual
<1> QED BY <1>1, <1>2

\* SubSeq(a,1,k) = SubSeq(b,1,k) with k within both is Agree.
LEMMA SubSeqAgree ==
  ASSUME NEW S, NEW a \in Seq(S), NEW b \in Seq(S), NEW k \in Nat, k <= Len(a), k <= Len(b)
  PROVE  (SubSeq(a, 1, k) = SubSeq(b, 1, k)) <=> Agree(a, b, k)
BY SubSeqEq DEF Agree

LEMMA IsPrefixPre ==
  ASSUME NEW S, NEW a \in Seq(S), NEW b \in Seq(S)
  PROVE  IsPrefix(a, b) <=> Pre(a, b)
<1>1. ASSUME Len(a) <= Len(b) PROVE (a = SubSeq(b, 1, Len(a))) <=> (\A q \in 1..Len(a) : a[q] = b[q])
  <2>1. SubSeq(a, 1, Len(a)) = a OBVIOUS
  <2> QED BY <1>1, <2>1, SubSeqEq
<1> QED BY <1>1 DEF IsPrefix, Agree, Pre

\* The first k entries of a, as a sequence.
LEMMA SubSeqFacts ==
  ASSUME NEW S, NEW a \in Seq(S), NEW k \in Nat, k <= Len(a)
  PROVE  /\ SubSeq(a, 1, k) \in Seq(S)
         /\ Len(SubSeq(a, 1, k)) = k
         /\ \A q \in 1..k : SubSeq(a, 1, k)[q] = a[q]
OBVIOUS

----
\* Quorums.

LEMMA MajInter ==
  ASSUME NEW V, IsFiniteSet(V), NEW P, NEW Q, Majority(P, V), Majority(Q, V)
  PROVE  \E s \in V : s \in P /\ s \in Q
<1> DEFINE A == P \cap V  B == Q \cap V
<1>1. IsFiniteSet(A) /\ IsFiniteSet(B) /\ IsFiniteSet(A \cup B) /\ IsFiniteSet(A \cap B) BY FS_Subset, FS_Union
<1>2. Cardinality(A \cup B) = Cardinality(A) + Cardinality(B) - Cardinality(A \cap B) BY <1>1, FS_Union
<1>3. Cardinality(A \cup B) <= Cardinality(V) BY FS_Subset
<1>4. Cardinality(A) \in Nat /\ Cardinality(B) \in Nat /\ Cardinality(A \cap B) \in Nat /\ Cardinality(V) \in Nat /\ Cardinality(A \cup B) \in Nat BY <1>1, FS_CardinalityType
<1>5. Cardinality(A \cap B) > 0 BY <1>2, <1>3, <1>4 DEF Majority
<1>6. A \cap B # {} BY <1>5, <1>1, FS_EmptySet
<1> QED BY <1>6

LEMMA MajMono ==
  ASSUME NEW V, IsFiniteSet(V), NEW P, NEW Q, P \subseteq Q, Majority(P, V)
  PROVE  Majority(Q, V)
<1>1. IsFiniteSet(Q \cap V) /\ IsFiniteSet(P \cap V) BY FS_Subset
<1>2. Cardinality(P \cap V) <= Cardinality(Q \cap V) BY <1>1, FS_Subset
<1>3. Cardinality(P \cap V) \in Nat /\ Cardinality(Q \cap V) \in Nat /\ Cardinality(V) \in Nat BY <1>1, FS_CardinalityType
<1> QED BY <1>2, <1>3 DEF Majority

\* W is V less one element: majorities of the two share a node.
LEMMA MajInterLess ==
  ASSUME NEW V, IsFiniteSet(V), NEW x \in V, NEW P, NEW Q, Majority(P, V), Majority(Q, V \ {x})
  PROVE  \E s \in V \ {x} : s \in P /\ s \in Q
<1> DEFINE W == V \ {x}  A == P \cap V  B == Q \cap W
<1>0. IsFiniteSet(W) /\ Cardinality(W) = Cardinality(V) - 1 BY FS_RemoveElement
<1>1. IsFiniteSet(A) /\ IsFiniteSet(B) /\ IsFiniteSet(A \cup B) /\ IsFiniteSet(A \cap B) BY FS_Subset, FS_Union
<1>2. Cardinality(A \cup B) = Cardinality(A) + Cardinality(B) - Cardinality(A \cap B) BY <1>1, FS_Union
<1>3. Cardinality(A \cup B) <= Cardinality(V) BY FS_Subset
<1>4. Cardinality(A) \in Nat /\ Cardinality(B) \in Nat /\ Cardinality(A \cap B) \in Nat /\ Cardinality(V) \in Nat /\ Cardinality(A \cup B) \in Nat /\ Cardinality(W) \in Nat BY <1>0, <1>1, FS_CardinalityType
<1>5. Cardinality(A \cap B) > 0 BY <1>0, <1>2, <1>3, <1>4 DEF Majority
<1>6. A \cap B # {} BY <1>5, <1>1, FS_EmptySet
<1> QED BY <1>6

LEMMA MajInterNear ==
  ASSUME NEW V, IsFiniteSet(V), NEW W, IsFiniteSet(W),
         Cardinality((V \ W) \cup (W \ V)) <= 1,
         NEW P, NEW Q, Majority(P, V), Majority(Q, W)
  PROVE  \E s \in V \cap W : s \in P /\ s \in Q
<1> DEFINE D == (V \ W) \cup (W \ V)
<1>1. IsFiniteSet(D) BY FS_Union, FS_Difference
<1>2. Cardinality(D) \in Nat BY <1>1, FS_CardinalityType
<1>3. CASE Cardinality(D) = 0
  <2>1. D = {} BY <1>3, <1>1, FS_EmptySet
  <2>2. V = W BY <2>1
  <2> QED BY <2>2, MajInter
<1>4. CASE Cardinality(D) = 1
  <2>1. PICK x : D = {x} BY <1>4, <1>1, FS_Singleton
  <2>2. CASE x \in V \ W
    <3>1. W = V \ {x} BY <2>1, <2>2
    <3>2. \E s \in V \ {x} : s \in P /\ s \in Q BY <3>1, <2>2, MajInterLess
    <3> QED BY <3>2, <3>1
  <2>3. CASE x \in W \ V
    <3>1. V = W \ {x} BY <2>1, <2>3
    <3>2. \E s \in W \ {x} : s \in Q /\ s \in P BY <3>1, <2>3, MajInterLess
    <3> QED BY <3>2, <3>1
  <2> QED BY <2>1, <2>2, <2>3
<1> QED BY <1>2, <1>3, <1>4

LEMMA MajNonEmpty ==
  ASSUME NEW V, IsFiniteSet(V), NEW P, Majority(P, V)
  PROVE  V # {}
<1>1. Cardinality(P \cap V) \in Nat BY FS_Subset, FS_CardinalityType
<1>2. Cardinality({}) = 0 BY FS_EmptySet
<1> QED BY <1>1, <1>2 DEF Majority

LEMMA QuorumMono ==
  ASSUME ConstOK, NEW C \in ConfT, NEW P, NEW Q, P \subseteq Q, IsQuorum(P, C)
  PROVE  IsQuorum(Q, C)
<1>1. IsFiniteSet(C.in) /\ IsFiniteSet(C.out) BY FS_Subset DEF ConfT, ConstOK
<1> QED BY <1>1, MajMono DEF IsQuorum

LEMMA QuorumInter ==
  ASSUME ConstOK, NEW C \in ConfT, NEW P, NEW Q, IsQuorum(P, C), IsQuorum(Q, C)
  PROVE  \E s \in Server : s \in P /\ s \in Q
<1>1. IsFiniteSet(C.in) /\ C.in \subseteq Server BY FS_Subset DEF ConfT, ConstOK
<1> QED BY <1>1, MajInter DEF IsQuorum

LEMMA NextConfType ==
  ASSUME NEW C \in ConfT, NEW d, ChangeOK(d)
  PROVE  NextConf(C, d) \in ConfT
BY DEF NextConf, ConfT, Target, ChangeOK

\* Quorums of a configuration and of the one a legal change makes of it share a node.
LEMMA QuorumInterNext ==
  ASSUME ConstOK, NEW C \in ConfT, NEW d, ChangeOK(d), Legal(C, d),
         NEW P, NEW Q, IsQuorum(P, C), IsQuorum(Q, NextConf(C, d))
  PROVE  \E s \in Server : s \in P /\ s \in Q
<1>0. IsFiniteSet(C.in) /\ C.in \subseteq Server /\ IsFiniteSet(C.out) BY FS_Subset DEF ConfT, ConstOK
<1>1. CASE d.leave
  <2>1. NextConf(C, d).in = C.in BY <1>1 DEF NextConf
  <2> QED BY <2>1, <1>0, MajInter DEF IsQuorum
<1>2. CASE ~d.leave /\ d.joint
  <2>1. NextConf(C, d).out = C.in BY <1>2 DEF NextConf
  <2>2. C.in # {} BY <1>0, MajNonEmpty DEF IsQuorum
  <2>3. Majority(Q, C.in) BY <2>1, <2>2 DEF IsQuorum
  <2> QED BY <2>3, <1>0, MajInter DEF IsQuorum
<1>3. CASE ~d.leave /\ ~d.joint
  <2> DEFINE T == Target(C, d)
  <2>1. NextConf(C, d).in = T BY <1>3 DEF NextConf
  <2>2. T \subseteq Server /\ IsFiniteSet(T) BY FS_Subset DEF Target, ChangeOK, ConfT, ConstOK
  <2>3. Cardinality((C.in \ T) \cup (T \ C.in)) <= 1 BY <1>3 DEF Legal
  <2>4. \E s \in C.in \cap T : s \in P /\ s \in Q BY <2>1, <2>2, <2>3, <1>0, MajInterNear DEF IsQuorum
  <2> QED BY <2>4, <1>0
<1> QED BY <1>1, <1>2, <1>3 DEF ChangeOK

----
\* Configurations made by a log.

CDef(l, v, k) == IF IsConf(l[k]) THEN NextConf(v, l[k].value) ELSE v
CF(l, a) == CHOOSE f : f = [k \in 0..a |-> IF k = 0 THEN InitConf ELSE CDef(l, f[k - 1], k)]

LEMMA ConfOfCF == ASSUME NEW l, NEW a PROVE ConfOf(l, a) = CF(l, a)[a]
BY DEF ConfOf, CF, CDef

LEMMA CFDef ==
  ASSUME NEW l, NEW a \in Nat
  PROVE  CF(l, a) = [k \in 0..a |-> IF k = 0 THEN InitConf ELSE CDef(l, CF(l, a)[k - 1], k)]
<1>1. \E f : f = [k \in 0..a |-> IF k = 0 THEN InitConf ELSE CDef(l, f[k - 1], k)]
  BY FinRecExists
<1> QED BY <1>1 DEF CF

LEMMA CFSame ==
  ASSUME NEW l, NEW a \in Nat, NEW b \in Nat
  PROVE  \A k \in Nat : k <= a /\ k <= b => CF(l, a)[k] = CF(l, b)[k]
<1> DEFINE P(k) == k <= a /\ k <= b => CF(l, a)[k] = CF(l, b)[k]
<1>1. P(0) BY CFDef
<1>2. ASSUME NEW k \in Nat, P(k) PROVE P(k + 1)
  <2> SUFFICES ASSUME k + 1 <= a, k + 1 <= b PROVE CF(l, a)[k + 1] = CF(l, b)[k + 1] OBVIOUS
  <2>1. CF(l, a)[k + 1] = CDef(l, CF(l, a)[k], k + 1) BY CFDef
  <2>2. CF(l, b)[k + 1] = CDef(l, CF(l, b)[k], k + 1) BY CFDef
  <2> QED BY <2>1, <2>2, <1>2
<1> HIDE DEF P
<1>3. \A k \in Nat : P(k) BY <1>1, <1>2, NatInduction
<1> QED BY <1>3 DEF P

LEMMA ConfOf0 == ASSUME NEW l PROVE ConfOf(l, 0) = InitConf
BY ConfOfCF, CFDef

LEMMA ConfOfStep ==
  ASSUME NEW l, NEW k \in Nat, k >= 1
  PROVE  ConfOf(l, k) = IF IsConf(l[k]) THEN NextConf(ConfOf(l, k - 1), l[k].value) ELSE ConfOf(l, k - 1)
<1>1. CF(l, k)[k] = CDef(l, CF(l, k)[k - 1], k) BY CFDef
<1>2. CF(l, k)[k - 1] = CF(l, k - 1)[k - 1] BY CFSame
<1> QED BY <1>1, <1>2, ConfOfCF DEF CDef

LEMMA ConfOfCongr ==
  ASSUME NEW l, NEW l2, NEW a \in Nat, \A q \in 1..a : l[q] = l2[q]
  PROVE  ConfOf(l, a) = ConfOf(l2, a)
<1> DEFINE P(k) == k <= a => ConfOf(l, k) = ConfOf(l2, k)
<1>1. P(0) BY ConfOf0
<1>2. ASSUME NEW k \in Nat, P(k) PROVE P(k + 1)
  <2> SUFFICES ASSUME k + 1 <= a PROVE ConfOf(l, k + 1) = ConfOf(l2, k + 1) OBVIOUS
  <2>1. l[k + 1] = l2[k + 1] OBVIOUS
  <2>2. ConfOf(l, k) = ConfOf(l2, k) BY <1>2
  <2>3. ConfOf(l, k + 1) = IF IsConf(l[k + 1]) THEN NextConf(ConfOf(l, k), l[k + 1].value) ELSE ConfOf(l, k) BY ConfOfStep
  <2>4. ConfOf(l2, k + 1) = IF IsConf(l2[k + 1]) THEN NextConf(ConfOf(l2, k), l2[k + 1].value) ELSE ConfOf(l2, k) BY ConfOfStep
  <2> QED BY <2>1, <2>2, <2>3, <2>4
<1> HIDE DEF P
<1>3. \A k \in Nat : P(k) BY <1>1, <1>2, NatInduction
<1> QED BY <1>3 DEF P

LEMMA ConfOfSkip ==
  ASSUME NEW l, NEW a \in Nat, NEW b \in Nat, a <= b, \A q \in (a + 1)..b : ~IsConf(l[q])
  PROVE  ConfOf(l, b) = ConfOf(l, a)
<1> DEFINE P(k) == a + k <= b => ConfOf(l, a + k) = ConfOf(l, a)
<1>1. P(0) OBVIOUS
<1>2. ASSUME NEW k \in Nat, P(k) PROVE P(k + 1)
  <2> SUFFICES ASSUME a + k + 1 <= b PROVE ConfOf(l, a + k + 1) = ConfOf(l, a) OBVIOUS
  <2>1. ~IsConf(l[a + k + 1]) OBVIOUS
  <2>2. ConfOf(l, a + k + 1) = ConfOf(l, a + k) BY <2>1, ConfOfStep
  <2> QED BY <2>2, <1>2
<1> HIDE DEF P
<1>3. \A k \in Nat : P(k) BY <1>1, <1>2, NatInduction
<1>4. P(b - a) BY <1>3
<1> QED BY <1>4 DEF P

LEMMA EntryChange ==
  ASSUME NEW e \in EntryT, IsConf(e)
  PROVE  ChangeOK(e.value)
BY ChangeFacts DEF EntryT, IsConf

LEMMA ConfOfType ==
  ASSUME ConstOK, NEW l \in Seq(EntryT), NEW a \in Nat, a <= Len(l)
  PROVE  ConfOf(l, a) \in ConfT
<1> DEFINE P(k) == k <= a => ConfOf(l, k) \in ConfT
<1>1. P(0) BY ConfOf0 DEF InitConf, ConfT, ConstOK
<1>2. ASSUME NEW k \in Nat, P(k) PROVE P(k + 1)
  <2> SUFFICES ASSUME k + 1 <= a PROVE ConfOf(l, k + 1) \in ConfT OBVIOUS
  <2>1. ConfOf(l, k) \in ConfT BY <1>2
  <2>2. l[k + 1] \in EntryT OBVIOUS
  <2>3. ConfOf(l, k + 1) = IF IsConf(l[k + 1]) THEN NextConf(ConfOf(l, k), l[k + 1].value) ELSE ConfOf(l, k) BY ConfOfStep
  <2> QED BY <2>1, <2>2, <2>3, EntryChange, NextConfType
<1> HIDE DEF P
<1>3. \A k \in Nat : P(k) BY <1>1, <1>2, NatInduction
<1> QED BY <1>3 DEF P

\* The last change among the first a entries.
LEMMA MaxExists ==
  ASSUME NEW a \in Nat
  PROVE  \A S \in SUBSET (1..a) : S # {} => \E k \in S : \A q \in S : q <= k
<1> DEFINE P(n) == \A S \in SUBSET (1..n) : S # {} => \E k \in S : \A q \in S : q <= k
<1>1. P(0) OBVIOUS
<1>2. ASSUME NEW n \in Nat, P(n) PROVE P(n + 1)
  <2> SUFFICES ASSUME NEW S \in SUBSET (1..(n + 1)), S # {} PROVE \E k \in S : \A q \in S : q <= k OBVIOUS
  <2>1. CASE n + 1 \in S BY <2>1
  <2>2. CASE n + 1 \notin S
    <3>1. S \in SUBSET (1..n) BY <2>2
    <3> QED BY <3>1, <1>2
  <2> QED BY <2>1, <2>2
<1> HIDE DEF P
<1>3. \A n \in Nat : P(n) BY <1>1, <1>2, NatInduction
<1> QED BY <1>3 DEF P

LEMMA LastConfFacts ==
  ASSUME NEW l, NEW a \in Nat
  PROVE  /\ LastConf(l, a) \in 0..a
         /\ LastConf(l, a) = 0 \/ IsConf(l[LastConf(l, a)])
         /\ \A q \in (LastConf(l, a) + 1)..a : ~IsConf(l[q])
<1> DEFINE S == ConfIdx(l, a)
<1>1. S \in SUBSET (1..a) BY DEF ConfIdx
<1>2. CASE S = {} BY <1>2 DEF LastConf, ConfIdx
<1>3. CASE S # {}
  <2>1. \E k \in S : \A q \in S : q <= k BY <1>1, <1>3, MaxExists
  <2> DEFINE m == CHOOSE k \in S : \A q \in S : q <= k
  <2>2. m \in S /\ \A q \in S : q <= m BY <2>1
  <2>3. LastConf(l, a) = m BY <1>3 DEF LastConf
  <2> HIDE DEF m, S
  <2>4. m \in 1..a /\ IsConf(l[m]) BY <2>2 DEF S, ConfIdx
  <2>5. \A q \in (m + 1)..a : ~IsConf(l[q])
    <3> TAKE q \in (m + 1)..a
    <3>1. q \in 1..a /\ ~(q <= m) BY <2>4
    <3>2. IsConf(l[q]) => q \in S BY <3>1 DEF S, ConfIdx
    <3> QED BY <3>1, <3>2, <2>2
  <2> QED BY <2>3, <2>4, <2>5
<1> QED BY <1>2, <1>3

LEMMA ConfOfLastConf ==
  ASSUME NEW l, NEW a \in Nat
  PROVE  ConfOf(l, LastConf(l, a)) = ConfOf(l, a)
BY LastConfFacts, ConfOfSkip
====
