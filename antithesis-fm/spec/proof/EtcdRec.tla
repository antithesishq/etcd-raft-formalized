---- MODULE EtcdRec ----
\* A function defined by recursion over 0..a exists. In a module without
\* variables: the backends fail to apply FiniteNatInductiveDef inside EtcdRaft.
EXTENDS Naturals, NaturalsInduction, TLAPS

LEMMA FinRecExists ==
  ASSUME NEW c0, NEW D(_, _), NEW a \in Nat
  PROVE  \E f : f = [k \in 0..a |-> IF k = 0 THEN c0 ELSE D(f[k - 1], k)]
<1> DEFINE F == CHOOSE f : f = [k \in 0..a |-> IF k = 0 THEN c0 ELSE D(f[k - 1], k)]
<1>1. FiniteNatInductiveDefHypothesis(F, c0, D, 0, a) BY DEF FiniteNatInductiveDefHypothesis
<1>2. FiniteNatInductiveDefConclusion(F, c0, D, 0, a) BY <1>1, FiniteNatInductiveDef
<1>3. F = [k \in 0..a |-> IF k = 0 THEN c0 ELSE D(F[k - 1], k)] BY <1>2 DEF FiniteNatInductiveDefConclusion
<1> HIDE DEF F
<1> QED BY <1>3
====
