---- MODULE EtcdCommitBase ----
\* State-level consequences of Inv about commits, and how roots of commits
\* survive a step (monotonicity). Used by EtcdCommit.tla.
EXTENDS EtcdLog, EtcdLC

\* Two prefixes of one sequence are comparable.
LEMMA PreCmp ==
  ASSUME NEW S, NEW a \in Seq(S), NEW b \in Seq(S), NEW L \in Seq(S), Pre(a, L), Pre(b, L)
  PROVE  Pre(a, b) \/ Pre(b, a)
BY DEF Pre, Agree

LEMMA PreRefl == ASSUME NEW S, NEW a \in Seq(S) PROVE Pre(a, a)
BY DEF Pre, Agree

\* A commit's entries are a prefix of every leader log of its term or a later one.
LEMMA RootInLed ==
  ASSUME Inv, NEW k \in commits, NEW u \in DOMAIN ledLog, k.term <= u
  PROVE  Pre(k.entries, ledLog[u])
<1>1. TypeOK /\ CommitRoot BY DEF Inv
<1>2. LC BY LCThm
<1>3. PICK r \in commits : Pre(k.entries, r.entries) /\ Root(r) /\ r.term <= k.term
  BY <1>1 DEF CommitRoot
<1> DEFINE t == r.term  c == Len(r.entries)
<1>4. /\ k.entries \in Seq(EntryT) /\ r.entries \in Seq(EntryT) /\ k.term \in Nat /\ t \in Nat
      /\ u \in Nat /\ ledLog[u] \in Seq(EntryT)
  BY <1>1, TypeFacts
<1>5. t \in DOMAIN ledLog /\ Pre(r.entries, ledLog[t]) /\ \E d \in 0..Len(ledLog[t]) : MRoot(t, c, d)
  BY <1>3 DEF Root
<1>6. ledLog[t] \in Seq(EntryT) BY <1>5, <1>1, TypeFacts
<1>7. Pre(r.entries, ledLog[u])
  <2>1. CASE t = u BY <2>1, <1>5
  <2>2. CASE t < u
    <3>1. PICK d \in 0..Len(ledLog[t]) : MRoot(t, c, d) BY <1>5
    <3>2. c \in 1..Len(ledLog[t]) BY <3>1, <1>6, <1>4 DEF MRoot, Good
    <3>3. Agree(ledLog[t], ledLog[u], c) BY <3>1, <3>2, <2>2, <1>5, <1>2 DEF LC
    <3> QED BY <3>3, <1>5, <1>4, <1>6 DEF Pre, Agree
  <2> QED BY <2>1, <2>2, <1>3, <1>4
<1> HIDE DEF t, c
<1> QED BY <1>3, <1>4, <1>7, PreTrans

----
\* Monotonicity.

LEMMA AckedByGrow ==
  ASSUME msgs \subseteq msgs', NEW t, NEW c
  PROVE  AckedBy(t, c) \subseteq AckedBy(t, c)'
BY DEF AckedBy

\* What a leader may commit, it may commit after a step.
LEMMA MRootMono ==
  ASSUME TypeOK, Grows, NEW t \in DOMAIN ledLog, NEW c \in Nat, NEW d \in Nat, MRoot(t, c, d)
  PROVE  MRoot(t, c, d)'
<1> DEFINE L == ledLog[t]  M == ledLog'[t]
<1>1. /\ Good(t, c) /\ 1 <= c /\ c <= Len(L) /\ d <= Len(L)
      /\ L \in Seq(EntryT) /\ t \in Nat
      /\ IsQuorum(AckedBy(t, c), ConfOf(L, d))
      /\ ConfOf(L, d) \in ConfT
  BY RootFacts
<1>2. M \in Seq(EntryT) /\ Pre(L, M) /\ t \in DOMAIN ledLog' BY DEF Grows
<1>3. Len(L) <= Len(M) /\ \A q \in 1..Len(L) : M[q] = L[q] BY <1>1, <1>2 DEF Pre, Agree
<1>4. Good(t, c)' BY <1>1, <1>2, <1>3 DEF Good
<1>5. d <= Len(M) BY <1>1, <1>2, <1>3
<1>6. Cover(ledLog[t], d, t)'
  <2>1. CASE d = 0 BY <2>1 DEF Cover
  <2>2. CASE d # 0
    <3>1. PICK k \in commits : k.term <= t /\ Agree(k.entries, L, d) BY <2>2 DEF MRoot, Cover
    <3>2. k.entries \in Seq(EntryT) BY TypeFacts
    <3>3. Agree(k.entries, M, d) BY <3>1, <3>2, AgreeGrowL
    <3>4. k \in commits' BY DEF Grows
    <3> QED BY <3>1, <3>3, <3>4 DEF Cover
  <2> QED BY <2>1, <2>2
<1>7. AtMostOne(ledLog[t], d, c)'
  <2>1. AtMostOne(L, d, c) BY DEF MRoot
  <2>2. \A q \in (d + 1)..c : M[q] = L[q] BY <1>1, <1>3
  <2> QED BY <2>1, <2>2 DEF AtMostOne
<1>8. IsQuorum(AckedBy(t, c)', ConfOf(M, d))
  <2>1. \A q \in 1..d : L[q] = M[q] BY <1>1, <1>3
  <2>2. ConfOf(L, d) = ConfOf(M, d) BY <2>1, ConfOfCongr
  <2>3. AckedBy(t, c) \subseteq AckedBy(t, c)' BY AckedByGrow DEF Grows
  <2>4. ConstOK BY TypeFacts
  <2>5. IsQuorum(AckedBy(t, c)', ConfOf(L, d)) BY <1>1, <2>3, <2>4, QuorumMono
  <2> QED BY <2>2, <2>5
<1> HIDE DEF L, M
<1> QED BY <1>4, <1>5, <1>6, <1>7, <1>8 DEF MRoot, L, M

LEMMA RootMono ==
  ASSUME TypeOK, Grows, NEW r \in commits, Root(r)
  PROVE  Root(r)'
<1> DEFINE t == r.term  c == Len(r.entries)
<1>1. t \in DOMAIN ledLog /\ Pre(r.entries, ledLog[t]) BY DEF Root
<1>2. PICK d \in 0..Len(ledLog[t]) : MRoot(t, c, d) BY DEF Root
<1>3. r.entries \in Seq(EntryT) /\ ledLog[t] \in Seq(EntryT) BY <1>1, TypeFacts
<1>4. c \in Nat /\ d \in Nat BY <1>3
<1>5. MRoot(t, c, d)' BY <1>1, <1>2, <1>4, MRootMono
<1>6. Agree(r.entries, ledLog'[t], c) BY <1>1, <1>3, <1>4, AgreeGrowL DEF Pre
<1>7. t \in DOMAIN ledLog' /\ ledLog'[t] \in Seq(EntryT) /\ Pre(ledLog[t], ledLog'[t]) BY <1>1 DEF Grows
<1>8. d \in 0..Len(ledLog'[t]) BY <1>3, <1>7 DEF Pre, Agree
<1> HIDE DEF t, c
<1> QED BY <1>5, <1>6, <1>7, <1>8 DEF Root, Pre, t, c

\* The bodies of CommitRoot and FirstRoot.
CRB(e, kt) == \E r \in commits : Pre(e, r.entries) /\ Root(r) /\ r.term <= kt
FRB(kt, p) ==
    \E r \in commits :
        /\ r.term <= kt /\ p <= Len(r.entries)
        /\ r.term \in DOMAIN ledLog
        /\ Pre(r.entries, ledLog[r.term])
        /\ \E d \in 0..(p - 1) : MRoot(r.term, Len(r.entries), d)

LEMMA CRBMono ==
  ASSUME TypeOK, Grows, NEW e, NEW kt, CRB(e, kt)
  PROVE  CRB(e, kt)'
<1>1. PICK r \in commits : Pre(e, r.entries) /\ Root(r) /\ r.term <= kt BY DEF CRB
<1>2. Root(r)' BY <1>1, RootMono
<1>3. r \in commits' BY DEF Grows
<1> QED BY <1>1, <1>2, <1>3 DEF CRB

LEMMA FRBMono ==
  ASSUME TypeOK, Grows, NEW kt, NEW p \in Nat, FRB(kt, p)
  PROVE  FRB(kt, p)'
<1>1. PICK r \in commits :
        /\ r.term <= kt /\ p <= Len(r.entries)
        /\ r.term \in DOMAIN ledLog
        /\ Pre(r.entries, ledLog[r.term])
        /\ \E d \in 0..(p - 1) : MRoot(r.term, Len(r.entries), d)
  BY DEF FRB
<1> DEFINE t == r.term  c == Len(r.entries)
<1>2. PICK d \in 0..(p - 1) : MRoot(t, c, d) BY <1>1
<1>3. r.entries \in Seq(EntryT) /\ ledLog[t] \in Seq(EntryT) BY <1>1, TypeFacts
<1>4. c \in Nat /\ d \in Nat BY <1>3
<1>5. MRoot(t, c, d)' BY <1>1, <1>2, <1>4, MRootMono
<1>6. Agree(r.entries, ledLog'[t], c) BY <1>1, <1>3, <1>4, AgreeGrowL DEF Pre
<1>7. t \in DOMAIN ledLog' /\ r \in commits' BY <1>1 DEF Grows
<1> HIDE DEF t, c
<1> QED BY <1>1, <1>2, <1>5, <1>6, <1>7 DEF FRB, Pre, t, c

LEMMA CRBWeaken ==
  ASSUME NEW e \in Seq(EntryT), NEW f \in Seq(EntryT), NEW kt \in Nat, NEW kt2 \in Nat,
         TypeOK, CRB(f, kt), Pre(e, f), kt <= kt2
  PROVE  CRB(e, kt2)
<1>1. PICK r \in commits : Pre(f, r.entries) /\ Root(r) /\ r.term <= kt BY DEF CRB
<1>2. r.entries \in Seq(EntryT) /\ r.term \in Nat BY TypeFacts
<1>3. Pre(e, r.entries) BY <1>1, <1>2, PreTrans
<1> QED BY <1>1, <1>2, <1>3 DEF CRB

LEMMA FRBWeaken ==
  ASSUME NEW kt \in Nat, NEW kt2 \in Nat, NEW p, TypeOK, FRB(kt, p), kt <= kt2
  PROVE  FRB(kt2, p)
<1>1. PICK r \in commits :
        /\ r.term <= kt /\ p <= Len(r.entries)
        /\ r.term \in DOMAIN ledLog
        /\ Pre(r.entries, ledLog[r.term])
        /\ \E d \in 0..(p - 1) : MRoot(r.term, Len(r.entries), d)
  BY DEF FRB
<1>2. r.term \in Nat BY TypeFacts
<1> QED BY <1>1, <1>2 DEF FRB
====
