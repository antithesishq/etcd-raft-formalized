---- MODULE EtcdSafety ----
\* The safety properties of EtcdRaft: Spec => []P.
EXTENDS EtcdCommit, EtcdAck, EtcdReadCore, EtcdReadStep

LEMMA InvFromGroups ==
  ASSUME Basic, S1, S2, S3, MG, CG, AG PROVE Inv
BY DEF Inv, Basic, S1, S2, S3, MG, CG, AG

LEMMA GroupsFromInv ==
  ASSUME Inv PROVE Basic /\ S1 /\ S2 /\ S3 /\ MG /\ CG /\ AG
BY DEF Inv, Basic, S1, S2, S3, MG, CG, AG

\* The whole invariant.
II == Inv /\ RInv

THEOREM IIInit == ASSUME ConstOK, Init PROVE II
BY BasicInit, S1Init, S2Init, S3Init, MGInit, CGInit, AGInit, RInit, InvFromGroups DEF II

THEOREM IIStep == ASSUME II, [Next]_rvars PROVE II'
<1>0. Inv /\ RInv /\ Basic /\ S1 /\ S2 /\ S3 /\ MG /\ CG /\ AG BY GroupsFromInv DEF II
<1>1. Basic' BY <1>0, BasicStep
<1>2. TypeOK /\ LedDom BY <1>0 DEF Basic
<1>3. ASSUME UNCHANGED vars PROVE Inv'
  <2>1. S1' /\ S2' /\ S3' /\ MG' /\ CG' /\ AG' BY <1>0, <1>3, S1Unch, S2Unch, S3Unch, MGUnch, CGUnch, AGUnch
  <2> QED BY <1>1, <2>1 DEF Inv, Basic, S1, S2, S3, MG, CG, AG
<1>4. ASSUME ProtoCases PROVE Inv'
  <2>1. S1' /\ S2' /\ S3' /\ MG' /\ CG' /\ AG' BY <1>0, <1>4, S1Step, S2Step, S3Step, MGStep, CGStep, AGStep
  <2> QED BY <1>1, <2>1 DEF Inv, Basic, S1, S2, S3, MG, CG, AG
<1>5. CASE UNCHANGED rvars
  <2>1. UNCHANGED vars BY <1>5 DEF rvars
  <2> QED BY <1>0, <1>3, <1>5, <2>1, RUnch DEF II
<1>6. CASE ProtoCases /\ UNCHANGED read
  BY <1>0, <1>4, <1>6, RProto DEF II
<1>7. CASE ReadCases /\ UNCHANGED vars
  <2>1. ReadSafeP BY <1>0, ReadSafe
  <2> QED BY <1>0, <1>3, <1>7, <2>1, RRead DEF II
<1> QED BY <1>2, <1>5, <1>6, <1>7, NextCasesR

\* ---- The properties, from the invariant.
LEMMA LogMatchingInv == ASSUME Inv PROVE LogMatching
<1>1. TypeOK /\ LogFromLed BY DEF Inv
<1> SUFFICES ASSUME NEW a \in Server, NEW b \in Server, NEW k \in 1..Min(Len(log[a]), Len(log[b])),
                    log[a][k].term = log[b][k].term
             PROVE SubSeq(log[a], 1, k) = SubSeq(log[b], 1, k)
  BY DEF LogMatching
<1>2. log[a] \in Seq(EntryT) /\ log[b] \in Seq(EntryT) BY <1>1 DEF TypeOK
<1>3. k \in 1..Len(log[a]) /\ k \in 1..Len(log[b]) /\ k \in Nat BY <1>2 DEF Min
<1> DEFINE t == log[a][k].term
<1>4. Agree(log[a], ledLog[t], k) BY <1>1, <1>3 DEF LogFromLed, FromLed
<1>5. Agree(log[b], ledLog[t], k) BY <1>1, <1>3 DEF LogFromLed, FromLed
<1>6. Agree(log[a], log[b], k) BY <1>4, <1>5, <1>3 DEF Agree
<1> QED BY <1>2, <1>3, <1>6, SubSeqAgree

LEMMA CommitSafetyInv == ASSUME Inv PROVE CommitSafety
<1>1. TypeOK /\ CommitSafetyP BY DEF Inv
<1> SUFFICES ASSUME NEW a \in commits, NEW b \in commits
             PROVE IsPrefix(a.entries, b.entries) \/ IsPrefix(b.entries, a.entries)
  BY DEF CommitSafety
<1>2. a.entries \in Seq(EntryT) /\ b.entries \in Seq(EntryT) BY <1>1 DEF TypeOK, CommitT
<1>3. Pre(a.entries, b.entries) \/ Pre(b.entries, a.entries) BY <1>1 DEF CommitSafetyP
<1> QED BY <1>2, <1>3, IsPrefixPre

LEMMA StateMachineSafetyInv == ASSUME Inv PROVE StateMachineSafety
<1>1. TypeOK /\ CommitSafetyP /\ AppliedCommitted BY DEF Inv
<1> SUFFICES ASSUME NEW a \in applied, NEW b \in applied, a.index = b.index
             PROVE a.entry = b.entry
  BY DEF StateMachineSafety
<1>2. PICK ka \in commits : 1 <= a.index /\ a.index <= Len(ka.entries) /\ ka.entries[a.index] = a.entry
  BY <1>1 DEF AppliedCommitted
<1>3. PICK kb \in commits : 1 <= b.index /\ b.index <= Len(kb.entries) /\ kb.entries[b.index] = b.entry
  BY <1>1 DEF AppliedCommitted
<1>4. ka.entries \in Seq(EntryT) /\ kb.entries \in Seq(EntryT) /\ a.index \in Nat
  BY <1>1 DEF TypeOK, CommitT, AppliedT
<1>5. Pre(ka.entries, kb.entries) \/ Pre(kb.entries, ka.entries) BY <1>1 DEF CommitSafetyP
<1> QED BY <1>2, <1>3, <1>4, <1>5 DEF Pre, Agree

LEMMA LeaderCompletenessInv == ASSUME Inv PROVE LeaderCompleteness
<1>1. TypeOK /\ CommitRoot BY DEF Inv
<1>2. LC BY LCThm
<1> SUFFICES ASSUME NEW t \in DOMAIN ledLog, NEW c \in commits, c.term < t
             PROVE IsPrefix(c.entries, ledLog[t])
  BY DEF LeaderCompleteness
<1>3. PICK r \in commits : Pre(c.entries, r.entries) /\ Root(r) /\ r.term <= c.term
  BY <1>1 DEF CommitRoot
<1>4. /\ r.term \in DOMAIN ledLog /\ Pre(r.entries, ledLog[r.term])
      /\ \E d \in 0..Len(ledLog[r.term]) : MRoot(r.term, Len(r.entries), d)
  BY <1>3 DEF Root
<1>5. PICK d \in 0..Len(ledLog[r.term]) : MRoot(r.term, Len(r.entries), d) BY <1>4
<1>6. /\ c.entries \in Seq(EntryT) /\ r.entries \in Seq(EntryT) /\ ledLog[t] \in Seq(EntryT)
      /\ ledLog[r.term] \in Seq(EntryT) /\ c.term \in Nat /\ r.term \in Nat /\ t \in Nat
  BY <1>1, <1>4 DEF TypeOK, CommitT
<1>7. Len(r.entries) \in 1..Len(ledLog[r.term]) BY <1>5, <1>6 DEF MRoot, Good
<1>8. r.term < t BY <1>3, <1>6
<1>9. Agree(ledLog[r.term], ledLog[t], Len(r.entries)) BY <1>2, <1>4, <1>5, <1>7, <1>8 DEF LC
<1>10. Pre(c.entries, ledLog[t]) BY <1>3, <1>4, <1>6, <1>9 DEF Pre, Agree
<1> QED BY <1>6, <1>10, IsPrefixPre

LEMMA ReadIndexSafetyInv == ASSUME II PROVE ReadIndexSafety
BY DEF II, RInv

\* ---- The theorems.
\* ConstOK == IsFiniteSet(Server) /\ InitVoters \subseteq Server: it follows from
\* the spec's assumptions ServerFinite and VotersOK.
THEOREM ConstOKHolds == ConstOK
BY ServerFinite, VotersOK DEF ConstOK

THEOREM IIAlways == Spec => []II
<1>1. Init => II BY IIInit, ConstOKHolds
<1>2. II /\ [Next]_rvars => II' BY IIStep
<1> QED BY <1>1, <1>2, PTL DEF Spec

THEOREM ElectionSafetyThm == Spec => []ElectionSafety
<1>1. II => ElectionSafety BY DEF II, Inv
<1> QED BY <1>1, IIAlways, PTL

THEOREM LogMatchingThm == Spec => []LogMatching
<1>1. II => LogMatching BY LogMatchingInv DEF II
<1> QED BY <1>1, IIAlways, PTL

THEOREM CommitSafetyThm == Spec => []CommitSafety
<1>1. II => CommitSafety BY CommitSafetyInv DEF II
<1> QED BY <1>1, IIAlways, PTL

THEOREM StateMachineSafetyThm == Spec => []StateMachineSafety
<1>1. II => StateMachineSafety BY StateMachineSafetyInv DEF II
<1> QED BY <1>1, IIAlways, PTL

THEOREM LeaderCompletenessThm == Spec => []LeaderCompleteness
<1>1. II => LeaderCompleteness BY LeaderCompletenessInv DEF II
<1> QED BY <1>1, IIAlways, PTL

THEOREM ReadIndexSafetyThm == Spec => []ReadIndexSafety
<1>1. II => ReadIndexSafety BY ReadIndexSafetyInv
<1> QED BY <1>1, IIAlways, PTL
====
