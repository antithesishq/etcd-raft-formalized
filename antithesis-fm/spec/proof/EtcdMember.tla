---- MODULE EtcdMember ----
\* Invariants about configurations: ConfIsCommitted, LeaderConfS, LedOld, LegalChain.
EXTENDS EtcdSimple3

MG == ConfIsCommitted /\ LeaderConfS /\ LedOld /\ LegalChain

LEMMA InvParts == ASSUME Inv PROVE Basic /\ S1 /\ S2 /\ S3 /\ MG /\ CommitSafetyP
BY DEF Inv, Basic, S1, S2, S3, MG

LEMMA MGInit == ASSUME Init PROVE MG
BY DEF Init, MG, ConfIsCommitted, LeaderConfS, LedOld, LegalChain

LEMMA MGUnch == ASSUME MG, UNCHANGED vars PROVE MG'
BY DEF vars, protoVars, durable, MG, ConfIsCommitted, LeaderConfS, LedOld, LegalChain,
       AtMostOne, Cover, CoverLt, Agree

LEMMA ConfsAfterOne ==
  ASSUME NEW l \in Seq(EntryT), NEW a \in Nat, Cardinality(ConfsAfter(l, a)) <= 1
  PROVE  AtMostOne(l, a, Len(l))
<1> DEFINE S == ConfsAfter(l, a)
<1>1. S \subseteq (a + 1)..Len(l) BY DEF ConfsAfter
<1>2. IsFiniteSet((a + 1)..Len(l)) BY FS_Interval
<1>3. IsFiniteSet(S) BY <1>1, <1>2, FS_Subset
<1> SUFFICES ASSUME NEW p \in (a + 1)..Len(l), NEW q \in (a + 1)..Len(l), p < q, IsConf(l[p]), IsConf(l[q])
             PROVE FALSE
  BY DEF AtMostOne
<1>4. p \in S /\ q \in S BY DEF ConfsAfter
<1>5. IsFiniteSet({p}) /\ Cardinality({p}) = 1 BY FS_Singleton
<1>6. Cardinality({p} \cup {q}) = 2 /\ IsFiniteSet({p} \cup {q}) BY <1>5, FS_AddElement
<1>7. {p} \cup {q} \subseteq S BY <1>4
<1>8. Cardinality({p} \cup {q}) <= Cardinality(S) BY <1>3, <1>7, FS_Subset
<1>9. Cardinality(S) \in Nat BY <1>3, FS_CardinalityType
<1> QED BY <1>6, <1>8, <1>9

\* A candidate that may lead counts with the configuration its own log makes.
LEMMA CandConf ==
  ASSUME TypeOK, ConfIsCommitted, CommitSafetyP, NEW i \in Server,
         CommittedBefore(log[i], confAt[i], currentTerm[i])
  PROVE  /\ confAt[i] <= Len(log[i])
         /\ config[i] = ConfOf(log[i], confAt[i])
         /\ CoverLt(log[i], confAt[i], currentTerm[i])
<1> DEFINE a == confAt[i]  l == log[i]
<1>1. a \in Nat /\ l \in Seq(EntryT) BY DEF TypeOK
<1>2. CASE a = 0
  <2>1. config[i] = InitConf
    <3>1. CASE config[i] = InitConf BY <3>1
    <3>2. CASE \E c \in commits : config[i] = ConfOf(c.entries, a) BY <3>2, <1>2, ConfOf0
    <3> QED BY <3>1, <3>2 DEF ConfIsCommitted
  <2> QED BY <2>1, <1>1, <1>2, ConfOf0 DEF CoverLt
<1>3. CASE a # 0
  <2>1. a <= Len(l) BY <1>3 DEF CommittedBefore
  <2>2. PICK k \in commits : k.term < currentTerm[i] /\ a <= Len(k.entries) /\ SubSeq(k.entries, 1, a) = SubSeq(l, 1, a)
    BY <1>3 DEF CommittedBefore
  <2>3. k.entries \in Seq(EntryT) BY DEF TypeOK, CommitT
  <2>4. Agree(k.entries, l, a) BY <2>1, <2>2, <2>3, <1>1, SubSeqAgree
  <2>5. PICK c \in commits : a <= Len(c.entries) /\ config[i] = ConfOf(c.entries, a)
    BY <1>3 DEF ConfIsCommitted
  <2>6. c.entries \in Seq(EntryT) BY DEF TypeOK, CommitT
  <2>7. Pre(c.entries, k.entries) \/ Pre(k.entries, c.entries) BY DEF CommitSafetyP
  <2>8. \A q \in 1..a : c.entries[q] = l[q] BY <2>4, <2>5, <2>7, <2>3, <2>6, <1>1 DEF Pre, Agree
  <2>9. ConfOf(c.entries, a) = ConfOf(l, a) BY <2>8, <1>1, ConfOfCongr
  <2> QED BY <2>1, <2>2, <2>4, <2>5, <2>9 DEF CoverLt
<1> QED BY <1>2, <1>3

\* ---- ConfIsCommitted
LEMMA ConfIsCommittedKeep ==
  ASSUME ConfIsCommitted, UNCHANGED <<config, confAt>>, commits \subseteq commits'
  PROVE  ConfIsCommitted'
BY DEF ConfIsCommitted

LEMMA ConfIsCommittedStep ==
  ASSUME Inv, ProtoCases
  PROVE  ConfIsCommitted'
<1>B. Basic /\ S1 /\ S2 /\ S3 /\ MG /\ CommitSafetyP BY InvParts
<1>G. Grows BY <1>B, GrowsStep
<1>T. TypeOK BY <1>B DEF Basic
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE ConfIsCommitted'
  BY <1>a, <1>B, <1>G, ConfIsCommittedKeep DEF BecomeCandidate, durable, MG, Grows
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE ConfIsCommitted'
  BY <1>b, <1>B, <1>G, ConfIsCommittedKeep DEF BecomeFollower, durable, MG, Grows
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE ConfIsCommitted'
  BY <1>c, <1>B, <1>G, ConfIsCommittedKeep DEF BecomeLeader, durable, MG, Grows
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE ConfIsCommitted'
  BY <1>d, <1>B, <1>G, ConfIsCommittedKeep DEF StartElection, durable, MG, Grows
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE ConfIsCommitted'
  <2>1. config' = [config EXCEPT ![i] = InitConf] /\ confAt' = [confAt EXCEPT ![i] = 0] /\ UNCHANGED commits
    BY <1>e DEF Restart
  <2>2. config \in [Server -> ConfT] /\ confAt \in [Server -> Nat] BY <1>T DEF TypeOK
  <2> QED BY <2>1, <2>2, <1>B DEF MG, ConfIsCommitted
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE ConfIsCommitted'
  BY <1>f, <1>B, <1>G, ConfIsCommittedKeep DEF Apply, durable, MG, Grows
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE ConfIsCommitted'
  BY <1>g, <1>B, <1>G, ConfIsCommittedKeep DEF Restore, durable, MG, Grows
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE ConfIsCommitted'
  <2> DEFINE a == confAt[i]  l == log[i]
  <2>1. /\ k > a /\ IsCommitted(l, k) /\ IsConf(l[k])
        /\ \A q \in (a + 1)..(k - 1) : ~IsConf(l[q])
        /\ config' = [config EXCEPT ![i] = NextConf(config[i], l[k].value)]
        /\ confAt' = [confAt EXCEPT ![i] = k] /\ UNCHANGED commits
    BY <1>h DEF SwitchConf
  <2>2. config \in [Server -> ConfT] /\ confAt \in [Server -> Nat] /\ l \in Seq(EntryT) /\ a \in Nat
    BY <1>T DEF TypeOK
  <2>3. PICK c \in commits : k <= Len(c.entries) /\ SubSeq(c.entries, 1, k) = SubSeq(l, 1, k)
    BY <2>1 DEF IsCommitted
  <2>4. c.entries \in Seq(EntryT) BY <1>T DEF TypeOK, CommitT
  <2>5. Agree(c.entries, l, k) BY <2>3, <2>4, <2>2, SubSeqAgree
  <2>6. ConfOf(c.entries, a) = config[i]
    <3>1. CASE a = 0
      <4>1. config[i] = InitConf
        <5>1. CASE config[i] = InitConf BY <5>1
        <5>2. CASE \E c0 \in commits : config[i] = ConfOf(c0.entries, a) BY <5>2, <3>1, ConfOf0
        <5> QED BY <5>1, <5>2, <1>B DEF MG, ConfIsCommitted
      <4> QED BY <4>1, <3>1, ConfOf0
    <3>2. CASE a # 0
      <4>1. PICK c0 \in commits : a <= Len(c0.entries) /\ config[i] = ConfOf(c0.entries, a)
        BY <3>2, <1>B DEF MG, ConfIsCommitted
      <4>2. c0.entries \in Seq(EntryT) BY <1>T DEF TypeOK, CommitT
      <4>3. Pre(c0.entries, c.entries) \/ Pre(c.entries, c0.entries) BY <1>B DEF CommitSafetyP
      <4>4. \A q \in 1..a : c0.entries[q] = c.entries[q] BY <4>1, <4>2, <4>3, <2>4, <2>3, <2>2, <2>1 DEF Pre, Agree
      <4> QED BY <4>1, <4>4, <2>2, ConfOfCongr
    <3> QED BY <3>1, <3>2
  <2>7. \A q \in (a + 1)..(k - 1) : ~IsConf(c.entries[q]) BY <2>1, <2>2, <2>5 DEF Agree
  <2>8. ConfOf(c.entries, k - 1) = ConfOf(c.entries, a) BY <2>7, <2>1, <2>2, ConfOfSkip
  <2>9. c.entries[k] = l[k] BY <2>5, <2>1, <2>2 DEF Agree
  <2>10. ConfOf(c.entries, k) = NextConf(ConfOf(c.entries, k - 1), c.entries[k].value)
    BY <2>9, <2>1, <2>2, ConfOfStep
  <2>11. confAt'[i] <= Len(c.entries) /\ config'[i] = ConfOf(c.entries, confAt'[i])
    BY <2>1, <2>2, <2>3, <2>6, <2>8, <2>9, <2>10
  <2>12. \A s \in Server : s # i => config'[s] = config[s] /\ confAt'[s] = confAt[s] BY <2>1, <2>2
  <2> HIDE DEF a, l
  <2> QED BY <2>1, <2>11, <2>12, <1>B DEF MG, ConfIsCommitted
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE ConfIsCommitted'
  <2>1. /\ config' = [config EXCEPT ![i] = ConfOf(c.entries, a)]
        /\ confAt' = [confAt EXCEPT ![i] = LastConf(c.entries, a)] /\ UNCHANGED commits
    BY <1>i DEF RestoreConf
  <2>2. config \in [Server -> ConfT] /\ confAt \in [Server -> Nat] BY <1>T DEF TypeOK
  <2>3. c.entries \in Seq(EntryT) /\ a \in Nat /\ a <= Len(c.entries) BY <1>T DEF TypeOK, CommitT
  <2>4. LastConf(c.entries, a) \in 0..a /\ ConfOf(c.entries, LastConf(c.entries, a)) = ConfOf(c.entries, a)
    BY <2>3, LastConfFacts, ConfOfLastConf
  <2>5. confAt'[i] <= Len(c.entries) /\ config'[i] = ConfOf(c.entries, confAt'[i]) BY <2>1, <2>2, <2>3, <2>4
  <2>6. \A s \in Server : s # i => config'[s] = config[s] /\ confAt'[s] = confAt[s] BY <2>1, <2>2
  <2> QED BY <2>1, <2>5, <2>6, <1>B DEF MG, ConfIsCommitted
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE ConfIsCommitted'
  BY <1>j, <1>B, <1>G, ConfIsCommittedKeep DEF LeaderAppend1, durable, MG, Grows
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE ConfIsCommitted'
  BY <1>k, <1>B, <1>G, ConfIsCommittedKeep DEF AdoptTerm, durable, MG, Grows
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE ConfIsCommitted'
  BY <1>l, <1>B, <1>G, ConfIsCommittedKeep DEF CastVote, durable, MG, Grows
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE ConfIsCommitted'
  BY <1>m, <1>B, <1>G, ConfIsCommittedKeep DEF GrantVote, durable, MG, Grows
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE ConfIsCommitted'
  BY <1>n, <1>B, <1>G, ConfIsCommittedKeep DEF LeaderCommit, durable, MG, Grows
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE ConfIsCommitted'
  BY <1>o, <1>B, <1>G, ConfIsCommittedKeep DEF SendAppend, durable, MG, Grows
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE ConfIsCommitted'
  BY <1>p, <1>B, <1>G, ConfIsCommittedKeep DEF Ack, durable, MG, Grows
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE ConfIsCommitted'
  BY <1>q, <1>B, <1>G, ConfIsCommittedKeep DEF AckCommitted, durable, MG, Grows
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE ConfIsCommitted'
  BY <1>r, <1>B, <1>G, ConfIsCommittedKeep DEF DeleteSuffix, durable, MG, Grows
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE ConfIsCommitted'
  BY <1>s, <1>B, <1>G, ConfIsCommittedKeep DEF StoreEntries, durable, MG, Grows
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE ConfIsCommitted'
  BY <1>t, <1>B, <1>G, ConfIsCommittedKeep DEF FollowerCommit, durable, MG, Grows
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases


\* ---- LeaderConfS
\* One term's part of LeaderConfS, with everything it speaks of as a parameter.
CovK(K, l, d, t) == d = 0 \/ \E k \in K : k.term <= t /\ Agree(k.entries, l, d)
CovLtK(K, l, d, t) == d = 0 \/ \E k \in K : k.term < t /\ Agree(k.entries, l, d)
LCS2(t, LL, cf, la, ea, K) ==
    /\ ea <= la /\ la <= Len(LL)
    /\ cf = ConfOf(LL, la)
    /\ AtMostOne(LL, la, Len(LL))
    /\ CovK(K, LL, la, t)
    /\ CovLtK(K, LL, ea, t)
LCS(t) == LCS2(t, ledLog[t], ledConf[t], ledAt[t], elAt[t], commits)

LEMMA LCSDef == LeaderConfS <=> \A t \in DOMAIN ledLog : LCS(t)
BY DEF LeaderConfS, LCS, LCS2, Cover, CoverLt, CovK, CovLtK

LEMMA LCSDef2 ==
  LeaderConfS' <=> \A t \in DOMAIN ledLog' : LCS2(t, ledLog'[t], ledConf'[t], ledAt'[t], elAt'[t], commits')
BY DEF LeaderConfS, LCS2, Cover, CoverLt, CovK, CovLtK

LEMMA LCSSame ==
  ASSUME NEW t \in DOMAIN ledLog, LCS(t), commits \subseteq commits',
         ledLog'[t] = ledLog[t], ledConf'[t] = ledConf[t], ledAt'[t] = ledAt[t], elAt'[t] = elAt[t]
  PROVE  LCS2(t, ledLog'[t], ledConf'[t], ledAt'[t], elAt'[t], commits')
BY DEF LCS, LCS2, CovK, CovLtK

LEMMA LeaderConfSKeep ==
  ASSUME LeaderConfS, UNCHANGED <<ledLog, ledConf, ledAt, elAt>>, commits \subseteq commits'
  PROVE  LeaderConfS'
BY DEF LeaderConfS, Cover, CoverLt

LEMMA LeaderConfSStep ==
  ASSUME Inv, ProtoCases
  PROVE  LeaderConfS'
<1>B. Basic /\ S1 /\ S2 /\ S3 /\ MG /\ CommitSafetyP BY InvParts
<1>G. Grows BY <1>B, GrowsStep
<1>T. TypeOK BY <1>B DEF Basic
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE LeaderConfS'
  BY <1>a, <1>B, <1>G, LeaderConfSKeep DEF BecomeCandidate, durable, MG, Grows
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE LeaderConfS'
  BY <1>b, <1>B, <1>G, LeaderConfSKeep DEF BecomeFollower, durable, MG, Grows
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE LeaderConfS'
  <2> DEFINE u == currentTerm[i]
  <2>1. /\ u \notin DOMAIN ledLog /\ DOMAIN ledLog' = DOMAIN ledLog \cup {u}
        /\ ledLog'[u] = log[i] /\ elAt'[u] = confAt[i] /\ ledAt'[u] = confAt[i] /\ ledConf'[u] = config[i]
        /\ \A t \in DOMAIN ledLog : /\ ledLog'[t] = ledLog[t] /\ elAt'[t] = elAt[t]
                                    /\ ledAt'[t] = ledAt[t] /\ ledConf'[t] = ledConf[t]
        /\ UNCHANGED commits
    BY <1>c, <1>B, BecomeLeaderLed
  <2>2. OneWaiting(i, log[i]) /\ CommittedBefore(log[i], confAt[i], u) BY <1>c DEF BecomeLeader
  <2>3. /\ confAt[i] <= Len(log[i]) /\ config[i] = ConfOf(log[i], confAt[i]) /\ CoverLt(log[i], confAt[i], u)
    BY <2>2, <1>T, <1>B, CandConf DEF MG
  <2>4. log[i] \in Seq(EntryT) /\ confAt[i] \in Nat /\ u \in Nat BY <1>T DEF TypeOK
  <2>5. AtMostOne(log[i], confAt[i], Len(log[i])) BY <2>2, <2>4, ConfsAfterOne DEF OneWaiting
  <2>6. CovLtK(commits, log[i], confAt[i], u) /\ CovK(commits, log[i], confAt[i], u)
    <3>1. \A kk \in commits : kk.term \in Nat BY <1>T DEF TypeOK, CommitT
    <3> QED BY <2>3, <2>4, <3>1 DEF CoverLt, CovK, CovLtK
  <2> HIDE DEF u
  <2>7. LCS2(u, ledLog'[u], ledConf'[u], ledAt'[u], elAt'[u], commits')
    BY <2>1, <2>3, <2>4, <2>5, <2>6 DEF LCS2
  <2>8. ASSUME NEW t \in DOMAIN ledLog PROVE LCS2(t, ledLog'[t], ledConf'[t], ledAt'[t], elAt'[t], commits')
    <3>1. LCS(t) BY <1>B, LCSDef DEF MG
    <3> QED BY <3>1, <2>1, LCSSame
  <2> QED BY <2>1, <2>7, <2>8, LCSDef2
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE LeaderConfS'
  BY <1>d, <1>B, <1>G, LeaderConfSKeep DEF StartElection, durable, MG, Grows
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE LeaderConfS'
  BY <1>e, <1>B, <1>G, LeaderConfSKeep DEF Restart, durable, MG, Grows
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE LeaderConfS'
  BY <1>f, <1>B, <1>G, LeaderConfSKeep DEF Apply, durable, MG, Grows
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE LeaderConfS'
  BY <1>g, <1>B, <1>G, LeaderConfSKeep DEF Restore, durable, MG, Grows
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE LeaderConfS'
  <2>1. CASE role[i] # Leader
    BY <2>1, <1>h, <1>B, LeaderConfSKeep DEF SwitchConf, MG
  <2>2. CASE role[i] = Leader
    <3> DEFINE u == currentTerm[i]  LL == ledLog[u]  l == log[i]  a == confAt[i]
               C == NextConf(config[i], l[k].value)
    <3>1. /\ k > a /\ IsConf(l[k]) /\ LeaderKnows(i, k)
          /\ \A q \in (a + 1)..(k - 1) : ~IsConf(l[q])
          /\ ledConf' = WithConf(u, C) /\ ledAt' = With(ledAt, u, k)
          /\ UNCHANGED <<ledLog, elAt, commits>>
      BY <2>2, <1>h DEF SwitchConf, durable
    <3>2. IsLd(i, u) /\ u \in DOMAIN ledLog BY <2>2, <1>B DEF Basic, LeaderIsElected, LedDom, IsLd
    <3>3. Pre(l, LL) BY <3>2, <1>B DEF S2, LedOwner, IsLd
    <3>4. a = ledAt[u] /\ config[i] = ledConf[u] BY <2>2, <1>B DEF S3, LeaderSync
    <3>5. LCS2(u, LL, ledConf[u], ledAt[u], elAt[u], commits) BY <3>2, <1>B, LCSDef DEF MG, LCS
    <3>6. l \in Seq(EntryT) /\ LL \in Seq(EntryT) /\ a \in Nat /\ elAt[u] \in Nat /\ u \in Nat
          /\ DOMAIN ledConf = DOMAIN ledLog /\ DOMAIN ledAt = DOMAIN ledLog
      BY <3>2, <1>T DEF TypeOK
    <3>7. k <= Len(LL) /\ \A q \in 1..k : LL[q] = l[q] BY <3>3, <3>6 DEF Pre, Agree
    <3>8. ConfOf(LL, k - 1) = ConfOf(LL, a)
      <4>1. \A q \in (a + 1)..(k - 1) : ~IsConf(LL[q]) BY <3>1, <3>6, <3>7
      <4> QED BY <4>1, <3>1, <3>6, ConfOfSkip
    <3>9. ConfOf(LL, k) = NextConf(ConfOf(LL, k - 1), LL[k].value) BY <3>1, <3>6, <3>7, ConfOfStep
    <3>10. C = ConfOf(LL, k) BY <3>4, <3>5, <3>7, <3>8, <3>9 DEF LCS2
    <3>11. AtMostOne(LL, k, Len(LL)) BY <3>1, <3>4, <3>5, <3>6 DEF LCS2, AtMostOne
    <3>12. CovK(commits, LL, k, u)
      <4>1. PICK kk \in commits : kk.term <= u /\ k <= Len(kk.entries) /\ SubSeq(kk.entries, 1, k) = SubSeq(l, 1, k)
        BY <3>1 DEF LeaderKnows, CommittedIn, KnownIn
      <4>2. kk.entries \in Seq(EntryT) BY <1>T DEF TypeOK, CommitT
      <4>3. Agree(kk.entries, l, k) BY <4>1, <4>2, <3>6, SubSeqAgree
      <4>4. Agree(kk.entries, LL, k) BY <4>3, <3>7 DEF Agree
      <4> QED BY <4>1, <4>4 DEF CovK
    <3>13. ledConf'[u] = C /\ ledAt'[u] = k
           /\ \A t \in DOMAIN ledLog : t # u => ledConf'[t] = ledConf[t] /\ ledAt'[t] = ledAt[t]
      BY <3>1, <3>2, <3>6 DEF WithConf, With
    <3> HIDE DEF C
    <3>14. LCS2(u, LL, C, k, elAt[u], commits)
      BY <3>1, <3>4, <3>5, <3>6, <3>7, <3>10, <3>11, <3>12 DEF LCS2
    <3>15. ASSUME NEW t \in DOMAIN ledLog, t # u PROVE LCS2(t, ledLog'[t], ledConf'[t], ledAt'[t], elAt'[t], commits')
      <4>1. LCS(t) BY <1>B, LCSDef DEF MG
      <4> QED BY <4>1, <3>1, <3>13, <3>15, LCSSame
    <3>16. LCS2(u, ledLog'[u], ledConf'[u], ledAt'[u], elAt'[u], commits') BY <3>1, <3>13, <3>14
    <3> HIDE DEF u, LL, l, a
    <3> QED BY <3>1, <3>15, <3>16, LCSDef2
  <2> QED BY <2>1, <2>2
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE LeaderConfS'
  BY <1>i, <1>B, <1>G, LeaderConfSKeep DEF RestoreConf, durable, MG, Grows
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE LeaderConfS'
  <2> DEFINE u == currentTerm[i]  LL == ledLog[u]  L2 == ledLog'[u]
  <2>1. /\ u \in DOMAIN ledLog /\ e.term = u /\ role[i] = Leader /\ DOMAIN ledLog' = DOMAIN ledLog
        /\ LL \in Seq(EntryT) /\ L2 \in Seq(EntryT) /\ Len(L2) = Len(LL) + 1 /\ L2[Len(LL) + 1] = e
        /\ \A q \in 1..Len(LL) : L2[q] = LL[q]
        /\ \A t \in DOMAIN ledLog : t # u => ledLog'[t] = ledLog[t]
        /\ (IsConf(e) => AllSwitched(i, LL) /\ Legal(config[i], e.value))
        /\ UNCHANGED <<ledConf, ledAt, elAt, commits>>
    BY <1>j, <1>B, AppendLed
  <2>2. LCS2(u, LL, ledConf[u], ledAt[u], elAt[u], commits) BY <2>1, <1>B, LCSDef DEF MG, LCS
  <2>3. ledAt[u] \in Nat /\ elAt[u] \in Nat BY <2>1, <1>T DEF TypeOK
  <2>4. confAt[i] = ledAt[u] BY <2>1, <1>B DEF S3, LeaderSync
  <2>5. ConfOf(L2, ledAt[u]) = ConfOf(LL, ledAt[u]) BY <2>1, <2>2, <2>3, ConfOfCongr DEF LCS2
  <2>6. AtMostOne(L2, ledAt[u], Len(L2))
    <3>1. AtMostOne(LL, ledAt[u], Len(LL)) BY <2>2 DEF LCS2
    <3>2. IsConf(e) => \A q \in (ledAt[u] + 1)..Len(LL) : ~IsConf(LL[q])
      BY <2>1, <2>4 DEF AllSwitched, ConfsAfter
    <3> QED BY <3>1, <3>2, <2>1, <2>2, <2>3 DEF AtMostOne, LCS2
  <2>7. CovK(commits, L2, ledAt[u], u) /\ CovLtK(commits, L2, elAt[u], u)
    <3>1. \A kk \in commits : \A d \in Nat : d <= Len(LL) /\ Agree(kk.entries, LL, d) => Agree(kk.entries, L2, d)
      BY <2>1 DEF Agree
    <3>2. elAt[u] <= ledAt[u] /\ ledAt[u] <= Len(LL) /\ CovK(commits, LL, ledAt[u], u) /\ CovLtK(commits, LL, elAt[u], u)
      BY <2>2 DEF LCS2
    <3>3. CovK(commits, L2, ledAt[u], u)
      <4>1. CASE ledAt[u] = 0 BY <4>1 DEF CovK
      <4>2. CASE ledAt[u] # 0
        <5>1. PICK kk \in commits : kk.term <= u /\ Agree(kk.entries, LL, ledAt[u]) BY <4>2, <3>2 DEF CovK
        <5>2. Agree(kk.entries, L2, ledAt[u]) BY <5>1, <3>1, <3>2, <2>3
        <5> QED BY <5>1, <5>2 DEF CovK
      <4> QED BY <4>1, <4>2
    <3>4. CovLtK(commits, L2, elAt[u], u)
      <4>1. CASE elAt[u] = 0 BY <4>1 DEF CovLtK
      <4>2. CASE elAt[u] # 0
        <5>1. PICK kk \in commits : kk.term < u /\ Agree(kk.entries, LL, elAt[u]) BY <4>2, <3>2 DEF CovLtK
        <5>2. elAt[u] <= Len(LL) BY <3>2, <2>3, <2>1
        <5>3. Agree(kk.entries, L2, elAt[u]) BY <5>1, <5>2, <3>1, <2>3
        <5> QED BY <5>1, <5>3 DEF CovLtK
      <4> QED BY <4>1, <4>2
    <3> QED BY <3>3, <3>4
  <2>8. LCS2(u, L2, ledConf[u], ledAt[u], elAt[u], commits)
    BY <2>1, <2>2, <2>3, <2>5, <2>6, <2>7 DEF LCS2
  <2>9. ASSUME NEW t \in DOMAIN ledLog, t # u PROVE LCS2(t, ledLog'[t], ledConf'[t], ledAt'[t], elAt'[t], commits')
    <3>1. LCS(t) BY <1>B, LCSDef DEF MG
    <3> QED BY <3>1, <2>1, <2>9, LCSSame
  <2>10. LCS2(u, ledLog'[u], ledConf'[u], ledAt'[u], elAt'[u], commits') BY <2>1, <2>8
  <2> HIDE DEF u, LL, L2
  <2> QED BY <2>1, <2>9, <2>10, LCSDef2
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE LeaderConfS'
  BY <1>k, <1>B, <1>G, LeaderConfSKeep DEF AdoptTerm, durable, MG, Grows
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE LeaderConfS'
  BY <1>l, <1>B, <1>G, LeaderConfSKeep DEF CastVote, durable, MG, Grows
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE LeaderConfS'
  BY <1>m, <1>B, <1>G, LeaderConfSKeep DEF GrantVote, durable, MG, Grows
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE LeaderConfS'
  BY <1>n, <1>B, <1>G, LeaderConfSKeep DEF LeaderCommit, durable, MG, Grows
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE LeaderConfS'
  BY <1>o, <1>B, <1>G, LeaderConfSKeep DEF SendAppend, durable, MG, Grows
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE LeaderConfS'
  BY <1>p, <1>B, <1>G, LeaderConfSKeep DEF Ack, durable, MG, Grows
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE LeaderConfS'
  BY <1>q, <1>B, <1>G, LeaderConfSKeep DEF AckCommitted, durable, MG, Grows
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE LeaderConfS'
  BY <1>r, <1>B, <1>G, LeaderConfSKeep DEF DeleteSuffix, durable, MG, Grows
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE LeaderConfS'
  BY <1>s, <1>B, <1>G, LeaderConfSKeep DEF StoreEntries, durable, MG, Grows
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE LeaderConfS'
  BY <1>t, <1>B, <1>G, LeaderConfSKeep DEF FollowerCommit, durable, MG, Grows
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases


\* ---- LedOld
LEMMA LedOldStep ==
  ASSUME Inv, ProtoCases
  PROVE  LedOld'
<1>B. Basic /\ S1 /\ S2 /\ S3 /\ MG /\ CommitSafetyP BY InvParts
<1>G. Grows BY <1>B, GrowsStep
<1>T. TypeOK BY <1>B DEF Basic
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE LedOld'
  BY <1>a, <1>B DEF BecomeCandidate, durable, MG, LedOld
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE LedOld'
  BY <1>b, <1>B DEF BecomeFollower, durable, MG, LedOld
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE LedOld'
  <2> DEFINE u == currentTerm[i]
  <2>1. /\ u \notin DOMAIN ledLog /\ DOMAIN ledLog' = DOMAIN ledLog \cup {u}
        /\ ledLog'[u] = log[i] /\ elAt'[u] = confAt[i]
        /\ \A t \in DOMAIN ledLog : ledLog'[t] = ledLog[t] /\ elAt'[t] = elAt[t]
    BY <1>c, <1>B, BecomeLeaderLed
  <2>2. OneWaiting(i, log[i]) BY <1>c DEF BecomeLeader
  <2>4. log[i] \in Seq(EntryT) /\ confAt[i] \in Nat BY <1>T DEF TypeOK
  <2>5. AtMostOne(log[i], confAt[i], Len(log[i])) BY <2>2, <2>4, ConfsAfterOne DEF OneWaiting
  <2> HIDE DEF u
  <2> QED BY <2>1, <2>5, <1>B DEF MG, LedOld, AtMostOne
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE LedOld'
  BY <1>d, <1>B DEF StartElection, durable, MG, LedOld
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE LedOld'
  BY <1>e, <1>B DEF Restart, durable, MG, LedOld
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE LedOld'
  BY <1>f, <1>B DEF Apply, durable, MG, LedOld
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE LedOld'
  BY <1>g, <1>B DEF Restore, durable, MG, LedOld
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE LedOld'
  BY <1>h, <1>B DEF SwitchConf, durable, MG, LedOld
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE LedOld'
  BY <1>i, <1>B DEF RestoreConf, durable, MG, LedOld
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE LedOld'
  <2> DEFINE u == currentTerm[i]  L == ledLog[u]  L2 == ledLog'[u]
  <2>1. /\ u \in DOMAIN ledLog /\ e.term = u /\ DOMAIN ledLog' = DOMAIN ledLog
        /\ L \in Seq(EntryT) /\ L2 \in Seq(EntryT) /\ Len(L2) = Len(L) + 1 /\ L2[Len(L) + 1] = e
        /\ \A q \in 1..Len(L) : L2[q] = L[q]
        /\ \A t \in DOMAIN ledLog : t # u => ledLog'[t] = ledLog[t]
        /\ UNCHANGED elAt
    BY <1>j, <1>B, AppendLed
  <2>2. u \in Nat /\ elAt[u] \in Nat BY <2>1, <1>T DEF TypeOK
  <2> SUFFICES ASSUME NEW w \in DOMAIN ledLog, NEW p \in (elAt[w] + 1)..Len(ledLog'[w]), NEW q \in (elAt[w] + 1)..Len(ledLog'[w]),
                      p < q, IsConf(ledLog'[w][p]), IsConf(ledLog'[w][q]), ledLog'[w][p].term < w, ledLog'[w][q].term < w
               PROVE FALSE
    BY <2>1 DEF LedOld
  <2>3. CASE w # u BY <2>3, <2>1, <1>B DEF MG, LedOld
  <2>4. CASE w = u
    <3>1. q # Len(L) + 1 BY <2>4, <2>1, <2>2
    <3>2. p \in (elAt[u] + 1)..Len(L) /\ q \in (elAt[u] + 1)..Len(L) BY <3>1, <2>4, <2>1, <2>2
    <3>3. L2[p] = L[p] /\ L2[q] = L[q] BY <3>2, <2>1, <2>2
    <3> QED BY <3>2, <3>3, <2>4, <2>1, <1>B DEF MG, LedOld
  <2> QED BY <2>3, <2>4
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE LedOld'
  BY <1>k, <1>B DEF AdoptTerm, durable, MG, LedOld
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE LedOld'
  BY <1>l, <1>B DEF CastVote, durable, MG, LedOld
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE LedOld'
  BY <1>m, <1>B DEF GrantVote, durable, MG, LedOld
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE LedOld'
  BY <1>n, <1>B DEF LeaderCommit, durable, MG, LedOld
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE LedOld'
  BY <1>o, <1>B DEF SendAppend, durable, MG, LedOld
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE LedOld'
  BY <1>p, <1>B DEF Ack, durable, MG, LedOld
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE LedOld'
  BY <1>q, <1>B DEF AckCommitted, durable, MG, LedOld
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE LedOld'
  BY <1>r, <1>B DEF DeleteSuffix, durable, MG, LedOld
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE LedOld'
  BY <1>s, <1>B DEF StoreEntries, durable, MG, LedOld
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE LedOld'
  BY <1>t, <1>B DEF FollowerCommit, durable, MG, LedOld
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases


\* ---- LegalChain
LEMMA LegalChainStep ==
  ASSUME Inv, ProtoCases
  PROVE  LegalChain'
<1>B. Basic /\ S1 /\ S2 /\ S3 /\ MG /\ CommitSafetyP BY InvParts
<1>G. Grows BY <1>B, GrowsStep
<1>T. TypeOK BY <1>B DEF Basic
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE LegalChain'
  BY <1>a, <1>B DEF BecomeCandidate, durable, MG, LegalChain
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE LegalChain'
  BY <1>b, <1>B DEF BecomeFollower, durable, MG, LegalChain
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE LegalChain'
  <2> DEFINE u == currentTerm[i]  l == log[i]
  <2>1. /\ u \notin DOMAIN ledLog /\ DOMAIN ledLog' = DOMAIN ledLog \cup {u}
        /\ ledLog'[u] = l
        /\ \A t \in DOMAIN ledLog : ledLog'[t] = ledLog[t]
    BY <1>c, <1>B, BecomeLeaderLed
  <2>2. l \in Seq(EntryT) BY <1>T DEF TypeOK
  <2>3. ASSUME NEW p \in 1..Len(l), IsConf(l[p]) PROVE Legal(ConfOf(l, p - 1), l[p].value)
    <3> DEFINE tp == l[p].term
    <3>1. tp \in DOMAIN ledLog /\ Agree(l, ledLog[tp], p) BY <1>B DEF S2, LogFromLed, FromLed
    <3>2. ledLog[tp] \in Seq(EntryT) BY <3>1, <1>T DEF TypeOK
    <3>3. p \in 1..Len(ledLog[tp]) /\ ledLog[tp][p] = l[p] /\ \A q \in 1..(p - 1) : l[q] = ledLog[tp][q]
      BY <3>1, <3>2, <2>2 DEF Agree
    <3>4. Legal(ConfOf(ledLog[tp], p - 1), ledLog[tp][p].value) BY <3>1, <3>3, <2>3, <1>B DEF MG, LegalChain
    <3>5. ConfOf(l, p - 1) = ConfOf(ledLog[tp], p - 1) BY <3>3, ConfOfCongr
    <3> QED BY <3>3, <3>4, <3>5
  <2> HIDE DEF u, l
  <2> QED BY <2>1, <2>3, <1>B DEF MG, LegalChain
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE LegalChain'
  BY <1>d, <1>B DEF StartElection, durable, MG, LegalChain
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE LegalChain'
  BY <1>e, <1>B DEF Restart, durable, MG, LegalChain
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE LegalChain'
  BY <1>f, <1>B DEF Apply, durable, MG, LegalChain
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE LegalChain'
  BY <1>g, <1>B DEF Restore, durable, MG, LegalChain
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE LegalChain'
  BY <1>h, <1>B DEF SwitchConf, durable, MG, LegalChain
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE LegalChain'
  BY <1>i, <1>B DEF RestoreConf, durable, MG, LegalChain
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE LegalChain'
  <2> DEFINE u == currentTerm[i]  L == ledLog[u]  L2 == ledLog'[u]
  <2>1. /\ u \in DOMAIN ledLog /\ e.term = u /\ role[i] = Leader /\ DOMAIN ledLog' = DOMAIN ledLog
        /\ L \in Seq(EntryT) /\ L2 \in Seq(EntryT) /\ Len(L2) = Len(L) + 1 /\ L2[Len(L) + 1] = e
        /\ \A q \in 1..Len(L) : L2[q] = L[q]
        /\ \A t \in DOMAIN ledLog : t # u => ledLog'[t] = ledLog[t]
        /\ (IsConf(e) => AllSwitched(i, L) /\ Legal(config[i], e.value))
    BY <1>j, <1>B, AppendLed
  <2>2. LCS2(u, L, ledConf[u], ledAt[u], elAt[u], commits) BY <2>1, <1>B, LCSDef DEF MG, LCS
  <2>3. ledAt[u] \in Nat BY <2>1, <1>T DEF TypeOK
  <2>4. confAt[i] = ledAt[u] /\ config[i] = ledConf[u] BY <2>1, <1>B DEF S3, LeaderSync
  <2> SUFFICES ASSUME NEW w \in DOMAIN ledLog, NEW p \in 1..Len(ledLog'[w]), IsConf(ledLog'[w][p])
               PROVE Legal(ConfOf(ledLog'[w], p - 1), ledLog'[w][p].value)
    BY <2>1 DEF LegalChain
  <2>5. CASE w # u BY <2>5, <2>1, <1>B DEF MG, LegalChain
  <2>6. CASE w = u /\ p <= Len(L)
    <3>1. L2[p] = L[p] /\ \A q \in 1..(p - 1) : L2[q] = L[q] BY <2>6, <2>1
    <3>2. ConfOf(L2, p - 1) = ConfOf(L, p - 1) BY <3>1, ConfOfCongr
    <3>3. Legal(ConfOf(L, p - 1), L[p].value) BY <2>6, <3>1, <2>1, <1>B DEF MG, LegalChain
    <3> QED BY <3>1, <3>2, <3>3, <2>6
  <2>7. CASE w = u /\ p = Len(L) + 1
    <3>1. IsConf(e) BY <2>7, <2>1
    <3>2. \A q \in (ledAt[u] + 1)..Len(L) : ~IsConf(L[q]) BY <3>1, <2>1, <2>4 DEF AllSwitched, ConfsAfter
    <3>3. ConfOf(L, Len(L)) = ConfOf(L, ledAt[u]) BY <3>2, <2>2, <2>3, <2>1, ConfOfSkip DEF LCS2
    <3>4. ConfOf(L2, Len(L)) = ConfOf(L, Len(L)) BY <2>1, ConfOfCongr
    <3>5. config[i] = ConfOf(L, ledAt[u]) BY <2>4, <2>2 DEF LCS2
    <3> QED BY <3>1, <3>3, <3>4, <3>5, <2>7, <2>1
  <2> QED BY <2>5, <2>6, <2>7, <2>1
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE LegalChain'
  BY <1>k, <1>B DEF AdoptTerm, durable, MG, LegalChain
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE LegalChain'
  BY <1>l, <1>B DEF CastVote, durable, MG, LegalChain
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE LegalChain'
  BY <1>m, <1>B DEF GrantVote, durable, MG, LegalChain
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE LegalChain'
  BY <1>n, <1>B DEF LeaderCommit, durable, MG, LegalChain
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE LegalChain'
  BY <1>o, <1>B DEF SendAppend, durable, MG, LegalChain
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE LegalChain'
  BY <1>p, <1>B DEF Ack, durable, MG, LegalChain
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE LegalChain'
  BY <1>q, <1>B DEF AckCommitted, durable, MG, LegalChain
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE LegalChain'
  BY <1>r, <1>B DEF DeleteSuffix, durable, MG, LegalChain
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE LegalChain'
  BY <1>s, <1>B DEF StoreEntries, durable, MG, LegalChain
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE LegalChain'
  BY <1>t, <1>B DEF FollowerCommit, durable, MG, LegalChain
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases


THEOREM MGStep == ASSUME Inv, ProtoCases PROVE MG'
BY ConfIsCommittedStep, LeaderConfSStep, LedOldStep, LegalChainStep DEF MG
====
