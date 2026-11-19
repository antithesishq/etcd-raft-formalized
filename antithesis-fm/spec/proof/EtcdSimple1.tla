---- MODULE EtcdSimple1 ----
\* First group of simple invariants.
EXTENDS EtcdGrow

S1 == /\ ElectionSafety /\ VoteTermBound /\ VotesBound /\ GrantsAreVotes
      /\ LeadersTermBound /\ AppendFromLeader /\ ConfirmedTermBound /\ CommitTermBound

LEMMA S1Init == ASSUME Init PROVE S1
BY DEF Init, S1, ElectionSafety, VoteTermBound, VotesBound, GrantsAreVotes,
       LeadersTermBound, AppendFromLeader, ConfirmedTermBound, CommitTermBound

LEMMA S1Unch == ASSUME S1, UNCHANGED vars PROVE S1'
BY DEF vars, protoVars, durable, S1, ElectionSafety, VoteTermBound, VotesBound, GrantsAreVotes,
       LeadersTermBound, AppendFromLeader, ConfirmedTermBound, CommitTermBound, IsLd

LEMMA ElectionSafetyStep ==
  ASSUME Basic, S1, ProtoCases
  PROVE  ElectionSafety'
<1> USE DEF S1, ElectionSafety, durable
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE ElectionSafety'
  BY <1>a DEF BecomeCandidate
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE ElectionSafety'
  BY <1>b DEF BecomeFollower
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE ElectionSafety'
  <2>1. currentTerm[i] \notin {ld.term : ld \in leaders} BY <1>c DEF BecomeLeader, Basic, LedDom
  <2>2. leaders' = leaders \cup {[server |-> i, term |-> currentTerm[i]]} BY <1>c DEF BecomeLeader
  <2> QED BY <2>1, <2>2
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE ElectionSafety'
  BY <1>d DEF StartElection
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE ElectionSafety'
  BY <1>e DEF Restart
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE ElectionSafety'
  BY <1>f DEF Apply
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE ElectionSafety'
  BY <1>g DEF Restore
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE ElectionSafety'
  BY <1>h DEF SwitchConf
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE ElectionSafety'
  BY <1>i DEF RestoreConf
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE ElectionSafety'
  BY <1>j DEF LeaderAppend1
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE ElectionSafety'
  BY <1>k DEF AdoptTerm
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE ElectionSafety'
  BY <1>l DEF CastVote
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE ElectionSafety'
  BY <1>m DEF GrantVote
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE ElectionSafety'
  BY <1>n DEF LeaderCommit
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE ElectionSafety'
  BY <1>o DEF SendAppend
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE ElectionSafety'
  BY <1>p DEF Ack
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE ElectionSafety'
  BY <1>q DEF AckCommitted
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE ElectionSafety'
  BY <1>r DEF DeleteSuffix
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE ElectionSafety'
  BY <1>s DEF StoreEntries
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE ElectionSafety'
  BY <1>t DEF FollowerCommit
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases

LEMMA VoteTermBoundStep ==
  ASSUME Basic, S1, ProtoCases
  PROVE  VoteTermBound'
<1> USE DEF S1, Basic, TypeOK, VoteTermBound, durable
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE VoteTermBound'
  BY <1>a DEF BecomeCandidate
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE VoteTermBound'
  BY <1>b DEF BecomeFollower
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE VoteTermBound'
  BY <1>c DEF BecomeLeader
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE VoteTermBound'
  BY <1>d DEF StartElection
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE VoteTermBound'
  BY <1>e DEF Restart
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE VoteTermBound'
  BY <1>f DEF Apply
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE VoteTermBound'
  BY <1>g DEF Restore
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE VoteTermBound'
  BY <1>h DEF SwitchConf
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE VoteTermBound'
  BY <1>i DEF RestoreConf
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE VoteTermBound'
  BY <1>j DEF LeaderAppend1
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE VoteTermBound'
  BY <1>k DEF AdoptTerm
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE VoteTermBound'
  BY <1>l DEF CastVote
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE VoteTermBound'
  BY <1>m DEF GrantVote
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE VoteTermBound'
  BY <1>n DEF LeaderCommit
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE VoteTermBound'
  BY <1>o DEF SendAppend
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE VoteTermBound'
  BY <1>p DEF Ack
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE VoteTermBound'
  BY <1>q DEF AckCommitted
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE VoteTermBound'
  BY <1>r DEF DeleteSuffix
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE VoteTermBound'
  BY <1>s DEF StoreEntries
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE VoteTermBound'
  BY <1>t DEF FollowerCommit
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases

LEMMA VotesBoundStep ==
  ASSUME Basic, S1, ProtoCases
  PROVE  VotesBound'
<1> USE DEF S1, Basic, TypeOK, VotesBound, VoteTermBound, durable
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE VotesBound'
  BY <1>a DEF BecomeCandidate
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE VotesBound'
  BY <1>b DEF BecomeFollower
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE VotesBound'
  BY <1>c DEF BecomeLeader
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE VotesBound'
  BY <1>d DEF StartElection
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE VotesBound'
  BY <1>e DEF Restart
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE VotesBound'
  BY <1>f DEF Apply
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE VotesBound'
  BY <1>g DEF Restore
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE VotesBound'
  BY <1>h DEF SwitchConf
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE VotesBound'
  BY <1>i DEF RestoreConf
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE VotesBound'
  BY <1>j DEF LeaderAppend1
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE VotesBound'
  BY <1>k DEF AdoptTerm
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE VotesBound'
  <2>1. \A v \in votes : v.voter \in Server /\ v.term \in Nat BY DEF VoteT
  <2> QED BY <1>l, <2>1 DEF CastVote
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE VotesBound'
  BY <1>m DEF GrantVote
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE VotesBound'
  BY <1>n DEF LeaderCommit
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE VotesBound'
  BY <1>o DEF SendAppend
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE VotesBound'
  BY <1>p DEF Ack
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE VotesBound'
  BY <1>q DEF AckCommitted
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE VotesBound'
  BY <1>r DEF DeleteSuffix
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE VotesBound'
  BY <1>s DEF StoreEntries
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE VotesBound'
  BY <1>t DEF FollowerCommit
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases

LEMMA GrantsAreVotesStep ==
  ASSUME Basic, S1, ProtoCases
  PROVE  GrantsAreVotes'
<1> USE DEF S1, GrantsAreVotes, durable
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE GrantsAreVotes'
  BY <1>a DEF BecomeCandidate
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE GrantsAreVotes'
  BY <1>b DEF BecomeFollower
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE GrantsAreVotes'
  BY <1>c DEF BecomeLeader
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE GrantsAreVotes'
  BY <1>d DEF StartElection, VoteRequest
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE GrantsAreVotes'
  BY <1>e DEF Restart
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE GrantsAreVotes'
  BY <1>f DEF Apply
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE GrantsAreVotes'
  BY <1>g DEF Restore
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE GrantsAreVotes'
  BY <1>h DEF SwitchConf
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE GrantsAreVotes'
  BY <1>i DEF RestoreConf
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE GrantsAreVotes'
  BY <1>j DEF LeaderAppend1
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE GrantsAreVotes'
  BY <1>k DEF AdoptTerm
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE GrantsAreVotes'
  BY <1>l DEF CastVote
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE GrantsAreVotes'
  BY <1>m DEF GrantVote
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE GrantsAreVotes'
  BY <1>n DEF LeaderCommit
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE GrantsAreVotes'
  BY <1>o DEF SendAppend
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE GrantsAreVotes'
  BY <1>p DEF Ack
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE GrantsAreVotes'
  BY <1>q DEF AckCommitted
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE GrantsAreVotes'
  BY <1>r DEF DeleteSuffix
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE GrantsAreVotes'
  BY <1>s DEF StoreEntries
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE GrantsAreVotes'
  BY <1>t DEF FollowerCommit
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases

LEMMA LeadersTermBoundStep ==
  ASSUME Basic, S1, ProtoCases
  PROVE  LeadersTermBound'
<1> USE DEF S1, Basic, TypeOK, LeadersTermBound, durable
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE LeadersTermBound'
  BY <1>a DEF BecomeCandidate
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE LeadersTermBound'
  BY <1>b DEF BecomeFollower
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE LeadersTermBound'
  <2>1. \A ld \in leaders : ld.server \in Server /\ ld.term \in Nat BY DEF LeaderT
  <2> QED BY <1>c, <2>1 DEF BecomeLeader
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE LeadersTermBound'
  <2>1. \A ld \in leaders : ld.server \in Server /\ ld.term \in Nat BY DEF LeaderT
  <2> QED BY <1>d, <2>1 DEF StartElection
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE LeadersTermBound'
  BY <1>e DEF Restart
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE LeadersTermBound'
  BY <1>f DEF Apply
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE LeadersTermBound'
  BY <1>g DEF Restore
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE LeadersTermBound'
  BY <1>h DEF SwitchConf
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE LeadersTermBound'
  BY <1>i DEF RestoreConf
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE LeadersTermBound'
  BY <1>j DEF LeaderAppend1
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE LeadersTermBound'
  <2>1. \A ld \in leaders : ld.server \in Server /\ ld.term \in Nat BY DEF LeaderT
  <2> QED BY <1>k, <2>1 DEF AdoptTerm
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE LeadersTermBound'
  BY <1>l DEF CastVote
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE LeadersTermBound'
  BY <1>m DEF GrantVote
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE LeadersTermBound'
  BY <1>n DEF LeaderCommit
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE LeadersTermBound'
  BY <1>o DEF SendAppend
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE LeadersTermBound'
  BY <1>p DEF Ack
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE LeadersTermBound'
  BY <1>q DEF AckCommitted
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE LeadersTermBound'
  BY <1>r DEF DeleteSuffix
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE LeadersTermBound'
  BY <1>s DEF StoreEntries
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE LeadersTermBound'
  BY <1>t DEF FollowerCommit
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases

LEMMA AppendFromLeaderStep ==
  ASSUME Basic, S1, ProtoCases
  PROVE  AppendFromLeader'
<1> USE DEF S1, AppendFromLeader, IsLd, durable
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE AppendFromLeader'
  BY <1>a DEF BecomeCandidate
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE AppendFromLeader'
  BY <1>b DEF BecomeFollower
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE AppendFromLeader'
  BY <1>c DEF BecomeLeader
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE AppendFromLeader'
  BY <1>d DEF StartElection, VoteRequest
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE AppendFromLeader'
  BY <1>e DEF Restart
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE AppendFromLeader'
  BY <1>f DEF Apply
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE AppendFromLeader'
  BY <1>g DEF Restore
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE AppendFromLeader'
  BY <1>h DEF SwitchConf
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE AppendFromLeader'
  BY <1>i DEF RestoreConf
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE AppendFromLeader'
  BY <1>j DEF LeaderAppend1
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE AppendFromLeader'
  BY <1>k DEF AdoptTerm
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE AppendFromLeader'
  BY <1>l DEF CastVote
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE AppendFromLeader'
  BY <1>m DEF GrantVote
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE AppendFromLeader'
  BY <1>n DEF LeaderCommit
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE AppendFromLeader'
  BY <1>o DEF SendAppend
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE AppendFromLeader'
  BY <1>p DEF Ack
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE AppendFromLeader'
  BY <1>q DEF AckCommitted
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE AppendFromLeader'
  BY <1>r DEF DeleteSuffix
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE AppendFromLeader'
  BY <1>s DEF StoreEntries
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE AppendFromLeader'
  BY <1>t DEF FollowerCommit
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases

LEMMA ConfirmedTermBoundStep ==
  ASSUME Basic, S1, ProtoCases
  PROVE  ConfirmedTermBound'
<1> USE DEF S1, Basic, TypeOK, ConfirmedTermBound, durable
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE ConfirmedTermBound'
  BY <1>a DEF BecomeCandidate
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE ConfirmedTermBound'
  BY <1>b DEF BecomeFollower
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE ConfirmedTermBound'
  BY <1>c DEF BecomeLeader
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE ConfirmedTermBound'
  BY <1>d DEF StartElection
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE ConfirmedTermBound'
  BY <1>e DEF Restart
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE ConfirmedTermBound'
  BY <1>f DEF Apply
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE ConfirmedTermBound'
  BY <1>g DEF Restore
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE ConfirmedTermBound'
  BY <1>h DEF SwitchConf
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE ConfirmedTermBound'
  BY <1>i DEF RestoreConf
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE ConfirmedTermBound'
  BY <1>j DEF LeaderAppend1
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE ConfirmedTermBound'
  BY <1>k DEF AdoptTerm
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE ConfirmedTermBound'
  BY <1>l DEF CastVote
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE ConfirmedTermBound'
  BY <1>m DEF GrantVote
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE ConfirmedTermBound'
  BY <1>n DEF LeaderCommit
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE ConfirmedTermBound'
  BY <1>o DEF SendAppend
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE ConfirmedTermBound'
  BY <1>p DEF Ack, Confirm, AppendT
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE ConfirmedTermBound'
  BY <1>q DEF AckCommitted
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE ConfirmedTermBound'
  BY <1>r DEF DeleteSuffix, Confirm, AppendT
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE ConfirmedTermBound'
  BY <1>s DEF StoreEntries, Confirm, AppendT
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE ConfirmedTermBound'
  BY <1>t DEF FollowerCommit
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases

LEMMA CommitTermBoundStep ==
  ASSUME Basic, S1, ProtoCases
  PROVE  CommitTermBound'
<1> USE DEF S1, Basic, TypeOK, CommitTermBound, durable
<1>a. ASSUME NEW i \in Server, BecomeCandidate(i) PROVE CommitTermBound'
  BY <1>a DEF BecomeCandidate
<1>b. ASSUME NEW i \in Server, BecomeFollower(i) PROVE CommitTermBound'
  BY <1>b DEF BecomeFollower
<1>c. ASSUME NEW i \in Server, BecomeLeader(i) PROVE CommitTermBound'
  BY <1>c DEF BecomeLeader
<1>d. ASSUME NEW i \in Server, StartElection(i) PROVE CommitTermBound'
  <2>1. \A c \in commits : c.server \in Server /\ c.term \in Nat BY DEF CommitT
  <2> QED BY <1>d, <2>1 DEF StartElection
<1>e. ASSUME NEW i \in Server, Restart(i) PROVE CommitTermBound'
  BY <1>e DEF Restart
<1>f. ASSUME NEW i \in Server, Apply(i) PROVE CommitTermBound'
  BY <1>f DEF Apply
<1>g. ASSUME NEW i \in Server, NEW a \in 0..Len(log[i]), Restore(i, a) PROVE CommitTermBound'
  BY <1>g DEF Restore
<1>h. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]), SwitchConf(i, k) PROVE CommitTermBound'
  BY <1>h DEF SwitchConf
<1>i. ASSUME NEW i \in Server, NEW c \in commits, NEW a \in 0..Len(c.entries), RestoreConf(i, c, a) PROVE CommitTermBound'
  BY <1>i DEF RestoreConf
<1>j. ASSUME NEW i \in Server, NEW e \in EntryT, LeaderAppend1(i, e) PROVE CommitTermBound'
  BY <1>j DEF LeaderAppend1
<1>k. ASSUME NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE CommitTermBound'
  <2>1. \A c \in commits : c.server \in Server /\ c.term \in Nat BY DEF CommitT
  <2> QED BY <1>k, <2>1 DEF AdoptTerm
<1>l. ASSUME NEW i \in Server, NEW c \in Server, CastVote(i, c) PROVE CommitTermBound'
  BY <1>l DEF CastVote
<1>m. ASSUME NEW i \in Server, NEW c \in Server, NEW t \in Nat, GrantVote(i, c, t) PROVE CommitTermBound'
  BY <1>m DEF GrantVote
<1>n. ASSUME NEW i \in Server, NEW t \in Nat, NEW c \in Nat, LeaderCommit(i, t, c) PROVE CommitTermBound'
  <2>1. t <= currentTerm[i] BY <1>n DEF LeaderCommit, LeadersTermBound
  <2> QED BY <1>n, <2>1 DEF LeaderCommit
<1>o. ASSUME NEW i \in Server, NEW j \in Server, NEW t \in Nat, NEW p \in Nat, NEW n \in Nat, NEW c \in Nat, SendAppend(i, j, t, p, n, c) PROVE CommitTermBound'
  BY <1>o DEF SendAppend
<1>p. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, Ack(j, m) PROVE CommitTermBound'
  BY <1>p DEF Ack
<1>q. ASSUME NEW j \in Server, NEW m \in msgs, m \in AppendT, AckCommitted(j, m) PROVE CommitTermBound'
  BY <1>q DEF AckCommitted
<1>r. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, DeleteSuffix(j, m, k) PROVE CommitTermBound'
  BY <1>r DEF DeleteSuffix
<1>s. ASSUME NEW j \in Server, NEW m \in msgs, NEW k \in 1..Len(m.entries), m \in AppendT, StoreEntries(j, m, k) PROVE CommitTermBound'
  BY <1>s DEF StoreEntries
<1>t. ASSUME NEW j \in Server, NEW m \in msgs, NEW c \in Nat, m \in AppendT, FollowerCommit(j, m, c) PROVE CommitTermBound'
  <2>1. m.term <= currentTerm[j] BY <1>t DEF FollowerCommit, ConfirmedTermBound
  <2> QED BY <1>t, <2>1 DEF FollowerCommit, Committed
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f, <1>g, <1>h, <1>i, <1>j, <1>k, <1>l, <1>m, <1>n, <1>o, <1>p, <1>q, <1>r, <1>s, <1>t DEF ProtoCases

THEOREM S1Step == ASSUME Basic, S1, ProtoCases PROVE S1'
BY ElectionSafetyStep, VoteTermBoundStep, VotesBoundStep, GrantsAreVotesStep, LeadersTermBoundStep,
   AppendFromLeaderStep, ConfirmedTermBoundStep, CommitTermBoundStep DEF S1
====
