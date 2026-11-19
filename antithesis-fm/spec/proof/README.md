# TLAPS proofs of EtcdRaft

Machine-checked proofs, with the [TLA+ Proof System](https://proofs.tlapl.us), that the
safety properties of `../EtcdRaft.tla` hold in every reachable state, with membership changes
and read indexes. The theorems are about the TLA+ module itself, not about a translation.
`SPEC.sha256` records the spec files the proofs were checked against
(`cd .. && sha256sum -c proof/SPEC.sha256`).

## Theorems

In `EtcdSafety.tla`:

| Theorem | Statement |
|---|---|
| `IIAlways` | `Spec => []II`, where `II == Inv /\ RInv` |
| `ElectionSafetyThm` | `Spec => []ElectionSafety` |
| `LogMatchingThm` | `Spec => []LogMatching` |
| `CommitSafetyThm` | `Spec => []CommitSafety` |
| `StateMachineSafetyThm` | `Spec => []StateMachineSafety` |
| `LeaderCompletenessThm` | `Spec => []LeaderCompleteness` |
| `ReadIndexSafetyThm` | `Spec => []ReadIndexSafety` |

**Assumptions.** Only the spec's own: `ASSUME ServerFinite == IsFiniteSet(Server)`,
`ASSUME VotersOK == InitVoters \subseteq Server /\ InitVoters # {}`, and
`Nil \notin Server`. `ConstOKHolds` derives from them the constant facts the invariant
needs, so the theorems have no hypotheses. `ConfChanges` (which changes may be proposed) is
left arbitrary. No proof step is omitted (`--strict` fails on any unproved obligation).

## The inductive invariant

`Inv` (`EtcdInv.tla`) and `RInv` (`EtcdReadInv.tla`) are definitions only, so TLC can
evaluate them. `ledLog[t]` (the log of the leader of term t) is the reference every log is
compared to; `MRoot(t, c, d)` says the leader of t may commit its first c entries counting
with the configuration its first d entries make.

| Group | Conjuncts | Say |
|---|---|---|
| Types | `TypeOK` | Types of all variables, and the constant facts (`ConstOK`) |
| Elections | `ElectionSafety`, `VoteTermBound`, `VotesBound`, `GrantsAreVotes`, `LeaderSync`, `LeaderIsElected`, `LeadersTermBound`, `LedOwner`, `LedDom` | One leader per term; votes and grants are consistent with vote records; a leader's configuration is its term's (`ledConf`); a leader's disk is a prefix of its leader log while it is in its term |
| Requests | `AppendFromLeader`, `ReqFromLed` | An append request is from its term's leader, carries a segment of its leader log, and a commit index covered by a commit of that term or earlier |
| Logs | `LogFromLed`, `LedFromLed`, `TermsPositive`, `LogTermsBound`, `LedTermsBound` | Every entry is, with all before it, in the leader log of its term (`FromLed`); terms are bounded by the owner's term |
| Vote requests | `ReqFacts`, `ReqUnique`, `VoteHasReq`, `CandLog`, `LedExtendsReq` | A request describes an existing log of a reached term; one per node and term; every vote answers one; until the term has a leader, the candidate's log is the one described; a leader log extends it |
| Acknowledgements | `AckFacts`, `AckedHeld`, `AckVote`, `EarlyQuorum` | A node keeps what it acknowledged unless a later leader log up to its term lacks it; a node that acknowledged and later voted, voted for a log that has it, unless a leader in between lacks it; every leader was elected by a quorum, in its election configuration, of such voters |
| Commits | `ConfirmedIsLed`, `ConfirmedWithinLog`, `CommitRoot`, `CommitSafetyP`, `ConfirmedTermBound`, `CommitTermBound`, `CommitKept`, `AppliedCommitted` | Every committed prefix is part of one a leader committed with a quorum of its configuration (`CommitRoot`); committed prefixes agree; a commit index covers a committed prefix the log holds; applied entries are committed |
| Membership | `ConfIsCommitted`, `LeaderConfS`, `FirstRoot`, `LedOld`, `LegalChain` | Configurations are made by committed changes; a leader has at most one pending change; every committed change was first committed by a leader not yet counting with it (`FirstRoot`); changes in a leader log are legal for the configuration before them |
| Read index (`RInv`) | `ReadMsgsOld`, `ReadFloorOld`, `ReadFloorBound`, `ReadIndexSafety`, `ReadTermLed`, `ReadFloorRooted`, `ReadFirstRoot`, `ReadRespBound` | `CommitRoot` and `FirstRoot` as they were when the read was requested; a node that answered had acknowledged nothing in a later term |

Two state-level consequences carry the main arguments:

- `LC` (theorem `LCThm`, `EtcdLC.tla`): leader completeness for anything a leader may
  commit, by induction on terms. With membership changes, the committing quorum and a later
  candidate's quorum are of configurations at most one legal change apart, or the argument
  is first applied to the commit of the intervening change (`FirstRoot`).
- `ReadSafeP` (theorem `ReadSafe`, `EtcdReadCore.tla`): when a quorum has answered a read,
  its index covers every prefix committed at the request.

## Modules

In dependency order (each EXTENDS earlier ones):

| Module | Contents |
|---|---|
| `EtcdInv`, `EtcdReadInv` | The invariants. No proofs |
| `EtcdRec` | `FinRecExists`, a recursion lemma (stated variable-free so the standard library's induction theorems apply) |
| `EtcdChange` | `ChangeFacts`: facts about `ConfChanges` |
| `EtcdBase` | Sequences, quorums (`MajInter`, …), configurations (`ConfOf`) |
| `EtcdActs` | `NextCases`: `Next` split into 20 typed action cases (`ProtoCases`) |
| `EtcdType`, `EtcdGrow` | Typing is preserved; facts only grow, leader logs only extend |
| `EtcdLog` | Storing and deleting entries keep logs consistent with leader logs |
| `EtcdSimple1/2/3` | Step lemmas for the election, request and log invariants |
| `EtcdMember` | Step lemmas for the membership invariants |
| `EtcdLC` | `LCThm` |
| `EtcdCommitBase`, `EtcdCommit` | Step lemmas for the commit invariants |
| `EtcdAckBase`, `EtcdAck` | Step lemmas for `AckedHeld`, `AckVote`, `EarlyQuorum` |
| `EtcdReadCore`, `EtcdReadStep` | `ReadSafe`; step lemmas for `RInv` |
| `EtcdSafety` | `IIInit`, `IIStep`, the theorems |

19 modules, 9,148 obligations. `MCInv.tla` with `proof/*.cfg` has TLC check `Inv`, `RInv`,
`LC` and `ReadSafeP` on bounded instances (`tlc.sh CFG [seconds]`).

## Checking

```sh
spec/proof/final.sh                # all modules, in order, --cleanfp --strict; one line per module in final.log
spec/proof/final.sh EtcdLC         # selected modules
spec/proof/chk.sh EtcdLog          # one module, with failures listed (development)
```

`TLAPM` selects the binary (default `tlapm` on `PATH`), `THREADS` the prover threads
(default 2), `MEM_KB` the virtual-memory cap (default 24 GB). Two `final.sh` runs on
disjoint module lists can run at once.

**Prover setup.** tlapm 1.6.0-pre (checked with build `bf665f4`), with its default backends:
Zenon, Isabelle and Z3 through the default SMT encoding. Notes:

- Z3 has no memory limit of its own, and one hard obligation can use all of a machine's
  memory. The scripts cap every prover process with `ulimit -v`; 24 GB is about the least
  Isabelle starts with.
- `EtcdChange` is checked with `--debug no_smt_set_extensionality` (`flags.sh`). Set
  constructors with two bound variables, as in `ConfChanges`, make tlapm's SMT encoding of set
  extensionality fail; without those axioms Z3 proves the module. No other module uses the
  flag, and `ConfChanges` is not expanded elsewhere.
- Obligations are kept small: conjuncts of `Inv` are extracted before use, action
  definitions hidden, and expressions with primes passed as operator arguments rather than
  primed again.
