# Lean proofs of EtcdRaft

`EtcdRaftVeil.lean` is `../spec/EtcdRaft.tla` translated into [Veil](https://veil.dev), a
Lean 4 framework for transition systems: the same variables, actions (with the same
parameters) and properties, membership changes and the read index included. Each TLA+
definition is quoted in a comment above its translation. The file proves that 53 invariants
hold initially and are preserved by each of the 23 actions: 1,272 goals, every one with a
stored proof checked by Lean's kernel.

## What is proved

For any finite number of servers, any initial voters, any number of terms and entries, and
any meaning of a `conf` entry: what a change adds and removes, and whether it is joint or
leaves a joint configuration, are free functions (`chAdd`, `chRemove`, `chJoint`,
`chLeave`), so the proofs cover every `ConfChanges`.

Every state invariant of `EtcdRaft.tla` (17):

| Invariant | Statement |
|---|---|
| `ElectionSafety` | At most one server is elected in a term |
| `OneVotePerTerm` | A node never votes for two candidates in one term |
| `LogMatching` | Two logs with an entry of the same term at an index agree up to that index |
| `CommitSafety` | Two committed prefixes never disagree |
| `StateMachineSafety` | No two state machines are handed different entries at one index |
| `LeaderCompleteness` | The leader log of a term has every prefix committed under an earlier term |
| `CommittedEntriesPreserved`, `CommitWithinLog` | What a node's commit index covers is in its log and is a committed prefix |
| `ReadIndexSafety` | A read that may be served has an index covering every prefix committed when it was requested |
| `ReadMsgsOld`, `ReadFloorOld`, `ReadFloorBound` | The followed read's recorded state is consistent |
| `LeaderLogIsLed`, `RequestsFromLed`, `ConfirmedWithinLog` | Bookkeeping: `ledLog`, requests and `confirmed` are consistent |
| `ConfIsCommitted` | A node's configuration is the initial one or what the changes in a committed prefix make |
| `LeaderConf` | A leader counts with what its own log makes up to its switch point; at most one change after it; both points within committed prefixes |

Not stated in Lean: the step properties `TermMonotonic`, `CommitMonotonic`,
`NoAppliesSkipped`.

Supporting invariants (36), grouped:

| Group | Invariants say |
|---|---|
| Elections | A vote record is not ahead of its term; every vote is at or before its voter's record; a granted reply states an existing vote; a leader's configuration is its term's (`LeaderSync`) |
| Leaders | A node in the leader role was elected in its term; nobody was elected in a term it has not reached; while the leader of t is in t, its disk is a prefix of `ledLog[t]` (`LedOwner`); a term has a leader log iff it had a leader; append requests come from their term's leader |
| Logs | Every entry is, with all before it, in the leader log of its term (`FromLed`); terms along a leader log do not decrease and do not exceed its term; no log has an entry of a term its node has not reached |
| Vote requests | A request is of a reached term and describes an existing log; one per node and term; every vote answers one; until the term has a leader, the candidate's log is the one described; a leader log starts with it |
| Acknowledgements | Acks go to the leader of their term; `AckedHeld`; `AckVote`; every leader was elected by a quorum, of its election configuration, of early voters (`EarlyQuorum`) |
| Commits | `confirmed` is a prefix of the confirming leader's log; every committed prefix is part of one a leader committed with a quorum of its configuration, in a term not after its own (`CommitRoot`) |
| Applies | Every applied entry is in a committed prefix |
| Membership | Every committed change was first committed by a leader not yet counting with it (`FirstRoot`); a leader log has at most one older-term change after its election point (`LedOld`); each change is legal for the configuration before it (`LegalChain`) |
| Read index | As of the read request: the reader's term has a leader log; `CommitRoot` and `FirstRoot` held (`ReadFloorRooted`, `ReadFirstRoot`); a node that answered had acknowledged nothing in a later term (`ReadRespBound`) |

How the safety properties follow:

- `LogMatching` from `FromLed`.
- `leader_complete` (by induction on the later term): entries a quorum acknowledged to the
  leader of their term are in every later leader log. A leader is in a quorum only through
  its own acknowledgement of what is on its disk.
- With membership changes the two quorums can be of different configurations. The argument
  is `MemberCore.core`, in plain Lean independent of the model: quorums of configurations one
  legal change apart intersect (`IsQ.inter_next`); if more changes lie between, the first of
  them was itself committed by a leader not yet counting with it (`FirstRoot`), and the
  argument is applied to that commit first, by induction on the distance. The model's guards
  (`OneWaiting`, `CommittedBefore`, `LeaderKnows`) keep the compared configurations at most
  one change apart.
- `CommitSafety`, `LeaderCompleteness` from `CommitRoot` and `leader_complete` (`roots_cmp`,
  `root_in_later`, `cand_complete`). `CommittedEntriesPreserved` from `delete_keeps`.
  `StateMachineSafety`: applied entries are in committed prefixes, which agree.
- `ReadIndexSafety` (`MemberCore.read_core`, `read_safe`): a prefix committed when the read
  was requested was by then committed by some leader with a quorum; that quorum meets the
  quorum that answered the read (directly, or one change away via `FirstRoot`), and a node
  that answered had acknowledged nothing in a later term, so that leader's term is the
  reader's or earlier and the read index covers the prefix.

The section `Quorums` ties `MemberCore` to the model's variables.

## Proof structure and checking

The file is ordered: model; invariants; lemmas; proofs (`-- Proofs.`), one section per
action, one goal command per (action, invariant).

- Each proof first picks from the conjunction of the 53 invariants the ones it uses
  (`have hX := hinv.2.….1`) and drops the rest, so automation sees few hypotheses and an
  invariant added at the end does not affect existing proofs.
- More than half of the goals close with `grind only [...]` and named facts; the rest use
  the lemmas by hand. Initial-state goals use Veil's `tr` form.
- No SMT solver is involved: Veil's automatic `#check_invariants` cannot translate this
  model's set-typed state, so every proof is a Lean proof term. The trusted base is Lean's
  kernel and Veil's generation of the goals from the actions.
- The 53 goals of `SwitchConf` are stated with `prove_goal_unregistered` (defined at the top
  of the file) instead of `prove_veil_invariant_goal`. Both build the same statement
  (`Module.mkInvariantGoalVC`) and Lean checks the same proof; the former skips Veil's
  registration of the finished theorem, which does not terminate for these goals with this
  Veil version. Veil's own summary therefore does not list them; `veil-check.sh` counts
  them, because it requires Lean to accept every theorem.

```sh
scripts/veil-check.sh        # splits the proofs by action into parallel Lean processes;
                             # every file must be ok (no error, no sorry)
cd veil && lake build        # the same check in one process
```

On a 32-core machine, 23 of the 24 files take about 7 minutes and `Restart` about 20.
`ONLY="Restart Ack"` checks only those actions.

## Same model as the TLA+

Equal state counts on shared bounded instances (no symmetry, unrestricted `Spec`). This is
evidence, not proof, that the translation is faithful.

| Instance | TLC (`scripts/mc.sh …`) | Veil (`scripts/veil-count.sh …`) | Distinct states |
|---|---|---|---|
| 3 voters, no change, terms ≤ 2, log ≤ 2, msgs ≤ 2 | `MCCount2.cfg` | `2` | 17,168 |
| the same, msgs ≤ 3 | `MCCount3.cfg` | `3` | 305,896 |
| terms ≤ 1, log ≤ 1, msgs ≤ 6 (commit, apply and read index reached) | `MCCount4.cfg` | `4` | 1,631,864 |
| 2 of 3 voters, one change adds the third, msgs ≤ 2 | `MCMemCount2.cfg` | `m2` | 15,800 |
| the same, msgs ≤ 3 | `MCMemCount3.cfg` | `m3` | 204,552 |

`veil-count.sh` checks every invariant Veil's model checker can evaluate; the 22 between the
`PROOF-ONLY` marks quantify over all indexes and terms and are proved but not model-checked.
For model checking only, the file gives `ledLog` an equality and a hash over the reachable
terms (`ledLogBEq`, `ledLogHashable`); without them Veil merges states that differ only in a
leader log. The proofs do not use them.

## Setup

Install [elan](https://github.com/leanprover/elan). `lean-toolchain` pins Lean 4.35.0;
`lakefile.lean` pins Veil to commit `1287c31d`; `lake-manifest.json` pins Veil's
dependencies. The first `lake build` or `scripts/veil-check.sh` fetches and compiles them into
`.lake/` (several minutes).
