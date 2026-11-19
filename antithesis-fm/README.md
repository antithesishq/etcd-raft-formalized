# etcd-io/raft: a proved model, checked against the code

This directory holds a formal model of [etcd-io/raft](https://github.com/etcd-io/raft),
machine-checked proofs that the model is safe, and a test harness that checks the running
implementation against the model step by step under fault injection
([Antithesis](https://antithesis.com)) and in a deterministic simulator. Everything here is an
addition to the upstream checkout this branch starts from (`99f9ffb`). Raft's own source and
`go.mod` are not modified; the fixes described below are patch files.

## Claims

1. **A model of the implementation.** `spec/EtcdRaft.tla` is a TLA+ model of etcd-io/raft at
   its boundary with the application: one action per change of a node's disk, per message that
   may be sent, and per in-memory leader step that other nodes can come to depend on. It
   covers elections, log replication, commitment, application, crashes and restarts,
   snapshots, membership changes (single and joint `ConfChange`/`ConfChangeV2`), and
   linearizable reads by read index (`ReadIndex`, `ReadOnlySafe`), over a network that can
   delay, drop, duplicate and reorder messages. Because a node's variables are what it has on
   disk, one model covers the three ways an application may drive raft: write then send, a
   leader sending while it writes, and `AsyncStorageWrites`.
2. **The model is safe, proved twice.** For any finite set of servers, any initial voters, any
   sequence of membership changes, and any number of terms and log entries:
   - **TLAPS** proves `Spec => []P` on `EtcdRaft.tla` itself for election safety, log
     matching, commit safety, state machine safety, leader completeness and read-index safety
     (`spec/proof/`).
   - **Lean 4 / Veil** proves every state invariant of the model, those six included, on a
     line-by-line translation of it (`veil/`).
3. **The implementation follows the model.** Each node runs a `RawNode` through the
   `rawnode/` package, which reports every step at raft's boundary. TLC checks, while the
   cluster runs, that the reported steps are a behaviour of the model and that the model's
   safety properties hold in every state reached. With requests for votes held until their
   write (patch E1, or the application holding them) and atomic storage writes, raft passed
   this check in Antithesis runs totalling about 2,100 compute hours, on three and five nodes,
   in every mode above, with PreVote, CheckQuorum, leadership transfer, proposal forwarding,
   batching, snapshots, read indexes and membership changes, under crashes, pauses and
   network partitions, and in about 12,800 simulator runs: no step was rejected and no safety
   property failed.
4. **Faults in upstream raft.** Two break state machine safety and are fixed by small patches
   (E1, with `AsyncStorageWrites`, etcd-io/raft#551; E3, with membership changes and
   non-atomic storage writes, etcd-io/raft#558); two others make nodes panic. See
   `patches/README.md`.

The proofs are about the model; that the code follows the model is established by testing,
on the behaviours the tests reach. `spec/README.md` lists every assumption and limitation.

## Layout

| Path | Contents |
|---|---|
| `spec/` | The TLA+ model `EtcdRaft.tla`, the trace binding `EtcdBinding.tla` (report → model actions), bounded instances for TLC. [`spec/README.md`](spec/README.md): what is modelled, the properties, assumptions and limitations |
| `spec/proof/` | TLAPS proofs: 19 modules, 9,148 obligations. [`spec/proof/README.md`](spec/proof/README.md) |
| `veil/` | The model in Lean 4 / [Veil](https://veil.dev), with stored proofs: 53 invariants × (23 actions + initial state) = 1,272 goals. [`veil/README.md`](veil/README.md) |
| `patches/` | Two fixes to raft. [`patches/README.md`](patches/README.md): the faults, the fixes, and workarounds the harness uses |
| `repro/` | Reproducers of the faults against unmodified raft: `asyncvote` (E1), `confsplit` (E3), `emptyjoint` (E4), and `aba`, a schedule used to test the check |
| `rawnode/` | One raft node: drives a `RawNode`, writes its storage (bbolt), and reports each step; three write modes, batching, snapshots, read index, membership changes |
| `server/` | The service under test: `rawnode` with a running-sum state machine, TCP transport, HTTP API |
| `sim/` | Deterministic simulator: the same `rawnode` code with simulated time, network and disk, driven by a seed |
| `driver/` | The test driver (Rust): client workload, client-visible checks, collection of reports, the live trace check, Antithesis assertions |
| `tracekit/` | The raft-independent part of trace checking: report sink (Go), collector (Rust), streaming TLC checker (Python, Java), conventions (`tla/TraceKit.tla`) |
| `traces/` | Recorded report streams, used as test fixtures |
| `scripts/` | Entry points: setup, simulator batches, local runs, model checking, Lean checks, trace-check tests, reproducers, Antithesis launch |
| `config/`, `config5/`, `local/` | Docker Compose files for Antithesis (3 and 5 nodes) and for local runs |

## Verify independently

All commands run from this directory (`antithesis-fm/`).

### 1. Install

| Tool | Used for | Install |
|---|---|---|
| Java 17+, Python 3 | TLC and trace checking | system packages |
| Go 1.26+ | simulator, reproducers | [go.dev/dl](https://go.dev/dl) |
| Docker | local cluster runs; compiling the stream operator if `javac` is absent | system packages |
| elan (Lean 4) | Lean proofs. The toolchain (`v4.35.0`) is pinned in `veil/lean-toolchain`; Veil is pinned in `veil/lakefile.lean` | `curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \| sh -s -- -y --default-toolchain none` |
| tlapm 1.6.0-pre | TLAPS proofs (bundles Isabelle, Zenon, Z3). Checked with build `bf665f4` | `curl -fsSL https://github.com/tlaplus/tlapm/releases/download/1.6.0-pre/tlapm-1.6.0-pre-x86_64-linux-gnu.tar.gz \| tar xz && export PATH=$PWD/tlapm/bin:$PATH` |

Then:

```sh
scripts/setup.sh     # fetches tla2tools.jar v1.8.0 and CommunityModules, compiles the stream operator,
                     # lists missing tools
```

### 2. TLAPS proofs (about 45 minutes; needs up to 24 GB of memory)

```sh
(cd spec && sha256sum -c proof/SPEC.sha256)   # the proofs are about these exact spec files
spec/proof/final.sh                            # every module from a clean cache, --strict
```

Expected: one line per module, `All N obligations proved`, for all 19 modules, then
`DONE ... (exit 0)`. The theorems are in `spec/proof/EtcdSafety.tla`.

### 3. Lean proofs (about 20 minutes on 32 cores; first run also builds Veil)

```sh
scripts/veil-check.sh
```

Expected: every file `ok`, i.e. Lean accepts all 1,272 theorems with no error and no `sorry`.
The `Restart` file takes longest. `cd veil && lake build` checks the same file in one process
(slower).

That the Lean model is the TLA+ model is checked by counting states on shared bounded
instances. Both commands must print the same number (table in `veil/README.md`):

```sh
scripts/mc.sh MCMemCount2.cfg 900         # TLC: 15,800 distinct states (one membership change)
scripts/veil-count.sh m2                  # Veil: 15,800
```

### 4. Model checking with TLC

```sh
scripts/mc.sh MCCount4.cfg 1800       # read index included: 1,631,864 states, no violation
scripts/mc.sh MCReadMem3.cfg 3600     # membership change and read index: 1,312,146 states, no violation
```

Other instances are listed in `spec/README.md`. Output is one line (`completed, N states, no
violation`) and a log under `runs/mc/`.

### 5. Trace validation

```sh
scripts/validator-tests.sh                        # recorded streams in traces/ accepted, and
                                                  # 60 mutations of them rejected at the right event
scripts/sim-batch.sh 1 50 3 3000                  # 50 simulator seeds, 3 nodes, each stream checked
SIMARGS="-async -snap -reads" scripts/sim-batch.sh 1 50 3 4000
VOTERS=3 SIMARGS="-member -calm 4" scripts/sim-batch.sh 1 50 5 5000   # membership changes
scripts/local-run.sh 40                           # Docker: 3-node cluster, checked live
CHAOS=1 ASYNC=1 scripts/local-run.sh 60           # AsyncStorageWrites, crashes and partitions
NODES=5 VOTERS=raft1,raft2,raft3 CONF_RATE=0.5 CHAOS=1 scripts/local-run.sh 60
scripts/sut-mutants.sh                            # raft and rawnode with seeded bugs: each rejected
```

Simulator and local-run variants are listed in `spec/README.md` ("Modes").

### 6. Reproduce the faults

```sh
scripts/e1.sh                 # E1: unpatched raft diverges; with the patch it does not
scripts/e3.sh                 # E3: diverges with split writes; safe with atomic writes or the patch
go run ./repro/emptyjoint     # E4: panics on apply
```

### 7. Antithesis

`scripts/launch.sh 50` builds the images and submits a 50-hour run. It needs an Antithesis
tenant and the `snouty` CLI. The same environment variables as for `local-run.sh` select the
mode.
