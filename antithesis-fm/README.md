# etcd-io/raft: a proved model, checked against the code

> [!IMPORTANT]
> The contents of this directory and all sub-directories are almost entirely AI-generated.
> While the researchers who produced it have manually reviewed claims for integrity, this
> artifact is only intended to serve as a demonstration of a research project, not an
> authoritative or maintained work; owners and users of the upstream etcd-io/raft project
> should not rely on it as is.

This directory holds a formal model of [etcd-io/raft](https://github.com/etcd-io/raft),
machine-checked proofs that the model is safe, and a test harness that checks the running
implementation against the model step by step under fault injection
([Antithesis](https://antithesis.com)) and in a deterministic simulator. Everything here is an
addition to the upstream checkout this branch starts from (`99f9ffb`). Raft's own source and
[`go.mod`](../go.mod) are not modified; the fixes described below are patch files.

## Claims

1. **A model of the implementation.** [`spec/EtcdRaft.tla`](spec/EtcdRaft.tla) is a TLA+ model of etcd-io/raft at
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
   - **TLAPS** proves `Spec => []P` on [`EtcdRaft.tla`](spec/EtcdRaft.tla) itself for election safety, log
     matching, commit safety, state machine safety, leader completeness and read-index safety
     ([`spec/proof/`](spec/proof/)).
   - **Lean 4 / Veil** proves every state invariant of the model, those six included, on a
     line-by-line translation of it ([`veil/`](veil/)).
3. **The implementation follows the model.** Each node runs a `RawNode` through the
   [`rawnode/`](rawnode/) package, which reports every step at raft's boundary. TLC checks, while the
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
   [`patches/README.md`](patches/README.md).

The proofs are about the model; that the code follows the model is established by testing,
on the behaviours the tests reach. [`spec/README.md`](spec/README.md) lists every assumption and limitation.

## Layout

| Path | Contents |
|---|---|
| [`spec/`](spec/) | The TLA+ model `EtcdRaft.tla`, the trace binding `EtcdBinding.tla` (report → model actions), bounded instances for TLC. [`spec/README.md`](spec/README.md): what is modelled, the properties, assumptions and limitations |
| [`spec/proof/`](spec/proof/) | TLAPS proofs: 19 modules, 9,148 obligations. [`spec/proof/README.md`](spec/proof/README.md) |
| [`veil/`](veil/) | The model in Lean 4 / [Veil](https://veil.dev), with stored proofs: 53 invariants × (23 actions + initial state) = 1,272 goals. [`veil/README.md`](veil/README.md) |
| [`patches/`](patches/) | Two fixes to raft. [`patches/README.md`](patches/README.md): the faults, the fixes, and workarounds the harness uses |
| [`repro/`](repro/) | Reproducers of the faults against unmodified raft: `asyncvote` (E1), `confsplit` (E3), `emptyjoint` (E4), and `aba`, a schedule used to test the check |
| [`rawnode/`](rawnode/) | One raft node: drives a `RawNode`, writes its storage (bbolt), and reports each step; three write modes, batching, snapshots, read index, membership changes |
| [`server/`](server/) | The service under test: `rawnode` with a running-sum state machine, TCP transport, HTTP API |
| [`sim/`](sim/) | Deterministic simulator: the same `rawnode` code with simulated time, network and disk, driven by a seed |
| [`driver/`](driver/) | The test driver (Rust): client workload, client-visible checks, collection of reports, the live trace check, Antithesis assertions |
| [`tracekit/`](tracekit/) | The raft-independent part of trace checking: report sink (Go), collector (Rust), streaming TLC checker (Python, Java), conventions ([`tracekit/tla/TraceKit.tla`](tracekit/tla/TraceKit.tla)) |
| [`traces/`](traces/) | Recorded report streams, used as test fixtures |
| [`scripts/`](scripts/) | Entry points: setup, simulator batches, local runs, model checking, Lean checks, trace-check tests, reproducers, Antithesis launch |
| [`config/`](config/), [`config5/`](config5/), [`local/`](local/) | Docker Compose files for Antithesis (3 and 5 nodes) and for local runs |

## Verify independently

All commands run from this directory (`antithesis-fm/`).

### 1. Install

| Tool | Used for | Install |
|---|---|---|
| Java 17+, Python 3 | TLC and trace checking | system packages |
| Go 1.26+ | simulator, reproducers | [go.dev/dl](https://go.dev/dl) |
| Docker | local cluster runs; compiling the stream operator if `javac` is absent | system packages |
| elan (Lean 4) | Lean proofs. The toolchain (`v4.35.0`) is pinned in [`veil/lean-toolchain`](veil/lean-toolchain); Veil is pinned in [`veil/lakefile.lean`](veil/lakefile.lean) | `curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \| sh -s -- -y --default-toolchain none` |
| tlapm 1.6.0-pre | TLAPS proofs (bundles Isabelle, Zenon, Z3) | `curl -fsSL https://github.com/tlaplus/tlapm/releases/download/1.6.0-pre/tlapm-1.6.0-pre-x86_64-linux-gnu.tar.gz \| tar xz -C "$HOME" && export PATH=$HOME/tlapm/bin:$PATH` |

`1.6.0-pre` is a rolling pre-release. The proofs were checked with tlapm commit
[`bf665f4`](https://github.com/tlaplus/tlapm/commit/bf665f4); if the downloaded binary does not
run (it needs glibc 2.42 or later) or gives different results, build that commit
([DEVELOPING.md](https://github.com/tlaplus/tlapm/blob/bf665f4/DEVELOPING.md)) and set `TLAPM` to it.

Then:

```sh
scripts/setup.sh     # fetches tla2tools.jar v1.8.0 and CommunityModules, compiles the stream operator,
                     # lists missing tools
```

### 2. TLAPS proofs (about 45 minutes; needs up to 24 GB of memory)

```sh
(cd spec && sha256sum -c proof/SPEC.sha256)   # the proofs are about these exact spec files
spec/proof/final.sh                            # every module from a clean cache, --strict;
                                               # TLAPM=/path/to/tlapm to use another binary
```

Expected: one line per module, `All N obligations proved`, for all 19 modules, then
`DONE ... (exit 0)`. The theorems are in [`spec/proof/EtcdSafety.tla`](spec/proof/EtcdSafety.tla).

### 3. Lean proofs (about 20 minutes on 32 cores, plus a few for the first Veil build)

```sh
scripts/veil-check.sh
```

Expected: last line `24 of 24 files ok` (Lean accepts all 1,272 theorems, no error, no `sorry`).
The `Restart` file takes longest. `cd veil && lake build` checks the same file in one process
(slower).

That the Lean model is the TLA+ model is checked by counting states on shared bounded
instances. Both commands must print the same number (table in [`veil/README.md`](veil/README.md)):

```sh
scripts/mc.sh MCMemCount2.cfg 900         # TLC: `completed, 15800 states, no violation`
scripts/veil-count.sh m2                  # Veil: `No violation (explored 15800 states)`
```

### 4. Model checking with TLC

```sh
scripts/mc.sh MCCount4.cfg 1800       # read index included: 1631864 states, no violation
scripts/mc.sh MCReadMem3.cfg 3600     # membership change and read index: 1312146 states, no violation
```

Other instances are listed in [`spec/README.md`](spec/README.md). Output is one line (`completed, N states, no
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

Simulator and local-run variants are listed in [`spec/README.md`](spec/README.md) ("Modes").

### 6. Reproduce the faults

```sh
scripts/e1.sh                 # E1: unpatched raft diverges; with the patch it does not
scripts/e3.sh                 # E3: diverges with split writes; safe with atomic writes or the patch
go run ./repro/emptyjoint     # E4: panics on apply
```

### 7. Antithesis

`scripts/launch.sh 50` builds the images and submits a 50-hour run. It needs an Antithesis
tenant and the `snouty` CLI. The same environment variables as for [`local-run.sh`](scripts/local-run.sh) select the
mode.
