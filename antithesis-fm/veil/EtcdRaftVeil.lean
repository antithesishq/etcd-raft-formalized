module

public import Veil

/-!
`../spec/EtcdRaft.tla` in Veil, one to one: same variables, actions, parameters and properties,
including membership changes and the read index. Each TLA+ definition is quoted above its
translation.

Layout: TSet lemmas and the record types; the namespace `MemberCore`, the membership argument
in plain Lean, independent of the model (`IsQ.inter_next`, `core`, `read_core`); the state and
actions; lemmas on logs (`LogLemmas`) and the section `Quorums`, which ties `MemberCore` to the
model's variables; the invariants; and the proofs, one section per action.

Proved invariants: every state invariant of `EtcdRaft.tla` (ElectionSafety, OneVotePerTerm,
LogMatching, CommitSafety, StateMachineSafety, LeaderCompleteness, CommittedEntriesPreserved,
LeaderLogIsLed, ConfirmedWithinLog, RequestsFromLed, ConfIsCommitted, LeaderConf,
ReadIndexSafety, ReadMsgsOld, ReadFloorOld, ReadFloorBound) and 36 supporting ones, 53 in all.

Encoding:
* `Server` is the type `server`; `Cardinality` of a set given by a condition is `Card`,
  counted over the list of servers given by the class `Servers`.
* `Nil` is `none`. A log is a `List`; entry `k` is element `k - 1`.
* `confirmed[i]` is `confirmedTerm i`, `confirmedIndex i`; `read` is `readOn`, `readDone`,
  `readTerm`, `readIndex`, `readFloor`, `readMsgs`, `readResp`.
* `msgs` facts are the constructors of `Msg`; `msgs`, `votes`, `leaders`, `commits` are TSets.
* `ledLog` is `Nat → Option log`, `none` outside its domain.
* `config[i]` is `cIn i`, `cOut i`; `ledConf[t]` is `lIn t`, `lOut t`; `InitVoters` is `initV`.
* A `conf` entry with value `v` adds `chAdd v`, removes `chRemove v`, is joint if `chJoint v`,
  leaves joint if `chLeave v`. These are arbitrary, so the proofs cover every `ConfChanges`.
* Actions read message fields through accessors, not `match`: Veil generates no goals for a
  match inside an action.
-/

namespace EtcdRaftVeil.Lemmas
open Veil

-- `prove_goal_unregistered A I by …` states the same goal as `prove_veil_invariant_goal A I
-- using wp by …` (Module.mkInvariantGoalVC, then `unveil`) and checks the proof, but omits the
-- `@[veil]` registration. For SwitchConf goals that registration (validateTheoremWitness) does
-- not terminate with Veil 1287c31d / Lean 4.35.0, so SwitchConf uses this command.
open Lean Elab Command in
elab "prove_goal_unregistered " actionId:ident propertyId:ident " by " proof:Lean.Parser.Tactic.tacticSeqIndentGt : command => do
  let mod ← getCurrentModule (errMsg := "not in a Veil module")
  mod.throwIfSpecNotFinalized
  withRef actionId do
    let mod ← mod.ensureVerificationSpec actionId
    let vc ← mod.mkInvariantGoalVC actionId propertyId VCStyle.wp
    let thmId := mkIdentFrom actionId vc.name
    let proof : TSyntax ``Lean.Parser.Tactic.tacticSeq := ⟨proof.raw⟩
    let cmd ← `(command|
      theorem $thmId $(vc.params)* : $(vc.statement) := by
        unveil
        ($proof))
    elabCommand cmd

-- Facts about TSets, without decidable equality on elements (none is available for `server`).

theorem ifPos {c : Prop} {h : Decidable c} {α : Sort _} {a b : α} (hc : c) : @ite α c h a b = a := by
  simp [hc]

theorem ifNeg {c : Prop} {h : Decidable c} {α : Sort _} {a b : α} (hc : ¬ c) : @ite α c h a b = b := by
  simp [hc]

theorem mem_iff {α κ : Type} [TSet α κ] (a : α) (s : κ) : a ∈ s ↔ TSet.contains a s = true := Iff.rfl

theorem contains_insert_iff {α κ : Type} [TSet α κ] (a b : α) (s : κ) :
    TSet.contains a (TSet.insert b s) = true ↔ a = b ∨ TSet.contains a s = true := by
  rcases Classical.em (a = b) with h | h
  · subst h; simp [TSet.contains_insert_self]
  · simp [TSet.contains_insert_other _ _ _ h, h]

theorem mem_insert {α κ : Type} [TSet α κ] (a b : α) (s : κ) :
    a ∈ TSet.insert b s ↔ a = b ∨ a ∈ s := contains_insert_iff a b s

theorem not_mem_empty {α κ : Type} [TSet α κ] (a : α) : ¬ a ∈ (TSet.empty : κ) := by
  simp [mem_iff, TSet.empty_contains]

theorem sub_empty {α κ : Type} [TSet α κ] (a : { x : α // x ∈ (TSet.empty : κ) }) : False :=
  not_mem_empty _ a.property

end EtcdRaftVeil.Lemmas

veil module EtcdRaftVeil

@[veil_decl]
inductive EntryType where
  | config
  | noop
  | command
  | conf

deriving instance Veil.Enumeration for EntryType

-- Entry(t, ty, v) == [term |-> t, type |-> ty, value |-> v]
@[veil_decl]
structure Entry (value : Type) where
  term : Nat
  kind : EntryType
  value : Option value

@[veil_decl]
inductive Msg (server value : Type) where
  -- [type |-> "vote", src, term, lastLogIndex, lastLogTerm]
  | vote (src : server) (term : Nat) (lastLogIndex : Nat) (lastLogTerm : Nat)
  -- [type |-> "grant", src, dst, term]
  | grant (src : server) (dst : server) (term : Nat)
  -- [type |-> "append", src, dst, term, prevLogIndex, prevLogTerm, entries, commit]
  | append (src : server) (dst : server) (term : Nat) (prevLogIndex : Nat) (prevLogTerm : Nat)
      (entries : List (Entry value)) (commit : Nat)
  -- [type |-> "ack", src, dst, term, index]
  | ack (src : server) (dst : server) (term : Nat) (index : Nat)

-- Append-request fields (`m.dst`, `m.entries`, ...); other kinds' values are never read.
def Msg.isAppend {server value : Type} (m : Msg server value) : Bool :=
  match m with | .append .. => true | _ => false
def Msg.src {server value : Type} (m : Msg server value) : server :=
  match m with | .vote s .. => s | .grant s .. => s | .append s .. => s | .ack s .. => s
def Msg.dst {server value : Type} (m : Msg server value) : server :=
  match m with | .vote s .. => s | .grant _ d _ => d | .append _ d .. => d | .ack _ d .. => d
def Msg.term {server value : Type} (m : Msg server value) : Nat :=
  match m with | .vote _ t .. => t | .grant _ _ t => t | .append _ _ t .. => t | .ack _ _ t _ => t
def Msg.prevLogIndex {server value : Type} (m : Msg server value) : Nat :=
  match m with | .append _ _ _ p .. => p | _ => 0
def Msg.prevLogTerm {server value : Type} (m : Msg server value) : Nat :=
  match m with | .append _ _ _ _ pt .. => pt | _ => 0
def Msg.entries {server value : Type} (m : Msg server value) : List (Entry value) :=
  match m with | .append _ _ _ _ _ es _ => es | _ => []
def Msg.commit {server value : Type} (m : Msg server value) : Nat :=
  match m with | .append _ _ _ _ _ _ c => c | _ => 0

-- An element of `votes`: [voter, term, cand].
@[veil_decl]
structure Vote (server : Type) where
  voter : server
  term : Nat
  cand : server

-- An element of `leaders`: [server, term].
@[veil_decl]
structure Elected (server : Type) where
  server : server
  term : Nat

-- An element of `commits`: [server, term, entries].
@[veil_decl]
structure Commit (server value : Type) where
  server : server
  term : Nat
  entries : List (Entry value)

-- An element of `applied`: [server, index, entry].
@[veil_decl]
structure Applied (server value : Type) where
  server : server
  index : Nat
  entry : Entry value

-- TermAt(l, k) == IF k > 0 /\ k <= Len(l) THEN l[k].term ELSE 0
def TermAt {value : Type} (l : List (Entry value)) (k : Nat) : Nat :=
  match k with
  | 0 => 0
  | k + 1 => match l[k]? with
    | some e => e.term
    | none => 0

-- Stands for `l[k]` where k is outside the log; never read (see Apply).
def noEntry {value : Type} : Entry value := { term := 0, kind := .config, value := none }

-- SubSeq(l, m, n)
def SubSeq {α : Type} (l : List α) (m n : Nat) : List α := (l.drop (m - 1)).take (n + 1 - m)

-- IsPrefix(a, b) == Len(a) <= Len(b) /\ a = SubSeq(b, 1, Len(a))
def IsPrefix {α : Type} [DecidableEq α] (a b : List α) : Bool :=
  decide (a.length ≤ b.length ∧ a = SubSeq b 1 a.length)

/-- The servers are finitely many: a list of all of them, without repeats. -/
class Servers (server : Type) where
  all : List server
  complete : ∀ s, s ∈ all
  nodup : all.Nodup

instance (n : Nat) : Servers (Fin n) where
  all := List.finRange n
  complete := by simp
  nodup := List.nodup_finRange n

-- Cardinality({s \in Server : p(s)})
def Card {server : Type} [Servers server] (p : server → Bool) : Nat :=
  ((Servers.all (server := server)).filter p).length

-- IsQuorum(S) == Cardinality(S) * 2 > Cardinality(Server)
def IsQuorum {server : Type} [Servers server] (p : server → Bool) : Bool :=
  decide (Card p * 2 > Card (fun _ : server => true))

-- Facts about quorums, for the proofs at the end of this file.

theorem filter_len_le_of_imp {α : Type} (l : List α) (p q : α → Bool) (h : ∀ a, p a = true → q a = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons]
    cases hp : p x <;> cases hq : q x <;> simp <;> first | omega | (have := h x hp; simp_all)

theorem filter_len_add {α : Type} (l : List α) (p q : α → Bool) :
    (l.filter p).length + (l.filter q).length ≤ l.length + (l.filter (fun a => p a && q a)).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons, List.length_cons]
    cases hp : p x <;> cases hq : q x <;> simp <;> omega

theorem filter_true_len {α : Type} (l : List α) : (l.filter (fun _ => true)).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp

theorem IsQuorum.iff {server : Type} [Servers server] (p : server → Bool) :
    IsQuorum p = true ↔
      ((Servers.all (server := server)).filter p).length * 2 > (Servers.all (server := server)).length := by
  unfold IsQuorum Card
  rw [filter_true_len]
  exact decide_eq_true_iff

theorem IsQuorum.mono {server : Type} [Servers server] (p q : server → Bool)
    (h : ∀ a, p a = true → q a = true) (hp : IsQuorum p = true) : IsQuorum q = true := by
  rw [IsQuorum.iff] at *
  have := filter_len_le_of_imp (Servers.all (server := server)) p q h
  omega

theorem IsQuorum.inter {server : Type} [Servers server] (p q : server → Bool)
    (hp : IsQuorum p = true) (hq : IsQuorum q = true) : ∃ a, p a = true ∧ q a = true := by
  rw [IsQuorum.iff] at *
  have h := filter_len_add (Servers.all (server := server)) p q
  have hpos : 0 < ((Servers.all (server := server)).filter (fun a => p a && q a)).length := by omega
  obtain ⟨a, ha⟩ := List.exists_mem_of_length_pos hpos
  simp only [List.mem_filter, Bool.and_eq_true] at ha
  exact ⟨a, ha.2⟩

-- Configurations, quorums and leader completeness with membership changes, over plain lists.
namespace MemberCore

theorem filter_len_add_eq {α : Type} (l : List α) (p q : α → Bool) :
    (l.filter p).length + (l.filter q).length =
      (l.filter (fun a => p a || q a)).length + (l.filter (fun a => p a && q a)).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons, List.length_cons]
    cases hp : p x <;> cases hq : q x <;> simp <;> omega

theorem filter_len_le' {α : Type} (l : List α) (p q : α → Bool) (h : ∀ a, p a = true → q a = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons]
    cases hp : p x <;> cases hq : q x <;> simp <;> first | omega | (have := h x hp; simp_all)

theorem filter_pos {α : Type} (l : List α) (p : α → Bool) (h : 0 < (l.filter p).length) :
    ∃ a, p a = true := by
  obtain ⟨a, ha⟩ := List.exists_mem_of_length_pos h
  exact ⟨a, (List.mem_filter.1 ha).2⟩

section Quorums
variable {server : Type} [Servers server]

theorem Card.add (p q : server → Bool) :
    Card p + Card q = Card (fun a => p a || q a) + Card (fun a => p a && q a) :=
  filter_len_add_eq _ p q

theorem Card.le (p q : server → Bool) (h : ∀ a, p a = true → q a = true) : Card p ≤ Card q :=
  filter_len_le' _ p q h

theorem Card.pos (p : server → Bool) (h : 0 < Card p) : ∃ a, p a = true := filter_pos _ p h

theorem Card.zero (p : server → Bool) (h : ∀ a, p a = false) : Card p = 0 := by
  unfold Card
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro a _; simp [h a]

/-- A majority of the voters `v` is in `p`. -/
def Maj (p v : server → Bool) : Prop := Card (fun s => p s && v s) * 2 > Card v

theorem Maj.mono (p q v : server → Bool) (h : ∀ a, p a = true → q a = true) (hp : Maj p v) : Maj q v := by
  unfold Maj at *
  have := Card.le (fun s => p s && v s) (fun s => q s && v s) (by
    intro a ha; simp only [Bool.and_eq_true] at ha ⊢; exact ⟨h a ha.1, ha.2⟩)
  omega

theorem Maj.inter (p q v : server → Bool) (hp : Maj p v) (hq : Maj q v) : ∃ a, p a = true ∧ q a = true := by
  unfold Maj at *
  have h := Card.add (fun s => p s && v s) (fun s => q s && v s)
  have hle : Card (fun a => (p a && v a) || (q a && v a)) ≤ Card v :=
    Card.le _ _ (by intro a ha; cases hv : v a <;> simp_all)
  have hpos : 0 < Card (fun a => (p a && v a) && (q a && v a)) := by omega
  obtain ⟨a, ha⟩ := Card.pos _ hpos
  simp only [Bool.and_eq_true] at ha
  exact ⟨a, ha.1.1, ha.2.1⟩

/-- Majorities of two sets of voters that differ in at most one node share a node. -/
theorem Maj.inter_near (p q v w : server → Bool) (hd : Card (fun s => v s != w s) ≤ 1)
    (hp : Maj p v) (hq : Maj q w) : ∃ a, p a = true ∧ q a = true := by
  unfold Maj at *
  -- a: in w and not in v; b: in v and not in w
  have hab : Card (fun s => w s && !v s) + Card (fun s => v s && !w s) ≤ 1 := by
    have h := Card.add (fun s => w s && !v s) (fun s => v s && !w s)
    have h0 : Card (fun a => (w a && !v a) && (v a && !w a)) = 0 :=
      Card.zero _ (by intro a; cases v a <;> cases w a <;> rfl)
    have hle : Card (fun a => (w a && !v a) || (v a && !w a)) ≤ Card (fun s => v s != w s) :=
      Card.le _ _ (by intro a; cases v a <;> cases w a <;> simp)
    omega
  -- |w| + |v \ w| = |v| + |w \ v|
  have hvw : Card w + Card (fun s => v s && !w s) = Card v + Card (fun s => w s && !v s) := by
    have h1 := Card.add w (fun s => v s && !w s)
    have h2 := Card.add v (fun s => w s && !v s)
    have e1 : Card (fun a => w a && (v a && !w a)) = 0 :=
      Card.zero _ (by intro a; cases v a <;> cases w a <;> rfl)
    have e2 : Card (fun a => v a && (w a && !v a)) = 0 :=
      Card.zero _ (by intro a; cases v a <;> cases w a <;> rfl)
    have e3 : Card (fun a => w a || (v a && !w a)) = Card (fun a => v a || (w a && !v a)) := by
      congr 1; funext a; cases v a <;> cases w a <;> rfl
    omega
  -- q's part of w is, but for the node only w has, in v
  have hqv : Card (fun s => q s && w s) ≤ Card (fun s => q s && v s) + Card (fun s => w s && !v s) := by
    have h := Card.add (fun s => q s && v s) (fun s => w s && !v s)
    have hle : Card (fun s => q s && w s) ≤ Card (fun a => (q a && v a) || (w a && !v a)) :=
      Card.le _ _ (by intro a; cases q a <;> cases v a <;> cases w a <;> simp)
    omega
  have h := Card.add (fun s => p s && v s) (fun s => q s && v s)
  have hle : Card (fun a => (p a && v a) || (q a && v a)) ≤ Card v :=
    Card.le _ _ (by intro a ha; cases hv : v a <;> simp_all)
  have hpos : 0 < Card (fun a => (p a && v a) && (q a && v a)) := by omega
  obtain ⟨a, ha⟩ := Card.pos _ hpos
  simp only [Bool.and_eq_true] at ha
  exact ⟨a, ha.1.1, ha.2.1⟩

end Quorums

/-- A change of membership: nodes added, nodes removed, joint, leaves joint. -/
structure Change (server : Type) where
  add : List server
  remove : List server
  joint : Bool
  leave : Bool

/-- The voters, and the voters before a joint change that is not left yet. -/
structure Conf (server : Type) where
  inn : server → Bool
  out : server → Bool

section Confs
variable {server : Type} [DecidableEq server]

def noVoters : server → Bool := fun _ => false

/-- Target(C, d) == (C.in \cup Range(d.add)) \ Range(d.remove) -/
def target (C : Conf server) (d : Change server) : server → Bool :=
  fun s => (C.inn s || decide (s ∈ d.add)) && !decide (s ∈ d.remove)

/-- NextConf(C, d) -/
def nextConf (C : Conf server) (d : Change server) : Conf server :=
  if d.leave then { inn := C.inn, out := noVoters }
  else { inn := target C d, out := if d.joint then C.inn else noVoters }

variable [Servers server]

/-- IsQuorum(S, C) -/
def IsQ (p : server → Bool) (C : Conf server) : Prop :=
  Maj p C.inn ∧ (Card C.out = 0 ∨ Maj p C.out)

instance (p : server → Bool) (C : Conf server) : Decidable (IsQ p C) := by
  unfold IsQ Maj; infer_instance

/-- Legal(C, d) -/
def Legal (C : Conf server) (d : Change server) : Prop :=
  if d.leave then 0 < Card C.out
  else Card C.out = 0 ∧ 0 < Card (target C d) ∧
    (d.joint = true ∨ Card (fun s => C.inn s != target C d s) ≤ 1)

instance (C : Conf server) (d : Change server) : Decidable (Legal C d) := by
  unfold Legal; infer_instance

theorem IsQ.mono (p q : server → Bool) (C : Conf server) (h : ∀ a, p a = true → q a = true)
    (hp : IsQ p C) : IsQ q C :=
  ⟨Maj.mono p q _ h hp.1, hp.2.imp id (Maj.mono p q _ h)⟩

theorem IsQ.inter (p q : server → Bool) (C : Conf server) (hp : IsQ p C) (hq : IsQ q C) :
    ∃ a, p a = true ∧ q a = true := Maj.inter p q _ hp.1 hq.1

/-- Quorums of a configuration and of the one a change it takes makes of it share a node. -/
theorem IsQ.inter_next (p q : server → Bool) (C : Conf server) (d : Change server) (hl : Legal C d)
    (hp : IsQ p C) (hq : IsQ q (nextConf C d)) : ∃ a, p a = true ∧ q a = true := by
  unfold Legal at hl
  unfold nextConf at hq
  cases hlv : d.leave with
  | true =>
    rw [hlv] at hq
    exact Maj.inter p q _ hp.1 hq.1
  | false =>
    rw [hlv] at hl hq
    simp only [Bool.false_eq_true, if_false] at hl hq
    obtain ⟨hout, _, hj⟩ := hl
    cases hjt : d.joint with
    | true =>
      rw [hjt] at hq
      simp only [if_true] at hq
      rcases hq.2 with h0 | hm
      · -- no voters at all: then p is no majority of them
        have := hp.1
        unfold Maj at this
        have e1 : Card C.inn = 0 := h0
        have e2 := Card.le (fun s => p s && C.inn s) C.inn (by intro a ha; simp only [Bool.and_eq_true] at ha; exact ha.2)
        omega
      · exact Maj.inter p q _ hp.1 hm
    | false =>
      rw [hjt] at hj
      rcases hj with hj | hj
      · exact absurd hj (by simp)
      · exact Maj.inter_near p q _ _ hj hp.1 hq.1

end Confs

/-!
Logs. `ε` is the type of entries; `isc e`: the entry is a change of membership, `chg e` which.
Positions are counted from 1, as in the model.
-/
section Logs
variable {server ε : Type} [DecidableEq server]
variable (tm : ε → Nat) (isc : ε → Bool) (chg : ε → Change server)

/-- The entry at position p (from 1) is a change of membership. -/
def isC (l : List ε) (p : Nat) : Bool :=
  match p with
  | 0 => false
  | p + 1 => (l[p]?).any isc

/-- The term of the entry at position p; 0 if there is none. -/
def tmAt (l : List ε) (p : Nat) : Nat :=
  match p with
  | 0 => 0
  | p + 1 => ((l[p]?).map tm).getD 0

/-- ConfOf(l, a): what the changes among the first a entries make of the first configuration. -/
def confOf (init : Conf server) (l : List ε) : Nat → Conf server
  | 0 => init
  | a + 1 =>
    match l[a]? with
    | some e => if isc e then nextConf (confOf init l a) (chg e) else confOf init l a
    | none => confOf init l a

theorem isC_take (l : List ε) (a p : Nat) (h : p ≤ a) : isC isc (l.take a) p = isC isc l p := by
  cases p with
  | zero => rfl
  | succ p => simp only [isC]; rw [List.getElem?_take_of_lt (by omega)]

theorem tmAt_take (l : List ε) (a p : Nat) (h : p ≤ a) : tmAt tm (l.take a) p = tmAt tm l p := by
  cases p with
  | zero => rfl
  | succ p => simp only [tmAt]; rw [List.getElem?_take_of_lt (by omega)]

theorem isC_le (l : List ε) (p : Nat) (h : isC isc l p = true) : 1 ≤ p ∧ p ≤ l.length := by
  cases p with
  | zero => simp [isC] at h
  | succ p =>
    simp only [isC] at h
    cases hg : l[p]? with
    | none => rw [hg] at h; simp at h
    | some e => have := List.getElem?_eq_some_iff.1 hg; obtain ⟨hl, _⟩ := this; omega

theorem isC_congr (l l' : List ε) (a p : Nat) (h : l.take a = l'.take a) (hp : p ≤ a) :
    isC isc l p = isC isc l' p := by
  rw [← isC_take isc l a p hp, ← isC_take isc l' a p hp, h]

theorem tmAt_congr (l l' : List ε) (a p : Nat) (h : l.take a = l'.take a) (hp : p ≤ a) :
    tmAt tm l p = tmAt tm l' p := by
  rw [← tmAt_take tm l a p hp, ← tmAt_take tm l' a p hp, h]

theorem take_take_eq {α : Type} (l l' : List α) (a b : Nat) (h : l.take a = l'.take a) (hb : b ≤ a) :
    l.take b = l'.take b := by
  have : (l.take a).take b = (l'.take a).take b := by rw [h]
  rwa [List.take_take, List.take_take, Nat.min_eq_left hb] at this

theorem confOf_congr (init : Conf server) (l l' : List ε) (a : Nat) (h : l.take a = l'.take a) :
    confOf isc chg init l a = confOf isc chg init l' a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    have h' := take_take_eq l l' (a + 1) a h (by omega)
    have hg : l[a]? = l'[a]? := by
      have : (l.take (a + 1))[a]? = (l'.take (a + 1))[a]? := by rw [h]
      rwa [List.getElem?_take_of_lt (by omega), List.getElem?_take_of_lt (by omega)] at this
    simp only [confOf]
    rw [hg, ih h']

/-- No change of membership at the positions in (a, b]. -/
def NoC (l : List ε) (a b : Nat) : Prop := ∀ p, a < p → p ≤ b → isC isc l p = false

theorem confOf_skip (init : Conf server) (l : List ε) (a b : Nat) (hab : a ≤ b) (h : NoC isc l a b) :
    confOf isc chg init l b = confOf isc chg init l a := by
  induction b with
  | zero => have : a = 0 := by omega
            subst this; rfl
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le hab with heq | hlt
    · rw [heq]
    · have hn := h (b + 1) (by omega) (by omega)
      have ih' := ih (by omega) (fun p h1 h2 => h p h1 (by omega))
      simp only [confOf]
      simp only [isC] at hn
      cases hg : l[b]? with
      | none => simpa using ih'
      | some e =>
        rw [hg] at hn
        simp only [Option.any_some] at hn
        simp [hn, ih']

theorem confOf_step (init : Conf server) (l : List ε) (p : Nat) (h : isC isc l (p + 1) = true) :
    ∃ e, l[p]? = some e ∧ confOf isc chg init l (p + 1) = nextConf (confOf isc chg init l p) (chg e) := by
  simp only [isC] at h
  cases hg : l[p]? with
  | none => rw [hg] at h; simp at h
  | some e =>
    rw [hg] at h
    simp only [Option.any_some] at h
    exact ⟨e, rfl, by simp [confOf, hg, h]⟩

/-- The first change of membership after position a, up to b, if there is one. -/
theorem first_change (l : List ε) (a b : Nat) :
    NoC isc l a b ∨ ∃ p, a < p ∧ p ≤ b ∧ isC isc l p = true ∧ NoC isc l a (p - 1) := by
  induction b with
  | zero => exact Or.inl (fun p h1 h2 => by omega)
  | succ b ih =>
    rcases ih with h | ⟨p, h1, h2, h3, h4⟩
    · by_cases hb : a < b + 1 ∧ isC isc l (b + 1) = true
      · exact Or.inr ⟨b + 1, hb.1, Nat.le_refl _, hb.2, by simpa using h⟩
      · refine Or.inl (fun p h1 h2 => ?_)
        rcases Nat.eq_or_lt_of_le h2 with heq | hlt
        · subst heq
          cases hc : isC isc l (b + 1) with
          | false => rfl
          | true => exact absurd ⟨h1, hc⟩ hb
        · exact h p h1 (by omega)
    · exact Or.inr ⟨p, h1, by omega, h3, h4⟩

/-- At most one change of membership at the positions in (a, b]. -/
def AtMostOne (l : List ε) (a b : Nat) : Prop :=
  ∀ p q, a < p → p < q → q ≤ b → isC isc l p = true → isC isc l q = true → False

end Logs

section Lists
variable {α : Type}

theorem prefix_take (a b : List α) (m : Nat) (h : a <+: b) (hm : m ≤ a.length) : a.take m = b.take m := by
  obtain ⟨s, rfl⟩ := h
  rw [List.take_append_of_le_length hm]

theorem take_eq_of_prefix (A X : List α) (c : Nat) (h : A.take c <+: X) (hc : c ≤ A.length) :
    A.take c = X.take c := by
  have := prefix_take _ _ c h (by simp; omega)
  rwa [List.take_take, Nat.min_self] at this

theorem take_prefix_of_eq (A X : List α) (c : Nat) (h : A.take c = X.take c) : A.take c <+: X := by
  rw [h]; exact List.take_prefix _ _

/-- Lists whose first d and e entries are parts of comparable lists agree up to m ≤ d, e. -/
theorem agree (A B kD kE : List α) (d e m : Nat) (hcmp : kD <+: kE ∨ kE <+: kD)
    (hd : d ≤ kD.length) (he : e ≤ kE.length) (hA : kD.take d = A.take d) (hB : kE.take e = B.take e)
    (hmd : m ≤ d) (hme : m ≤ e) : A.take m = B.take m := by
  have h1 : A.take m = kD.take m := (take_take_eq _ _ d m hA hmd).symm
  have h2 : B.take m = kE.take m := (take_take_eq _ _ e m hB hme).symm
  rw [h1, h2]
  rcases hcmp with h | h
  · exact prefix_take _ _ m h (by omega)
  · exact (prefix_take _ _ m h (by omega)).symm

end Lists

/-!
The argument. `led t` is the log of the leader of term t. `K k t`: the entries k are recorded
as committed under term t. `acked t c n`: node n has acknowledged the first c entries of the
leader log of term t to its leader. `good t c`: what else a committed prefix needs (in the
model: it is not empty and ends with an entry of its term).
-/
section Core
variable {server ε : Type} [DecidableEq server] [Servers server]
variable (tm : ε → Nat) (isc : ε → Bool) (chg : ε → Change server) (init : Conf server)
variable (led : Nat → Option (List ε)) (K : List ε → Nat → Prop)
variable (acked : Nat → Nat → server → Bool) (good : Nat → Nat → Prop)

/-- The leader of term t (log A) committed its first c entries with the configuration of A's
first d entries: a quorum of it acknowledged them, the d entries were committed at term ≤ t,
and at most one change lies in (d, c]. -/
structure RootAt (t c d : Nat) (A : List ε) : Prop where
  isLed : led t = some A
  len : c ≤ A.length
  isGood : good t c
  cover : d = 0 ∨ ∃ k tk, K k tk ∧ tk ≤ t ∧ d ≤ k.length ∧ k.take d = A.take d
  one : AtMostOne isc A d c
  quorum : IsQ (acked t c) (confOf isc chg init A d)

/-- What `core` asks of the model's state, besides the log it is about. -/
structure World : Prop where
  /-- CommitSafety, of what is recorded so far. -/
  cmp : ∀ k1 t1 k2 t2, K k1 t1 → K k2 t2 → k1 <+: k2 ∨ k2 <+: k1
  /-- A change in a committed prefix was first committed by a leader not yet counting with it. -/
  first : ∀ k tk, K k tk → ∀ p, isC isc k p = true →
    ∃ t1 c1 d1 A1, RootAt isc chg init led K acked good t1 c1 d1 A1 ∧ K (A1.take c1) t1 ∧ t1 ≤ tk ∧ p ≤ c1 ∧ d1 < p
  /-- A change in a leader log is one that the configuration before it takes. -/
  legal : ∀ t A, led t = some A → ∀ p e, A[p]? = some e → isc e = true →
    Legal (confOf isc chg init A p) (chg e)
  /-- A leader log has no entry of a later term. -/
  sorted : ∀ t A, led t = some A → ∀ p, p ≤ A.length → tmAt tm A p ≤ t

variable (u : Nat) (B : List ε) (e : Nat) (V : server → Bool)

/-- What `core` asks of the log B of the (prospective) leader of term u, elected by V with the
configuration of B's first e entries. -/
structure Target : Prop where
  cover : e = 0 ∨ ∃ k tk, K k tk ∧ tk < u ∧ e ≤ k.length ∧ k.take e = B.take e
  /-- At most one change of earlier terms after e. -/
  one : ∀ p q, e < p → p < q → isC isc B p = true → isC isc B q = true →
    tmAt tm B p < u → tmAt tm B q < u → False
  quorum : IsQ V (confOf isc chg init B e)
  /-- Entries a voter acknowledged earlier are in B, or missing from a leader log in between. -/
  early : ∀ n, V n = true → ∀ t c A, led t = some A → good t c → c ≤ A.length → acked t c n = true → t < u →
    A.take c <+: B ∨ ∃ w Bw, t < w ∧ w < u ∧ led w = some Bw ∧ ¬ A.take c <+: Bw
  legal : ∀ p e', B[p]? = some e' → isc e' = true → Legal (confOf isc chg init B p) (chg e')
  /-- Leader completeness for the terms before u. -/
  before : ∀ w, w < u → ∀ t c d A, RootAt isc chg init led K acked good t c d A → t < w →
    ∀ Bw, led w = some Bw → A.take c <+: Bw

variable {tm isc chg init led K acked good u B e V}

/-- A voter of the election had acknowledged the entries: the standard argument. -/
theorem near (hT : Target tm isc chg init led K acked good u B e V) {t c d : Nat} {A : List ε}
    (hr : RootAt isc chg init led K acked good t c d A) (htu : t < u)
    (hn : ∃ n, acked t c n = true ∧ V n = true) : A.take c <+: B := by
  obtain ⟨n, h1, h2⟩ := hn
  rcases hT.early n h2 t c A hr.isLed hr.isGood hr.len h1 htu with h | ⟨w, Bw, htw, hwu, hBw, hnot⟩
  · exact h
  · exact absurd (hT.before w hwu t c d A hr htw Bw hBw) hnot

/-- The configuration at d when the only change in (a, d] is the one at p. -/
theorem confOf_one (l : List ε) (a p d : Nat) (hap : a < p) (hpd : p ≤ d)
    (h1 : NoC isc l a (p - 1)) (hp : isC isc l p = true) (h2 : NoC isc l p d) :
    ∃ x, l[p - 1]? = some x ∧ isc x = true ∧
      confOf isc chg init l d = nextConf (confOf isc chg init l a) (chg x) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  obtain ⟨x, hx, hstep⟩ := confOf_step isc chg init l q hp
  refine ⟨x, by simpa using hx, ?_, ?_⟩
  · simp only [isC, hx, Option.any_some] at hp; exact hp
  · rw [confOf_skip isc chg init l (q + 1) d hpd h2, hstep,
      confOf_skip isc chg init l a q (by omega) (by simpa using h1)]

/-- Leader completeness with membership changes: B has every prefix committed in an earlier term. -/
theorem core (hW : World tm isc chg init led K acked good)
    (hT : Target tm isc chg init led K acked good u B e V) :
    ∀ t c d A, RootAt isc chg init led K acked good t c d A → t < u → A.take c <+: B := by
  -- the committing leader's configuration is the later one
  have later : ∀ t c d A, RootAt isc chg init led K acked good t c d A → t < u → e < d → A.take c <+: B := by
    intro t c d A hr htu hed
    obtain ⟨kD, tk, hkD, htk, hdk, hkA⟩ : ∃ k tk, K k tk ∧ tk ≤ t ∧ d ≤ k.length ∧ k.take d = A.take d := by
      rcases hr.cover with h | h
      · omega
      · exact h
    have hAB : A.take e = B.take e := by
      rcases hT.cover with h | ⟨kE, tkE, hkE, _, hek, hkB⟩
      · subst h; simp
      · exact agree A B kD kE d e e (hW.cmp _ _ _ _ hkD hkE) hdk hek hkA hkB (by omega) (Nat.le_refl _)
    have hE : confOf isc chg init A e = confOf isc chg init B e := confOf_congr isc chg init A B e hAB
    rcases first_change isc A e d with hno | ⟨p1, hp1a, hp1b, hp1c, hp1d⟩
    · have hq := hr.quorum
      rw [confOf_skip isc chg init A e d (by omega) hno, hE] at hq
      exact near hT hr htu (IsQ.inter _ _ _ hq hT.quorum)
    · have hleg : ∀ x, A[p1 - 1]? = some x → isc x = true →
          Legal (confOf isc chg init B e) (chg x) := by
        intro x hx hxc
        have := hW.legal t A hr.isLed (p1 - 1) x hx hxc
        rwa [confOf_skip isc chg init A e (p1 - 1) (by omega) hp1d, hE] at this
      rcases first_change isc A p1 d with hno2 | ⟨p2, hp2a, hp2b, hp2c, hp2d⟩
      · obtain ⟨x, hx, hxc, hconf⟩ := confOf_one (chg := chg) (init := init) A e p1 d hp1a hp1b hp1d hp1c hno2
        have hq := hr.quorum
        rw [hconf, hE] at hq
        obtain ⟨a, ha1, ha2⟩ := IsQ.inter_next _ _ _ _ (hleg x hx hxc) hT.quorum hq
        exact near hT hr htu ⟨a, ha2, ha1⟩
      · -- two changes after e that the committing leader counted with: the second was first
        -- committed by a leader that counted with the first only, and that one is near
        exfalso
        have hk2 : isC isc kD p2 = true := by rw [isC_congr isc kD A d p2 hkA hp2b]; exact hp2c
        obtain ⟨t1, c1, d1, A1, hr1, hK1, ht1, hpc1, hd1⟩ := hW.first kD tk hkD p2 hk2
        have hA1 : A1.take p2 = A.take p2 := by
          have h := agree A1 A (A1.take c1) kD c1 d p2 (hW.cmp _ _ _ _ hK1 hkD)
            (by have := hr1.len; simp; omega) hdk (by rw [List.take_take, Nat.min_self]) hkA hpc1 hp2b
          exact h
        have hc1 : isC isc A1 p1 = true := by rw [isC_congr isc A1 A p2 p1 hA1 (by omega)]; exact hp1c
        have hc2 : isC isc A1 p2 = true := by rw [isC_congr isc A1 A p2 p2 hA1 (Nat.le_refl _)]; exact hp2c
        have hd1p : p1 ≤ d1 := by
          rcases Nat.lt_or_ge d1 p1 with h | h
          · exact absurd (hr1.one p1 p2 h hp2a hpc1 hc1 hc2) id
          · exact h
        have hnear : A1.take c1 <+: B := by
          have hA1d : A1.take d1 = A.take d1 := take_take_eq _ _ p2 d1 hA1 (by omega)
          have hno2 : NoC isc A p1 d1 := fun p h1 h2 => hp2d p h1 (by omega)
          obtain ⟨x, hx, hxc, hconf⟩ := confOf_one (chg := chg) (init := init) A e p1 d1 hp1a hd1p hp1d hp1c hno2
          have hq := hr1.quorum
          rw [confOf_congr isc chg init A1 A d1 hA1d, hconf, hE] at hq
          obtain ⟨a, ha1, ha2⟩ := IsQ.inter_next _ _ _ _ (hleg x hx hxc) hT.quorum hq
          exact near hT hr1 (by omega) ⟨a, ha2, ha1⟩
        have hB : A1.take p2 = B.take p2 := by
          have := take_eq_of_prefix A1 B c1 hnear hr1.len
          exact take_take_eq _ _ c1 p2 this hpc1
        have hb1 : isC isc B p1 = true := by rw [← isC_congr isc A1 B p2 p1 hB (by omega)]; exact hc1
        have hb2 : isC isc B p2 = true := by rw [← isC_congr isc A1 B p2 p2 hB (Nat.le_refl _)]; exact hc2
        have hl2 := (isC_le isc A1 p2 hc2).2
        have ht1p : tmAt tm B p1 < u := by
          rw [← tmAt_congr tm A1 B p2 p1 hB (by omega)]
          have := hW.sorted t1 A1 hr1.isLed p1 (by omega)
          omega
        have ht2p : tmAt tm B p2 < u := by
          rw [← tmAt_congr tm A1 B p2 p2 hB (Nat.le_refl _)]
          have := hW.sorted t1 A1 hr1.isLed p2 hl2
          omega
        exact hT.one p1 p2 hp1a hp2a hb1 hb2 ht1p ht2p
  -- the elected node's configuration is the later one, or they are the same
  have earlier : ∀ m t c d A, RootAt isc chg init led K acked good t c d A → t < u → d ≤ e → e - d ≤ m →
      A.take c <+: B := by
    intro m
    induction m with
    | zero =>
      intro t c d A hr htu hde hm
      have : d = e := by omega
      subst this
      have hAB : A.take d = B.take d := by
        rcases hr.cover with h | ⟨kD, tk, hkD, _, hdk, hkA⟩
        · subst h; simp
        · rcases hT.cover with h | ⟨kE, tkE, hkE, _, hek, hkB⟩
          · subst h; simp
          · exact agree A B kD kE d d d (hW.cmp _ _ _ _ hkD hkE) hdk hek hkA hkB (Nat.le_refl _) (Nat.le_refl _)
      have hq := hr.quorum
      rw [confOf_congr isc chg init A B d hAB] at hq
      exact near hT hr htu (IsQ.inter _ _ _ hq hT.quorum)
    | succ m ih =>
      intro t c d A hr htu hde hm
      have hAB : A.take d = B.take d := by
        rcases hr.cover with h | ⟨kD, tk, hkD, _, hdk, hkA⟩
        · subst h; simp
        · rcases hT.cover with h | ⟨kE, tkE, hkE, _, hek, hkB⟩
          · have : d = 0 := by omega
            subst this; simp
          · exact agree A B kD kE d e d (hW.cmp _ _ _ _ hkD hkE) hdk hek hkA hkB (Nat.le_refl _) hde
      have hD : confOf isc chg init A d = confOf isc chg init B d := confOf_congr isc chg init A B d hAB
      rcases first_change isc B d e with hno | ⟨p1, hp1a, hp1b, hp1c, hp1d⟩
      · have hq := hT.quorum
        rw [confOf_skip isc chg init B d e hde hno, ← hD] at hq
        exact near hT hr htu (IsQ.inter _ _ _ hr.quorum hq)
      · rcases first_change isc B p1 e with hno2 | ⟨p2, hp2a, hp2b, hp2c, hp2d⟩
        · obtain ⟨x, hx, hxc, hconf⟩ := confOf_one (chg := chg) (init := init) B d p1 e hp1a hp1b hp1d hp1c hno2
          have hleg := hT.legal (p1 - 1) x hx hxc
          rw [confOf_skip isc chg init B d (p1 - 1) (by omega) hp1d, ← hD] at hleg
          have hq := hT.quorum
          rw [hconf, ← hD] at hq
          exact near hT hr htu (IsQ.inter_next _ _ _ _ hleg hr.quorum hq)
        · -- two changes after d that the elected node counted with: the leader that first
          -- committed the second counted with the first, and its prefix has this one
          obtain ⟨kE, tkE, hkE, htkE, hek, hkB⟩ : ∃ k tk, K k tk ∧ tk < u ∧ e ≤ k.length ∧ k.take e = B.take e := by
            rcases hT.cover with h | h
            · omega
            · exact h
          have hk2 : isC isc kE p2 = true := by rw [isC_congr isc kE B e p2 hkB hp2b]; exact hp2c
          obtain ⟨t2, c2, d2, A2, hr2, hK2, ht2, hpc2, hd2⟩ := hW.first kE tkE hkE p2 hk2
          have hA2 : A2.take p2 = B.take p2 :=
            agree A2 B (A2.take c2) kE c2 e p2 (hW.cmp _ _ _ _ hK2 hkE)
              (by have := hr2.len; simp; omega) hek (by rw [List.take_take, Nat.min_self]) hkB hpc2 hp2b
          have hc1 : isC isc A2 p1 = true := by rw [isC_congr isc A2 B p2 p1 hA2 (by omega)]; exact hp1c
          have hc2 : isC isc A2 p2 = true := by rw [isC_congr isc A2 B p2 p2 hA2 (Nat.le_refl _)]; exact hp2c
          have hd2p : p1 ≤ d2 := by
            rcases Nat.lt_or_ge d2 p1 with h | h
            · exact absurd (hr2.one p1 p2 h hp2a hpc2 hc1 hc2) id
            · exact h
          -- the two leader logs agree on min c c2 entries
          have hAA : ∀ k, k ≤ c → k ≤ c2 → A.take k = A2.take k := by
            intro k hkc hkc2
            rcases Nat.lt_trichotomy t t2 with h | h | h
            · have := hT.before t2 (by omega) t c d A hr h A2 hr2.isLed
              exact take_take_eq _ _ c k (take_eq_of_prefix A A2 c this hr.len) hkc
            · subst h
              have := hr.isLed.symm.trans hr2.isLed
              cases this; rfl
            · have := hT.before t htu t2 c2 d2 A2 hr2 h A hr.isLed
              exact (take_take_eq _ _ c2 k (take_eq_of_prefix A2 A c2 this hr2.len) hkc2).symm
          have hcp : c < p2 := by
            rcases Nat.lt_or_ge c p2 with h | h
            · exact h
            · exfalso
              have hAp : A.take p2 = B.take p2 := (hAA p2 h hpc2).trans hA2
              have ha1 : isC isc A p1 = true := by rw [isC_congr isc A B p2 p1 hAp (by omega)]; exact hp1c
              have ha2 : isC isc A p2 = true := by rw [isC_congr isc A B p2 p2 hAp (Nat.le_refl _)]; exact hp2c
              exact hr.one p1 p2 hp1a hp2a h ha1 ha2
          have h12 : A.take c <+: A2.take c2 := by
            have h1 := hAA c (Nat.le_refl _) (by omega)
            rw [h1, show A2.take c = (A2.take c2).take c by rw [List.take_take, Nat.min_eq_left (by omega)]]
            exact List.take_prefix _ _
          exact h12.trans (ih t2 c2 d2 A2 hr2 (by omega) (by omega) (by omega))
  intro t c d A hr htu
  rcases Nat.lt_or_ge e d with h | h
  · exact later t c d A hr htu h
  · exact earlier (e - d) t c d A hr htu h (Nat.le_refl _)

/-- Read index with membership changes. The leader of term T (log AT) counts with the
configuration of AT's first e entries; R is a quorum of it. `Ks`, `ackeds` are the commits and
acknowledgements when the read was requested, when no node of R had acknowledged anything after
T. Then no leader of a term after T had committed anything.

Proof idea: that leader's configuration equals the reader's, is one change away (quorums
intersect), or further. Further ahead: the second change beyond the reader's was first committed
by a leader one change away, unless its term is ≤ T, but then the reader's log has both changes,
contradicting at most one pending. Further behind: it committed less than what made the reader's
configuration, committed at ≤ T, so its entry would be in an earlier leader log. -/
theorem read_core
    (Ks : List ε → Nat → Prop) (ackeds : Nat → Nat → server → Bool)
    (hW : World tm isc chg init led K acked good)
    (hKs : ∀ k t, Ks k t → K k t)
    (hacks : ∀ t c n, ackeds t c n = true → acked t c n = true)
    (hFs : ∀ k tk, Ks k tk → ∀ p, isC isc k p = true →
      ∃ t1 c1 d1 A1, RootAt isc chg init led Ks ackeds good t1 c1 d1 A1 ∧ Ks (A1.take c1) t1 ∧ t1 ≤ tk ∧ p ≤ c1 ∧ d1 < p)
    (hLC : ∀ t c d A, RootAt isc chg init led K acked good t c d A → ∀ u, t < u →
      ∀ B, led u = some B → A.take c <+: B)
    (hRooted : ∀ k tk, K k tk → ∃ t c d A, RootAt isc chg init led K acked good t c d A ∧ t ≤ tk ∧ k <+: A.take c)
    (hgood : ∀ t c A, good t c → led t = some A → tmAt tm A c = t)
    (T e : Nat) (AT : List ε) (R : server → Bool)
    (hAT : led T = some AT)
    (hcov : e = 0 ∨ ∃ k tk, K k tk ∧ tk ≤ T ∧ e ≤ k.length ∧ k.take e = AT.take e)
    (hone : AtMostOne isc AT e AT.length)
    (hq : IsQ R (confOf isc chg init AT e))
    (hR : ∀ n, R n = true → ∀ t c, T < t → ackeds t c n = false) :
    ∀ t c d A, RootAt isc chg init led Ks ackeds good t c d A → t ≤ T := by
  intro t c d A hr
  rcases Nat.lt_or_ge T t with hlt | hle
  swap
  · exact hle
  exfalso
  have up : ∀ t c d A, RootAt isc chg init led Ks ackeds good t c d A →
      RootAt isc chg init led K acked good t c d A := by
    intro t c d A h
    refine ⟨h.isLed, h.len, h.isGood, ?_, h.one, IsQ.mono _ _ _ (hacks t c) h.quorum⟩
    rcases h.cover with h0 | ⟨k, tk, hk, h1, h2, h3⟩
    · exact Or.inl h0
    · exact Or.inr ⟨k, tk, hKs _ _ hk, h1, h2, h3⟩
  have contra : ∀ n t' c', R n = true → ackeds t' c' n = true → T < t' → False := by
    intro n t' c' h1 h2 h3
    rw [hR n h1 t' c' h3] at h2
    cases h2
  -- the later leader's log has what made the reader's configuration
  have hAe : A.take e = AT.take e := by
    rcases hcov with h0 | ⟨kE, tkE, hkE, htk, hek, hkA⟩
    · subst h0; simp
    · obtain ⟨t0, c0, d0, A0, hr0, ht0, hk0⟩ := hRooted kE tkE hkE
      have h1 := hLC t0 c0 d0 A0 hr0 t (by omega) A hr.isLed
      have h2 : kE <+: A := hk0.trans h1
      rw [← prefix_take kE A e h2 hek]; exact hkA
  have hE : confOf isc chg init A e = confOf isc chg init AT e := confOf_congr isc chg init A AT e hAe
  rcases Nat.lt_or_ge e d with hed | hde
  · obtain ⟨kD, tk, hkD, htk, hdk, hkA⟩ : ∃ k tk, Ks k tk ∧ tk ≤ t ∧ d ≤ k.length ∧ k.take d = A.take d := by
      rcases hr.cover with h | h
      · omega
      · exact h
    rcases first_change isc A e d with hno | ⟨p1, hp1a, hp1b, hp1c, hp1d⟩
    · have hq' := hr.quorum
      rw [confOf_skip isc chg init A e d (by omega) hno, hE] at hq'
      obtain ⟨n, h1, h2⟩ := IsQ.inter _ _ _ hq hq'
      exact contra n t c h1 h2 hlt
    · have hleg : ∀ x, A[p1 - 1]? = some x → isc x = true →
          Legal (confOf isc chg init AT e) (chg x) := by
        intro x hx hxc
        have := hW.legal t A hr.isLed (p1 - 1) x hx hxc
        rwa [confOf_skip isc chg init A e (p1 - 1) (by omega) hp1d, hE] at this
      rcases first_change isc A p1 d with hno2 | ⟨p2, hp2a, hp2b, hp2c, hp2d⟩
      · obtain ⟨x, hx, hxc, hconf⟩ := confOf_one (chg := chg) (init := init) A e p1 d hp1a hp1b hp1d hp1c hno2
        have hq' := hr.quorum
        rw [hconf, hE] at hq'
        obtain ⟨n, h1, h2⟩ := IsQ.inter_next _ _ _ _ (hleg x hx hxc) hq hq'
        exact contra n t c h1 h2 hlt
      · have hk2 : isC isc kD p2 = true := by rw [isC_congr isc kD A d p2 hkA hp2b]; exact hp2c
        obtain ⟨t1, c1, d1, A1, hr1, hK1, ht1, hpc1, hd1⟩ := hFs kD tk hkD p2 hk2
        have hA1 : A1.take p2 = A.take p2 :=
          agree A1 A (A1.take c1) kD c1 d p2 (hW.cmp _ _ _ _ (hKs _ _ hK1) (hKs _ _ hkD))
            (by have := hr1.len; simp; omega) hdk (by rw [List.take_take, Nat.min_self]) hkA hpc1 hp2b
        have hc1 : isC isc A1 p1 = true := by rw [isC_congr isc A1 A p2 p1 hA1 (by omega)]; exact hp1c
        have hc2 : isC isc A1 p2 = true := by rw [isC_congr isc A1 A p2 p2 hA1 (Nat.le_refl _)]; exact hp2c
        have hd1p : p1 ≤ d1 := by
          rcases Nat.lt_or_ge d1 p1 with h | h
          · exact absurd (hr1.one p1 p2 h hp2a hpc1 hc1 hc2) id
          · exact h
        rcases Nat.lt_or_ge T t1 with h | h
        · have hA1d : A1.take d1 = A.take d1 := take_take_eq _ _ p2 d1 hA1 (by omega)
          have hno2 : NoC isc A p1 d1 := fun p h1 h2 => hp2d p h1 (by omega)
          obtain ⟨x, hx, hxc, hconf⟩ := confOf_one (chg := chg) (init := init) A e p1 d1 hp1a hd1p hp1d hp1c hno2
          have hq' := hr1.quorum
          rw [confOf_congr isc chg init A1 A d1 hA1d, hconf, hE] at hq'
          obtain ⟨n, h1, h2⟩ := IsQ.inter_next _ _ _ _ (hleg x hx hxc) hq hq'
          exact contra n t1 c1 h1 h2 h
        · have hAT1 : A1.take c1 <+: AT := by
            rcases Nat.eq_or_lt_of_le h with heq | hlt1
            · have := hr1.isLed
              rw [heq, hAT] at this
              cases this; exact List.take_prefix _ _
            · exact hLC t1 c1 d1 A1 (up _ _ _ _ hr1) T hlt1 AT hAT
          have hT2 : A1.take p2 = AT.take p2 :=
            take_take_eq _ _ c1 p2 (take_eq_of_prefix A1 AT c1 hAT1 hr1.len) hpc1
          have ha1 : isC isc AT p1 = true := by rw [← isC_congr isc A1 AT p2 p1 hT2 (by omega)]; exact hc1
          have ha2 : isC isc AT p2 = true := by rw [← isC_congr isc A1 AT p2 p2 hT2 (Nat.le_refl _)]; exact hc2
          exact hone p1 p2 hp1a hp2a (isC_le isc AT p2 ha2).2 ha1 ha2
  · rcases first_change isc A d e with hno | ⟨p1, hp1a, hp1b, hp1c, hp1d⟩
    · have hq' := hr.quorum
      rw [← confOf_skip isc chg init A d e hde hno, hE] at hq'
      obtain ⟨n, h1, h2⟩ := IsQ.inter _ _ _ hq hq'
      exact contra n t c h1 h2 hlt
    · rcases first_change isc A p1 e with hno2 | ⟨p2, hp2a, hp2b, hp2c, hp2d⟩
      · obtain ⟨x, hx, hxc, hconf⟩ := confOf_one (chg := chg) (init := init) A d p1 e hp1a hp1b hp1d hp1c hno2
        have hleg := hW.legal t A hr.isLed (p1 - 1) x hx hxc
        rw [confOf_skip isc chg init A d (p1 - 1) (by omega) hp1d] at hleg
        have hq2 := hq
        rw [← hE, hconf] at hq2
        obtain ⟨n, h1, h2⟩ := IsQ.inter_next _ _ _ _ hleg hr.quorum hq2
        exact contra n t c h2 h1 hlt
      · have hcp : c < p2 := by
          rcases Nat.lt_or_ge c p2 with h | h
          · exact h
          · exact absurd (hr.one p1 p2 hp1a hp2a h hp1c hp2c) id
        obtain ⟨kE, tkE, hkE, htkE, hek, hkAT⟩ : ∃ k tk, K k tk ∧ tk ≤ T ∧ e ≤ k.length ∧ k.take e = AT.take e := by
          rcases hcov with h | h
          · omega
          · exact h
        obtain ⟨t0, c0, d0, A0, hr0, ht0, hk0⟩ := hRooted kE tkE hkE
        have h1 : A0.take c0 <+: A := hLC t0 c0 d0 A0 hr0 t (by omega) A hr.isLed
        have hlen : kE.length ≤ c0 ∧ kE.length ≤ A0.length := by
          have := hk0.length_le
          simp at this; omega
        have hA0 : A0.take c0 = A.take c0 := take_eq_of_prefix A0 A c0 h1 hr0.len
        have htm : tmAt tm A0 c = tmAt tm A c := tmAt_congr tm A0 A c0 c hA0 (by omega)
        have hs := hW.sorted t0 A0 hr0.isLed c (by omega)
        have hg := hgood t c A hr.isGood hr.isLed
        omega

end Core

end MemberCore

open MemberCore in
-- IsConf(e)
def Entry.isConf {value : Type} (e : Entry value) : Bool :=
  match e.kind with
  | .conf => true
  | _ => false

-- The change held by a "conf" entry; `ad rm jt lv` are the model's `chAdd chRemove chJoint chLeave`.
def chgOf {server value : Type} (ad rm : value → List server) (jt lv : value → Bool)
    (e : Entry value) : MemberCore.Change server :=
  match e.value with
  | some v => { add := ad v, remove := rm v, joint := jt v, leave := lv v }
  | none => { add := [], remove := [], joint := false, leave := false }

-- ConfsAfter(l, a), counted.
def confsAfter {value : Type} (l : List (Entry value)) (a : Nat) : Nat :=
  ((l.drop a).filter Entry.isConf).length

-- LastConf(l, a)
def lastConf {value : Type} (l : List (Entry value)) : Nat → Nat
  | 0 => 0
  | a + 1 => if MemberCore.isC Entry.isConf l (a + 1) then a + 1 else lastConf l a

theorem lastConf_le {value : Type} (l : List (Entry value)) (a : Nat) : lastConf l a ≤ a := by
  induction a with
  | zero => exact Nat.le_refl _
  | succ a ih => simp only [lastConf]; split <;> omega

-- The configuration at LastConf(l, a) is the configuration at a.
theorem confOf_lastConf {server value : Type} [DecidableEq server] (chg : Entry value → MemberCore.Change server)
    (init : MemberCore.Conf server) (l : List (Entry value)) (a : Nat) :
    MemberCore.confOf Entry.isConf chg init l (lastConf l a) = MemberCore.confOf Entry.isConf chg init l a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    simp only [lastConf]
    split
    · rfl
    · rename_i h
      rw [ih]
      simp only [MemberCore.isC] at h
      simp only [MemberCore.confOf]
      cases hg : l[a]? with
      | none => rfl
      | some e =>
        rw [hg] at h
        simp only [Option.any_some] at h
        simp [h]

theorem isC_get {value : Type} (l : List (Entry value)) (q : Nat) (x : Entry value) (h : l[q]? = some x) :
    MemberCore.isC Entry.isConf l (q + 1) = x.isConf := by
  simp [MemberCore.isC, h]

theorem isC_last {value : Type} (l : List (Entry value)) (e : Entry value) :
    MemberCore.isC Entry.isConf (l ++ [e]) (l.length + 1) = e.isConf :=
  isC_get _ _ _ (by simp)

-- A list with two entries that satisfy p has at least two that do.
theorem filter_two {α : Type} (m : List α) (p : α → Bool) (j1 j2 : Nat) (x1 x2 : α) (hj : j1 < j2)
    (h1 : m[j1]? = some x1) (h2 : m[j2]? = some x2) (p1 : p x1 = true) (p2 : p x2 = true) :
    2 ≤ (m.filter p).length := by
  have hsplit : m = m.take j2 ++ m.drop j2 := (List.take_append_drop j2 m).symm
  have ha : x1 ∈ (m.take j2).filter p := by
    rw [List.mem_filter]
    refine ⟨?_, p1⟩
    rw [List.mem_iff_getElem?]
    exact ⟨j1, by rw [List.getElem?_take_of_lt hj]; exact h1⟩
  have hb : x2 ∈ (m.drop j2).filter p := by
    rw [List.mem_filter]
    refine ⟨?_, p2⟩
    rw [List.mem_iff_getElem?]
    exact ⟨0, by rw [List.getElem?_drop]; simpa using h2⟩
  have la := List.length_pos_of_mem ha
  have lb := List.length_pos_of_mem hb
  rw [hsplit, List.filter_append, List.length_append]
  omega

-- AllSwitched: no change of membership after a.
theorem confsAfter_zero {value : Type} (l : List (Entry value)) (a : Nat) (h : confsAfter l a = 0) :
    MemberCore.NoC Entry.isConf l a l.length := by
  intro p h1 h2
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hq : q < l.length := by omega
  rw [isC_get l q l[q] (List.getElem?_eq_getElem hq)]
  unfold confsAfter at h
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at h
  have hm : l[q] ∈ l.drop a := by
    rw [List.mem_iff_getElem?]
    exact ⟨q - a, by rw [List.getElem?_drop, show a + (q - a) = q by omega]; exact List.getElem?_eq_getElem hq⟩
  simpa using h _ hm

-- OneWaiting: at most one change of membership after a.
theorem confsAfter_one {value : Type} (l : List (Entry value)) (a : Nat) (h : confsAfter l a ≤ 1) :
    MemberCore.AtMostOne Entry.isConf l a l.length := by
  intro p q h1 h2 h3 hp hq
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hpl : p' < l.length := by omega
  have hql : q' < l.length := by omega
  rw [isC_get l p' l[p'] (List.getElem?_eq_getElem hpl)] at hp
  rw [isC_get l q' l[q'] (List.getElem?_eq_getElem hql)] at hq
  have := filter_two (l.drop a) Entry.isConf (p' - a) (q' - a) l[p'] l[q'] (by omega)
    (by rw [List.getElem?_drop, show a + (p' - a) = p' by omega]; exact List.getElem?_eq_getElem hpl)
    (by rw [List.getElem?_drop, show a + (q' - a) = q' by omega]; exact List.getElem?_eq_getElem hql) hp hq
  unfold confsAfter at h
  omega

-- InitConf, given the first voters.
def conf0 {server : Type} (iv : server → Bool) : MemberCore.Conf server :=
  { inn := iv, out := MemberCore.noVoters }

-- ConfOf(l, a)
abbrev cOf {server value : Type} [DecidableEq server] (iv : server → Bool) (ad rm : value → List server)
    (jt lv : value → Bool) (l : List (Entry value)) (a : Nat) : MemberCore.Conf server :=
  MemberCore.confOf Entry.isConf (chgOf ad rm jt lv) (conf0 iv) l a

-- SwitchConf: the entry at k is the next change in l after ca, legal for (vin, vout).
def switchOk {server value : Type} [DecidableEq server] [Servers server] (ad rm : value → List server)
    (jt lv : value → Bool) (l : List (Entry value)) (ca k : Nat) (vin vout : server → Bool) : Prop :=
  MemberCore.isC Entry.isConf l k = true ∧
  (∀ q ∈ List.range' (ca + 1) (k - 1 - ca), MemberCore.isC Entry.isConf l q = false) ∧
  MemberCore.Legal { inn := vin, out := vout } (chgOf ad rm jt lv ((l[k - 1]?).getD noEntry))

instance {server value : Type} [DecidableEq server] [Servers server] (ad rm : value → List server)
    (jt lv : value → Bool) (l : List (Entry value)) (ca k : Nat) (vin vout : server → Bool) :
    Decidable (switchOk ad rm jt lv l ca k vin vout) := by
  unfold switchOk; infer_instance

-- SwitchConf: the configuration that the entry at k makes of (vin, vout).
def switchTo {server value : Type} [DecidableEq server] (ad rm : value → List server)
    (jt lv : value → Bool) (l : List (Entry value)) (k : Nat) (vin vout : server → Bool) :
    MemberCore.Conf server :=
  MemberCore.nextConf { inn := vin, out := vout } (chgOf ad rm jt lv ((l[k - 1]?).getD noEntry))

theorem switchOk_iff {server value : Type} [DecidableEq server] [Servers server] (ad rm : value → List server)
    (jt lv : value → Bool) (l : List (Entry value)) (ca k : Nat) (vin vout : server → Bool) :
    switchOk ad rm jt lv l ca k vin vout ↔
      (MemberCore.isC Entry.isConf l k = true ∧
       (∀ q ∈ List.range' (ca + 1) (k - 1 - ca), MemberCore.isC Entry.isConf l q = false) ∧
       MemberCore.Legal { inn := vin, out := vout } (chgOf ad rm jt lv ((l[k - 1]?).getD noEntry))) := Iff.rfl

theorem switchTo_eq {server value : Type} [DecidableEq server] (ad rm : value → List server)
    (jt lv : value → Bool) (l : List (Entry value)) (k : Nat) (vin vout : server → Bool) :
    switchTo ad rm jt lv l k vin vout =
      MemberCore.nextConf { inn := vin, out := vout } (chgOf ad rm jt lv ((l[k - 1]?).getD noEntry)) := rfl

-- Unfolded only via the two lemmas above: definitional unfolding under an action does not terminate.
attribute [irreducible] switchOk switchTo

type server
type value
type MsgSet
type VoteSet
type LeaderSet
type CommitSet
type AppliedSet
instantiate srv : Servers server
instantiate msgSet : TSet (Msg server value) MsgSet
instantiate vSet : TSet (Vote server) VoteSet
instantiate lSet : TSet (Elected server) LeaderSet
instantiate cSet : TSet (Commit server value) CommitSet
instantiate aSet : TSet (Applied server value) AppliedSet

-- The bounds of MCEtcd.tla's `Bounded`.
immutable individual MaxTerm : Nat
immutable individual MaxLog : Nat
immutable individual MaxBatch : Nat
immutable individual MaxMsgs : Nat

enum Role = {Follower, Candidate, Leader}

function currentTerm : server → Nat
function voteTerm : server → Nat
function voteFor : server → Option server
function log : server → List (Entry value)
function role : server → Role
function commitIndex : server → Nat
function confirmedTerm : server → Nat
function confirmedIndex : server → Nat
individual msgs : MsgSet
individual votes : VoteSet
individual leaders : LeaderSet
function ledLog : Nat → Option (List (Entry value))
individual commits : CommitSet
function lastApplied : server → Nat
individual applied : AppliedSet
-- InitVoters, and the change a "conf" entry's value stands for.
immutable relation initV : server → Bool
immutable function chAdd : value → List server
immutable function chRemove : value → List server
immutable relation chJoint : value → Bool
immutable relation chLeave : value → Bool
-- config[i].in and config[i].out, as conditions on servers; confAt[i].
relation cIn : server → server → Bool
relation cOut : server → server → Bool
function confAt : server → Nat
-- ledConf[t].in and .out; ledAt[t]; elAt[t] (empty / 0 outside DOMAIN ledLog).
relation lIn : Nat → server → Bool
relation lOut : Nat → server → Bool
function ledAt : Nat → Nat
function elAt : Nat → Nat
-- read: one field for each of its parts.
individual readOn : Bool
individual readDone : Bool
individual readTerm : Nat
individual readIndex : Nat
individual readFloor : CommitSet
individual readMsgs : MsgSet
function readResp : server → Bool
-- Model checker only: by default functions over Nat compare equal, merging states that differ
-- only in a leader log. Compare and hash them on the terms a bounded instance reaches.
instance (priority := high) ledLogBEq {β : Type} [BEq β] : BEq (Veil.CanonicalFieldWrapper [Nat] β) where
  beq a b := (List.range 16).all fun t => a.inner t == b.inner t

instance (priority := high) ledLogHashable {β : Type} [Hashable β] : Hashable (Veil.CanonicalFieldWrapper [Nat] β) where
  hash a := (List.range 16).foldl (fun r t => mixHash r (hash (a.inner t))) 7

-- The warning is moot given the instances above.
set_option veil.warnHybridFields false

set_option veil.deferVCGeneration true
#gen_state

after_init {
  currentTerm S := 0
  voteTerm S := 0
  voteFor S := none
  log S := []
  role S := Follower
  commitIndex S := 0
  confirmedTerm S := 0
  confirmedIndex S := 0
  msgs := msgSet.empty
  votes := vSet.empty
  leaders := lSet.empty
  ledLog T := none
  commits := cSet.empty
  lastApplied S := 0
  applied := aSet.empty
  cIn S T := initV T
  cOut S T := false
  confAt S := 0
  lIn N T := false
  lOut N T := false
  ledAt N := 0
  elAt N := 0
  readOn := false
  readDone := false
  readTerm := 0
  readIndex := 0
  readFloor := cSet.empty
  readMsgs := msgSet.empty
  readResp S := false
}

-- BecomeCandidate(i) == role' = [role EXCEPT ![i] = Candidate]
action BecomeCandidate (i : server) {
  role i := Candidate
}

-- BecomeFollower(i) == role' = [role EXCEPT ![i] = Follower]
action BecomeFollower (i : server) {
  role i := Follower
}

-- StartElection(i) ==
--     /\ role[i] = Candidate
--     /\ currentTerm' = [currentTerm EXCEPT ![i] = @ + 1]
--     /\ msgs' = msgs \cup {VoteRequest(i, currentTerm[i] + 1)}
action StartElection (i : server) {
  require role i = Candidate
  let t := currentTerm i + 1
  let l := log i
  currentTerm i := t
  msgs := msgSet.insert (.vote i t l.length (TermAt l l.length)) msgs
}

-- AdoptTerm(i, t) ==
--     /\ t > currentTerm[i]
--     /\ \E k \in Server \ {i} : currentTerm[k] >= t
--     /\ currentTerm' = [currentTerm EXCEPT ![i] = t]
--     /\ role' = [role EXCEPT ![i] = Follower]
-- Next: \E t \in {currentTerm[k] : k \in Server} : AdoptTerm(i, t)
action AdoptTerm (i : server) {
  let k ← pick server
  let t := currentTerm k
  require t > currentTerm i
  require ∃ k', k' ≠ i ∧ currentTerm k' ≥ t
  currentTerm i := t
  role i := Follower
}

-- UpToDate(m, i) ==
--     \/ m.lastLogTerm > LastTerm(i)
--     \/ m.lastLogTerm = LastTerm(i) /\ m.lastLogIndex >= Len(log[i])
-- MayVote(i, c) ==
--     \E m \in msgs : m.type = "vote" /\ m.src = c /\ m.term = currentTerm[i] /\ UpToDate(m, i)
-- CastVote(i, c) ==
--     /\ voteTerm[i] # currentTerm[i]
--     /\ MayVote(i, c)
--     /\ voteTerm' = [voteTerm EXCEPT ![i] = currentTerm[i]]
--     /\ voteFor' = [voteFor EXCEPT ![i] = c]
--     /\ votes' = votes \cup {[voter |-> i, term |-> currentTerm[i], cand |-> c]}
action CastVote (i : server) (c : server) {
  require voteTerm i ≠ currentTerm i
  let l := log i
  let lastTerm := TermAt l l.length
  let cur := currentTerm i
  require ∃ m : { m // m ∈ msgs },
    (match m.val with
      | .vote src term lastLogIndex lastLogTerm =>
        decide (src = c ∧ term = cur ∧
          (lastLogTerm > lastTerm ∨ (lastLogTerm = lastTerm ∧ lastLogIndex ≥ l.length)))
      | _ => false) = true
  voteFor i := some c
  voteTerm i := cur
  votes := vSet.insert { voter := i, term := cur, cand := c } votes
}

-- GrantVote(i, c, t) ==
--     /\ c # i
--     /\ [voter |-> i, term |-> t, cand |-> c] \in votes
--     /\ msgs' = msgs \cup {[type |-> "grant", src |-> i, dst |-> c, term |-> t]}
-- Next: \E v \in votes : v.voter = i /\ GrantVote(i, v.cand, v.term)
action GrantVote (i : server) {
  let v : { v // v ∈ votes } :| v.val.voter = i ∧ v.val.cand ≠ i
  msgs := msgSet.insert (.grant i v.val.cand v.val.term) msgs
}

-- Granted(i) ==
--     {j \in Server \ {i} : [type |-> "grant", src |-> j, dst |-> i, term |-> currentTerm[i]] \in msgs}
--     \cup (IF [voter |-> i, term |-> currentTerm[i], cand |-> i] \in votes THEN {i} ELSE {})
-- OneWaiting(i, l) == Cardinality(ConfsAfter(l, confAt[i])) <= 1
-- CommittedBefore(l, c, t) ==
--     \/ c = 0
--     \/ /\ c <= Len(l)
--        /\ \E k \in commits : k.term < t /\ c <= Len(k.entries) /\ SubSeq(k.entries, 1, c) = SubSeq(l, 1, c)
-- BecomeLeader(i) ==
--     /\ role[i] = Candidate
--     /\ currentTerm[i] \notin DOMAIN ledLog
--     /\ IsQuorum(Granted(i), config[i])
--     /\ OneWaiting(i, log[i])
--     /\ CommittedBefore(log[i], confAt[i], currentTerm[i])
--     /\ role' = [role EXCEPT ![i] = Leader]
--     /\ leaders' = leaders \cup {[server |-> i, term |-> currentTerm[i]]}
--     /\ ledLog' = WithLed(currentTerm[i], log[i])
--     /\ ledConf' = WithConf(currentTerm[i], config[i])
--     /\ ledAt' = With(ledAt, currentTerm[i], confAt[i])
--     /\ elAt' = With(elAt, currentTerm[i], confAt[i])
action BecomeLeader (i : server) {
  require role i = Candidate
  let cur := currentTerm i
  require ledLog cur = none
  let vs := votes
  let ms := msgs
  let vin := cIn i
  let vout := cOut i
  require MemberCore.IsQ (fun j =>
    if j = i then vSet.contains { voter := i, term := cur, cand := i } vs
    else msgSet.contains (.grant j i cur) ms) { inn := vin, out := vout }
  let l := log i
  let ca := confAt i
  require confsAfter l ca ≤ 1
  require ca = 0 ∨ (ca ≤ l.length ∧ ∃ k : { k // k ∈ commits },
    k.val.term < cur ∧ ca ≤ k.val.entries.length ∧ SubSeq k.val.entries 1 ca = SubSeq l 1 ca)
  role i := Leader
  leaders := lSet.insert { server := i, term := cur } leaders
  ledLog cur := some l
  lIn cur S := vin S
  lOut cur S := vout S
  ledAt cur := ca
  elAt cur := ca
}

-- AllSwitched(i, l) == ConfsAfter(l, confAt[i]) = {}
-- LeaderAppend(i, es) ==
--     /\ role[i] = Leader
--     /\ currentTerm[i] \in DOMAIN ledLog
--     /\ Len(es) > 0
--     /\ \A k \in 1..Len(es) : es[k].term = currentTerm[i]
--     /\ \A k \in 1..Len(es) : IsConf(es[k]) =>
--           /\ AllSwitched(i, ledLog[currentTerm[i]])
--           /\ \A q \in 1..(k - 1) : ~IsConf(es[q])
--           /\ Legal(config[i], es[k].value)
--     /\ ledLog' = WithLed(currentTerm[i], ledLog[currentTerm[i]] \o es)
-- Next: \E ty \in {"noop", "config"} : LeaderAppend(i, <<Entry(currentTerm[i], ty, Nil)>>)
--       \E v \in Values : LeaderAppend(i, <<Entry(currentTerm[i], "command", v)>>)
--       \E d \in ConfChanges(Server) : LeaderAppend(i, <<Entry(currentTerm[i], "conf", d)>>)
-- `ty`, `v` select the disjunct: marker entry (`v` unused), command `v`, or change `v`.
action LeaderAppend (i : server) (ty : EntryType) (v : value) {
  require role i = Leader
  let cur := currentTerm i
  require ledLog cur ≠ none
  let l0 := (ledLog cur).getD []
  let vin := cIn i
  let vout := cOut i
  require ty = EntryType.conf →
    (confsAfter l0 (confAt i) = 0 ∧
      MemberCore.Legal { inn := vin, out := vout }
        { add := chAdd v, remove := chRemove v, joint := chJoint v, leave := chLeave v })
  let val := if (ty = EntryType.command ∨ ty = EntryType.conf) then some v else none
  let l := l0 ++ [{ term := cur, kind := ty, value := val }]
  ledLog cur := some l
}

-- KnownIn(k, t) == k.term <= t
-- CommittedIn(l, c, t) ==
--     \/ c = 0
--     \/ /\ c <= Len(l)
--        /\ \E k \in commits : /\ KnownIn(k, t)
--                              /\ c <= Len(k.entries)
--                              /\ SubSeq(k.entries, 1, c) = SubSeq(l, 1, c)
-- SendAppend(i, j, t, p, n, c) ==
--     /\ [server |-> i, term |-> t] \in leaders
--     /\ p + n <= Len(ledLog[t])
--     /\ CommittedIn(ledLog[t], c, t)
--     /\ msgs' = msgs \cup {[type |-> "append", src |-> i, dst |-> j, term |-> t,
--                            prevLogIndex |-> p, prevLogTerm |-> TermAt(ledLog[t], p),
--                            entries |-> SubSeq(ledLog[t], p + 1, p + n), commit |-> c]}
-- Next: \E j \in Server, l \in leaders : l.server = i /\
--          \E p, n, c \in 0..Len(ledLog[l.term]) : SendAppend(i, j, l.term, p, n, c)
action SendAppend (i : server) (j : server) {
  let ld : { ld // ld ∈ leaders } :| ld.val.server = i
  let t := ld.val.term
  let l := (ledLog t).getD []
  let (p, n, c) : { p // p ∈ List.range (l.length + 1) } × { n // n ∈ List.range (l.length + 1) }
      × { c // c ∈ List.range (l.length + 1) } :|
    p.val + n.val ≤ l.length ∧
    (c.val = 0 ∨ ∃ k : { k // k ∈ commits },
      k.val.term ≤ t ∧ c.val ≤ k.val.entries.length ∧ SubSeq k.val.entries 1 c.val = SubSeq l 1 c.val)
  msgs := msgSet.insert
    (.append i j t p.val (TermAt l p.val) (SubSeq l (p.val + 1) (p.val + n.val)) c.val) msgs
}

-- Acked(i, t, c) ==
--     {j \in Server :
--         \E a \in msgs : a.type = "ack" /\ a.src = j /\ a.dst = i /\ a.term = t /\ a.index >= c}
-- LeaderCommit(i, t, c) ==
--     /\ [server |-> i, term |-> t] \in leaders
--     /\ c >= 1
--     /\ c <= Len(ledLog[t])
--     /\ ledLog[t][c].term = t
--     /\ IsQuorum(Acked(i, t, c), ledConf[t])
--     /\ commits' = commits \cup {[server |-> i, term |-> t, entries |-> SubSeq(ledLog[t], 1, c)]}
-- Next: \E l \in leaders : l.server = i /\ \E c \in 1..Len(ledLog[l.term]) : LeaderCommit(i, l.term, c)
action LeaderCommit (i : server) {
  let ld : { ld // ld ∈ leaders } :| ld.val.server = i
  let t := ld.val.term
  let l := (ledLog t).getD []
  let c : { c // c ∈ List.range' 1 l.length } :| TermAt l c.val = t
  let ms := msgs
  let vin := lIn t
  let vout := lOut t
  require MemberCore.IsQ (fun j =>
    decide (∃ a : { a // a ∈ ms },
      (match a.val with
        | .ack src dst term index => decide (src = j ∧ dst = i ∧ term = t ∧ index ≥ c.val)
        | _ => false) = true)) { inn := vin, out := vout }
  commits := cSet.insert { server := i, term := t, entries := SubSeq l 1 c.val } commits
}

-- PrevOk(j, m) ==
--     IF m.prevLogIndex = 0 THEN TRUE
--     ELSE /\ m.prevLogIndex <= Len(log[j])
--          /\ log[j][m.prevLogIndex].term = m.prevLogTerm
def PrevOk {value : Type} (l : List (Entry value)) (prevLogIndex prevLogTerm : Nat) : Bool :=
  match prevLogIndex with
  | 0 => true
  | p + 1 => match l[p]? with
    | some e => e.term == prevLogTerm
    | none => false

-- HasFirst(j, m, k) ==
--     \A q \in 1..k :
--         /\ m.prevLogIndex + q <= Len(log[j])
--         /\ log[j][m.prevLogIndex + q].term = m.entries[q].term
def HasFirst {value : Type} (l : List (Entry value)) (prevLogIndex : Nat) (entries : List (Entry value))
    (k : Nat) : Bool :=
  (List.range k).all fun q =>
    match l[prevLogIndex + q]?, entries[q]? with
    | some a, some b => a.term == b.term
    | _, _ => false

-- DeleteSuffix(j, m, k) ==
--     /\ m \in msgs /\ m.type = "append" /\ m.dst = j
--     /\ m.term = currentTerm[j]
--     /\ PrevOk(j, m)
--     /\ k \in 1..Len(m.entries)
--     /\ HasFirst(j, m, k - 1)
--     /\ m.prevLogIndex + k <= Len(log[j])
--     /\ log[j][m.prevLogIndex + k].term # m.entries[k].term
--     /\ log' = [log EXCEPT ![j] = SubSeq(@, 1, m.prevLogIndex + k - 1)]
--     /\ confirmed' = Confirm(j, m.term, m.prevLogIndex + k - 1)
-- Next: \E m \in msgs : m.type = "append" /\ \E k \in 1..Len(m.entries) : DeleteSuffix(m.dst, m, k)
action DeleteSuffix {
  let m : { m // m ∈ msgs } :| m.val.isAppend = true
  let m := m.val
  let j := m.dst
  let l := log j
  require m.term = currentTerm j
  require PrevOk l m.prevLogIndex m.prevLogTerm
  let k : { k // k ∈ List.range' 1 m.entries.length } :|
    HasFirst l m.prevLogIndex m.entries (k.val - 1) ∧
    m.prevLogIndex + k.val ≤ l.length ∧
    TermAt l (m.prevLogIndex + k.val) ≠ TermAt m.entries k.val
  log j := SubSeq l 1 (m.prevLogIndex + k.val - 1)
  confirmedTerm j := m.term
  confirmedIndex j := m.prevLogIndex + k.val - 1
}

-- StoreEntries(j, m, k) ==
--     /\ m \in msgs /\ m.type = "append" /\ m.dst = j
--     /\ m.term = currentTerm[j]
--     /\ PrevOk(j, m)
--     /\ k \in 1..Len(m.entries)
--     /\ HasFirst(j, m, k - 1)
--     /\ m.prevLogIndex + k = Len(log[j]) + 1
--     /\ log' = [log EXCEPT ![j] = @ \o SubSeq(m.entries, k, Len(m.entries))]
--     /\ confirmed' = Confirm(j, m.term, m.prevLogIndex + Len(m.entries))
action StoreEntries {
  let m : { m // m ∈ msgs } :| m.val.isAppend = true
  let m := m.val
  let j := m.dst
  let l := log j
  require m.term = currentTerm j
  require PrevOk l m.prevLogIndex m.prevLogTerm
  let k : { k // k ∈ List.range' 1 m.entries.length } :|
    HasFirst l m.prevLogIndex m.entries (k.val - 1) ∧
    m.prevLogIndex + k.val = l.length + 1
  log j := l ++ SubSeq m.entries k.val m.entries.length
  confirmedTerm j := m.term
  confirmedIndex j := m.prevLogIndex + m.entries.length
}

-- Ack(j, m) ==
--     /\ m \in msgs /\ m.type = "append" /\ m.dst = j
--     /\ currentTerm[j] = m.term
--     /\ PrevOk(j, m)
--     /\ HasFirst(j, m, Len(m.entries))
--     /\ LET last == m.prevLogIndex + Len(m.entries)
--        IN /\ msgs' = msgs \cup {[type |-> "ack", src |-> j, dst |-> m.src, term |-> m.term, index |-> last]}
--           /\ confirmed' = Confirm(j, m.term,
--                 IF confirmed[j].term = m.term THEN Max(confirmed[j].index, last) ELSE last)
action Ack {
  let m : { m // m ∈ msgs } :| m.val.isAppend = true
  let m := m.val
  let j := m.dst
  let l := log j
  require currentTerm j = m.term
  require PrevOk l m.prevLogIndex m.prevLogTerm
  require HasFirst l m.prevLogIndex m.entries m.entries.length
  let last := m.prevLogIndex + m.entries.length
  let idx := if confirmedTerm j = m.term then max (confirmedIndex j) last else last
  msgs := msgSet.insert (.ack j m.src m.term last) msgs
  confirmedTerm j := m.term
  confirmedIndex j := idx
}

-- AckCommitted(j, m) ==
--     /\ m \in msgs /\ m.type = "append" /\ m.dst = j
--     /\ currentTerm[j] = m.term
--     /\ m.prevLogIndex < commitIndex[j]
--     /\ msgs' = msgs \cup {[type |-> "ack", src |-> j, dst |-> m.src, term |-> m.term,
--                             index |-> commitIndex[j]]}
action AckCommitted {
  let m : { m // m ∈ msgs } :| m.val.isAppend = true
  let m := m.val
  let j := m.dst
  require currentTerm j = m.term
  require m.prevLogIndex < commitIndex j
  msgs := msgSet.insert (.ack j m.src m.term (commitIndex j)) msgs
}

-- FollowerCommit(j, m, c) ==
--     /\ m \in msgs /\ m.type = "append" /\ m.dst = j
--     /\ m.term = confirmed[j].term
--     /\ c > commitIndex[j]
--     /\ c <= Min(m.commit, confirmed[j].index)
--     /\ commitIndex' = [commitIndex EXCEPT ![j] = c]
--     /\ commits' = commits \cup {Committed(j, m.term, c)}
-- Next: \E c \in 1..m.commit : FollowerCommit(m.dst, m, c)
action FollowerCommit {
  let m : { m // m ∈ msgs } :| m.val.isAppend = true
  let m := m.val
  let j := m.dst
  require m.term = confirmedTerm j
  let ci := commitIndex j
  let cf := confirmedIndex j
  let c : { c // c ∈ List.range' 1 m.commit } :| c.val > ci ∧ c.val ≤ min m.commit cf
  commitIndex j := c.val
  commits := cSet.insert { server := j, term := m.term, entries := SubSeq (log j) 1 c.val } commits
}

-- IsCommitted(l, k) ==
--     \E c \in commits : k <= Len(c.entries) /\ SubSeq(c.entries, 1, k) = SubSeq(l, 1, k)
-- Apply(i) ==
--     LET k == lastApplied[i] + 1 IN
--     /\ k <= Len(log[i])
--     /\ IsCommitted(log[i], k)
--     /\ lastApplied' = [lastApplied EXCEPT ![i] = k]
--     /\ applied' = applied \cup {[server |-> i, index |-> k, entry |-> log[i][k]]}
-- `log[i][k]` is read with a default that the first requirement makes unreachable.
action Apply (i : server) {
  let k := lastApplied i + 1
  let l := log i
  require k ≤ l.length
  require ∃ c : { c // c ∈ commits }, k ≤ c.val.entries.length ∧ SubSeq c.val.entries 1 k = SubSeq l 1 k
  lastApplied i := k
  applied := aSet.insert { server := i, index := k, entry := (l[k - 1]?).getD noEntry } applied
}

-- Restart(i) ==
--     /\ role' = [role EXCEPT ![i] = Follower]
--     /\ lastApplied' = [lastApplied EXCEPT ![i] = 0]
--     /\ config' = [config EXCEPT ![i] = InitConf]
--     /\ confAt' = [confAt EXCEPT ![i] = 0]
action Restart (i : server) {
  role i := Follower
  lastApplied i := 0
  cIn i S := initV S
  cOut i S := false
  confAt i := 0
}

-- Restore(i, a) ==
--     /\ a \in 0..Len(log[i])
--     /\ a = 0 \/ IsCommitted(log[i], a)
--     /\ lastApplied' = [lastApplied EXCEPT ![i] = a]
-- Next: \E a \in 0..Len(log[i]) : Restore(i, a)
action Restore (i : server) {
  let l := log i
  let cs := commits
  let a : { a // a ∈ List.range (l.length + 1) } :|
    a.val = 0 ∨ ∃ c : { c // c ∈ cs }, a.val ≤ c.val.entries.length ∧ SubSeq c.val.entries 1 a.val = SubSeq l 1 a.val
  lastApplied i := a.val
}

-- RestoreConf(i, c, a) ==
--     /\ c \in commits /\ a \in 0..Len(c.entries)
--     /\ role[i] # Leader
--     /\ config' = [config EXCEPT ![i] = ConfOf(c.entries, a)]
--     /\ confAt' = [confAt EXCEPT ![i] = LastConf(c.entries, a)]
-- Next: \E c \in commits : \E a \in 0..Len(c.entries) : RestoreConf(i, c, a)
action RestoreConf (i : server) {
  require role i ≠ Leader
  let c : { c // c ∈ commits } :| True
  let es := c.val.entries
  let a : { a // a ∈ List.range (es.length + 1) } :| True
  let iv := initV
  let ad := chAdd
  let rm := chRemove
  let jt := chJoint
  let lv := chLeave
  cIn i S := (cOf iv ad rm jt lv es a.val).inn S
  cOut i S := (cOf iv ad rm jt lv es a.val).out S
  confAt i := lastConf es a.val
}

-- LeaderKnows(i, k) == CommittedIn(log[i], k, currentTerm[i])
-- SwitchConf(i, k) ==
--     /\ k > confAt[i] /\ k <= lastApplied[i] /\ k <= Len(log[i])
--     /\ IsCommitted(log[i], k)
--     /\ IsConf(log[i][k])
--     /\ \A q \in (confAt[i] + 1)..(k - 1) : ~IsConf(log[i][q])
--     /\ Legal(config[i], log[i][k].value)
--     /\ role[i] = Leader => LeaderKnows(i, k)
--     /\ LET C == NextConf(config[i], log[i][k].value) IN
--        /\ config' = [config EXCEPT ![i] = C]
--        /\ ledConf' = IF role[i] = Leader THEN WithConf(currentTerm[i], C) ELSE ledConf
--     /\ ledAt' = IF role[i] = Leader THEN With(ledAt, currentTerm[i], k) ELSE ledAt
--     /\ confAt' = [confAt EXCEPT ![i] = k]
-- Next: \E k \in 1..Len(log[i]) : SwitchConf(i, k)
action SwitchConf (i : server) {
  let l := log i
  let ca := confAt i
  let cur := currentTerm i
  let cs := commits
  let vin := cIn i
  let vout := cOut i
  let ad := chAdd
  let rm := chRemove
  let jt := chJoint
  let lv := chLeave
  let rl := role i
  let k : { k // k ∈ List.range' 1 l.length } :|
    k.val > ca ∧ k.val ≤ lastApplied i ∧
    (∃ c : { c // c ∈ cs }, k.val ≤ c.val.entries.length ∧ SubSeq c.val.entries 1 k.val = SubSeq l 1 k.val) ∧
    (rl = Leader → ∃ c : { c // c ∈ cs },
      c.val.term ≤ cur ∧ k.val ≤ c.val.entries.length ∧ SubSeq c.val.entries 1 k.val = SubSeq l 1 k.val)
  require switchOk ad rm jt lv l ca k.val vin vout
  cIn i S := (switchTo ad rm jt lv l k.val vin vout).inn S
  cOut i S := (switchTo ad rm jt lv l k.val vin vout).out S
  confAt i := k.val
  lIn N S := if (N = cur ∧ rl = Leader) then (switchTo ad rm jt lv l k.val vin vout).inn S else lIn N S
  lOut N S := if (N = cur ∧ rl = Leader) then (switchTo ad rm jt lv l k.val vin vout).out S else lOut N S
  ledAt N := if (N = cur ∧ rl = Leader) then k.val else ledAt N
}

-- Facts about logs, for the proofs at the end of this file.

-- ReadRequest(i, c) ==
--     /\ role[i] = Leader
--     /\ LET t == currentTerm[i] IN
--        /\ t \in DOMAIN ledLog /\ c <= Len(ledLog[t])
--        /\ \E k \in commits : k.term = t
--        /\ \A k \in commits : k.term <= t => Len(k.entries) <= c
--        /\ read' = [on |-> TRUE, done |-> FALSE, term |-> t, index |-> c,
--                    floor |-> commits, msgs |-> msgs, resp |-> {}]
-- Next: \E c \in 0..Len(ledLog[currentTerm[i]]) : ReadRequest(i, c)
action ReadRequest (i : server) {
  require role i = Leader
  let t := currentTerm i
  let l := (ledLog t).getD []
  let cs := commits
  require ∃ k : { k // k ∈ cs }, k.val.term = t
  let c : { c // c ∈ List.range (l.length + 1) } :|
    ∀ k : { k // k ∈ cs }, k.val.term ≤ t → k.val.entries.length ≤ c.val
  readOn := true
  readDone := false
  readTerm := t
  readIndex := c.val
  readFloor := cs
  readMsgs := msgs
  readResp J := false
}

-- ReadAck(j) ==
--     /\ read.on /\ currentTerm[j] <= read.term
--     /\ read' = [read EXCEPT !.resp = @ \cup {j}]
action ReadAck (j : server) {
  require readOn = true
  require currentTerm j ≤ readTerm
  readResp j := true
}

-- ReadConfirm ==
--     /\ read.on /\ IsQuorum(read.resp, ledConf[read.term])
--     /\ read' = [read EXCEPT !.done = TRUE]
action ReadConfirm {
  require readOn = true
  let t := readTerm
  let vin := lIn t
  let vout := lOut t
  require MemberCore.IsQ (fun j => readResp j) { inn := vin, out := vout }
  readDone := true
}

-- Every entry of `l`, with its predecessors, is in the leader log of its term.
def FromLed {value : Type} [DecidableEq value] (led : Nat → Option (List (Entry value)))
    (l : List (Entry value)) : Prop :=
  ∀ q ∈ List.range l.length,
    ((led (TermAt l (q + 1))).any fun L => decide (l.take (q + 1) = L.take (q + 1))) = true

instance {value : Type} [DecidableEq value] (led : Nat → Option (List (Entry value)))
    (l : List (Entry value)) : Decidable (FromLed led l) := by
  unfold FromLed; infer_instance

section LogLemmas
set_option linter.unusedSectionVars false
variable {value : Type} [DecidableEq value]

theorem termAt_succ (l : List (Entry value)) (q : Nat) (h : q < l.length) :
    TermAt l (q + 1) = l[q].term := by
  simp [TermAt, List.getElem?_eq_getElem h]

theorem subSeq_one {α : Type} (l : List α) (k : Nat) : SubSeq l 1 k = l.take k := by
  simp [SubSeq]

theorem subSeq_length {α : Type} (l : List α) (p n : Nat) (h : p + n ≤ l.length) :
    (SubSeq l (p + 1) (p + n)).length = n := by
  simp [SubSeq]; omega

theorem termAt_take (l : List (Entry value)) (c k : Nat) (h : k ≤ c) :
    TermAt (l.take c) k = TermAt l k := by
  cases k with
  | zero => rfl
  | succ q => simp [TermAt, show q < c by omega]

theorem termAt_append_left (l es : List (Entry value)) (k : Nat) (h : k ≤ l.length) :
    TermAt (l ++ es) k = TermAt l k := by
  cases k with
  | zero => rfl
  | succ q => simp [TermAt, List.getElem?_append_left (show q < l.length by omega)]

theorem subSeq_append_left {α : Type} (l es : List α) (a b : Nat) (ha : 1 ≤ a) (h : b ≤ l.length) :
    SubSeq (l ++ es) a b = SubSeq l a b := by
  unfold SubSeq
  by_cases hab : a ≤ b
  · rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
  · simp [show b + 1 - a = 0 by omega]

theorem FromLed.iff (led : Nat → Option (List (Entry value))) (l : List (Entry value)) :
    FromLed led l ↔ ∀ q, q < l.length →
      ∃ L, led (TermAt l (q + 1)) = some L ∧ l.take (q + 1) = L.take (q + 1) := by
  unfold FromLed
  constructor
  · intro h q h2
    have h' := h q (List.mem_range.2 h2)
    cases hl : led (TermAt l (q + 1)) with
    | none => simp [hl] at h'
    | some L => exact ⟨L, rfl, by simpa [hl] using h'⟩
  · intro h q hq
    obtain ⟨L, hL, he⟩ := h q (List.mem_range.1 hq)
    simp [hL, he]

theorem FromLed.take (led : Nat → Option (List (Entry value))) (l : List (Entry value)) (c : Nat)
    (h : FromLed led l) : FromLed led (l.take c) := by
  rw [FromLed.iff] at *
  intro q h2
  have hq : q < c ∧ q < l.length := by simp at h2; omega
  obtain ⟨L, hL, he⟩ := h q hq.2
  refine ⟨L, by rw [termAt_take _ _ _ (by omega)]; exact hL, ?_⟩
  rw [List.take_take, Nat.min_eq_left (by omega)]; exact he

theorem FromLed.mono (led led' : Nat → Option (List (Entry value))) (l : List (Entry value))
    (hm : ∀ t L, led t = some L → ∃ L', led' t = some L' ∧ L <+: L')
    (h : FromLed led l) : FromLed led' l := by
  rw [FromLed.iff] at *
  intro q h2
  obtain ⟨L, hL, he⟩ := h q h2
  obtain ⟨L', hL', hp⟩ := hm _ _ hL
  refine ⟨L', hL', ?_⟩
  have hlen : q + 1 ≤ L.length := by
    have := congrArg List.length he
    simp at this; omega
  obtain ⟨s, rfl⟩ := hp
  rw [he, List.take_append_of_le_length hlen]

theorem FromLed.append_own (led : Nat → Option (List (Entry value))) (l es : List (Entry value))
    (t : Nat) (hled : led t = some (l ++ es)) (hes : ∀ e ∈ es, e.term = t)
    (h : FromLed led l) : FromLed led (l ++ es) := by
  rw [FromLed.iff] at *
  intro q h2
  by_cases hq : q < l.length
  · obtain ⟨L, hL, he⟩ := h q hq
    refine ⟨L, by rw [termAt_append_left _ _ _ (by omega)]; exact hL, ?_⟩
    rw [List.take_append_of_le_length (by omega)]; exact he
  · refine ⟨l ++ es, ?_, rfl⟩
    rw [termAt_succ _ _ h2]
    have : (l ++ es)[q] ∈ es := by
      rw [List.getElem_append_right (by omega)]
      exact List.getElem_mem _
    rw [hes _ this]; exact hled

-- Two logs that are both from leader logs match.
theorem FromLed.matching (led : Nat → Option (List (Entry value))) (a b : List (Entry value))
    (ha : FromLed led a) (hb : FromLed led b) :
    ∀ k ∈ List.range' 1 (min a.length b.length),
      TermAt a k = TermAt b k → SubSeq a 1 k = SubSeq b 1 k := by
  rw [FromLed.iff] at *
  intro k hk ht
  rw [subSeq_one, subSeq_one]
  have hk' : 1 ≤ k ∧ k ≤ a.length ∧ k ≤ b.length := by
    simp [List.mem_range'] at hk; omega
  obtain ⟨q, rfl⟩ : ∃ q, k = q + 1 := ⟨k - 1, by omega⟩
  obtain ⟨L, hL, he⟩ := ha q (by omega)
  obtain ⟨L', hL', he'⟩ := hb q (by omega)
  rw [ht, hL'] at hL
  cases hL
  rw [he, he']

theorem FromLed.prefix_of_term (led : Nat → Option (List (Entry value))) (l L : List (Entry value))
    (hl : FromLed led l) (hL : FromLed led L)
    (c : Nat) (hc1 : 1 ≤ c) (hcl : c ≤ l.length) (hcL : c ≤ L.length)
    (ht : TermAt l c = TermAt L c) : l.take c = L.take c := by
  have := FromLed.matching led l L hl hL c (List.mem_range'_1.2 ⟨hc1, by omega⟩) ht
  simpa [subSeq_one] using this

theorem hasFirst_get (l es : List (Entry value)) (p k q : Nat) (h : HasFirst l p es k = true)
    (hq : q < k) : ∃ a b, l[p + q]? = some a ∧ es[q]? = some b ∧ a.term = b.term := by
  unfold HasFirst at h
  rw [List.all_eq_true] at h
  have := h q (List.mem_range.2 hq)
  split at this
  · next a b ha hb => exact ⟨a, b, ha, hb, by simpa using this⟩
  · simp at this

-- What a node acknowledges is within its log.
theorem ack_within (l es : List (Entry value)) (p pt : Nat) (hp : PrevOk l p pt = true)
    (h : HasFirst l p es es.length = true) : p + es.length ≤ l.length := by
  rcases Nat.eq_zero_or_pos es.length with h0 | hpos
  · rw [h0]
    cases p with
    | zero => exact Nat.zero_le _
    | succ q =>
      unfold PrevOk at hp
      cases hq : l[q]? with
      | none => simp [hq] at hp
      | some e =>
        obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.1 hq
        omega
  · obtain ⟨a, b, ha, _, _⟩ := hasFirst_get l es p es.length (es.length - 1) h (by omega)
    obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.1 ha
    omega

-- StoreEntries: a follower passing the checks ends with the first p + n entries of the leader log.
theorem store_eq (led : Nat → Option (List (Entry value))) (l L : List (Entry value)) (p k : Nat)
    (es : List (Entry value))
    (hl : FromLed led l) (hL : FromLed led L)
    (hpn : p + es.length ≤ L.length)
    (hes : es = SubSeq L (p + 1) (p + es.length))
    (hprev : PrevOk l p (TermAt L p) = true)
    (hk : k ∈ List.range' 1 es.length)
    (hfirst : HasFirst l p es (k - 1) = true)
    (hlen : p + k = l.length + 1) :
    l ++ SubSeq es k es.length = L.take (p + es.length) := by
  have hk' : 1 ≤ k ∧ k ≤ es.length := by simp [List.mem_range'] at hk; omega
  rcases Nat.eq_zero_or_pos l.length with hl0 | hlpos
  · -- an empty log: the request starts at the first entry and is stored whole
    have hl' : l = [] := List.length_eq_zero_iff.1 hl0
    have hp : p = 0 := by omega
    have hk1 : k = 1 := by omega
    subst hl' hp hk1
    rw [List.nil_append, subSeq_one, List.take_length]
    conv => lhs; rw [hes]
    simp [SubSeq]
  -- the last entry of l has the term of the entry of L at the same index
  have hterm : TermAt l l.length = TermAt L l.length := by
    rcases Nat.lt_or_ge 1 k with h2 | h1
    · obtain ⟨a, b, ha, hb, hab⟩ := hasFirst_get l es p (k - 1) (k - 2) hfirst (by omega)
      have hidx : p + (k - 2) = l.length - 1 := by omega
      have hb' : L[l.length - 1]? = some b := by
        rw [hes] at hb
        simp only [SubSeq, List.getElem?_take, List.getElem?_drop] at hb
        split at hb
        · rw [show p + 1 - 1 + (k - 2) = l.length - 1 by omega] at hb; exact hb
        · simp at hb
      rw [hidx] at ha
      obtain ⟨c, hc⟩ : ∃ c, l.length = c + 1 := ⟨l.length - 1, by omega⟩
      simp only [hc, Nat.add_sub_cancel] at ha hb' ⊢
      simp [TermAt, ha, hb', hab]
    · have hk1 : k = 1 := by omega
      subst hk1
      have hp : p = l.length := by omega
      subst hp
      obtain ⟨c, hc⟩ : ∃ c, l.length = c + 1 := ⟨l.length - 1, by omega⟩
      rw [hc] at hprev ⊢
      simp only [PrevOk] at hprev
      split at hprev
      · next e he =>
        have : e.term = TermAt L (c + 1) := by simpa using hprev
        rw [← this]; simp [TermAt, he]
      · simp at hprev
  have hpre : l = L.take l.length := by
    have := FromLed.prefix_of_term led l L hl hL l.length hlpos (Nat.le_refl _) (by omega) hterm
    simpa using this
  have hdrop : SubSeq es k es.length = (L.drop l.length).take (p + es.length - l.length) := by
    rw [hes]
    simp only [SubSeq, List.length_take, List.length_drop, List.drop_take, List.drop_drop, List.take_take]
    rw [show p + 1 - 1 + (k - 1) = l.length by omega]
    congr 1
    omega
  rw [hdrop]
  conv => lhs; lhs; rw [hpre]
  rw [← List.take_add]
  congr 1; omega

theorem optAll_iff {α : Type} (o : Option α) (P : α → Prop) {d : DecidablePred P} :
    (o.all fun L => @decide (P L) (d L)) = true ↔ ∀ L, o = some L → P L := by
  cases o <;> simp

-- Facts about logs for the proof of StateMachineSafety.

-- Terms in `l` never decrease along the log and are at most `t`.
def Sorted (l : List (Entry value)) (t : Nat) : Prop :=
  (∀ a b, 1 ≤ a → a ≤ b → b ≤ l.length → TermAt l a ≤ TermAt l b) ∧ ∀ a, TermAt l a ≤ t

theorem termAt_le_of_gt (l : List (Entry value)) (k : Nat) (h : l.length < k) : TermAt l k = 0 := by
  cases k with
  | zero => rfl
  | succ q => simp [TermAt, List.getElem?_eq_none (show l.length ≤ q by omega)]

theorem termAt_append_right (l es : List (Entry value)) (k : Nat) (h1 : l.length < k)
    (h2 : k ≤ l.length + es.length) : ∃ e ∈ es, TermAt (l ++ es) k = e.term := by
  obtain ⟨q, rfl⟩ : ∃ q, k = q + 1 := ⟨k - 1, by omega⟩
  have hq : q < (l ++ es).length := by simp; omega
  refine ⟨(l ++ es)[q], ?_, termAt_succ _ _ hq⟩
  rw [List.getElem_append_right (by omega)]
  exact List.getElem_mem _

theorem termAt_of_prefix (a l : List (Entry value)) (k : Nat) (h : a <+: l) (hk : k ≤ a.length) :
    TermAt l k = TermAt a k := by
  obtain ⟨s, rfl⟩ := h
  exact termAt_append_left _ _ _ hk

theorem take_prefix_iff (a l : List (Entry value)) (c : Nat) (hc : c ≤ a.length) :
    a.take c <+: l ↔ c ≤ l.length ∧ a.take c = l.take c := by
  constructor
  · intro h
    have hl := h.length_le
    simp at hl
    refine ⟨by omega, ?_⟩
    obtain ⟨s, hs⟩ := h
    rw [← hs, List.take_append_of_le_length (by simp; omega)]
    simp [List.take_take]
  · rintro ⟨_, h⟩
    rw [h]; exact List.take_prefix _ _

-- Sortedness is kept by appending entries of a term at least as high as every term so far.
theorem Sorted.append (l es : List (Entry value)) (t : Nat) (h : Sorted l t)
    (hes : ∀ e ∈ es, e.term = t) : Sorted (l ++ es) t := by
  obtain ⟨h1, h2⟩ := h
  have hb : ∀ a, TermAt (l ++ es) a ≤ t := by
    intro a
    rcases Nat.lt_or_ge l.length a with ha | ha
    · rcases Nat.lt_or_ge (l.length + es.length) a with hb | hb
      · rw [termAt_le_of_gt _ _ (by simp; omega)]; omega
      · obtain ⟨e, he, heq⟩ := termAt_append_right l es a ha hb
        rw [heq, hes e he]; omega
    · rw [termAt_append_left _ _ _ ha]; exact h2 a
  refine ⟨?_, hb⟩
  intro a b ha hab hbl
  simp at hbl
  rcases Nat.lt_or_ge l.length b with hb' | hb'
  · obtain ⟨e, he, heq⟩ := termAt_append_right l es b hb' hbl
    rw [heq, hes e he]; exact hb a
  · rw [termAt_append_left _ _ _ hb', termAt_append_left _ _ _ (by omega)]
    exact h1 a b ha hab hb'

theorem Sorted.take (l : List (Entry value)) (t c : Nat) (h : Sorted l t) : Sorted (l.take c) t := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro a b ha hab hb
    simp at hb
    rw [termAt_take _ _ _ (by omega), termAt_take _ _ _ (by omega)]
    exact h1 a b ha hab (by omega)
  · intro a
    rcases Nat.lt_or_ge c a with hc | hc
    · rw [termAt_le_of_gt _ _ (by simp; omega)]; omega
    · rw [termAt_take _ _ _ hc]; exact h2 a

-- A leader log lacking `a`'s first c entries still lacks them after growing by its own term.
theorem lacks_append (a l es : List (Entry value)) (c w : Nat) (hc : c ≤ a.length)
    (ha : ∀ x, TermAt a x < w) (hes : ∀ e ∈ es, e.term = w)
    (h : ¬ a.take c <+: l) : ¬ a.take c <+: l ++ es := by
  intro hp
  rw [take_prefix_iff _ _ _ hc] at hp h
  obtain ⟨hlen, heq⟩ := hp
  simp at hlen
  rcases Nat.lt_or_ge l.length c with hlc | hlc
  · -- position l.length + 1 of `a` has a term below w, of l ++ es the term w
    obtain ⟨e, he, hterm⟩ := termAt_append_right l es (l.length + 1) (by omega) (by omega)
    have h1 : TermAt (a.take c) (l.length + 1) = TermAt ((l ++ es).take c) (l.length + 1) := by rw [heq]
    rw [termAt_take _ _ _ (by omega), termAt_take _ _ _ (by omega), hterm, hes e he] at h1
    have := ha (l.length + 1)
    omega
  · apply h
    refine ⟨hlc, ?_⟩
    rw [heq, List.take_append_of_le_length hlc]

-- Vote-time argument: a voter holding the first c entries of the term-t leader log (the c-th of
-- term t) votes for (li, lt): the candidate holds them, or the leader log of lt > t lacks them.
theorem vote_cover (led : Nat → Option (List (Entry value))) (ln A : List (Entry value))
    (t c li lt : Nat)
    (hA : led t = some A) (hc2 : 1 ≤ c) (hcA : c ≤ A.length) (hct : TermAt A c = t)
    (hheld : A.take c <+: ln)
    (hln : FromLed led ln)
    (hsorted : ∀ w B, led w = some B → Sorted B w)
    (hreq : li = 0 ∧ lt = 0 ∨ ∃ B, led lt = some B ∧ li ≤ B.length ∧ TermAt B li = lt)
    (hup : lt > TermAt ln ln.length ∨ (lt = TermAt ln ln.length ∧ li ≥ ln.length)) :
    (c ≤ li ∧ ∃ B, led lt = some B ∧ A.take c = B.take c) ∨
    (t < lt ∧ ∃ B, led lt = some B ∧ ¬ A.take c <+: B) := by
  rw [take_prefix_iff _ _ _ hcA] at hheld
  obtain ⟨hcl, heq⟩ := hheld
  -- the voter's log is a prefix of the leader log of its last term, s
  rw [FromLed.iff] at hln
  obtain ⟨S, hS, hSeq⟩ := hln (ln.length - 1) (by omega)
  rw [show ln.length - 1 + 1 = ln.length by omega] at hS hSeq
  have hlS : ln.length ≤ S.length := by
    have := congrArg List.length hSeq; simp at this; omega
  have hlnS : ln = S.take ln.length := by simpa using hSeq
  have hterm : ∀ k, k ≤ ln.length → TermAt ln k = TermAt S k := by
    intro k hk; rw [hlnS, termAt_take _ _ _ hk]
  have hAS : A.take c = S.take c := by
    rw [heq, hlnS, List.take_take, Nat.min_eq_left hcl]
  have hSc : TermAt S c = t := by
    rw [← hterm c hcl, ← hct]
    have : TermAt (ln.take c) c = TermAt (A.take c) c := by rw [heq]
    rw [termAt_take _ _ _ (Nat.le_refl c), termAt_take _ _ _ (Nat.le_refl c)] at this
    exact this
  have hSs := hsorted _ S hS
  have hts : t ≤ TermAt ln ln.length := by
    rw [hterm _ (Nat.le_refl _), ← hSc]
    exact hSs.1 c ln.length (by omega) hcl hlS
  rcases hup with hgt | ⟨heqt, hli⟩
  · -- the candidate's last term is above the voter's
    rcases hreq with ⟨_, h1⟩ | ⟨B, hB, hliB, hBt⟩
    · -- an empty log has last term 0, which is not above the voter's
      omega
    · by_cases hpre : A.take c <+: B
      · left
        rw [take_prefix_iff _ _ _ hcA] at hpre
        refine ⟨?_, B, hB, hpre.2⟩
        -- entry li of B has term lt > t, entries up to c have terms at most t
        have hBs := hsorted _ B hB
        have hBc : TermAt B c = t := by
          have : TermAt (A.take c) c = TermAt (B.take c) c := by rw [hpre.2]
          rw [termAt_take _ _ _ (Nat.le_refl c), termAt_take _ _ _ (Nat.le_refl c)] at this
          rw [← this]; exact hct
        rcases Nat.lt_or_ge li c with hlt | hge
        · rcases Nat.eq_zero_or_pos li with h0 | hpos
          · subst h0; simp [TermAt] at hBt; omega
          · have := hBs.1 li c hpos (by omega) hpre.1
            omega
        · exact hge
      · right
        exact ⟨by omega, B, hB, hpre⟩
  · -- same last term: the candidate's log is at least as long, on the same leader log
    left
    refine ⟨by omega, ?_⟩
    rcases hreq with ⟨h1, _⟩ | ⟨B, hB, _, _⟩
    · omega
    · rw [heqt, hS] at hB
      cases hB
      exact ⟨S, by rw [heqt]; exact hS, hAS⟩

theorem termAt_subSeq (L : List (Entry value)) (p n k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ n)
    (h : p + n ≤ L.length) : TermAt (SubSeq L (p + 1) (p + n)) k = TermAt L (p + k) := by
  obtain ⟨q, rfl⟩ : ∃ q, k = q + 1 := ⟨k - 1, by omega⟩
  simp only [TermAt, SubSeq, List.getElem?_take, List.getElem?_drop]
  rw [show p + 1 - 1 + q = p + q by omega]
  simp [show q < n by omega, show p + (q + 1) = p + q + 1 by omega]

-- Passing the checks up to entry k: the log agrees with the leader log on the first p + k entries.
theorem checked_prefix (led : Nat → Option (List (Entry value))) (l L : List (Entry value)) (p k : Nat)
    (es : List (Entry value))
    (hl : FromLed led l) (hL : FromLed led L)
    (hpn : p + es.length ≤ L.length)
    (hes : es = SubSeq L (p + 1) (p + es.length))
    (hprev : PrevOk l p (TermAt L p) = true)
    (hk : k ≤ es.length)
    (hfirst : HasFirst l p es k = true) :
    p + k ≤ l.length ∧ l.take (p + k) = L.take (p + k) := by
  rcases Nat.eq_zero_or_pos (p + k) with h0 | hpos
  · simp [h0]
  · -- the entry of l at p + k has the term of L's
    have hboth : p + k ≤ l.length ∧ TermAt l (p + k) = TermAt L (p + k) := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        obtain ⟨c, hc⟩ : ∃ c, p = c + 1 := ⟨p - 1, by omega⟩
        subst hc
        simp only [PrevOk] at hprev
        split at hprev
        · next e he =>
          have hlt : c < l.length := by
            rcases Nat.lt_or_ge c l.length with h | h
            · exact h
            · rw [List.getElem?_eq_none h] at he; cases he
          have : e.term = TermAt L (c + 1) := by simpa using hprev
          exact ⟨by omega, by rw [← this]; simp [TermAt, he]⟩
        · simp at hprev
      · obtain ⟨a, b, ha, hb, hab⟩ := hasFirst_get l es p k (k - 1) hfirst (by omega)
        have hlt : p + (k - 1) < l.length := by
          rcases Nat.lt_or_ge (p + (k - 1)) l.length with h | h
          · exact h
          · rw [List.getElem?_eq_none h] at ha; cases ha
        refine ⟨by omega, ?_⟩
        have h1 : TermAt l (p + k) = a.term := by
          rw [show p + k = p + (k - 1) + 1 by omega]; simp [TermAt, ha]
        have h2 : TermAt es k = b.term := by
          rw [show k = (k - 1) + 1 by omega]; simp [TermAt, hb]
        rw [h1, hab, ← h2, hes, termAt_subSeq L p es.length k hkpos hk hpn]
    refine ⟨hboth.1, ?_⟩
    exact FromLed.prefix_of_term led l L hl hL (p + k) hpos hboth.1 (by omega) hboth.2

-- DeleteSuffix: a held prefix of another leader log survives, or the request's leader log lacks it.
theorem delete_held (a l B : List (Entry value)) (c p k : Nat) (es : List (Entry value))
    (hc : c ≤ a.length) (hheld : a.take c <+: l)
    (hpn : p + es.length ≤ B.length) (hes : es = SubSeq B (p + 1) (p + es.length))
    (hk1 : 1 ≤ k) (hk : k ≤ es.length) (hkl : p + k ≤ l.length)
    (hne : TermAt l (p + k) ≠ TermAt es k) :
    a.take c <+: SubSeq l 1 (p + k - 1) ∨ ¬ a.take c <+: B := by
  rw [subSeq_one]
  rcases Nat.lt_or_ge c (p + k) with hlt | hge
  · left
    rw [take_prefix_iff _ _ _ hc] at hheld ⊢
    refine ⟨by simp; omega, ?_⟩
    rw [List.take_take, Nat.min_eq_left (by omega)]; exact hheld.2
  · right
    intro hB
    apply hne
    rw [take_prefix_iff _ _ _ hc] at hheld hB
    have h1 : TermAt (l.take c) (p + k) = TermAt (B.take c) (p + k) := by rw [← hheld.2, hB.2]
    rw [termAt_take _ _ _ hge, termAt_take _ _ _ hge] at h1
    rw [h1, hes, termAt_subSeq B p es.length k hk1 hk hpn]

-- DeleteSuffix: a prefix shared with the request's leader log ends before the conflict.
theorem delete_keeps (l B : List (Entry value)) (ci p k : Nat) (es : List (Entry value))
    (hci : ci ≤ l.length) (hB : l.take ci <+: B)
    (hpn : p + es.length ≤ B.length) (hes : es = SubSeq B (p + 1) (p + es.length))
    (hk1 : 1 ≤ k) (hk : k ≤ es.length) (hkl : p + k ≤ l.length)
    (hne : TermAt l (p + k) ≠ TermAt es k) : ci ≤ p + k - 1 := by
  rcases delete_held l l B ci p k es hci (List.take_prefix _ _) hpn hes hk1 hk hkl hne with h | h
  · have := h.length_le
    simp [subSeq_one] at this
    omega
  · exact absurd hB h

-- A log from leader logs whose terms are bounded is sorted, given that leader logs are.
theorem sorted_of_fromLed (led : Nat → Option (List (Entry value))) (l : List (Entry value)) (u : Nat)
    (hl : FromLed led l) (hsorted : ∀ w B, led w = some B → Sorted B w)
    (hb : ∀ k, TermAt l k ≤ u) : Sorted l u := by
  refine ⟨?_, hb⟩
  intro a b ha hab hbl
  rcases Nat.lt_or_ge 1 b with h2 | h1
  · rw [FromLed.iff] at hl
    obtain ⟨S, hS, heq⟩ := hl (b - 1) (by omega)
    rw [show b - 1 + 1 = b by omega] at hS heq
    have hbS : b ≤ S.length := by have := congrArg List.length heq; simp at this; omega
    have e1 : TermAt l a = TermAt S a := by
      have : TermAt (l.take b) a = TermAt (S.take b) a := by rw [heq]
      rwa [termAt_take _ _ _ hab, termAt_take _ _ _ hab] at this
    have e2 : TermAt l b = TermAt S b := by
      have : TermAt (l.take b) b = TermAt (S.take b) b := by rw [heq]
      rwa [termAt_take _ _ _ (Nat.le_refl b), termAt_take _ _ _ (Nat.le_refl b)] at this
    rw [e1, e2]; exact (hsorted _ S hS).1 a b ha hab hbS
  · have : a = b := by omega
    subst this; exact Nat.le_refl _

-- What the proof of StateMachineSafety says about leader logs.
-- The leader log of term w does not have the first c entries of `a`.
def Lacks {value : Type} (led : Nat → Option (List (Entry value))) (a : List (Entry value)) (c w : Nat) : Prop :=
  ∃ B, led w = some B ∧ ¬ a.take c <+: B

-- Some leader log of a term in (lo, hi] does not have them.
def LostIn {value : Type} (led : Nat → Option (List (Entry value))) (a : List (Entry value))
    (c lo hi : Nat) : Prop :=
  ∃ w, lo < w ∧ w ≤ hi ∧ Lacks led a c w

-- A log of li entries, the last of term lt, has them.
def Covers {value : Type} (led : Nat → Option (List (Entry value))) (a : List (Entry value))
    (c li lt : Nat) : Prop :=
  c ≤ li ∧ ∃ B, led lt = some B ∧ a.take c = B.take c

-- A vote request's (li, lt) describes a prefix of the leader log of lt.
def ReqOk {value : Type} (led : Nat → Option (List (Entry value))) (u li lt : Nat) : Prop :=
  lt < u ∧ ((li = 0 ∧ lt = 0) ∨ ∃ B, led lt = some B ∧ li ≤ B.length ∧ TermAt B li = lt)
-- Leader logs only grow, each by entries of its own term: what every step does to them.
def LedGrows (led led' : Nat → Option (List (Entry value))) : Prop :=
  ∀ w B, led w = some B → ∃ es, led' w = some (B ++ es) ∧ ∀ e ∈ es, e.term = w

theorem LedGrows.refl (led : Nat → Option (List (Entry value))) : LedGrows led led :=
  fun _ B h => ⟨[], by simpa using h, by simp⟩

theorem LostIn.mono_hi (led : Nat → Option (List (Entry value))) (a : List (Entry value))
    (c lo hi hi' : Nat) (h : LostIn led a c lo hi) (hh : hi ≤ hi') : LostIn led a c lo hi' := by
  obtain ⟨w, h1, h2, h3⟩ := h
  exact ⟨w, h1, by omega, h3⟩

theorem LostIn.grows (led led' : Nat → Option (List (Entry value))) (a : List (Entry value))
    (c lo hi : Nat) (hg : LedGrows led led') (hc : c ≤ a.length) (ha : ∀ x, TermAt a x ≤ lo)
    (h : LostIn led a c lo hi) : LostIn led' a c lo hi := by
  obtain ⟨w, h1, h2, B, hB, hl⟩ := h
  obtain ⟨es, hB', hes⟩ := hg w B hB
  exact ⟨w, h1, h2, B ++ es, hB', lacks_append a B es c w hc (fun x => by have := ha x; omega) hes hl⟩

theorem Covers.grows (led led' : Nat → Option (List (Entry value))) (a : List (Entry value))
    (c li lt : Nat) (hg : LedGrows led led') (hc : c ≤ a.length)
    (h : Covers led a c li lt) : Covers led' a c li lt := by
  obtain ⟨h1, B, hB, heq⟩ := h
  obtain ⟨es, hB', _⟩ := hg lt B hB
  refine ⟨h1, B ++ es, hB', ?_⟩
  have hlen : c ≤ B.length := by
    have := congrArg List.length heq; simp at this; omega
  rw [List.take_append_of_le_length hlen]; exact heq

-- Both depend on `a` only through its first c entries.
theorem LostIn.congr (led : Nat → Option (List (Entry value))) (a a' : List (Entry value))
    (c lo hi : Nat) (heq : a.take c = a'.take c) (h : LostIn led a c lo hi) : LostIn led a' c lo hi := by
  unfold LostIn Lacks at *; rw [← heq]; exact h

theorem Covers.congr (led : Nat → Option (List (Entry value))) (a a' : List (Entry value))
    (c li lt : Nat) (heq : a.take c = a'.take c) (h : Covers led a c li lt) : Covers led a' c li lt := by
  unfold Covers at *; rw [← heq]; exact h

theorem ReqOk.grows (led led' : Nat → Option (List (Entry value))) (u li lt : Nat)
    (hg : LedGrows led led') (h : ReqOk led u li lt) : ReqOk led' u li lt := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  rcases h2 with h2 | ⟨B, hB, hli, ht⟩
  · exact Or.inl h2
  · obtain ⟨es, hB', _⟩ := hg lt B hB
    exact Or.inr ⟨B ++ es, hB', by simp; omega, by rw [termAt_append_left _ _ _ hli]; exact ht⟩

theorem prefix_cmp_of_prefix {α : Type} (a b c : List α) (ha : a <+: c) (hb : b <+: c) :
    a <+: b ∨ b <+: a := by
  rcases Nat.le_total a.length b.length with h | h
  · exact Or.inl (List.prefix_of_prefix_length_le ha hb h)
  · exact Or.inr (List.prefix_of_prefix_length_le hb ha h)

-- Prefixes of two comparable lists are comparable.
theorem prefix_cmp_of_roots {α : Type} (k1 k2 r1 r2 : List α) (h1 : k1 <+: r1) (h2 : k2 <+: r2)
    (h : r1 <+: r2 ∨ r2 <+: r1) : k1 <+: k2 ∨ k2 <+: k1 := by
  rcases h with h | h
  · exact prefix_cmp_of_prefix k1 k2 r2 (h1.trans h) h2
  · exact prefix_cmp_of_prefix k1 k2 r1 h1 (h2.trans h)

-- An index within a prefix reads the same entry in the whole list.
theorem prefix_getD {α : Type} (a l : List α) (d : α) (q : Nat) (h : a <+: l) (hq : q < a.length) :
    a[q]? = some (l[q]?.getD d) := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_left hq, List.getElem?_eq_getElem hq]; rfl

-- Two comparable lists have the same element at an index both have.
theorem prefix_get_eq {α : Type} (a b : List α) (q : Nat) (x y : α) (h : a <+: b ∨ b <+: a)
    (ha : a[q]? = some x) (hb : b[q]? = some y) : x = y := by
  rcases h with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · have hq := (List.getElem?_eq_some_iff.1 ha).1
    rw [List.getElem?_append_left hq, ha] at hb; exact Option.some.inj hb
  · have hq := (List.getElem?_eq_some_iff.1 hb).1
    rw [List.getElem?_append_left hq, hb] at ha; exact (Option.some.inj ha).symm

theorem isPrefix_iff {α : Type} [DecidableEq α] (a b : List α) : IsPrefix a b = true ↔ a <+: b := by
  unfold IsPrefix
  rw [decide_eq_true_iff, subSeq_one]
  constructor
  · rintro ⟨_, h⟩; rw [h]; exact List.take_prefix _ _
  · intro h
    refine ⟨h.length_le, ?_⟩
    obtain ⟨t, rfl⟩ := h
    simp

-- Apply: the entry handed over is the one a committed prefix has at that index.
theorem applied_entry {α : Type} (c l : List α) (d : α) (k : Nat) (hkl : k + 1 ≤ l.length)
    (hkc : k + 1 ≤ c.length) (h : SubSeq c 1 (k + 1) = SubSeq l 1 (k + 1)) :
    c[k]? = some (l[k]?.getD d) := by
  rw [subSeq_one, subSeq_one] at h
  have h1 : (c.take (k + 1))[k]? = (l.take (k + 1))[k]? := by rw [h]
  simp [List.getElem?_take] at h1
  rw [h1, List.getElem?_eq_getElem (by omega)]; rfl

theorem isPrefix_refl {α : Type} [DecidableEq α] (l : List α) : IsPrefix l l = true :=
  (isPrefix_iff l l).2 (List.prefix_refl l)

-- `l` is the start of the list `o` holds; of whatever list `o` holds.
theorem anyPrefix_iff {α : Type} [DecidableEq α] (o : Option (List α)) (l : List α) :
    (o.any fun L => IsPrefix l L) = true ↔ ∃ L, o = some L ∧ l <+: L := by
  cases o <;> simp [isPrefix_iff]

theorem allPrefix_iff {α : Type} [DecidableEq α] (o : Option (List α)) (l : List α) :
    (o.all fun L => IsPrefix l L) = true ↔ ∀ L, o = some L → l <+: L := by
  cases o <;> simp [isPrefix_iff]

-- The two ways a step changes leader logs.
theorem ledGrows_set (led : Nat → Option (List (Entry value))) (cur : Nat) {d : ∀ x : Nat, Decidable (cur = x)} (l : List (Entry value))
    (hsame : ∀ L, led cur = some L → L = l) :
    LedGrows led (fun x => @ite _ (cur = x) (d _) (some l) (led x)) := by
  intro w B hB
  by_cases hc : cur = w
  · subst hc
    refine ⟨[], ?_, by simp⟩
    show (@ite _ (cur = cur) (d _) (some l) (led cur)) = some (B ++ [])
    rw [EtcdRaftVeil.Lemmas.ifPos rfl, hsame B hB]; simp
  · refine ⟨[], ?_, by simp⟩
    show (@ite _ (cur = w) (d _) (some l) (led w)) = some (B ++ [])
    rw [EtcdRaftVeil.Lemmas.ifNeg hc, hB]; simp

theorem ledGrows_append (led : Nat → Option (List (Entry value))) (cur : Nat) {d : ∀ x : Nat, Decidable (cur = x)} (l : List (Entry value))
    (e : Entry value) (hl : led cur = some l) (he : e.term = cur) :
    LedGrows led (fun x => @ite _ (cur = x) (d _) (some (l ++ [e])) (led x)) := by
  intro w B hB
  by_cases hc : cur = w
  · subst hc
    rw [hl] at hB; cases hB
    refine ⟨[e], ?_, by simp [he]⟩
    show (@ite _ (cur = cur) (d _) (some (l ++ [e])) (led cur)) = some (l ++ [e])
    rw [EtcdRaftVeil.Lemmas.ifPos rfl]
  · refine ⟨[], ?_, by simp⟩
    show (@ite _ (cur = w) (d _) (some (l ++ [e])) (led w)) = some (B ++ [])
    rw [EtcdRaftVeil.Lemmas.ifNeg hc, hB]; simp

-- A node's log is one that a vote request can describe.
theorem reqOk_of_log (led : Nat → Option (List (Entry value))) (l : List (Entry value)) (u : Nat)
    (hl : FromLed led l) (hb : TermAt l l.length < u) :
    ReqOk led u l.length (TermAt l l.length) := by
  refine ⟨hb, ?_⟩
  rcases Nat.lt_or_ge 0 l.length with h2 | h1
  · right
    rw [FromLed.iff] at hl
    obtain ⟨L, hL, heq⟩ := hl (l.length - 1) (by omega)
    rw [show l.length - 1 + 1 = l.length by omega] at hL heq
    have hlen : l.length ≤ L.length := by have := congrArg List.length heq; simp at this; omega
    refine ⟨L, hL, hlen, ?_⟩
    have : TermAt (l.take l.length) l.length = TermAt (L.take l.length) l.length := by rw [heq]
    rw [termAt_take _ _ _ (Nat.le_refl _), termAt_take _ _ _ (Nat.le_refl _)] at this
    exact this.symm
  · left
    have h0 : l.length = 0 := by omega
    rw [h0]; exact ⟨rfl, rfl⟩

-- The step of voting: what the voter holds or has lost, the candidate covers or it is lost.
theorem vote_step (led : Nat → Option (List (Entry value))) (ln A : List (Entry value))
    (t c li lt u : Nat)
    (hA : led t = some A) (hc2 : 1 ≤ c) (hcA : c ≤ A.length) (hct : TermAt A c = t)
    (hheld : A.take c <+: ln ∨ LostIn led A c t u)
    (hln : FromLed led ln)
    (hsorted : ∀ w B, led w = some B → Sorted B w)
    (hreq : ReqOk led u li lt)
    (hup : lt > TermAt ln ln.length ∨ (lt = TermAt ln ln.length ∧ li ≥ ln.length)) :
    Covers led A c li lt ∨ LostIn led A c t u := by
  rcases hheld with hheld | hlost
  · rcases vote_cover led ln A t c li lt hA hc2 hcA hct hheld hln hsorted hreq.2 hup with h | ⟨h1, B, hB, hl⟩
    · exact Or.inl h
    · exact Or.inr ⟨lt, h1, Nat.le_of_lt hreq.1, B, hB, hl⟩
  · exact Or.inr hlost

-- A prefix of a log that ends in an entry of term t is a prefix of the leader log of t.
theorem take_prefix_led (led : Nat → Option (List (Entry value))) (l A : List (Entry value)) (t c : Nat)
    (hl : FromLed led l) (hA : led t = some A)
    (hc1 : 1 ≤ c) (hcl : c ≤ l.length) (ht : TermAt l c = t) :
    l.take c <+: A ∧ TermAt A c = t := by
  rw [FromLed.iff] at hl
  obtain ⟨L, hL, heq⟩ := hl (c - 1) (by omega)
  rw [show c - 1 + 1 = c by omega, ht, hA] at hL; cases hL
  rw [show c - 1 + 1 = c by omega] at heq
  refine ⟨by rw [heq]; exact List.take_prefix _ _, ?_⟩
  have : TermAt (l.take c) c = TermAt (A.take c) c := by rw [heq]
  rw [termAt_take _ _ _ (Nat.le_refl c), termAt_take _ _ _ (Nat.le_refl c)] at this
  rw [← this]; exact ht

end LogLemmas

-- Acknowledgements, elections and commits, for the proof of StateMachineSafety.
section Quorums
set_option linter.unusedSectionVars false
variable {server value MS VS LS CS : Type} [DecidableEq value] [DecidableEq server] [Servers server] [TSet (Msg server value) MS]
  [TSet (Vote server) VS] [TSet (Elected server) LS] [TSet (Commit server value) CS]

-- n acknowledged the first c entries of `A`, the term-t leader log, the c-th of term t (the
-- leader too, by a reply to itself).
def Acked (msgs : MS) (leaders : LS) (led : Nat → Option (List (Entry value))) (n : server) (t : Nat)
    (A : List (Entry value)) (c : Nat) : Prop :=
  led t = some A ∧ 1 ≤ c ∧ TermAt A c = t ∧
  ∃ i x, Msg.ack (value := value) n i t x ∈ msgs ∧ c ≤ x

-- n's vote for `cand` in term u was early: what n acknowledged earlier, the candidate's log
-- has, or a leader log strictly between lacks.
def Early (msgs : MS) (leaders : LS) (led : Nat → Option (List (Entry value))) (n cand : server)
    (u : Nat) : Prop :=
  ∀ t A c, Acked msgs leaders led n t A c → t < u →
    ∀ li lt, Msg.vote (value := value) cand u li lt ∈ msgs →
      Covers led A c li lt ∨ LostIn led A c t (u - 1)

-- Who has acknowledged the first c entries in term t (to the leader of t: AckFacts).
noncomputable def ackedBy (msgs : MS) (t c : Nat) : server → Bool :=
  fun n => @decide (∃ i x, Msg.ack (value := value) n i t x ∈ msgs ∧ c ≤ x) (Classical.propDecidable _)

-- The committed prefixes, with the terms they are recorded under.
def Kof (commits : CS) : List (Entry value) → Nat → Prop :=
  fun k tk => ∃ r : Commit server value, r ∈ commits ∧ r.entries = k ∧ r.term = tk

-- A prefix that a leader may commit: not empty, and ending with an entry of the leader's term.
def goodOf (led : Nat → Option (List (Entry value))) : Nat → Nat → Prop :=
  fun t c => 1 ≤ c ∧ ∃ A, led t = some A ∧ TermAt A c = t

-- MemberCore.RootAt, for the model.
def MRoot (iv : server → Bool) (ad rm : value → List server) (jt lv : value → Bool)
    (msgs : MS) (led : Nat → Option (List (Entry value))) (commits : CS)
    (t c d : Nat) (A : List (Entry value)) : Prop :=
  MemberCore.RootAt Entry.isConf (chgOf ad rm jt lv) (conf0 iv) led (Kof commits) (ackedBy msgs) (goodOf led) t c d A

-- A committed prefix that the leader of its term committed.
def Root (iv : server → Bool) (ad rm : value → List server) (jt lv : value → Bool)
    (msgs : MS) (led : Nat → Option (List (Entry value))) (commits : CS)
    (r : Commit server value) : Prop :=
  ∃ d A, MRoot iv ad rm jt lv msgs led commits r.term r.entries.length d A ∧ r.entries <+: A

theorem tmAt_eq (l : List (Entry value)) (p : Nat) : MemberCore.tmAt Entry.term l p = TermAt l p := by
  cases p with
  | zero => rfl
  | succ p => simp only [MemberCore.tmAt, TermAt]; cases l[p]? <;> rfl

theorem ackedBy.mono (msgs msgs' : MS) (t c : Nat) (h : ∀ a : Msg server value, a ∈ msgs → a ∈ msgs') :
    ∀ n, ackedBy msgs t c n = true → ackedBy msgs' t c n = true := by
  intro n hn
  simp only [ackedBy, decide_eq_true_eq] at hn ⊢
  obtain ⟨i, x, hx, hc⟩ := hn
  exact ⟨i, x, h _ hx, hc⟩

theorem isC_append (l es : List (Entry value)) (p : Nat) (h : p ≤ l.length) :
    MemberCore.isC Entry.isConf (l ++ es) p = MemberCore.isC Entry.isConf l p :=
  MemberCore.isC_congr Entry.isConf (l ++ es) l l.length p (by simp) h

-- What a leader committed stays so when facts are added and leader logs grow.
theorem MRoot.mono (iv : server → Bool) (ad rm : value → List server) (jt lv : value → Bool)
    (msgs msgs' : MS) (led led' : Nat → Option (List (Entry value))) (commits commits' : CS)
    (t c d : Nat) (A : List (Entry value))
    (hm : ∀ a : Msg server value, a ∈ msgs → a ∈ msgs')
    (hc : ∀ k : Commit server value, k ∈ commits → k ∈ commits')
    (hg : LedGrows led led')
    (h : MRoot iv ad rm jt lv msgs led commits t c d A) :
    ∃ es, led' t = some (A ++ es) ∧ MRoot iv ad rm jt lv msgs' led' commits' t c d (A ++ es) := by
  obtain ⟨es, hA', _⟩ := hg t A h.isLed
  have hlen := h.len
  -- the first d entries are the same, unless d is 0
  have hd : d = 0 ∨ d ≤ A.length := by
    rcases h.cover with h0 | ⟨k, tk, _, _, hdk, htake⟩
    · exact Or.inl h0
    · have := congrArg List.length htake
      simp at this; exact Or.inr (by omega)
  have htk : (A ++ es).take d = A.take d := by
    rcases hd with h0 | hd
    · subst h0; simp
    · exact List.take_append_of_le_length hd
  refine ⟨es, hA', ⟨hA', by simp; omega, ?_, ?_, ?_, ?_⟩⟩
  · obtain ⟨h1, A0, hA0, ht⟩ := h.isGood
    rw [h.isLed] at hA0; cases hA0
    exact ⟨h1, A ++ es, hA', by rw [termAt_append_left _ _ _ hlen]; exact ht⟩
  · rcases h.cover with h0 | ⟨k, tk, ⟨r, hr, hrk, hrt⟩, htkle, hdk, htake⟩
    · exact Or.inl h0
    · exact Or.inr ⟨k, tk, ⟨r, hc r hr, hrk, hrt⟩, htkle, hdk, by rw [htk]; exact htake⟩
  · intro p q h1 h2 h3 hp hq
    rw [isC_append _ _ _ (by omega)] at hp hq
    exact h.one p q h1 h2 h3 hp hq
  · have hq := h.quorum
    rw [show MemberCore.confOf Entry.isConf (chgOf ad rm jt lv) (conf0 iv) (A ++ es) d =
        MemberCore.confOf Entry.isConf (chgOf ad rm jt lv) (conf0 iv) A d from
      MemberCore.confOf_congr _ _ _ _ _ _ htk]
    exact MemberCore.IsQ.mono _ _ _ (ackedBy.mono msgs msgs' t c hm) hq

theorem Root.mono (iv : server → Bool) (ad rm : value → List server) (jt lv : value → Bool)
    (msgs msgs' : MS) (led led' : Nat → Option (List (Entry value))) (commits commits' : CS)
    (r : Commit server value) (hm : ∀ a : Msg server value, a ∈ msgs → a ∈ msgs')
    (hc : ∀ k : Commit server value, k ∈ commits → k ∈ commits')
    (hg : LedGrows led led')
    (h : Root iv ad rm jt lv msgs led commits r) : Root iv ad rm jt lv msgs' led' commits' r := by
  obtain ⟨d, A, hr, hp⟩ := h
  obtain ⟨es, _, hr'⟩ := MRoot.mono iv ad rm jt lv msgs msgs' led led' commits commits' _ _ d A hm hc hg hr
  exact ⟨d, A ++ es, hr', hp.trans (List.prefix_append _ _)⟩

-- FirstRoot, for one committed prefix, when facts are added and leader logs grow.
theorem firstRoot_mono (iv : server → Bool) (ad rm : value → List server) (jt lv : value → Bool)
    (msgs msgs' : MS) (led led' : Nat → Option (List (Entry value))) (commits commits' : CS)
    (kt p : Nat)
    (hm : ∀ a : Msg server value, a ∈ msgs → a ∈ msgs')
    (hc : ∀ k : Commit server value, k ∈ commits → k ∈ commits')
    (hg : LedGrows led led')
    (h : ∃ r : Commit server value, r.term ≤ kt ∧ p ≤ r.entries.length ∧ r ∈ commits ∧
      ∃ d, d < p ∧ ∃ A, MRoot iv ad rm jt lv msgs led commits r.term r.entries.length d A ∧ r.entries <+: A) :
    ∃ r : Commit server value, r.term ≤ kt ∧ p ≤ r.entries.length ∧ r ∈ commits' ∧
      ∃ d, d < p ∧ ∃ A, MRoot iv ad rm jt lv msgs' led' commits' r.term r.entries.length d A ∧ r.entries <+: A := by
  obtain ⟨r, h1, h2, h3, d, h4, A, h5, h6⟩ := h
  obtain ⟨es, _, hr'⟩ := MRoot.mono iv ad rm jt lv msgs msgs' led led' commits commits' _ _ d A hm hc hg h5
  exact ⟨r, h1, h2, hc r h3, d, h4, A ++ es, hr', h6.trans (List.prefix_append _ _)⟩

-- What MemberCore.core asks of a state, from the invariants.
theorem world (iv : server → Bool) (ad rm : value → List server) (jt lv : value → Bool)
    (msgs : MS) (led : Nat → Option (List (Entry value))) (commits : CS)
    (hCS : ∀ a b : Commit server value, a ∈ commits → b ∈ commits →
      a.entries <+: b.entries ∨ b.entries <+: a.entries)
    (hFirst : ∀ k : Commit server value, k ∈ commits → ∀ p, MemberCore.isC Entry.isConf k.entries p = true →
      ∃ r : Commit server value, r ∈ commits ∧ r.term ≤ k.term ∧ p ≤ r.entries.length ∧
        ∃ d A, d < p ∧ MRoot iv ad rm jt lv msgs led commits r.term r.entries.length d A ∧ r.entries <+: A)
    (hLegal : ∀ t A, led t = some A → ∀ p e, A[p]? = some e → e.isConf = true →
      MemberCore.Legal (cOf iv ad rm jt lv A p) (chgOf ad rm jt lv e))
    (hLS : ∀ t L, led t = some L → Sorted L t) :
    MemberCore.World Entry.term Entry.isConf (chgOf ad rm jt lv) (conf0 iv) led (Kof commits)
      (ackedBy msgs) (goodOf led) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro k1 t1 k2 t2 ⟨r1, h1, rfl, rfl⟩ ⟨r2, h2, rfl, rfl⟩
    exact hCS r1 r2 h1 h2
  · rintro k tk ⟨r0, h0, rfl, rfl⟩ p hp
    obtain ⟨r, hr, hrt, hpl, d, A, hd, hroot, hpre⟩ := hFirst r0 h0 p hp
    refine ⟨r.term, r.entries.length, d, A, hroot, ⟨r, hr, ?_, rfl⟩, hrt, hpl, hd⟩
    obtain ⟨s, rfl⟩ := hpre; simp
  · intro t A hA p e hp he
    exact hLegal t A hA p e hp he
  · intro t A hA p _
    rw [tmAt_eq]; exact (hLS t A hA).2 p

-- A fact that is not an acknowledgement changes nothing about what is acknowledged.
theorem Acked.of_insert (msgs : MS) (leaders : LS) (led : Nat → Option (List (Entry value)))
    (m : Msg server value) (n : server) (t : Nat) (A : List (Entry value)) (c : Nat)
    (hm : ∀ j i t x, m ≠ Msg.ack j i t x)
    (h : Acked (TSet.insert m msgs) leaders led n t A c) : Acked msgs leaders led n t A c := by
  obtain ⟨h1, h2, h3, i, x, hx, hc⟩ := h
  refine ⟨h1, h2, h3, ?_⟩
  rw [EtcdRaftVeil.Lemmas.mem_insert] at hx
  rcases hx with hx | hx
  · exact absurd hx.symm (hm _ _ _ _)
  · exact ⟨i, x, hx, hc⟩

-- A new acknowledgement adds what it says, for its sender.
theorem Acked.of_insert_ack (msgs : MS) (leaders : LS) (led : Nat → Option (List (Entry value)))
    (j i0 : server) (t0 x0 : Nat) (n : server) (t : Nat) (A : List (Entry value)) (c : Nat)
    (h : Acked (TSet.insert (Msg.ack j i0 t0 x0) msgs) leaders led n t A c) :
    Acked msgs leaders led n t A c ∨ (n = j ∧ t = t0 ∧ c ≤ x0 ∧ led t = some A ∧ 1 ≤ c ∧ TermAt A c = t) := by
  obtain ⟨h1, h2, h3, i, x, hx, hc⟩ := h
  rw [EtcdRaftVeil.Lemmas.mem_insert] at hx
  rcases hx with hx | hx
  · cases hx; exact Or.inr ⟨rfl, rfl, hc, h1, h2, h3⟩
  · exact Or.inl ⟨h1, h2, h3, i, x, hx, hc⟩

-- Leaders are not part of what is acknowledged.
theorem Acked.leaders (msgs : MS) (leaders leaders' : LS) (led : Nat → Option (List (Entry value)))
    (n : server) (t : Nat) (A : List (Entry value)) (c : Nat)
    (h : Acked msgs leaders led n t A c) : Acked msgs leaders' led n t A c := h

theorem Early.of_insert (msgs : MS) (leaders : LS) (led : Nat → Option (List (Entry value)))
    (m : Msg server value) (n cand : server) (u : Nat)
    (hm : ∀ j i t x, m ≠ Msg.ack j i t x) (hv : ∀ li lt, m ≠ Msg.vote cand u li lt)
    (h : Early msgs leaders led n cand u) : Early (TSet.insert m msgs) leaders led n cand u := by
  intro t A c ha htu li lt hr
  rw [EtcdRaftVeil.Lemmas.mem_insert] at hr
  rcases hr with hr | hr
  · exact absurd hr.symm (hv _ _)
  · exact h t A c (Acked.of_insert _ _ _ _ _ _ _ _ hm ha) htu li lt hr

-- Leader completeness from the invariants: what a leader committed is in every later leader log.
theorem leader_complete (iv : server → Bool) (ad rm : value → List server) (jt lv : value → Bool)
    (msgs : MS) (leaders : LS) (votes : VS)
    (led : Nat → Option (List (Entry value))) (commits : CS) (elAt : Nat → Nat)
    (hW : MemberCore.World Entry.term Entry.isConf (chgOf ad rm jt lv) (conf0 iv) led (Kof commits)
      (ackedBy msgs) (goodOf led))
    (hEQ : ∀ ld : Elected server, ld ∈ leaders → ∀ B, led ld.term = some B →
      MemberCore.IsQ (fun n => @decide (
        TSet.contains ({ voter := n, term := ld.term, cand := ld.server } : Vote server) votes = true ∧
        Early msgs leaders led n ld.server ld.term) (Classical.propDecidable _))
        (cOf iv ad rm jt lv B (elAt ld.term)))
    (hElC : ∀ u B, led u = some B → elAt u = 0 ∨ ∃ k tk, Kof commits k tk ∧ tk < u ∧
      elAt u ≤ k.length ∧ k.take (elAt u) = B.take (elAt u))
    (hOld : ∀ u B, led u = some B → ∀ p q, elAt u < p → p < q →
      MemberCore.isC Entry.isConf B p = true → MemberCore.isC Entry.isConf B q = true →
      TermAt B p < u → TermAt B q < u → False)
    (hLHas : ∀ t : Nat, ¬ led t = none → ∃ a : Elected server, a ∈ leaders ∧ a.term = t)
    (hVHR : ∀ v : Vote server, v ∈ votes →
      ∃ m : Msg server value, m ∈ msgs ∧ ∃ li lt, m = Msg.vote v.cand v.term li lt)
    (hLER : ∀ ld : Elected server, ld ∈ leaders → ∀ m : Msg server value, m ∈ msgs → ∀ li lt : Nat,
      m = Msg.vote ld.server ld.term li lt → ∀ L : List (Entry value), led ld.term = some L →
        li ≤ L.length ∧ TermAt L li = lt)
    (hLedFL : ∀ t L, led t = some L → FromLed led L) :
    ∀ u t c d A, MRoot iv ad rm jt lv msgs led commits t c d A → t < u →
      ∀ B, led u = some B → A.take c <+: B := by
  intro u
  induction u using Nat.strongRecOn with
  | ind u ih =>
    intro t c d A hr htu B hB
    obtain ⟨ld, hld, hldt⟩ := hLHas u (by rw [hB]; exact Option.some_ne_none B)
    subst hldt
    refine MemberCore.core hW (V := fun n => @decide (
        TSet.contains ({ voter := n, term := ld.term, cand := ld.server } : Vote server) votes = true ∧
        Early msgs leaders led n ld.server ld.term) (Classical.propDecidable _)) (e := elAt ld.term)
      ⟨hElC _ B hB, ?_, hEQ ld hld B hB, ?_, fun p e' hp he => hW.legal _ B hB p e' hp he,
        fun w hw t c d A hr htw Bw hBw => ih w hw t c d A hr htw Bw hBw⟩ t c d A hr htu
    · intro p q h1 h2 hp hq ht1 ht2
      rw [tmAt_eq] at ht1 ht2
      exact hOld _ B hB p q h1 h2 hp hq ht1 ht2
    · intro n hn t c A hA hgood hcA hack htu
      simp only [decide_eq_true_eq] at hn
      obtain ⟨hvote, hearly⟩ := hn
      simp only [ackedBy, decide_eq_true_eq] at hack
      obtain ⟨i, x, hx, hcx⟩ := hack
      obtain ⟨hc1, A0, hA0, hct⟩ := hgood
      rw [hA] at hA0; cases hA0
      have hacked : Acked msgs leaders led n t A c := ⟨hA, hc1, hct, i, x, hx, hcx⟩
      obtain ⟨m, hm, li, lt, rfl⟩ := hVHR _ hvote
      rcases hearly t A c hacked htu li lt hm with ⟨hcli, B', hB', heq⟩ | ⟨w, htw, hwu, B2, hB2, hlack⟩
      · left
        obtain ⟨hliB, hBt⟩ := hLER ld hld _ hm li lt rfl B hB
        have hfl := hLedFL _ B hB
        rw [FromLed.iff] at hfl
        obtain ⟨L2, hL2, hBL2⟩ := hfl (li - 1) (by omega)
        rw [show li - 1 + 1 = li by omega, hBt, hB'] at hL2
        cases hL2
        rw [show li - 1 + 1 = li by omega] at hBL2
        rw [take_prefix_iff _ _ _ hcA]
        refine ⟨by omega, ?_⟩
        have : (B.take li).take c = (B'.take li).take c := by rw [hBL2]
        rw [List.take_take, List.take_take, Nat.min_eq_left hcli] at this
        rw [heq, this]
      · exact Or.inr ⟨w, B2, htw, by omega, hB2, hlack⟩

-- The same for a candidate elected by a quorum, before its term has a leader log.
theorem cand_complete (iv : server → Bool) (ad rm : value → List server) (jt lv : value → Bool)
    (msgs : MS) (leaders : LS) (votes : VS)
    (led : Nat → Option (List (Entry value))) (commits : CS) (elAt : Nat → Nat)
    (hW : MemberCore.World Entry.term Entry.isConf (chgOf ad rm jt lv) (conf0 iv) led (Kof commits)
      (ackedBy msgs) (goodOf led))
    (hEQ : ∀ ld : Elected server, ld ∈ leaders → ∀ B, led ld.term = some B →
      MemberCore.IsQ (fun n => @decide (
        TSet.contains ({ voter := n, term := ld.term, cand := ld.server } : Vote server) votes = true ∧
        Early msgs leaders led n ld.server ld.term) (Classical.propDecidable _))
        (cOf iv ad rm jt lv B (elAt ld.term)))
    (hElC : ∀ u B, led u = some B → elAt u = 0 ∨ ∃ k tk, Kof commits k tk ∧ tk < u ∧
      elAt u ≤ k.length ∧ k.take (elAt u) = B.take (elAt u))
    (hOld : ∀ u B, led u = some B → ∀ p q, elAt u < p → p < q →
      MemberCore.isC Entry.isConf B p = true → MemberCore.isC Entry.isConf B q = true →
      TermAt B p < u → TermAt B q < u → False)
    (hLHas : ∀ t : Nat, ¬ led t = none → ∃ a : Elected server, a ∈ leaders ∧ a.term = t)
    (hVHR : ∀ v : Vote server, v ∈ votes →
      ∃ m : Msg server value, m ∈ msgs ∧ ∃ li lt, m = Msg.vote v.cand v.term li lt)
    (hLER : ∀ ld : Elected server, ld ∈ leaders → ∀ m : Msg server value, m ∈ msgs → ∀ li lt : Nat,
      m = Msg.vote ld.server ld.term li lt → ∀ L : List (Entry value), led ld.term = some L →
        li ≤ L.length ∧ TermAt L li = lt)
    (hLedFL : ∀ t L, led t = some L → FromLed led L)
    (i : server) (cur e : Nat) (l : List (Entry value)) (V : server → Bool)
    (hV : ∀ n, V n = true → TSet.contains ({ voter := n, term := cur, cand := i } : Vote server) votes = true)
    (hAV : ∀ n t A c, Acked msgs leaders led n t A c →
      TSet.contains ({ voter := n, term := cur, cand := i } : Vote server) votes = true → t < cur →
      ∀ li lt, Msg.vote (value := value) i cur li lt ∈ msgs →
        Covers led A c li lt ∨ LostIn led A c t cur)
    (hnone : led cur = none)
    (hq : MemberCore.IsQ V (cOf iv ad rm jt lv l e))
    (hCL : ∀ li lt, Msg.vote (value := value) i cur li lt ∈ msgs → l.length = li ∧ TermAt l li = lt)
    (hl : FromLed led l)
    (hcov : e = 0 ∨ ∃ k tk, Kof commits k tk ∧ tk < cur ∧ e ≤ k.length ∧ k.take e = l.take e)
    (hone : ∀ p q, e < p → p < q → MemberCore.isC Entry.isConf l p = true →
      MemberCore.isC Entry.isConf l q = true → False) :
    ∀ t c d A, MRoot iv ad rm jt lv msgs led commits t c d A → t < cur → A.take c <+: l := by
  have hLC := leader_complete iv ad rm jt lv msgs leaders votes led commits elAt hW hEQ hElC hOld hLHas hVHR hLER hLedFL
  refine MemberCore.core hW (V := V) (e := e)
    ⟨hcov, fun p q h1 h2 hp hq _ _ => hone p q h1 h2 hp hq, hq, ?_, ?_,
      fun w _ t c d A hr htw Bw hBw => hLC w t c d A hr htw Bw hBw⟩
  · intro n hn t c A hA hgood hcA hack htu
    have hvote := hV n hn
    simp only [ackedBy, decide_eq_true_eq] at hack
    obtain ⟨i', x, hx, hcx⟩ := hack
    obtain ⟨hc1, A0, hA0, hct⟩ := hgood
    rw [hA] at hA0; cases hA0
    have hacked : Acked msgs leaders led n t A c := ⟨hA, hc1, hct, i', x, hx, hcx⟩
    obtain ⟨m, hm, li, lt, rfl⟩ := hVHR _ hvote
    rcases hAV n t A c hacked hvote htu li lt hm with ⟨hcli, B', hB', heq⟩ | ⟨w, htw, hwu, B2, hB2, hlack⟩
    · left
      obtain ⟨hlen, hlast⟩ := hCL li lt hm
      obtain ⟨hpre, -⟩ := take_prefix_led led l B' lt li hl hB' (by omega) (by omega) hlast
      rw [take_prefix_iff _ _ _ (by omega)] at hpre
      have h2 : (l.take li).take c = (B'.take li).take c := by rw [hpre.2]
      rw [List.take_take, List.take_take, Nat.min_eq_left hcli] at h2
      rw [heq, ← h2]; exact List.take_prefix _ _
    · rcases Nat.eq_or_lt_of_le hwu with hw | hw
      · rw [hw, hnone] at hB2; cases hB2
      · exact Or.inr ⟨w, B2, htw, hw, hB2, hlack⟩
  · -- a change in the candidate's log is in the leader log of its term, where it is legal
    intro p e' hp he
    have hpl : p < l.length := (List.getElem?_eq_some_iff.1 hp).1
    rw [FromLed.iff] at hl
    obtain ⟨L, hL, heq⟩ := hl p hpl
    have hLp : L[p]? = some e' := by
      have : (l.take (p + 1))[p]? = (L.take (p + 1))[p]? := by rw [heq]
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_take_of_lt (by omega)] at this
      rw [← this]; exact hp
    have hc : MemberCore.confOf Entry.isConf (chgOf ad rm jt lv) (conf0 iv) l p =
        MemberCore.confOf Entry.isConf (chgOf ad rm jt lv) (conf0 iv) L p :=
      MemberCore.confOf_congr _ _ _ _ _ _ (MemberCore.take_take_eq _ _ (p + 1) p heq (by omega))
    rw [hc]
    exact hW.legal _ L hL p e' hLp he

-- The same, from the invariants as the proof goals state them.
theorem world_inv (iv : server → Bool) (ad rm : value → List server) (jt lv : value → Bool)
    (msgs : MS) (led : Nat → Option (List (Entry value))) (commits : CS)
    (hSMS : ∀ a b : Commit server value, a ∈ commits → b ∈ commits →
      IsPrefix a.entries b.entries = true ∨ IsPrefix b.entries a.entries = true)
    (hFR : ∀ a : Commit server value, a ∈ commits → ∀ p, MemberCore.isC Entry.isConf a.entries p = true →
      ∃ r : Commit server value, r.term ≤ a.term ∧ p ≤ r.entries.length ∧ r ∈ commits ∧
        ∃ d, d < p ∧ ∃ x, MRoot iv ad rm jt lv msgs led commits r.term r.entries.length d x ∧ r.entries <+: x)
    (hLG : ∀ (e : Entry value) (t : Nat) (A : List (Entry value)), led t = some A → ∀ p : Nat,
      A[p]? = some e → e.isConf = true →
      MemberCore.Legal (cOf iv ad rm jt lv A p) (chgOf ad rm jt lv e))
    (hLS : ∀ t L, led t = some L → Sorted L t) :
    MemberCore.World Entry.term Entry.isConf (chgOf ad rm jt lv) (conf0 iv) led (Kof commits)
      (ackedBy msgs) (goodOf led) := by
  refine world iv ad rm jt lv msgs led commits ?_ ?_ (fun t A hA p e hp he => hLG e t A hA p hp he) hLS
  · intro a b ha hb
    have := hSMS a b ha hb
    rw [isPrefix_iff, isPrefix_iff] at this
    exact this
  · intro k hk p hp
    obtain ⟨r, h1, h2, h3, d, h4, A, h5, h6⟩ := hFR k hk p hp
    exact ⟨r, h3, h1, h2, d, A, h4, h5, h6⟩

-- A leader-committed prefix is in the leader log of its term and every later term.
theorem root_in_later (iv : server → Bool) (ad rm : value → List server) (jt lv : value → Bool)
    (msgs : MS) (leaders : LS) (votes : VS)
    (led : Nat → Option (List (Entry value))) (commits : CS) (ledAt elAt : Nat → Nat)
    (lIn lOut : Nat → server → Bool)
    (hSMS : ∀ a b : Commit server value, a ∈ commits → b ∈ commits →
      IsPrefix a.entries b.entries = true ∨ IsPrefix b.entries a.entries = true)
    (hFR : ∀ a : Commit server value, a ∈ commits → ∀ p, MemberCore.isC Entry.isConf a.entries p = true →
      ∃ r : Commit server value, r.term ≤ a.term ∧ p ≤ r.entries.length ∧ r ∈ commits ∧
        ∃ d, d < p ∧ ∃ x, MRoot iv ad rm jt lv msgs led commits r.term r.entries.length d x ∧ r.entries <+: x)
    (hLG : ∀ (e : Entry value) (t : Nat) (A : List (Entry value)), led t = some A → ∀ p : Nat,
      A[p]? = some e → e.isConf = true →
      MemberCore.Legal (cOf iv ad rm jt lv A p) (chgOf ad rm jt lv e))
    (hLS : ∀ t L, led t = some L → Sorted L t)
    (hEQ : ∀ (a : Elected server) (_ : a ∈ leaders) (B : List (Entry value)), led a.term = some B →
      MemberCore.IsQ (fun n => @decide (
        TSet.contains ({ voter := n, term := a.term, cand := a.server } : Vote server) votes = true ∧
        Early msgs leaders led n a.server a.term) (Classical.propDecidable _))
        (cOf iv ad rm jt lv B (elAt a.term)))
    (hLCf : ∀ (t : Nat) (A : List (Entry value)), led t = some A →
      ledAt t ≤ A.length ∧ elAt t ≤ ledAt t ∧
      (∀ s : server, lIn t s = (cOf iv ad rm jt lv A (ledAt t)).inn s ∧ lOut t s = (cOf iv ad rm jt lv A (ledAt t)).out s) ∧
      MemberCore.AtMostOne Entry.isConf A (ledAt t) A.length ∧
      (ledAt t = 0 ∨ ∃ k tk, Kof commits k tk ∧ tk ≤ t ∧ ledAt t ≤ k.length ∧ k.take (ledAt t) = A.take (ledAt t)) ∧
      (elAt t = 0 ∨ ∃ k tk, Kof commits k tk ∧ tk < t ∧ elAt t ≤ k.length ∧ k.take (elAt t) = A.take (elAt t)))
    (hLOld : ∀ (u : Nat) (B : List (Entry value)), led u = some B → ∀ p q : Nat, elAt u < p → p < q →
      MemberCore.isC Entry.isConf B p = true → MemberCore.isC Entry.isConf B q = true →
      TermAt B p < u → u ≤ TermAt B q)
    (hLHas : ∀ t : Nat, ¬ led t = none → ∃ a : Elected server, a ∈ leaders ∧ a.term = t)
    (hVHR : ∀ v : Vote server, v ∈ votes →
      ∃ m : Msg server value, m ∈ msgs ∧ ∃ li lt, m = Msg.vote v.cand v.term li lt)
    (hLER : ∀ ld : Elected server, ld ∈ leaders → ∀ m : Msg server value, m ∈ msgs → ∀ li lt : Nat,
      m = Msg.vote ld.server ld.term li lt → ∀ L : List (Entry value), led ld.term = some L →
        li ≤ L.length ∧ TermAt L li = lt)
    (hLedFL : ∀ t L, led t = some L → FromLed led L)
    (r : Commit server value) (hr : Root iv ad rm jt lv msgs led commits r) (u : Nat) (hu : r.term ≤ u)
    (B : List (Entry value)) (hB : led u = some B) : r.entries <+: B := by
  obtain ⟨d, A, hroot, hpre⟩ := hr
  have hrA : r.entries = A.take r.entries.length := by
    obtain ⟨s, rfl⟩ := hpre; simp
  rcases Nat.eq_or_lt_of_le hu with heq | hlt
  · have := hroot.isLed
    rw [heq, hB] at this; cases this; exact hpre
  · rw [hrA]
    exact leader_complete iv ad rm jt lv msgs leaders votes led commits elAt
      (world_inv iv ad rm jt lv msgs led commits hSMS hFR hLG hLS)
      hEQ (fun u B hB => (hLCf u B hB).2.2.2.2.2)
      (fun u B hB p q h1 h2 hp hq ht1 ht2 => by have := hLOld u B hB p q h1 h2 hp hq ht1; omega)
      hLHas hVHR hLER hLedFL
      u r.term r.entries.length d A hroot hlt B hB

-- Two committed prefixes that leaders committed are comparable.
theorem roots_cmp (iv : server → Bool) (ad rm : value → List server) (jt lv : value → Bool)
    (msgs : MS) (leaders : LS) (votes : VS)
    (led : Nat → Option (List (Entry value))) (commits : CS) (ledAt elAt : Nat → Nat)
    (lIn lOut : Nat → server → Bool)
    (hSMS : ∀ a b : Commit server value, a ∈ commits → b ∈ commits →
      IsPrefix a.entries b.entries = true ∨ IsPrefix b.entries a.entries = true)
    (hFR : ∀ a : Commit server value, a ∈ commits → ∀ p, MemberCore.isC Entry.isConf a.entries p = true →
      ∃ r : Commit server value, r.term ≤ a.term ∧ p ≤ r.entries.length ∧ r ∈ commits ∧
        ∃ d, d < p ∧ ∃ x, MRoot iv ad rm jt lv msgs led commits r.term r.entries.length d x ∧ r.entries <+: x)
    (hLG : ∀ (e : Entry value) (t : Nat) (A : List (Entry value)), led t = some A → ∀ p : Nat,
      A[p]? = some e → e.isConf = true →
      MemberCore.Legal (cOf iv ad rm jt lv A p) (chgOf ad rm jt lv e))
    (hLS : ∀ t L, led t = some L → Sorted L t)
    (hEQ : ∀ (a : Elected server) (_ : a ∈ leaders) (B : List (Entry value)), led a.term = some B →
      MemberCore.IsQ (fun n => @decide (
        TSet.contains ({ voter := n, term := a.term, cand := a.server } : Vote server) votes = true ∧
        Early msgs leaders led n a.server a.term) (Classical.propDecidable _))
        (cOf iv ad rm jt lv B (elAt a.term)))
    (hLCf : ∀ (t : Nat) (A : List (Entry value)), led t = some A →
      ledAt t ≤ A.length ∧ elAt t ≤ ledAt t ∧
      (∀ s : server, lIn t s = (cOf iv ad rm jt lv A (ledAt t)).inn s ∧ lOut t s = (cOf iv ad rm jt lv A (ledAt t)).out s) ∧
      MemberCore.AtMostOne Entry.isConf A (ledAt t) A.length ∧
      (ledAt t = 0 ∨ ∃ k tk, Kof commits k tk ∧ tk ≤ t ∧ ledAt t ≤ k.length ∧ k.take (ledAt t) = A.take (ledAt t)) ∧
      (elAt t = 0 ∨ ∃ k tk, Kof commits k tk ∧ tk < t ∧ elAt t ≤ k.length ∧ k.take (elAt t) = A.take (elAt t)))
    (hLOld : ∀ (u : Nat) (B : List (Entry value)), led u = some B → ∀ p q : Nat, elAt u < p → p < q →
      MemberCore.isC Entry.isConf B p = true → MemberCore.isC Entry.isConf B q = true →
      TermAt B p < u → u ≤ TermAt B q)
    (hLHas : ∀ t : Nat, ¬ led t = none → ∃ a : Elected server, a ∈ leaders ∧ a.term = t)
    (hVHR : ∀ v : Vote server, v ∈ votes →
      ∃ m : Msg server value, m ∈ msgs ∧ ∃ li lt, m = Msg.vote v.cand v.term li lt)
    (hLER : ∀ ld : Elected server, ld ∈ leaders → ∀ m : Msg server value, m ∈ msgs → ∀ li lt : Nat,
      m = Msg.vote ld.server ld.term li lt → ∀ L : List (Entry value), led ld.term = some L →
        li ≤ L.length ∧ TermAt L li = lt)
    (hLedFL : ∀ t L, led t = some L → FromLed led L)
    (r1 r2 : Commit server value) (h1 : Root iv ad rm jt lv msgs led commits r1)
    (h2 : Root iv ad rm jt lv msgs led commits r2) :
    r1.entries <+: r2.entries ∨ r2.entries <+: r1.entries := by
  have key : ∀ a b : Commit server value, Root iv ad rm jt lv msgs led commits a →
      Root iv ad rm jt lv msgs led commits b → a.term ≤ b.term →
      a.entries <+: b.entries ∨ b.entries <+: a.entries := by
    intro a b ha hb hle
    obtain ⟨d, B, hrootb, hpb⟩ := hb
    have := root_in_later iv ad rm jt lv msgs leaders votes led commits ledAt elAt lIn lOut hSMS hFR hLG hLS
      hEQ hLCf hLOld hLHas hVHR hLER hLedFL a ha b.term hle B hrootb.isLed
    exact prefix_cmp_of_prefix _ _ B this hpb
  rcases Nat.le_total r1.term r2.term with h | h
  · exact key r1 r2 h1 h2 h
  · exact (key r2 r1 h2 h1 h).symm

theorem conf_ext (C D : MemberCore.Conf server) (h : ∀ s, C.inn s = D.inn s ∧ C.out s = D.out s) : C = D := by
  cases C; cases D
  simp only [MemberCore.Conf.mk.injEq]
  exact ⟨funext fun s => (h s).1, funext fun s => (h s).2⟩

-- ReadConfirm: a prefix a leader had committed at ReadRequest was committed at ≤ the reader's
-- term, given a quorum of the reader's configuration had acknowledged nothing later.
theorem read_safe (iv : server → Bool) (ad rm : value → List server) (jt lv : value → Bool)
    (msgs : MS) (leaders : LS) (votes : VS)
    (led : Nat → Option (List (Entry value))) (commits : CS) (ledAt elAt : Nat → Nat)
    (lIn lOut : Nat → server → Bool)
    (hSMS : ∀ a b : Commit server value, a ∈ commits → b ∈ commits →
      IsPrefix a.entries b.entries = true ∨ IsPrefix b.entries a.entries = true)
    (hFR : ∀ a : Commit server value, a ∈ commits → ∀ p, MemberCore.isC Entry.isConf a.entries p = true →
      ∃ r : Commit server value, r.term ≤ a.term ∧ p ≤ r.entries.length ∧ r ∈ commits ∧
        ∃ d, d < p ∧ ∃ x, MRoot iv ad rm jt lv msgs led commits r.term r.entries.length d x ∧ r.entries <+: x)
    (hLG : ∀ (e : Entry value) (t : Nat) (A : List (Entry value)), led t = some A → ∀ p : Nat,
      A[p]? = some e → e.isConf = true →
      MemberCore.Legal (cOf iv ad rm jt lv A p) (chgOf ad rm jt lv e))
    (hLS : ∀ t L, led t = some L → Sorted L t)
    (hEQ : ∀ (a : Elected server) (_ : a ∈ leaders) (B : List (Entry value)), led a.term = some B →
      MemberCore.IsQ (fun n => @decide (
        TSet.contains ({ voter := n, term := a.term, cand := a.server } : Vote server) votes = true ∧
        Early msgs leaders led n a.server a.term) (Classical.propDecidable _))
        (cOf iv ad rm jt lv B (elAt a.term)))
    (hLCf : ∀ (t : Nat) (A : List (Entry value)), led t = some A →
      ledAt t ≤ A.length ∧ elAt t ≤ ledAt t ∧
      (∀ s : server, lIn t s = (cOf iv ad rm jt lv A (ledAt t)).inn s ∧ lOut t s = (cOf iv ad rm jt lv A (ledAt t)).out s) ∧
      MemberCore.AtMostOne Entry.isConf A (ledAt t) A.length ∧
      (ledAt t = 0 ∨ ∃ k tk, Kof commits k tk ∧ tk ≤ t ∧ ledAt t ≤ k.length ∧ k.take (ledAt t) = A.take (ledAt t)) ∧
      (elAt t = 0 ∨ ∃ k tk, Kof commits k tk ∧ tk < t ∧ elAt t ≤ k.length ∧ k.take (elAt t) = A.take (elAt t)))
    (hLOld : ∀ (u : Nat) (B : List (Entry value)), led u = some B → ∀ p q : Nat, elAt u < p → p < q →
      MemberCore.isC Entry.isConf B p = true → MemberCore.isC Entry.isConf B q = true →
      TermAt B p < u → u ≤ TermAt B q)
    (hLHas : ∀ t : Nat, ¬ led t = none → ∃ a : Elected server, a ∈ leaders ∧ a.term = t)
    (hVHR : ∀ v : Vote server, v ∈ votes →
      ∃ m : Msg server value, m ∈ msgs ∧ ∃ li lt, m = Msg.vote v.cand v.term li lt)
    (hLER : ∀ ld : Elected server, ld ∈ leaders → ∀ m : Msg server value, m ∈ msgs → ∀ li lt : Nat,
      m = Msg.vote ld.server ld.term li lt → ∀ L : List (Entry value), led ld.term = some L →
        li ≤ L.length ∧ TermAt L li = lt)
    (hLedFL : ∀ t L, led t = some L → FromLed led L)
    (hCR : ∀ k : Commit server value, k ∈ commits → ∃ r : Commit server value, r ∈ commits ∧
      k.entries <+: r.entries ∧ Root iv ad rm jt lv msgs led commits r ∧ r.term ≤ k.term)
    (readMsgs : MS) (readFloor : CS)
    (hMO : ∀ a : Msg server value, a ∈ readMsgs → a ∈ msgs)
    (hFO : ∀ k : Commit server value, k ∈ readFloor → k ∈ commits)
    (hRFR : ∀ a : Commit server value, a ∈ readFloor → ∀ p, MemberCore.isC Entry.isConf a.entries p = true →
      ∃ r : Commit server value, r.term ≤ a.term ∧ p ≤ r.entries.length ∧ r ∈ readFloor ∧
        ∃ d, d < p ∧ ∃ x, MRoot iv ad rm jt lv readMsgs led readFloor r.term r.entries.length d x ∧ r.entries <+: x)
    (T : Nat) (AT : List (Entry value)) (hAT : led T = some AT) (R : server → Bool)
    (hq : MemberCore.IsQ R { inn := lIn T, out := lOut T })
    (hR : ∀ n, R n = true → ∀ i t x, Msg.ack (value := value) n i t x ∈ readMsgs → t ≤ T)
    (r : Commit server value) (hr : Root iv ad rm jt lv readMsgs led readFloor r) : r.term ≤ T := by
  obtain ⟨d, A, hroot, _⟩ := hr
  have hW := world_inv iv ad rm jt lv msgs led commits hSMS hFR hLG hLS
  have hLC := leader_complete iv ad rm jt lv msgs leaders votes led commits elAt hW
      hEQ (fun u B hB => (hLCf u B hB).2.2.2.2.2)
      (fun u B hB p q h1 h2 hp hq ht1 ht2 => by have := hLOld u B hB p q h1 h2 hp hq ht1; omega)
      hLHas hVHR hLER hLedFL
  obtain ⟨_, _, h3, h4, h5, _⟩ := hLCf T AT hAT
  have he : ({ inn := lIn T, out := lOut T } : MemberCore.Conf server) = cOf iv ad rm jt lv AT (ledAt T) :=
    conf_ext _ _ h3
  rw [he] at hq
  refine MemberCore.read_core (Kof readFloor) (ackedBy readMsgs) hW ?_ ?_ ?_ ?_ ?_ ?_ T (ledAt T) AT R hAT h5 h4 hq ?_
    r.term r.entries.length d A hroot
  · rintro k t ⟨c, hc, e1, e2⟩
    exact ⟨c, hFO c hc, e1, e2⟩
  · exact fun t c => ackedBy.mono readMsgs msgs t c hMO
  · rintro k tk ⟨r0, h0, rfl, rfl⟩ p hp
    obtain ⟨r1, h1, h2, h3, d1, h4, A1, h5, h6⟩ := hRFR r0 h0 p hp
    refine ⟨r1.term, r1.entries.length, d1, A1, h5, ⟨r1, h3, ?_, rfl⟩, h1, h2, h4⟩
    obtain ⟨s, rfl⟩ := h6; simp
  · intro t c d A hr u htu B hB
    exact hLC u t c d A hr htu B hB
  · rintro k tk ⟨r0, h0, rfl, rfl⟩
    obtain ⟨r1, _, hpre, ⟨d1, A1, hroot1, hpre1⟩, hle⟩ := hCR r0 h0
    refine ⟨r1.term, r1.entries.length, d1, A1, hroot1, hle, ?_⟩
    obtain ⟨s, rfl⟩ := hpre1
    simpa using hpre
  · rintro t c A ⟨_, A', hA', h⟩ hA
    rw [hA] at hA'; cases hA'
    rw [tmAt_eq]; exact h
  · intro n hn t c htc
    cases h : ackedBy readMsgs t c n with
    | false => rfl
    | true =>
      simp only [ackedBy, decide_eq_true_eq] at h
      obtain ⟨i, x, hx, _⟩ := h
      have := hR n hn i t x hx
      omega

-- SwitchConf: from the configuration of K's first ca entries, with a log holding K's first k,
-- a node reaches the configuration of K's first k entries.
theorem switch_conf (iv : server → Bool) (ad rm : value → List server) (jt lv : value → Bool)
    (l K : List (Entry value)) (ca k : Nat) (vin vout : server → Bool)
    (hca : ca < k) (hkK : k ≤ K.length) (hagree : K.take k = l.take k)
    (hok : switchOk ad rm jt lv l ca k vin vout)
    (hold : ∀ s, vin s = (cOf iv ad rm jt lv K ca).inn s ∧ vout s = (cOf iv ad rm jt lv K ca).out s) :
    switchTo ad rm jt lv l k vin vout = cOf iv ad rm jt lv K k := by
  rw [switchOk_iff] at hok
  obtain ⟨hk, hno, _⟩ := hok
  have hC : ({ inn := vin, out := vout } : MemberCore.Conf server) = cOf iv ad rm jt lv K ca :=
    conf_ext _ _ hold
  have hkc : MemberCore.isC Entry.isConf K k = true := by
    rw [MemberCore.isC_congr Entry.isConf K l k k hagree (Nat.le_refl _)]; exact hk
  have h1 : MemberCore.NoC Entry.isConf K ca (k - 1) := by
    intro p hp1 hp2
    rw [MemberCore.isC_congr Entry.isConf K l k p hagree (by omega)]
    exact hno p (by rw [List.mem_range'_1]; omega)
  have h2 : MemberCore.NoC Entry.isConf K k k := fun p hp1 hp2 => by omega
  obtain ⟨x, hx, _, hstep⟩ := MemberCore.confOf_one (isc := Entry.isConf) (chg := chgOf ad rm jt lv)
    (init := conf0 iv) K ca k k hca (Nat.le_refl _) h1 hkc h2
  have hlx : l[k - 1]? = some x := by
    have e1 : (K.take k)[k - 1]? = K[k - 1]? := List.getElem?_take_of_lt (by omega)
    have e2 : (l.take k)[k - 1]? = l[k - 1]? := List.getElem?_take_of_lt (by omega)
    rw [← e2, ← hagree, e1, hx]
  rw [switchTo_eq, hlx, hC]
  exact hstep.symm

theorem Kof.mono (commits commits' : CS) (hc : ∀ k : Commit server value, k ∈ commits → k ∈ commits')
    (k : List (Entry value)) (tk : Nat) (h : Kof commits k tk) : Kof commits' k tk := by
  obtain ⟨r, hr, e1, e2⟩ := h
  exact ⟨r, hc r hr, e1, e2⟩

-- LeaderCommit: what the term-t leader commits with a quorum of its configuration is a root.
theorem mroot_of_commit (iv : server → Bool) (ad rm : value → List server) (jt lv : value → Bool)
    (msgs : MS) (led : Nat → Option (List (Entry value))) (commits : CS) (ledAt elAt : Nat → Nat)
    (lIn lOut : Nat → server → Bool)
    (hLCf : ∀ (t : Nat) (A : List (Entry value)), led t = some A →
      ledAt t ≤ A.length ∧ elAt t ≤ ledAt t ∧
      (∀ s : server, lIn t s = (cOf iv ad rm jt lv A (ledAt t)).inn s ∧ lOut t s = (cOf iv ad rm jt lv A (ledAt t)).out s) ∧
      MemberCore.AtMostOne Entry.isConf A (ledAt t) A.length ∧
      (ledAt t = 0 ∨ ∃ k tk, Kof commits k tk ∧ tk ≤ t ∧ ledAt t ≤ k.length ∧ k.take (ledAt t) = A.take (ledAt t)) ∧
      (elAt t = 0 ∨ ∃ k tk, Kof commits k tk ∧ tk < t ∧ elAt t ≤ k.length ∧ k.take (elAt t) = A.take (elAt t)))
    (t c : Nat) (A : List (Entry value)) (hA : led t = some A) (hc1 : 1 ≤ c) (hc2 : c ≤ A.length)
    (hct : TermAt A c = t) (P : server → Bool) (hP : ∀ j, P j = true → ackedBy msgs t c j = true)
    (hq : MemberCore.IsQ P { inn := lIn t, out := lOut t }) :
    MRoot iv ad rm jt lv msgs led commits t c (ledAt t) A := by
  obtain ⟨_, _, h3, h4, h5, _⟩ := hLCf t A hA
  refine ⟨hA, hc2, ⟨hc1, A, hA, hct⟩, h5, fun p q h1 h2 hq' => h4 p q h1 h2 (by omega), ?_⟩
  have he : ({ inn := lIn t, out := lOut t } : MemberCore.Conf server) = cOf iv ad rm jt lv A (ledAt t) :=
    conf_ext _ _ h3
  rw [he] at hq
  exact MemberCore.IsQ.mono _ _ _ hP hq

-- BecomeLeader: the candidate's configuration is that of its log's first `ca` entries,
-- committed under an earlier term.
theorem cand_facts (iv : server → Bool) (ad rm : value → List server) (jt lv : value → Bool)
    (commits : CS) (cur ca : Nat) (l : List (Entry value)) (cIn cOut : server → Bool)
    (hSMS : ∀ a b : Commit server value, a ∈ commits → b ∈ commits →
      IsPrefix a.entries b.entries = true ∨ IsPrefix b.entries a.entries = true)
    (hCC : (ca = 0 ∧ ∀ s : server, cIn s = iv s ∧ cOut s = false) ∨
      ∃ a : Commit server value, ca ≤ a.entries.length ∧ a ∈ commits ∧
        ∀ s : server, cIn s = (cOf iv ad rm jt lv a.entries ca).inn s ∧ cOut s = (cOf iv ad rm jt lv a.entries ca).out s)
    (hcb : ca = 0 ∨ ca ≤ l.length ∧ ∃ a : Commit server value, a.term < cur ∧ ca ≤ a.entries.length ∧
      a ∈ commits ∧ SubSeq a.entries 1 ca = SubSeq l 1 ca) :
    ca ≤ l.length ∧ ({ inn := cIn, out := cOut } : MemberCore.Conf server) = cOf iv ad rm jt lv l ca ∧
    (ca = 0 ∨ ∃ k tk, Kof commits k tk ∧ tk < cur ∧ ca ≤ k.length ∧ k.take ca = l.take ca) := by
  have h0 : ca = 0 → ({ inn := cIn, out := cOut } : MemberCore.Conf server) = cOf iv ad rm jt lv l ca := by
    intro hz
    subst hz
    apply conf_ext
    intro s
    rcases hCC with ⟨_, h⟩ | ⟨a, _, _, h⟩
    · exact ⟨(h s).1, (h s).2⟩
    · exact ⟨(h s).1, (h s).2⟩
  rcases hcb with hz | ⟨hle, a, hat, hal, ha, hsub⟩
  · exact ⟨by omega, h0 hz, Or.inl hz⟩
  · rw [subSeq_one, subSeq_one] at hsub
    refine ⟨hle, ?_, Or.inr ⟨a.entries, a.term, ⟨a, ha, rfl, rfl⟩, hat, hal, hsub⟩⟩
    rcases hCC with ⟨hz, _⟩ | ⟨b, hbl, hb, hbc⟩
    · exact h0 hz
    · apply conf_ext
      intro s
      have hab : b.entries.take ca = a.entries.take ca := by
        have := hSMS a b ha hb
        rw [isPrefix_iff, isPrefix_iff] at this
        rcases this with h | h
        · exact (MemberCore.prefix_take _ _ ca h hal).symm
        · exact MemberCore.prefix_take _ _ ca h hbl
      have e1 : cOf iv ad rm jt lv b.entries ca = cOf iv ad rm jt lv l ca :=
        MemberCore.confOf_congr _ _ _ _ _ _ (hab.trans hsub)
      rw [← e1]; exact hbc s

-- A change in a log is in the leader log of its term, where the configuration before it takes it.
theorem legal_of_fromLed (iv : server → Bool) (ad rm : value → List server) (jt lv : value → Bool)
    (led : Nat → Option (List (Entry value))) (l : List (Entry value)) (hl : FromLed led l)
    (hLG : ∀ (e : Entry value) (t : Nat) (A : List (Entry value)), led t = some A → ∀ p : Nat,
      A[p]? = some e → e.isConf = true →
      MemberCore.Legal (cOf iv ad rm jt lv A p) (chgOf ad rm jt lv e))
    (p : Nat) (e : Entry value) (hp : l[p]? = some e) (he : e.isConf = true) :
    MemberCore.Legal (cOf iv ad rm jt lv l p) (chgOf ad rm jt lv e) := by
  have hpl : p < l.length := (List.getElem?_eq_some_iff.1 hp).1
  rw [FromLed.iff] at hl
  obtain ⟨L, hL, heq⟩ := hl p hpl
  have hLp : L[p]? = some e := by
    have : (l.take (p + 1))[p]? = (L.take (p + 1))[p]? := by rw [heq]
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_take_of_lt (by omega)] at this
    rw [← this]; exact hp
  have hc : cOf iv ad rm jt lv l p = cOf iv ad rm jt lv L p :=
    MemberCore.confOf_congr _ _ _ _ _ _ (MemberCore.take_take_eq _ _ (p + 1) p heq (by omega))
  rw [hc]
  exact hLG e _ L hL p hLp he

-- BecomeLeader adds no acknowledgement: none exists in a term before its leader.
theorem Acked.of_becomeLeader (msgs : MS) (leaders : LS) (led : Nat → Option (List (Entry value)))
    (i : server) (cur : Nat) {d : ∀ x : Nat, Decidable (cur = x)} (l : List (Entry value)) (n : server) (t : Nat) (A : List (Entry value)) (c : Nat)
    (hnone : led cur = none)
    (hAF : ∀ j i x, Msg.ack (value := value) j i cur x ∈ msgs → ∃ L, led cur = some L ∧ x ≤ L.length)
    (h : Acked msgs (TSet.insert ({ server := i, term := cur } : Elected server) leaders)
      (fun x => @ite _ (cur = x) (d _) (some l) (led x)) n t A c) :
    Acked msgs leaders led n t A c := by
  obtain ⟨h1, h2, h3, i', x, hx, hc⟩ := h
  have h1' : (@ite _ (cur = t) (d _) (some l) (led t)) = some A := h1
  by_cases hct : cur = t
  · subst hct
    obtain ⟨L, hL, _⟩ := hAF _ _ _ hx
    rw [hnone] at hL; cases hL
  · rw [EtcdRaftVeil.Lemmas.ifNeg hct] at h1'
    exact ⟨h1', h2, h3, i', x, hx, hc⟩

-- LeaderAppend: nobody has acknowledged the new entry yet.
theorem Acked.of_leaderAppend (msgs : MS) (leaders : LS) (led : Nat → Option (List (Entry value)))
    (cur : Nat) {d : ∀ x : Nat, Decidable (cur = x)} (l : List (Entry value)) (e : Entry value) (n : server) (t : Nat)
    (A : List (Entry value)) (c : Nat)
    (hl : led cur = some l)
    (hAF : ∀ i x, Msg.ack (value := value) n i cur x ∈ msgs → x ≤ l.length)
    (h : Acked msgs leaders
      (fun x => @ite _ (cur = x) (d _) (some (l ++ [e])) (led x)) n t A c) :
    (t ≠ cur ∧ Acked msgs leaders led n t A c) ∨
    (t = cur ∧ A = l ++ [e] ∧ c ≤ l.length ∧ Acked msgs leaders led n cur l c) := by
  obtain ⟨h1, h2, h3, i, x, hx, hcx⟩ := h
  have h1' : (@ite _ (cur = t) (d _) (some (l ++ [e])) (led t)) = some A := h1
  by_cases hc : cur = t
  · subst hc
    rw [EtcdRaftVeil.Lemmas.ifPos rfl] at h1'; cases h1'
    have := hAF i x hx
    refine Or.inr ⟨rfl, rfl, by omega, hl, h2, ?_, i, x, hx, hcx⟩
    rw [← termAt_append_left l [e] c (by omega)]; exact h3
  · rw [EtcdRaftVeil.Lemmas.ifNeg hc] at h1'
    exact Or.inl ⟨fun h => hc h.symm, h1', h2, h3, i, x, hx, hcx⟩

theorem Acked.le_length (msgs : MS) (leaders : LS) (led : Nat → Option (List (Entry value)))
    (n : server) (t : Nat) (A : List (Entry value)) (c : Nat)
    (hAF : ∀ i x, Msg.ack (value := value) n i t x ∈ msgs → ∃ L, led t = some L ∧ x ≤ L.length)
    (h : Acked msgs leaders led n t A c) : c ≤ A.length := by
  obtain ⟨h1, _, _, i, x, hx, hc⟩ := h
  obtain ⟨L, hL, hxL⟩ := hAF i x hx
  rw [h1] at hL; cases hL; omega

end Quorums

-- ElectionSafety == \A a, b \in leaders : a.term = b.term => a.server = b.server
invariant [ElectionSafety]
  ∀ a b : { x // x ∈ leaders }, a.val.term = b.val.term → a.val.server = b.val.server

-- OneVotePerTerm ==
--     \A a, b \in votes : a.voter = b.voter /\ a.term = b.term => a.cand = b.cand
invariant [OneVotePerTerm]
  ∀ a b : { x // x ∈ votes }, a.val.voter = b.val.voter ∧ a.val.term = b.val.term → a.val.cand = b.val.cand

-- Not in EtcdRaft.tla: supporting invariants for ElectionSafety and OneVotePerTerm.

-- A node's vote record is never ahead of its term.
invariant [VoteTermBound] ∀ i : server, voteTerm i ≤ currentTerm i

-- Every vote a node has given is at or before its vote record's term.
invariant [VotesBound] ∀ v : { v // v ∈ votes }, v.val.term ≤ voteTerm v.val.voter

-- A granted reply states a vote that exists.
invariant [GrantsAreVotes]
  ∀ m : { m // m ∈ msgs }, (match m.val with
    | .grant src dst term => vSet.contains { voter := src, term := term, cand := dst } votes
    | _ => true) = true

-- A node that leads counts with its term's leader configuration.
invariant [LeaderSync]
  ∀ i : server, role i = Leader →
    confAt i = ledAt (currentTerm i) ∧
    ∀ s : server, cIn i s = lIn (currentTerm i) s ∧ cOut i s = lOut (currentTerm i) s

-- Not in EtcdRaft.tla: supporting invariants for LogMatching.

-- A node in the leader role was elected in its term.
invariant [LeaderIsElected]
  ∀ i : server, role i = Leader → lSet.contains { server := i, term := currentTerm i } leaders = true

-- No node was elected in a term it has not reached.
invariant [LeadersTermBound] ∀ ld : { x // x ∈ leaders }, ld.val.term ≤ currentTerm ld.val.server

-- While the term's elected node stays in the term, its log is a prefix of the leader log.
invariant [LedOwner]
  ∀ ld : { x // x ∈ leaders },
    ld.val.term = currentTerm ld.val.server →
      ((ledLog ld.val.term).any fun L => IsPrefix (log ld.val.server) L) = true

-- The terms that have a leader log are the terms that had a leader.
invariant [LeadersHaveLed] ∀ ld : { x // x ∈ leaders }, ledLog ld.val.term ≠ none
invariant [LedHasLeader]
  ∀ t : Nat, ledLog t ≠ none → ∃ ld : { x // x ∈ leaders }, ld.val.term = t

-- An append request is from the node elected in its term (to any node, itself included).
invariant [AppendFromLeader]
  ∀ m : { m // m ∈ msgs }, (match m.val with
    | .append src _ term _ _ _ _ => lSet.contains { server := src, term := term } leaders
    | _ => true) = true

-- LeaderLogIsLed ==
--     \A i \in Server : role[i] = Leader =>
--         /\ currentTerm[i] \in DOMAIN ledLog
--         /\ IsPrefix(log[i], ledLog[currentTerm[i]])
invariant [LeaderLogIsLed]
  ∀ i : server, role i = Leader → ((ledLog (currentTerm i)).any fun L => IsPrefix (log i) L) = true

-- RequestsFromLed ==
--     \A m \in msgs : m.type = "append" =>
--         /\ m.term \in DOMAIN ledLog
--         /\ m.prevLogIndex + Len(m.entries) <= Len(ledLog[m.term])
--         /\ m.prevLogTerm = TermAt(ledLog[m.term], m.prevLogIndex)
--         /\ m.entries = SubSeq(ledLog[m.term], m.prevLogIndex + 1, m.prevLogIndex + Len(m.entries))
--         /\ CommittedIn(ledLog[m.term], m.commit, m.term)
invariant [RequestsFromLed]
  ∀ m : { m // m ∈ msgs }, (match m.val with
    | .append _ _ term prevLogIndex prevLogTerm entries commit =>
      (match ledLog term with
        | none => false
        | some l => decide (
            prevLogIndex + entries.length ≤ l.length ∧
            prevLogTerm = TermAt l prevLogIndex ∧
            entries = SubSeq l (prevLogIndex + 1) (prevLogIndex + entries.length) ∧
            (commit = 0 ∨ (commit ≤ l.length ∧ ∃ k : { k // k ∈ commits },
              k.val.term ≤ term ∧ commit ≤ k.val.entries.length ∧
              SubSeq k.val.entries 1 commit = SubSeq l 1 commit))))
    | _ => true) = true

-- Every entry, with its predecessors, is in the leader log of its term.
invariant [LogFromLed] ∀ i : server, FromLed ledLog (log i)
invariant [LedFromLed] ∀ t : Nat, ((ledLog t).all fun L => decide (FromLed ledLog L)) = true

-- LogMatching ==
--     \A a, b \in Server :
--         \A k \in 1..Min(Len(log[a]), Len(log[b])) :
--             log[a][k].term = log[b][k].term => SubSeq(log[a], 1, k) = SubSeq(log[b], 1, k)
invariant [LogMatching]
  ∀ a b : server, ∀ k ∈ List.range' 1 (min (log a).length (log b).length),
    TermAt (log a) k = TermAt (log b) k → SubSeq (log a) 1 k = SubSeq (log b) 1 k

-- PROOF-ONLY BEGIN
-- For StateMachineSafety. Unbounded quantifiers: `../scripts/veil-count.sh` leaves them out.

-- No term 0 has a leader: every entry has a positive term.
invariant [TermsPositive] ∀ t : Nat, ledLog t ≠ none → 1 ≤ t

-- A log has no entry of a term its node has not reached.
invariant [LogTermsBound] ∀ i : server, ∀ k : Nat, TermAt (log i) k ≤ currentTerm i

-- Terms never decrease along a leader log and do not exceed its term.
invariant [LedSorted] ∀ t : Nat, ∀ L : List (Entry value), ledLog t = some L → Sorted L t

-- A vote request is of a term its sender has reached, and describes a log that exists.
invariant [ReqFacts]
  ∀ m : { m // m ∈ msgs }, ∀ c : server, ∀ u li lt : Nat, m.val = Msg.vote c u li lt →
    u ≤ currentTerm c ∧ ReqOk ledLog u li lt

-- A node asks once per term.
invariant [ReqUnique]
  ∀ m m' : { m // m ∈ msgs }, ∀ c : server, ∀ u li lt li' lt' : Nat,
    m.val = Msg.vote c u li lt → m'.val = Msg.vote c u li' lt' → li = li' ∧ lt = lt'

-- Every vote answers a request.
invariant [VoteHasReq]
  ∀ v : { v // v ∈ votes }, ∃ m : { m // m ∈ msgs }, ∃ li lt : Nat,
    m.val = Msg.vote v.val.cand v.val.term li lt

-- Until its term has a leader, a candidate's log is the one its request describes.
invariant [CandLog]
  ∀ m : { m // m ∈ msgs }, ∀ c : server, ∀ u li lt : Nat, m.val = Msg.vote c u li lt →
    currentTerm c = u → ledLog u = none → (log c).length = li ∧ TermAt (log c) li = lt

-- A leader log starts with the log its leader asked for votes with.
invariant [LedExtendsReq]
  ∀ ld : { x // x ∈ leaders }, ∀ m : { m // m ∈ msgs }, ∀ li lt : Nat,
    m.val = Msg.vote ld.val.server ld.val.term li lt →
    ∀ L : List (Entry value), ledLog ld.val.term = some L → li ≤ L.length ∧ TermAt L li = lt

-- An ack goes to its term's leader, from a node that reached the term, for leader-log entries.
invariant [AckFacts]
  ∀ m : { m // m ∈ msgs }, ∀ j i : server, ∀ t x : Nat, m.val = Msg.ack j i t x →
    lSet.contains { server := i, term := t } leaders = true ∧ t ≤ currentTerm j ∧
    ∃ L : List (Entry value), ledLog t = some L ∧ x ≤ L.length

-- What a node acknowledged it still holds, unless a later leader log up to its term lacks it.
invariant [AckedHeld]
  ∀ n : server, ∀ t : Nat, ∀ A : List (Entry value), ∀ c : Nat, Acked msgs leaders ledLog n t A c →
    A.take c <+: log n ∨ LostIn ledLog A c t (currentTerm n)

-- Acknowledged then voted: the candidate has the entries, unless a leader log between the two
-- terms (the vote's included) lacks them.
invariant [AckVote]
  ∀ n : server, ∀ t : Nat, ∀ A : List (Entry value), ∀ c : Nat, Acked msgs leaders ledLog n t A c →
    ∀ v : { v // v ∈ votes }, v.val.voter = n → t < v.val.term →
    ∀ li lt : Nat, msgSet.contains (Msg.vote v.val.cand v.val.term li lt) msgs = true →
      Covers ledLog A c li lt ∨ LostIn ledLog A c t v.val.term

-- Every leader was elected by a quorum of early votes.
invariant [EarlyQuorum]
  ∀ ld : { x // x ∈ leaders }, ∀ B : List (Entry value), ledLog ld.val.term = some B →
    MemberCore.IsQ (fun n => @decide (
      vSet.contains { voter := n, term := ld.val.term, cand := ld.val.server } votes = true ∧
      Early msgs leaders ledLog n ld.val.server ld.val.term) (Classical.propDecidable _))
      (cOf initV chAdd chRemove chJoint chLeave B (elAt ld.val.term))

-- What a leader has confirmed of a node's log is a prefix of that leader's log.
invariant [ConfirmedIsLed]
  ∀ j : server, confirmedIndex j = 0 ∨ ∃ L : List (Entry value),
    ledLog (confirmedTerm j) = some L ∧ confirmedIndex j ≤ (log j).length ∧
    (log j).take (confirmedIndex j) = L.take (confirmedIndex j)

-- Every committed prefix is part of one committed by a leader of a term ≤ its recorded term:
-- a prefix of that leader log, ending in an entry of that term, acknowledged by a quorum.
invariant [CommitRoot]
  ∀ k : { x // x ∈ commits }, k.val.entries ≠ [] ∧ ∃ r : { x // x ∈ commits },
    k.val.entries <+: r.val.entries ∧ Root initV chAdd chRemove chJoint chLeave msgs ledLog commits r.val ∧
      r.val.term ≤ k.val.term
-- PROOF-ONLY END

-- CommitSafety ==
--     \A a, b \in commits : IsPrefix(a.entries, b.entries) \/ IsPrefix(b.entries, a.entries)
invariant [CommitSafety]
  ∀ a b : { x // x ∈ commits },
    IsPrefix a.val.entries b.val.entries ∨ IsPrefix b.val.entries a.val.entries

-- Not in EtcdRaft.tla: supporting invariants for the four properties below.

-- What a node has had confirmed is from a leader of a term it has reached.
invariant [ConfirmedTermBound] ∀ i : server, confirmedTerm i ≤ currentTerm i

-- A committed prefix is recorded under a term its server has reached.
invariant [CommitTermBound] ∀ c : { x // x ∈ commits }, c.val.term ≤ currentTerm c.val.server

-- CommittedEntriesPreserved ==
--     \A i \in Server :
--         /\ commitIndex[i] <= Len(log[i])
--         /\ commitIndex[i] = 0 \/
--              \E c \in commits : c.server = i /\ IsPrefix(SubSeq(log[i], 1, commitIndex[i]), c.entries)
-- in two parts.
invariant [CommittedEntriesPreserved]
  ∀ i : server, commitIndex i = 0 ∨ ∃ k : { x // x ∈ commits },
    k.val.server = i ∧ IsPrefix ((log i).take (commitIndex i)) k.val.entries

invariant [CommitWithinLog] ∀ i : server, commitIndex i ≤ (log i).length

-- Every entry handed to a state machine is, at its index, in a committed prefix.
invariant [AppliedCommitted]
  ∀ a : { x // x ∈ applied }, ∃ k : { x // x ∈ commits },
    1 ≤ a.val.index ∧ k.val.entries[a.val.index - 1]? = some a.val.entry

-- StateMachineSafety == \A a, b \in applied : a.index = b.index => a.entry = b.entry
invariant [StateMachineSafety]
  ∀ a b : { x // x ∈ applied }, a.val.index = b.val.index → a.val.entry = b.val.entry

-- LeaderCompleteness ==
--     \A t \in DOMAIN ledLog, c \in commits : c.term < t => IsPrefix(c.entries, ledLog[t])
invariant [LeaderCompleteness]
  ∀ t : Nat, ∀ c : { x // x ∈ commits },
    c.val.term < t → ((ledLog t).all fun L => IsPrefix c.val.entries L) = true

-- ConfirmedWithinLog == \A i \in Server : confirmed[i].index <= Len(log[i])
invariant [ConfirmedWithinLog]
  ∀ i : server, confirmedIndex i ≤ (log i).length

-- Membership.

-- PROOF-ONLY BEGIN
-- ConfIsCommitted ==
--     \A i \in Server :
--         \/ confAt[i] = 0 /\ config[i] = InitConf
--         \/ \E c \in commits : confAt[i] <= Len(c.entries) /\ config[i] = ConfOf(c.entries, confAt[i])
invariant [ConfIsCommitted]
  ∀ i : server, (confAt i = 0 ∧ ∀ s : server, cIn i s = initV s ∧ cOut i s = false) ∨
    ∃ k : { x // x ∈ commits }, confAt i ≤ k.val.entries.length ∧
      ∀ s : server, cIn i s = (cOf initV chAdd chRemove chJoint chLeave k.val.entries (confAt i)).inn s ∧
        cOut i s = (cOf initV chAdd chRemove chJoint chLeave k.val.entries (confAt i)).out s

-- LeaderConf ==
--     \A t \in DOMAIN ledLog :
--         /\ t \in DOMAIN ledConf /\ t \in DOMAIN ledAt /\ t \in DOMAIN elAt
--         /\ elAt[t] <= ledAt[t] /\ ledAt[t] <= Len(ledLog[t])
--         /\ ledConf[t] = ConfOf(ledLog[t], ledAt[t])
--         /\ Cardinality(ConfsAfter(ledLog[t], ledAt[t])) <= 1
-- plus: the changes making a leader's configuration are committed at ≤ its term, those making
-- its election configuration at < its term.
invariant [LeaderConf]
  ∀ t : Nat, ∀ A : List (Entry value), ledLog t = some A →
    ledAt t ≤ A.length ∧ elAt t ≤ ledAt t ∧
    (∀ s : server, lIn t s = (cOf initV chAdd chRemove chJoint chLeave A (ledAt t)).inn s ∧ lOut t s = (cOf initV chAdd chRemove chJoint chLeave A (ledAt t)).out s) ∧
    MemberCore.AtMostOne Entry.isConf A (ledAt t) A.length ∧
    (ledAt t = 0 ∨ ∃ k tk, Kof commits k tk ∧ tk ≤ t ∧ ledAt t ≤ k.length ∧ k.take (ledAt t) = A.take (ledAt t)) ∧
    (elAt t = 0 ∨ ∃ k tk, Kof commits k tk ∧ tk < t ∧ elAt t ≤ k.length ∧ k.take (elAt t) = A.take (elAt t))

-- A change in a committed prefix was first committed, at ≤ the prefix's term, by a leader not
-- yet counting with it.
invariant [FirstRoot]
  ∀ k : { x // x ∈ commits }, ∀ p : Nat, MemberCore.isC Entry.isConf k.val.entries p = true →
    ∃ r : { x // x ∈ commits }, r.val.term ≤ k.val.term ∧ p ≤ r.val.entries.length ∧
      ∃ d A, d < p ∧ MRoot initV chAdd chRemove chJoint chLeave msgs ledLog commits r.val.term r.val.entries.length d A ∧
        r.val.entries <+: A

-- A leader log has at most one earlier-term change beyond its election configuration.
invariant [LedOld]
  ∀ u : Nat, ∀ B : List (Entry value), ledLog u = some B → ∀ p q : Nat, elAt u < p → p < q →
    MemberCore.isC Entry.isConf B p = true → MemberCore.isC Entry.isConf B q = true →
    TermAt B p < u → TermAt B q < u → False

-- A change in a leader log is one that the configuration made by the entries before it takes.
invariant [LegalChain]
  ∀ t : Nat, ∀ A : List (Entry value), ledLog t = some A → ∀ p : Nat, ∀ e : Entry value,
    A[p]? = some e → e.isConf = true →
    MemberCore.Legal (cOf initV chAdd chRemove chJoint chLeave A p) (chgOf chAdd chRemove chJoint chLeave e)
-- PROOF-ONLY END

-- Read index. read.msgs and read.floor are snapshots taken at ReadRequest.

-- ReadMsgsOld == read.on => read.msgs \subseteq msgs
invariant [ReadMsgsOld]
  readOn = true → ∀ m : { m // m ∈ readMsgs }, msgSet.contains m.val msgs = true

-- ReadFloorOld == read.on => read.floor \subseteq commits
invariant [ReadFloorOld]
  readOn = true → ∀ k : { k // k ∈ readFloor }, cSet.contains k.val commits = true

-- ReadFloorBound ==
--     read.on => \A k \in read.floor : k.term <= read.term => Len(k.entries) <= read.index
invariant [ReadFloorBound]
  readOn = true → ∀ k : { k // k ∈ readFloor }, k.val.term ≤ readTerm → k.val.entries.length ≤ readIndex

-- ReadIndexSafety == read.done => \A k \in read.floor : Len(k.entries) <= read.index
invariant [ReadIndexSafety]
  readDone = true → ∀ k : { k // k ∈ readFloor }, k.val.entries.length ≤ readIndex

-- The term of the read has a leader log.
invariant [ReadTermLed]
  readOn = true → ledLog readTerm ≠ none

-- PROOF-ONLY BEGIN
-- CommitRoot, at the snapshot.
invariant [ReadFloorRooted]
  readOn = true → ∀ k : { k // k ∈ readFloor }, ∃ r : { r // r ∈ readFloor },
    k.val.entries <+: r.val.entries ∧ Root initV chAdd chRemove chJoint chLeave readMsgs ledLog readFloor r.val

-- FirstRoot, as it was then.
invariant [ReadFirstRoot]
  readOn = true → ∀ k : { x // x ∈ readFloor }, ∀ p : Nat, MemberCore.isC Entry.isConf k.val.entries p = true →
    ∃ r : { x // x ∈ readFloor }, r.val.term ≤ k.val.term ∧ p ≤ r.val.entries.length ∧
      ∃ d A, d < p ∧ MRoot initV chAdd chRemove chJoint chLeave readMsgs ledLog readFloor r.val.term r.val.entries.length d A ∧
        r.val.entries <+: A

-- A node that has answered had, then, acknowledged nothing in a term after the leader's.
invariant [ReadRespBound]
  readOn = true → ∀ j : server, readResp j = true → ∀ m : { m // m ∈ readMsgs }, ∀ i : server, ∀ t x : Nat,
    m.val = Msg.ack j i t x → t ≤ readTerm
-- PROOF-ONLY END

-- Bounded (MCEtcd.tla) ==
--     /\ \A i \in Server : currentTerm[i] <= MaxTerm /\ Len(log[i]) <= MaxLog
--     /\ \A t \in DOMAIN ledLog : Len(ledLog[t]) <= MaxLog
--     /\ \A m \in msgs : m.type = "append" => Len(m.entries) <= MaxBatch
--     /\ Cardinality(msgs) <= MaxMsgs
state_constraint [Bounded]
  (∀ i, currentTerm i ≤ MaxTerm ∧ (log i).length ≤ MaxLog) ∧
  (∀ t ∈ List.range (MaxTerm + 1), ((ledLog t).all fun L => decide (L.length ≤ MaxLog)) = true) ∧
  (∀ m : { m // m ∈ msgs }, (match m.val with
    | .append _ _ _ _ _ entries _ => decide (entries.length ≤ MaxBatch)
    | _ => true) = true) ∧
  msgSet.count msgs ≤ MaxMsgs

-- Instance synthesis for 53 invariants needs a larger budget.
set_option synthInstance.maxHeartbeats 400000
#gen_spec
set_option synthInstance.maxHeartbeats 20000
#gen_executable

-- BecomeLeader: a candidate with a quorum is the only one elected in its term, so an existing
-- leader log for the term is its own.
theorem winner_unique {server value MsgSet VoteSet LeaderSet : Type} [Servers server]
    [TSet (Msg server value) MsgSet] [TSet (Vote server) VoteSet] [TSet (Elected server) LeaderSet]
    (msgs : MsgSet) (votes : VoteSet) (leaders : LeaderSet) (i : server) (cur : Nat)
    (hOV : ∀ a b : Vote server, a ∈ votes → b ∈ votes → a.voter = b.voter → a.term = b.term → a.cand = b.cand)
    (hGV : ∀ j, TSet.contains (Msg.grant (value := value) j i cur) msgs = true →
      TSet.contains ({ voter := j, term := cur, cand := i } : Vote server) votes = true)
    (hLQ : ∀ a : Elected server, a ∈ leaders →
      (IsQuorum fun j => TSet.contains ({ voter := j, term := a.term, cand := a.server } : Vote server) votes) = true)
    (hq : (IsQuorum fun j =>
      @ite Bool (j = i) (Classical.propDecidable _) (TSet.contains ({ voter := i, term := cur, cand := i } : Vote server) votes)
        (TSet.contains (Msg.grant (value := value) j i cur) msgs)) = true) :
    ∀ x : Elected server, x ∈ leaders → x.term = cur → x.server = i := by
  have hq' : IsQuorum (fun j => TSet.contains ({ voter := j, term := cur, cand := i } : Vote server) votes) = true := by
    refine IsQuorum.mono _ _ ?_ hq
    intro j hj
    by_cases hji : j = i
    · subst hji; simpa using hj
    · simp only [hji, ite_false] at hj
      exact hGV _ hj
  intro x hx hxt
  obtain ⟨j, h1, h2⟩ := IsQuorum.inter _ _ (hLQ x hx) hq'
  have := hOV _ _ h1 h2 rfl (by simpa using hxt)
  simpa using this

-- BecomeLeader: the term has no leader log, so no node was elected in it.
theorem winner_none {server value LeaderSet : Type} [TSet (Elected server) LeaderSet]
    (leaders : LeaderSet) (led : Nat → Option (List (Entry value))) (i : server) (cur : Nat)
    (hLHL : ∀ a : Elected server, a ∈ leaders → ¬ led a.term = none) (hnone : led cur = none) :
    ∀ x : Elected server, x ∈ leaders → x.term = cur → x.server = i :=
  fun x hx ht => absurd (by rw [ht]; exact hnone) (hLHL x hx)

-- Setting a term's leader log for the first time, or to itself, keeps all leader logs (for FromLed.mono).
theorem led_ext_set {value : Type} (ledLog : Nat → Option (List (Entry value))) (cur : Nat)
    (l : List (Entry value)) (hsame : ∀ L, ledLog cur = some L → L <+: l) :
    ∀ t L, ledLog t = some L →
      ∃ L', (fun x => @ite _ (cur = x) (Classical.propDecidable _) (some l) (ledLog x)) t = some L' ∧ L <+: L' := by
  intro t L hL
  by_cases hc : cur = t
  · subst hc
    refine ⟨l, ?_, hsame L hL⟩
    show (@ite _ (cur = cur) (Classical.propDecidable _) (some l) (ledLog cur)) = some l
    rw [EtcdRaftVeil.Lemmas.ifPos rfl]
  · refine ⟨L, ?_, List.prefix_refl _⟩
    show (@ite _ (cur = t) (Classical.propDecidable _) (some l) (ledLog t)) = some L
    rw [EtcdRaftVeil.Lemmas.ifNeg hc]; exact hL

-- RequestsFromLed for one append request, over the accessor fields (`X`: the commit part).
theorem req_facts {server value : Type} [DecidableEq value]
    (ledLog : Nat → Option (List (Entry value))) (X : Nat → List (Entry value) → Nat → Bool)
    (m : Msg server value)
    (h : (match m with
      | .append _ _ term prevLogIndex prevLogTerm entries commit =>
        (match ledLog term with
          | none => false
          | some l =>
            decide (prevLogIndex + entries.length ≤ l.length) &&
              (decide (prevLogTerm = TermAt l prevLogIndex) &&
                (decide (entries = SubSeq l (prevLogIndex + 1) (prevLogIndex + entries.length)) &&
                  X term l commit)))
      | _ => true) = true)
    (ha : m.isAppend = true) :
    ∃ L, ledLog m.term = some L ∧ m.prevLogIndex + m.entries.length ≤ L.length ∧
      m.prevLogTerm = TermAt L m.prevLogIndex ∧
      m.entries = SubSeq L (m.prevLogIndex + 1) (m.prevLogIndex + m.entries.length) ∧
      X m.term L m.commit = true := by
  cases m with
  | append src dst term p pt es c =>
    dsimp only [Msg.term, Msg.prevLogIndex, Msg.prevLogTerm, Msg.entries, Msg.commit] at h ⊢
    cases hL : ledLog term with
    | none => rw [hL] at h; exact Bool.noConfusion h
    | some L =>
      rw [hL] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨L, rfl, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  | _ => simp [Msg.isAppend] at ha

-- LeaderAppend: what appending an entry of its term to the leader's log, and to the term's
-- leader log with it, does to FromLed.
theorem leaderAppend_fromLed {value : Type} [DecidableEq value]
    (led : Nat → Option (List (Entry value))) (l : List (Entry value)) (e : Entry value) (t : Nat)
    (het : e.term = t) (hled : led t = some l) :
    (∀ l', FromLed led l' →
      FromLed (fun x => @ite _ (t = x) (Classical.propDecidable _) (some (l ++ [e])) (led x)) l') ∧
    (FromLed led l →
      FromLed (fun x => @ite _ (t = x) (Classical.propDecidable _) (some (l ++ [e])) (led x)) (l ++ [e])) := by
  subst het
  have hext := led_ext_set led e.term (l ++ [e])
    (fun L hL => by rw [hled] at hL; cases hL; exact List.prefix_append _ _)
  refine ⟨fun l' h => FromLed.mono _ _ _ hext h, fun h => ?_⟩
  refine FromLed.append_own _ l [e] e.term ?_ ?_ (FromLed.mono _ _ _ hext h)
  · show (@ite _ (e.term = e.term) (Classical.propDecidable _) (some (l ++ [e])) (led e.term)) = some (l ++ [e])
    rw [EtcdRaftVeil.Lemmas.ifPos rfl]
  · intro e' he'; simp at he'; rw [he']

-- StoreEntries: the follower's new log is from leader logs.
theorem store_fromLed {value : Type} [DecidableEq value]
    (led : Nat → Option (List (Entry value))) (l L : List (Entry value)) (p k : Nat)
    (es : List (Entry value))
    (hl : FromLed led l) (hL : FromLed led L)
    (hpn : p + es.length ≤ L.length)
    (hes : es = SubSeq L (p + 1) (p + es.length))
    (hprev : PrevOk l p (TermAt L p) = true)
    (hk : k ∈ List.range' 1 es.length)
    (hfirst : HasFirst l p es (k - 1) = true)
    (hlen : p + k = l.length + 1) :
    FromLed led (l ++ SubSeq es k es.length) := by
  rw [store_eq led l L p k es hl hL hpn hes hprev hk hfirst hlen]
  exact FromLed.take led L _ hL

-- RequestsFromLed is kept when leader logs only grow and the commit part (`X`, `X'`) is kept.
theorem req_mono {server value : Type} [DecidableEq value]
    (led led' : Nat → Option (List (Entry value))) (X X' : Nat → List (Entry value) → Nat → Bool)
    (m : Msg server value)
    (h : (match m with
      | .append _ _ term prevLogIndex prevLogTerm entries commit =>
        (match led term with
          | none => false
          | some l =>
            decide (prevLogIndex + entries.length ≤ l.length) &&
              (decide (prevLogTerm = TermAt l prevLogIndex) &&
                (decide (entries = SubSeq l (prevLogIndex + 1) (prevLogIndex + entries.length)) &&
                  X term l commit)))
      | _ => true) = true)
    (hled : ∀ t l, led t = some l → ∃ l', led' t = some l' ∧ l <+: l')
    (hX : ∀ t l l' c, l <+: l' → X t l c = true → X' t l' c = true) :
    (match (generalizing := false) m with
      | .append _ _ term prevLogIndex prevLogTerm entries commit =>
        (match led' term with
          | none => false
          | some l =>
            decide (prevLogIndex + entries.length ≤ l.length) &&
              (decide (prevLogTerm = TermAt l prevLogIndex) &&
                (decide (entries = SubSeq l (prevLogIndex + 1) (prevLogIndex + entries.length)) &&
                  X' term l commit)))
      | _ => true) = true := by
  cases m with
  | append src dst term p pt es c =>
    dsimp only at h ⊢
    cases hL : led term with
    | none => rw [hL] at h; exact Bool.noConfusion h
    | some l =>
      obtain ⟨l', hl', hp⟩ := hled term l hL
      rw [hL] at h; rw [hl']
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      obtain ⟨h1, h2, h3, h4⟩ := h
      obtain ⟨s, rfl⟩ := hp
      refine ⟨by simp; omega, ?_, ?_, hX term l (l ++ s) c ⟨s, rfl⟩ h4⟩
      · rw [termAt_append_left _ _ _ (by omega)]; exact h2
      · rw [subSeq_append_left _ _ _ _ (by omega) h1]; exact h3
  | _ => rfl

-- The commit part of RequestsFromLed is kept when the leader log and the set of commits grow.
theorem commitPart_mono {server value S S' : Type} [TSet (Commit server value) S]
    [TSet (Commit server value) S'] (cs : S) (cs' : S') (hS : ∀ k, k ∈ cs → k ∈ cs')
    (l l' : List (Entry value)) (c t : Nat) (hp : l <+: l')
    (h : c = 0 ∨ (c ≤ l.length ∧ ∃ k : { k // k ∈ cs },
      k.val.term ≤ t ∧ c ≤ k.val.entries.length ∧ SubSeq k.val.entries 1 c = SubSeq l 1 c)) :
    c = 0 ∨ (c ≤ l'.length ∧ ∃ k : { k // k ∈ cs' },
      k.val.term ≤ t ∧ c ≤ k.val.entries.length ∧ SubSeq k.val.entries 1 c = SubSeq l' 1 c) := by
  rcases h with h0 | ⟨hc, ⟨k, hk⟩, ht, h1, h2⟩
  · exact Or.inl h0
  · obtain ⟨s, rfl⟩ := hp
    refine Or.inr ⟨by simp; omega, ⟨k, hS k hk⟩, ht, h1, ?_⟩
    rw [subSeq_append_left _ _ _ _ (Nat.le_refl 1) hc]; exact h2

-- Cross-check with TLC on `Spec` of `../spec/EtcdRaft.tla` (no symmetry): at the bounds of
-- `../spec/MCCount2/3/4.cfg` both find 17,168 / 305,896 / 1,631,864 distinct states, at those of
-- `MCMemCount2/3.cfg` 15,800 / 204,552, no violation. Run with `../scripts/veil-count.sh`;
-- commented out so that `lake build` does not run it.
-- #model_check compiled
--   { server := Fin 3, value := Fin 1, Role := Role_IndT, MsgSet := OrdList _,
--     VoteSet := OrdList _, LeaderSet := OrdList _, CommitSet := OrdList _, AppliedSet := OrdList _ }
--   { MaxTerm := 2, MaxLog := 2, MaxBatch := 1, MaxMsgs := 2 }

-- ---------------------------------------------------------------------------------------
-- Proofs. One goal per (initializer or action, invariant): 24 × 53 = 1,272 goals. Proofs name
-- the facts they use (`grind only`, `simp only`, lemmas of this file).
--
-- `hinv` is the conjunction of the 53 invariants, in declaration order. Each proof extracts
-- what it uses by position (`have hX := hinv.2.….1`) and clears the rest. Names used:
-- hES hOV hVT hVB hGV hLSy hLE hLTB hLO hLHL hLHas hAFL hLLL hRFL hLFL hLedFL hLM
-- hTP hLogTB hLS hRF hRU hVHR hCL hLER hAF hAH hAV hEQ hCIL hCR hSMS
-- hCfT hCmT hCEP hCWL hAC hSM hLC hCfWL hCC hLCf hFR hLOld hLG
-- hRMO hRFO hRFB hRIS hRTL hRFR hRF1 hRRB
-- (hSMS is CommitSafety, hSM is StateMachineSafety, hCWL CommitWithinLog, hCfWL
-- ConfirmedWithinLog, hLSy LeaderSync; hCC to hLG are the invariants about membership, the
-- last eight the read index). New invariants go at the end, or the positions change.
--
-- SwitchConf goals use `prove_goal_unregistered` (see the top of this file).
-- Check with `../scripts/veil-check.sh` or `lake build`.

-- initializer

prove_veil_invariant_goal initializer ElectionSafety using tr by
  obtain ⟨-, -, -, -, -, -, -, -, hm, hv, hl, -, hc, -, happ, -⟩ := htr
  subst hm hv hl hc
  intros
  exact (EtcdRaftVeil.Lemmas.sub_empty a).elim

prove_veil_invariant_goal initializer OneVotePerTerm using tr by
  obtain ⟨-, -, -, -, -, -, -, -, hm, hv, hl, -, hc, -, happ, -⟩ := htr
  subst hm hv hl hc
  intros
  exact (EtcdRaftVeil.Lemmas.sub_empty a).elim

prove_veil_invariant_goal initializer VoteTermBound using tr by
  obtain ⟨h1, h2, -⟩ := htr
  rw [← h1 i, ← h2 i]
  exact Nat.zero_le _

prove_veil_invariant_goal initializer VotesBound using tr by
  obtain ⟨-, -, -, -, -, -, -, -, hm, hv, hl, -, hc, -, happ, -⟩ := htr
  subst hm hv hl hc
  intros
  exact (EtcdRaftVeil.Lemmas.sub_empty v).elim

prove_veil_invariant_goal initializer GrantsAreVotes using tr by
  obtain ⟨-, -, -, -, -, -, -, -, hm, hv, hl, -, hc, -, happ, -⟩ := htr
  subst hm hv hl hc
  intros
  exact (EtcdRaftVeil.Lemmas.sub_empty m).elim

prove_veil_invariant_goal initializer LeaderSync using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  intro h
  rw [← hrole i] at h
  have hR := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hR
  exact absurd h hR.2.1

prove_veil_invariant_goal initializer LeaderIsElected using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  intro h
  rw [← hrole i] at h
  have hR := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hR
  exact absurd h hR.2.1

prove_veil_invariant_goal initializer LeadersTermBound using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  subst hl
  exact (EtcdRaftVeil.Lemmas.sub_empty ld).elim

prove_veil_invariant_goal initializer LedOwner using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  subst hl
  exact (EtcdRaftVeil.Lemmas.sub_empty ld).elim

prove_veil_invariant_goal initializer LeadersHaveLed using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  subst hl
  exact (EtcdRaftVeil.Lemmas.sub_empty ld).elim

prove_veil_invariant_goal initializer LedHasLeader using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  intro h
  exact absurd (hled t).symm h

prove_veil_invariant_goal initializer AppendFromLeader using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  subst hm
  exact (EtcdRaftVeil.Lemmas.sub_empty m).elim

prove_veil_invariant_goal initializer LeaderLogIsLed using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  intro h
  rw [← hrole i] at h
  have hR := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hR
  exact absurd h hR.2.1

prove_veil_invariant_goal initializer RequestsFromLed using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  subst hm
  exact (EtcdRaftVeil.Lemmas.sub_empty m).elim

prove_veil_invariant_goal initializer LogFromLed using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  rw [hlog i, FromLed.iff]
  intro q h2
  simp at h2

prove_veil_invariant_goal initializer LedFromLed using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  rw [← hled t]
  rfl

prove_veil_invariant_goal initializer LogMatching using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  intro h1 hk _
  rw [hlog a] at hk
  simp at hk
  omega

prove_veil_invariant_goal initializer TermsPositive using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  intro h
  exact absurd (hled t).symm h

prove_veil_invariant_goal initializer LogTermsBound using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  rw [hlog i]
  cases k <;> simp [TermAt]

prove_veil_invariant_goal initializer LedSorted using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  intro hL
  rw [← hled t] at hL
  cases hL

prove_veil_invariant_goal initializer ReqFacts using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  subst hm
  exact (EtcdRaftVeil.Lemmas.sub_empty m).elim

prove_veil_invariant_goal initializer ReqUnique using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  subst hm
  exact (EtcdRaftVeil.Lemmas.sub_empty m).elim

prove_veil_invariant_goal initializer VoteHasReq using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  subst hv
  exact (EtcdRaftVeil.Lemmas.sub_empty v).elim

prove_veil_invariant_goal initializer CandLog using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  subst hm
  exact (EtcdRaftVeil.Lemmas.sub_empty m).elim

prove_veil_invariant_goal initializer LedExtendsReq using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  subst hl
  exact (EtcdRaftVeil.Lemmas.sub_empty ld).elim

prove_veil_invariant_goal initializer AckFacts using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  subst hm
  exact (EtcdRaftVeil.Lemmas.sub_empty m).elim

prove_veil_invariant_goal initializer AckedHeld using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  intro h
  have h1 := h.1
  rw [← hled t] at h1
  cases h1

prove_veil_invariant_goal initializer AckVote using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  intro v h
  have h1 := h.1
  rw [← hled t] at h1
  cases h1

prove_veil_invariant_goal initializer EarlyQuorum using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  subst hl
  exact (EtcdRaftVeil.Lemmas.sub_empty ld).elim

prove_veil_invariant_goal initializer ConfirmedIsLed using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  exact Or.inl (hcfi j).symm

prove_veil_invariant_goal initializer CommitRoot using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  subst hc
  exact (EtcdRaftVeil.Lemmas.sub_empty k).elim

prove_veil_invariant_goal initializer CommitSafety using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  subst hc
  exact (EtcdRaftVeil.Lemmas.sub_empty a).elim

prove_veil_invariant_goal initializer ConfirmedTermBound using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  rw [← hct i, ← hcft i]
  exact Nat.zero_le _

prove_veil_invariant_goal initializer CommitTermBound using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  subst hc
  exact (EtcdRaftVeil.Lemmas.sub_empty c).elim

prove_veil_invariant_goal initializer CommittedEntriesPreserved using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  exact Or.inl (hci i).symm

prove_veil_invariant_goal initializer CommitWithinLog using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  rw [← hci i]
  exact Nat.zero_le _

prove_veil_invariant_goal initializer AppliedCommitted using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  subst happ
  exact (EtcdRaftVeil.Lemmas.sub_empty a).elim

prove_veil_invariant_goal initializer StateMachineSafety using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  subst happ
  exact (EtcdRaftVeil.Lemmas.sub_empty a).elim

prove_veil_invariant_goal initializer LeaderCompleteness using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  subst hc
  exact (EtcdRaftVeil.Lemmas.sub_empty c).elim

prove_veil_invariant_goal initializer ConfirmedWithinLog using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  rw [← hcfi i]
  exact Nat.zero_le _

prove_veil_invariant_goal initializer ConfIsCommitted using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hcin, hcout, hcat, hlin, hlout, hlat, helat⟩ := htr
  grind

prove_veil_invariant_goal initializer LeaderConf using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hcin, hcout, hcat, hlin, hlout, hlat, helat⟩ := htr
  grind

prove_veil_invariant_goal initializer FirstRoot using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  subst hc
  exact (EtcdRaftVeil.Lemmas.sub_empty k).elim

prove_veil_invariant_goal initializer LedOld using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hcin, hcout, hcat, hlin, hlout, hlat, helat⟩ := htr
  grind

prove_veil_invariant_goal initializer LegalChain using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hcin, hcout, hcat, hlin, hlout, hlat, helat⟩ := htr
  grind

prove_veil_invariant_goal initializer ReadMsgsOld using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hcin, hcout, hcat, hlin, hlout, hlat, helat, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  first
    | (intro h; rw [hron] at h; exact absurd h (by decide))
    | (intro _ h; rw [hron] at h; exact absurd h (by decide))
    | (intros; simp_all)

prove_veil_invariant_goal initializer ReadFloorOld using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hcin, hcout, hcat, hlin, hlout, hlat, helat, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  first
    | (intro h; rw [hron] at h; exact absurd h (by decide))
    | (intro _ h; rw [hron] at h; exact absurd h (by decide))
    | (intros; simp_all)

prove_veil_invariant_goal initializer ReadFloorBound using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hcin, hcout, hcat, hlin, hlout, hlat, helat, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  first
    | (intro h; rw [hron] at h; exact absurd h (by decide))
    | (intro _ h; rw [hron] at h; exact absurd h (by decide))
    | (intros; simp_all)

prove_veil_invariant_goal initializer ReadIndexSafety using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hcin, hcout, hcat, hlin, hlout, hlat, helat, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  first
    | (intro h; rw [hrdone] at h; exact absurd h (by decide))
    | (intro _ h; rw [hrdone] at h; exact absurd h (by decide))
    | (intros; simp_all)

prove_veil_invariant_goal initializer ReadTermLed using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hcin, hcout, hcat, hlin, hlout, hlat, helat, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  first
    | (intro h; rw [hron] at h; exact absurd h (by decide))
    | (intro _ h; rw [hron] at h; exact absurd h (by decide))
    | (intros; simp_all)

prove_veil_invariant_goal initializer ReadFloorRooted using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hcin, hcout, hcat, hlin, hlout, hlat, helat, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  first
    | (intro h; rw [hron] at h; exact absurd h (by decide))
    | (intro _ h; rw [hron] at h; exact absurd h (by decide))
    | (intros; simp_all)

prove_veil_invariant_goal initializer ReadFirstRoot using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hcin, hcout, hcat, hlin, hlout, hlat, helat, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  first
    | (intro h; rw [hron] at h; exact absurd h (by decide))
    | (intro _ h; rw [hron] at h; exact absurd h (by decide))
    | (intros; simp_all)

prove_veil_invariant_goal initializer ReadRespBound using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, hcin, hcout, hcat, hlin, hlout, hlat, helat, hron, hrdone, hrterm, hridx, hrfloor, hrmsgs, hrresp⟩ := htr
  first
    | (intro h; rw [hron] at h; exact absurd h (by decide))
    | (intro _ h; rw [hron] at h; exact absurd h (by decide))
    | (intros; simp_all)

-- BecomeCandidate

prove_veil_invariant_goal BecomeCandidate ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LeaderSync using wp by
  have hLeaderSync := hinv.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate AckedHeld using wp by
  have hAckedHeld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate CommitRoot using wp by
  have hCommitRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate CommitWithinLog using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate ConfIsCommitted using wp by
  have hConfIsCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LeaderConf using wp by
  have hLeaderConf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate FirstRoot using wp by
  have hFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LedOld using wp by
  have hLedOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LegalChain using wp by
  have hLegalChain := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate ReadMsgsOld using wp by
  have hReadMsgsOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate ReadFloorOld using wp by
  have hReadFloorOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate ReadFloorBound using wp by
  have hReadFloorBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate ReadIndexSafety using wp by
  have hReadIndexSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate ReadTermLed using wp by
  have hReadTermLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate ReadFloorRooted using wp by
  have hReadFloorRooted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate ReadFirstRoot using wp by
  have hReadFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate ReadRespBound using wp by
  have hReadRespBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- BecomeFollower

prove_veil_invariant_goal BecomeFollower ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LeaderSync using wp by
  have hLeaderSync := hinv.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower AckedHeld using wp by
  have hAckedHeld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower CommitRoot using wp by
  have hCommitRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower CommitWithinLog using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower ConfIsCommitted using wp by
  have hConfIsCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LeaderConf using wp by
  have hLeaderConf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower FirstRoot using wp by
  have hFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LedOld using wp by
  have hLedOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LegalChain using wp by
  have hLegalChain := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower ReadMsgsOld using wp by
  have hReadMsgsOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower ReadFloorOld using wp by
  have hReadFloorOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower ReadFloorBound using wp by
  have hReadFloorBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower ReadIndexSafety using wp by
  have hReadIndexSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower ReadTermLed using wp by
  have hReadTermLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower ReadFloorRooted using wp by
  have hReadFloorRooted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower ReadFirstRoot using wp by
  have hReadFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower ReadRespBound using wp by
  have hReadRespBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- SwitchConf

prove_goal_unregistered SwitchConf ElectionSafety by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf OneVotePerTerm by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf VoteTermBound by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf VotesBound by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf GrantsAreVotes by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf LeaderSync by
  have hES := hinv.1
  have hLSy := hinv.2.2.2.2.2.1
  have hLIE := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  rename_i c h1 h2 hca h4 hck hc hsub hld hok j hj
  by_cases hij : i = j
  · subst hij
    simp only [hj, and_self, and_true, true_and, if_true, implies_true]
  · have key : ¬ (st.currentTerm j = st.currentTerm i ∧ st.role i = Leader) :=
      fun ⟨ht, hri⟩ => hij (hES _ _ (hLIE i hri) (hLIE j hj) ht.symm)
    simp only [hij, key, if_false]
    exact hLSy j hj

prove_goal_unregistered SwitchConf LeaderIsElected by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf LeadersTermBound by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf LedOwner by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf LeadersHaveLed by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf LedHasLeader by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf AppendFromLeader by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf LeaderLogIsLed by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf RequestsFromLed by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf LogFromLed by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf LedFromLed by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf LogMatching by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf TermsPositive by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf LogTermsBound by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf LedSorted by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf ReqFacts by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf ReqUnique by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf VoteHasReq by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf CandLog by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf LedExtendsReq by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf AckFacts by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf AckedHeld by
  have hAckedHeld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf AckVote by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf EarlyQuorum by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf ConfirmedIsLed by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf CommitRoot by
  have hCommitRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf CommitSafety by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf ConfirmedTermBound by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf CommitTermBound by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf CommittedEntriesPreserved by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf CommitWithinLog by
  have hCommitWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf AppliedCommitted by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf StateMachineSafety by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf LeaderCompleteness by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf ConfirmedWithinLog by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf ConfIsCommitted by
  have hSMS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCC := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  rename_i c h1 h2 hca h4 hck hc hsub hld hok j
  by_cases hij : i = j
  · subst hij
    simp only [if_true]
    right
    have hag : c.entries.take a = (st.log i).take a := by rw [← subSeq_one, ← subSeq_one]; exact hsub
    refine ⟨c, hck, hc, fun s => ?_⟩
    have hold : ∀ s, st.cIn i s = (cOf th.initV th.chAdd th.chRemove th.chJoint th.chLeave c.entries (st.confAt i)).inn s ∧
        st.cOut i s = (cOf th.initV th.chAdd th.chRemove th.chJoint th.chLeave c.entries (st.confAt i)).out s := by
      rcases hCC i with ⟨h0, hinit⟩ | ⟨k0, hk0, hk0c, hk0s⟩
      · intro s; rw [h0]; exact hinit s
      · intro s
        have htk : k0.entries.take (st.confAt i) = c.entries.take (st.confAt i) := by
          rcases hSMS k0 c hk0c hc with h | h
          · exact MemberCore.prefix_take _ _ _ ((isPrefix_iff _ _).1 h) hk0
          · exact (MemberCore.prefix_take _ _ _ ((isPrefix_iff _ _).1 h) (by omega)).symm
        have e : cOf th.initV th.chAdd th.chRemove th.chJoint th.chLeave c.entries (st.confAt i) = cOf th.initV th.chAdd th.chRemove th.chJoint th.chLeave k0.entries (st.confAt i) :=
          (MemberCore.confOf_congr Entry.isConf (chgOf th.chAdd th.chRemove th.chJoint th.chLeave)
            (conf0 th.initV) k0.entries c.entries (st.confAt i) htk).symm
        rw [e]; exact hk0s s
    rw [switch_conf th.initV th.chAdd th.chRemove th.chJoint th.chLeave (st.log i) c.entries (st.confAt i) a (st.cIn i) (st.cOut i) hca hck hag hok hold]
    exact ⟨rfl, rfl⟩
  · simp only [hij, if_false]
    exact hCC j

prove_goal_unregistered SwitchConf LeaderConf by
  have hLSy := hinv.2.2.2.2.2.1
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLCf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  rename_i c h1 h2 hca h4 hck hc hsub hld hok t A hA
  by_cases hcond : t = st.currentTerm i ∧ st.role i = Leader
  · obtain ⟨ht, hri⟩ := hcond
    subst ht
    simp only [hri, and_self, and_true, true_and, if_true]
    obtain ⟨hsy1, hsy2⟩ := hLSy i hri
    obtain ⟨hl1, hl2, hl3, hl4, hl5, hl6⟩ := hLCf _ A hA
    obtain ⟨L, hL, hpre⟩ := (anyPrefix_iff _ _).1 (hLLL i hri)
    rw [hA] at hL; cases hL
    have haA : a ≤ A.length := by have := hpre.length_le; omega
    have hagA : A.take a = (st.log i).take a := (MemberCore.prefix_take _ _ a hpre (by omega)).symm
    obtain ⟨c2, hc2t, hc2l, hc2, hc2s⟩ := hld hri
    have hold : ∀ s, st.cIn i s = (cOf th.initV th.chAdd th.chRemove th.chJoint th.chLeave A (st.confAt i)).inn s ∧
        st.cOut i s = (cOf th.initV th.chAdd th.chRemove th.chJoint th.chLeave A (st.confAt i)).out s := by
      intro s; rw [hsy1, (hsy2 s).1, (hsy2 s).2]; exact hl3 s
    have hsw := switch_conf th.initV th.chAdd th.chRemove th.chJoint th.chLeave (st.log i) A (st.confAt i) a (st.cIn i) (st.cOut i) hca haA hagA hok hold
    refine ⟨haA, by omega, fun s => by rw [hsw]; exact ⟨rfl, rfl⟩, ?_,
      Or.inr ⟨c2.entries, c2.term, ⟨c2, hc2, rfl, rfl⟩, hc2t, hc2l, ?_⟩, hl6⟩
    · intro p q hp hq hql hcp hcq
      exact hl4 p q (by omega) hq hql hcp hcq
    · rw [hagA, ← subSeq_one, ← subSeq_one]; exact hc2s
  · simp only [hcond, if_false]
    exact hLCf t A hA

prove_goal_unregistered SwitchConf FirstRoot by
  have hFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf LedOld by
  have hLedOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf LegalChain by
  have hLegalChain := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf ReadMsgsOld by
  have hReadMsgsOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf ReadFloorOld by
  have hReadFloorOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf ReadFloorBound by
  have hReadFloorBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf ReadIndexSafety by
  have hReadIndexSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf ReadTermLed by
  have hReadTermLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf ReadFloorRooted by
  have hReadFloorRooted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf ReadFirstRoot by
  have hReadFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_goal_unregistered SwitchConf ReadRespBound by
  have hReadRespBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- StartElection

prove_veil_invariant_goal StartElection ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection GrantsAreVotes using wp by
  have hGV := hinv.2.2.2.2.1
  clear hinv
  intros
  simp only [EtcdRaftVeil.Lemmas.mem_iff, EtcdRaftVeil.Lemmas.contains_insert_iff] at *
  repeat' split
  all_goals grind only

prove_veil_invariant_goal StartElection LeaderSync using wp by
  have hLeaderSync := hinv.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LedOwner using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection ReqFacts using wp by
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLogTB := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole a ha c u li lt heq
  rw [EtcdRaftVeil.Lemmas.mem_insert] at ha
  rcases ha with rfl | ha
  · injection heq with h1 h2 h3 h4
    subst h1 h2 h3 h4
    rw [EtcdRaftVeil.Lemmas.ifPos rfl]
    exact ⟨Nat.le_refl _, reqOk_of_log _ _ _ (hLFL i) (Nat.lt_succ_of_le (hLogTB i _))⟩
  · obtain ⟨h1, h2⟩ := hRF a ha c u li lt heq
    refine ⟨?_, h2⟩
    by_cases hic : i = c
    · subst hic; rw [EtcdRaftVeil.Lemmas.ifPos rfl]; omega
    · rw [EtcdRaftVeil.Lemmas.ifNeg hic]; exact h1

prove_veil_invariant_goal StartElection ReqUnique using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection CandLog using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LedExtendsReq using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection AckedHeld using wp by
  have hAH := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole n t A c hack
  have hack' := Acked.of_insert _ _ _ _ _ _ _ _ (fun _ _ _ _ h => by cases h) hack
  rcases hAH n t A c hack' with h | h
  · exact Or.inl h
  · right
    by_cases hin : i = n
    · subst hin; rw [EtcdRaftVeil.Lemmas.ifPos rfl]; exact LostIn.mono_hi _ _ _ _ _ _ h (by omega)
    · rw [EtcdRaftVeil.Lemmas.ifNeg hin]; exact h

prove_veil_invariant_goal StartElection AckVote using wp by
  have hRF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hVHR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAV := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro v hrole n t A c hack hv hvn htv li lt hreq
  rcases (EtcdRaftVeil.Lemmas.contains_insert_iff _ _ _).1 hreq with h | h
  · exfalso
    injection h with h1 h2
    obtain ⟨m, hm, li', lt', rfl⟩ := hVHR v hv
    have := (hRF _ hm v.cand v.term li' lt' rfl).1
    rw [h1, h2] at this
    omega
  · exact hAV v n t A c (Acked.of_insert _ _ _ _ _ _ _ _ (fun _ _ _ _ h => by cases h) hack) hv hvn htv li lt h

prove_veil_invariant_goal StartElection EarlyQuorum using wp by
  have hLTB := hinv.2.2.2.2.2.2.2.1
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ld hrole hld B hB
  refine MemberCore.IsQ.mono _ _ _ ?_ (hEQ ld hld B hB)
  intro n hn
  simp only [decide_eq_true_eq] at hn ⊢
  refine ⟨hn.1, Early.of_insert _ _ _ _ _ _ _ (fun _ _ _ _ h => by cases h) ?_ hn.2⟩
  intro li lt h
  injection h with h1 h2
  have := hLTB ld hld
  rw [← h2, ← h1] at this
  omega

prove_veil_invariant_goal StartElection ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection CommitRoot using wp by
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro k
  intros
  rename_i hk
  obtain ⟨h1, r, h2, h3, h4, h5⟩ := hCR k hk
  exact ⟨h1, r, h2, Root.mono _ _ _ _ _ _ _ _ _ _ _ _ (fun a ha => (EtcdRaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr ha))
    (fun a ha => ha) (LedGrows.refl _) h3, h4, h5⟩

prove_veil_invariant_goal StartElection CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection CommitWithinLog using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection ConfIsCommitted using wp by
  have hConfIsCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LeaderConf using wp by
  have hLeaderConf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection FirstRoot using wp by
  have hFR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro k
  intros
  rename_i hk p hp
  exact firstRoot_mono _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a ha => (EtcdRaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr ha))
    (fun a ha => ha) (LedGrows.refl _) (hFR k hk p hp)

prove_veil_invariant_goal StartElection LedOld using wp by
  have hLedOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LegalChain using wp by
  have hLegalChain := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection ReadMsgsOld using wp by
  have hReadMsgsOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection ReadFloorOld using wp by
  have hReadFloorOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection ReadFloorBound using wp by
  have hReadFloorBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection ReadIndexSafety using wp by
  have hReadIndexSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection ReadTermLed using wp by
  have hReadTermLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection ReadFloorRooted using wp by
  have hReadFloorRooted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection ReadFirstRoot using wp by
  have hReadFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection ReadRespBound using wp by
  have hReadRespBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- AdoptTerm

prove_veil_invariant_goal AdoptTerm ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LeaderSync using wp by
  have hLeaderSync := hinv.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LedOwner using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm CandLog using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm AckedHeld using wp by
  have hAH := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hlt k' hk' hge n t A c hack'
  rcases hAH n t A c hack' with h | h
  · exact Or.inl h
  · right
    by_cases hin : i = n
    · subst hin; rw [EtcdRaftVeil.Lemmas.ifPos rfl]; exact LostIn.mono_hi _ _ _ _ _ _ h (by omega)
    · rw [EtcdRaftVeil.Lemmas.ifNeg hin]; exact h

prove_veil_invariant_goal AdoptTerm AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm CommitRoot using wp by
  have hCommitRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm CommitWithinLog using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm ConfIsCommitted using wp by
  have hConfIsCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LeaderConf using wp by
  have hLeaderConf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm FirstRoot using wp by
  have hFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LedOld using wp by
  have hLedOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LegalChain using wp by
  have hLegalChain := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm ReadMsgsOld using wp by
  have hReadMsgsOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm ReadFloorOld using wp by
  have hReadFloorOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm ReadFloorBound using wp by
  have hReadFloorBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm ReadIndexSafety using wp by
  have hReadIndexSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm ReadTermLed using wp by
  have hReadTermLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm ReadFloorRooted using wp by
  have hReadFloorRooted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm ReadFirstRoot using wp by
  have hReadFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm ReadRespBound using wp by
  have hReadRespBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- CastVote

prove_veil_invariant_goal CastVote ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  have hVoteTermBound := hinv.2.2.1
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote VotesBound using wp by
  have hVT := hinv.2.2.1
  have hVB := hinv.2.2.2.1
  clear hinv
  intro a hne x hx hmay hb
  rw [EtcdRaftVeil.Lemmas.mem_insert] at hb
  rcases hb with rfl | hb
  · simp
  · have h1 := hVB a hb
    have h2 := hVT a.voter
    by_cases h : i = a.voter
    · subst h; simp; omega
    · simp [h]; exact h1

prove_veil_invariant_goal CastVote GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote LeaderSync using wp by
  have hLeaderSync := hinv.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote AckedHeld using wp by
  have hAckedHeld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote AckVote using wp by
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRU := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAH := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAV := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro v hne x hx hmay n t A c1 hack hv hvn htv li lt hreq
  rw [EtcdRaftVeil.Lemmas.mem_insert] at hv
  rcases hv with rfl | hv
  · subst hvn
    cases x with
    | vote src term lli llt =>
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hmay
      obtain ⟨rfl, rfl, hup⟩ := hmay
      obtain ⟨rfl, rfl⟩ := hRU _ hx _ hreq src (st.currentTerm i) lli llt li lt rfl rfl
      have hcA := Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' i i' t x' rfl).2.2) hack
      refine vote_step st.ledLog (st.log i) A t c1 lli llt (st.currentTerm i) hack.1 hack.2.1 hcA
        hack.2.2.1 (hAH i t A c1 hack) (hLFL i) hLS (hRF _ hx src _ lli llt rfl).2 ?_
      rcases hup with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, h2⟩
    | _ => simp at hmay
  · exact hAV v n t A c1 hack hv hvn htv li lt hreq

prove_veil_invariant_goal CastVote EarlyQuorum using wp by
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ld
  intros
  rename_i hld B hB
  refine MemberCore.IsQ.mono _ _ _ ?_ (hEQ ld hld B hB)
  intro n hn
  simp only [decide_eq_true_eq] at hn ⊢
  exact ⟨(EtcdRaftVeil.Lemmas.contains_insert_iff _ _ _).2 (Or.inr hn.1), hn.2⟩

prove_veil_invariant_goal CastVote ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote CommitRoot using wp by
  have hCommitRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote CommitWithinLog using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote ConfIsCommitted using wp by
  have hConfIsCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote LeaderConf using wp by
  have hLeaderConf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote FirstRoot using wp by
  have hFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote LedOld using wp by
  have hLedOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote LegalChain using wp by
  have hLegalChain := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote ReadMsgsOld using wp by
  have hReadMsgsOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote ReadFloorOld using wp by
  have hReadFloorOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote ReadFloorBound using wp by
  have hReadFloorBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote ReadIndexSafety using wp by
  have hReadIndexSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote ReadTermLed using wp by
  have hReadTermLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote ReadFloorRooted using wp by
  have hReadFloorRooted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote ReadFirstRoot using wp by
  have hReadFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CastVote ReadRespBound using wp by
  have hReadRespBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- GrantVote

prove_veil_invariant_goal GrantVote ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote GrantsAreVotes using wp by
  have hGV := hinv.2.2.2.2.1
  clear hinv
  intro ha hv hc m hm
  rw [EtcdRaftVeil.Lemmas.mem_insert] at hm
  rcases hm with rfl | hm
  · subst hv
    cases a
    exact ha
  · exact hGV m hm

prove_veil_invariant_goal GrantVote LeaderSync using wp by
  have hLeaderSync := hinv.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote AckedHeld using wp by
  have hAH := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  rename_i n t A c hack
  exact hAH n t A c (Acked.of_insert _ _ _ _ _ _ _ _ (fun _ _ _ _ h => by cases h) hack)

prove_veil_invariant_goal GrantVote AckVote using wp by
  have hAV := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro v
  intros
  rename_i n t A c hack hv hvn htv li lt hreq
  rcases (EtcdRaftVeil.Lemmas.contains_insert_iff _ _ _).1 hreq with h | h
  · cases h
  · exact hAV v n t A c (Acked.of_insert _ _ _ _ _ _ _ _ (fun _ _ _ _ h => by cases h) hack) hv hvn htv li lt h

prove_veil_invariant_goal GrantVote EarlyQuorum using wp by
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ld
  intros
  rename_i hld B hB
  refine MemberCore.IsQ.mono _ _ _ ?_ (hEQ ld hld B hB)
  intro n hn
  simp only [decide_eq_true_eq] at hn ⊢
  exact ⟨hn.1, Early.of_insert _ _ _ _ _ _ _ (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h) hn.2⟩

prove_veil_invariant_goal GrantVote ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote CommitRoot using wp by
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro k
  intros
  rename_i hk
  obtain ⟨h1, r, h2, h3, h4, h5⟩ := hCR k hk
  exact ⟨h1, r, h2, Root.mono _ _ _ _ _ _ _ _ _ _ _ _ (fun a ha => (EtcdRaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr ha))
    (fun a ha => ha) (LedGrows.refl _) h3, h4, h5⟩

prove_veil_invariant_goal GrantVote CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote CommitWithinLog using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote ConfIsCommitted using wp by
  have hConfIsCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LeaderConf using wp by
  have hLeaderConf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote FirstRoot using wp by
  have hFR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro k
  intros
  rename_i hk p hp
  exact firstRoot_mono _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a ha => (EtcdRaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr ha))
    (fun a ha => ha) (LedGrows.refl _) (hFR k hk p hp)

prove_veil_invariant_goal GrantVote LedOld using wp by
  have hLedOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LegalChain using wp by
  have hLegalChain := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote ReadMsgsOld using wp by
  have hReadMsgsOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote ReadFloorOld using wp by
  have hReadFloorOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote ReadFloorBound using wp by
  have hReadFloorBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote ReadIndexSafety using wp by
  have hReadIndexSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote ReadTermLed using wp by
  have hReadTermLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote ReadFloorRooted using wp by
  have hReadFloorRooted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote ReadFirstRoot using wp by
  have hReadFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote ReadRespBound using wp by
  have hReadRespBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- BecomeLeader

prove_veil_invariant_goal BecomeLeader ElectionSafety using wp by
  have hES := hinv.1
  have hLHL := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro a b hrole hnone hq hone hcb ha hb hterm
  have key := winner_none st.leaders st.ledLog i (st.currentTerm i) hLHL hnone
  rw [EtcdRaftVeil.Lemmas.mem_insert] at ha hb
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · rfl
  · exact (key b hb (by simpa using hterm.symm)).symm
  · exact key a ha (by simpa using hterm)
  · exact hES a b ha hb hterm

prove_veil_invariant_goal BecomeLeader OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader LeaderSync using wp by
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLSy := hinv.2.2.2.2.2.1
  clear hinv
  intro hrole hnone hq hone hcb j hj
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  by_cases hji : i = j
  · subst hji
    simp
  · simp only [hji, ite_false] at hj
    have hj := hj not_false
    have hne : ¬ st.currentTerm i = st.currentTerm j := by
      intro h
      have := hLLL j hj
      rw [← h, hnone] at this
      simp at this
    simp only [hji, hne, ite_false]
    exact hLSy j hj

prove_veil_invariant_goal BecomeLeader LeaderIsElected using wp by
  have hLE := hinv.2.2.2.2.2.2.1
  clear hinv
  intro hrole hnone hq hone hcb j hj
  apply (EtcdRaftVeil.Lemmas.contains_insert_iff _ _ _).2
  by_cases h : i = j
  · subst h; exact Or.inl rfl
  · exact Or.inr (hLE j (hj h))

prove_veil_invariant_goal BecomeLeader LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader LedOwner using wp by
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hLHL := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro a hrole hnone hq hone hcb ha hterm
  rw [EtcdRaftVeil.Lemmas.mem_insert] at ha
  rcases ha with rfl | ha
  · simp [isPrefix_refl]
  · by_cases hc : st.currentTerm i = a.term
    · exact absurd (hc ▸ hnone) (hLHL a ha)
    · rw [EtcdRaftVeil.Lemmas.ifNeg hc]; exact hLO a ha hterm

prove_veil_invariant_goal BecomeLeader LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader LeaderLogIsLed using wp by
  have hLE := hinv.2.2.2.2.2.2.1
  have hLHL := hinv.2.2.2.2.2.2.2.2.2.1
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hnone hq hone hcb j hj
  by_cases hij : i = j
  · subst hij; simp [isPrefix_refl]
  · by_cases hc : st.currentTerm i = st.currentTerm j
    · exact absurd (hc ▸ hnone) (hLHL _ (hLE j (hj hij)))
    · rw [EtcdRaftVeil.Lemmas.ifNeg hc]; exact hLLL j (hj hij)

prove_veil_invariant_goal BecomeLeader RequestsFromLed using wp by
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLHL := hinv.2.2.2.2.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hnone hq hone hcb
  have key := winner_none st.leaders st.ledLog i (st.currentTerm i) hLHL hnone
  have hsame : ∀ L, st.ledLog (st.currentTerm i) = some L → L = st.log i := fun L hL => by rw [hnone] at hL; cases hL
  have hext := led_ext_set st.ledLog (st.currentTerm i) (st.log i) (fun L hL => by rw [hsame L hL]; exact List.prefix_refl _)
  intro a ha
  have h := hRFL a ha
  cases a with
  | append src dst term p pt es c =>
    dsimp only at h ⊢
    by_cases hc : st.currentTerm i = term
    · subst hc
      rw [EtcdRaftVeil.Lemmas.ifPos rfl]
      cases hL : st.ledLog (st.currentTerm i) with
      | none => simp [hL] at h
      | some l => rw [hL, hsame l hL] at h; exact h
    · rw [EtcdRaftVeil.Lemmas.ifNeg hc]; exact h
  | _ => rfl

prove_veil_invariant_goal BecomeLeader LogFromLed using wp by
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLHL := hinv.2.2.2.2.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hnone hq hone hcb
  have key := winner_none st.leaders st.ledLog i (st.currentTerm i) hLHL hnone
  have hsame : ∀ L, st.ledLog (st.currentTerm i) = some L → L = st.log i := fun L hL => by rw [hnone] at hL; cases hL
  have hext := led_ext_set st.ledLog (st.currentTerm i) (st.log i) (fun L hL => by rw [hsame L hL]; exact List.prefix_refl _)
  intro j
  exact FromLed.mono st.ledLog _ _ hext (hLFL j)

prove_veil_invariant_goal BecomeLeader LedFromLed using wp by
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLHL := hinv.2.2.2.2.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hnone hq hone hcb
  have key := winner_none st.leaders st.ledLog i (st.currentTerm i) hLHL hnone
  have hsame : ∀ L, st.ledLog (st.currentTerm i) = some L → L = st.log i := fun L hL => by rw [hnone] at hL; cases hL
  have hext := led_ext_set st.ledLog (st.currentTerm i) (st.log i) (fun L hL => by rw [hsame L hL]; exact List.prefix_refl _)
  intro t
  refine (optAll_iff _ _).2 ?_
  intro L hL
  apply FromLed.mono st.ledLog _ _ hext
  by_cases hc : st.currentTerm i = t
  · rw [EtcdRaftVeil.Lemmas.ifPos hc] at hL; cases hL; exact hLFL i
  · rw [EtcdRaftVeil.Lemmas.ifNeg hc] at hL; exact (optAll_iff _ _).1 (hLedFL t) L hL

prove_veil_invariant_goal BecomeLeader LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader TermsPositive using wp by
  have hGV := hinv.2.2.2.2.1
  have hTP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hVHR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro hrole hnone hq hone hcb t ht | intro t hrole hnone hq hone hcb ht
  by_cases hc : st.currentTerm i = t
  · subst hc
    obtain ⟨n, hn, -⟩ := MemberCore.IsQ.inter _ _ _ hq hq
    have hj : TSet.contains ({ voter := n, term := st.currentTerm i, cand := i } : Vote server) st.votes = true := by
      by_cases hni : n = i
      · subst hni; simpa using hn
      · simp only [hni, ite_false] at hn
        simpa using hGV _ hn
    obtain ⟨m, hm, li, lt, heq⟩ := hVHR _ hj
    have := (hRF m hm i (st.currentTerm i) li lt heq).2.1
    omega
  · rw [EtcdRaftVeil.Lemmas.ifNeg hc] at ht; exact hTP t ht

prove_veil_invariant_goal BecomeLeader LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader LedSorted using wp by
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLHL := hinv.2.2.2.2.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hTP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLogTB := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hnone hq hone hcb
  have key := winner_none st.leaders st.ledLog i (st.currentTerm i) hLHL hnone
  have hsame : ∀ L, st.ledLog (st.currentTerm i) = some L → L = st.log i := fun L hL => by rw [hnone] at hL; cases hL
  have hg := ledGrows_set (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) hsame
  have hack : ∀ n t A c, Acked st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
      (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n t A c →
      Acked st.msgs st.leaders st.ledLog n t A c :=
    fun n t A c h => Acked.of_becomeLeader _ _ _ i _ _ n t A c hnone (fun j i' x hx => (hAF _ hx j i' _ x rfl).2.2) h
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hE : ∀ n cand u, Early st.msgs st.leaders st.ledLog n cand u →
      Early st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
        (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n cand u := by
    intro n cand u he t A c ha htu li lt hr
    have ha' := hack n t A c ha
    rcases he t A c ha' htu li lt hr with h1 | h1
    · exact Or.inl (Covers.grows _ _ _ _ _ _ hg (hlen n t A c ha') h1)
    · exact Or.inr (LostIn.grows _ _ _ _ _ _ hg (hlen n t A c ha') (hLS t A ha'.1).2 h1)
  intro t L hL
  by_cases hc : st.currentTerm i = t
  · rw [EtcdRaftVeil.Lemmas.ifPos hc] at hL; cases hL
    rw [← hc]; exact sorted_of_fromLed st.ledLog _ _ (hLFL i) hLS (hLogTB i)
  · rw [EtcdRaftVeil.Lemmas.ifNeg hc] at hL; exact hLS t L hL

prove_veil_invariant_goal BecomeLeader ReqFacts using wp by
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLHL := hinv.2.2.2.2.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hTP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (a : Msg server value) hrole hnone hq hone hcb | intro hrole hnone hq hone hcb (a : Msg server value)
  have key := winner_none st.leaders st.ledLog i (st.currentTerm i) hLHL hnone
  have hsame : ∀ L, st.ledLog (st.currentTerm i) = some L → L = st.log i := fun L hL => by rw [hnone] at hL; cases hL
  have hg := ledGrows_set (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) hsame
  have hack : ∀ n t A c, Acked st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
      (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n t A c →
      Acked st.msgs st.leaders st.ledLog n t A c :=
    fun n t A c h => Acked.of_becomeLeader _ _ _ i _ _ n t A c hnone (fun j i' x hx => (hAF _ hx j i' _ x rfl).2.2) h
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hE : ∀ n cand u, Early st.msgs st.leaders st.ledLog n cand u →
      Early st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
        (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n cand u := by
    intro n cand u he t A c ha htu li lt hr
    have ha' := hack n t A c ha
    rcases he t A c ha' htu li lt hr with h1 | h1
    · exact Or.inl (Covers.grows _ _ _ _ _ _ hg (hlen n t A c ha') h1)
    · exact Or.inr (LostIn.grows _ _ _ _ _ _ hg (hlen n t A c ha') (hLS t A ha'.1).2 h1)
  intro ha c u li lt heq
  obtain ⟨h1, h2⟩ := hRF a ha c u li lt heq
  exact ⟨h1, ReqOk.grows _ _ _ _ _ hg h2⟩

prove_veil_invariant_goal BecomeLeader ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader LedExtendsReq using wp by
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLHL := hinv.2.2.2.2.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hTP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLER := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (ld : Elected server) hrole hnone hq hone hcb | intro hrole hnone hq hone hcb (ld : Elected server)
  have key := winner_none st.leaders st.ledLog i (st.currentTerm i) hLHL hnone
  have hsame : ∀ L, st.ledLog (st.currentTerm i) = some L → L = st.log i := fun L hL => by rw [hnone] at hL; cases hL
  have hg := ledGrows_set (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) hsame
  have hack : ∀ n t A c, Acked st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
      (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n t A c →
      Acked st.msgs st.leaders st.ledLog n t A c :=
    fun n t A c h => Acked.of_becomeLeader _ _ _ i _ _ n t A c hnone (fun j i' x hx => (hAF _ hx j i' _ x rfl).2.2) h
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hE : ∀ n cand u, Early st.msgs st.leaders st.ledLog n cand u →
      Early st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
        (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n cand u := by
    intro n cand u he t A c ha htu li lt hr
    have ha' := hack n t A c ha
    rcases he t A c ha' htu li lt hr with h1 | h1
    · exact Or.inl (Covers.grows _ _ _ _ _ _ hg (hlen n t A c ha') h1)
    · exact Or.inr (LostIn.grows _ _ _ _ _ _ hg (hlen n t A c ha') (hLS t A ha'.1).2 h1)
  intro hld m hm li lt heq L hL
  by_cases hc : st.currentTerm i = ld.term
  · rw [EtcdRaftVeil.Lemmas.ifPos hc] at hL; cases hL
    have hsrv : ld.server = i := by
      rw [EtcdRaftVeil.Lemmas.mem_insert] at hld
      rcases hld with rfl | hld
      · rfl
      · exact key ld hld hc.symm
    obtain ⟨h1, h2⟩ := hCL m hm i (st.currentTerm i) li lt (by rw [heq, hsrv, hc]) rfl hnone
    exact ⟨by omega, h2⟩
  · rw [EtcdRaftVeil.Lemmas.ifNeg hc] at hL
    rw [EtcdRaftVeil.Lemmas.mem_insert] at hld
    rcases hld with rfl | hld
    · exact absurd rfl hc
    · exact hLER ld hld m hm li lt heq L hL

prove_veil_invariant_goal BecomeLeader AckFacts using wp by
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLHL := hinv.2.2.2.2.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hTP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (a : Msg server value) hrole hnone hq hone hcb | intro hrole hnone hq hone hcb (a : Msg server value)
  have key := winner_none st.leaders st.ledLog i (st.currentTerm i) hLHL hnone
  have hsame : ∀ L, st.ledLog (st.currentTerm i) = some L → L = st.log i := fun L hL => by rw [hnone] at hL; cases hL
  have hg := ledGrows_set (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) hsame
  have hack : ∀ n t A c, Acked st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
      (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n t A c →
      Acked st.msgs st.leaders st.ledLog n t A c :=
    fun n t A c h => Acked.of_becomeLeader _ _ _ i _ _ n t A c hnone (fun j i' x hx => (hAF _ hx j i' _ x rfl).2.2) h
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hE : ∀ n cand u, Early st.msgs st.leaders st.ledLog n cand u →
      Early st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
        (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n cand u := by
    intro n cand u he t A c ha htu li lt hr
    have ha' := hack n t A c ha
    rcases he t A c ha' htu li lt hr with h1 | h1
    · exact Or.inl (Covers.grows _ _ _ _ _ _ hg (hlen n t A c ha') h1)
    · exact Or.inr (LostIn.grows _ _ _ _ _ _ hg (hlen n t A c ha') (hLS t A ha'.1).2 h1)
  intro ha j i' t x heq
  obtain ⟨h1, h2, L, hL, hx⟩ := hAF a ha j i' t x heq
  obtain ⟨es, hL', _⟩ := hg t L hL
  exact ⟨(EtcdRaftVeil.Lemmas.contains_insert_iff _ _ _).2 (Or.inr h1), h2, L ++ es, hL', by simp; omega⟩

prove_veil_invariant_goal BecomeLeader AckedHeld using wp by
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLHL := hinv.2.2.2.2.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hTP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAH := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hnone hq hone hcb
  have key := winner_none st.leaders st.ledLog i (st.currentTerm i) hLHL hnone
  have hsame : ∀ L, st.ledLog (st.currentTerm i) = some L → L = st.log i := fun L hL => by rw [hnone] at hL; cases hL
  have hg := ledGrows_set (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) hsame
  have hack : ∀ n t A c, Acked st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
      (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n t A c →
      Acked st.msgs st.leaders st.ledLog n t A c :=
    fun n t A c h => Acked.of_becomeLeader _ _ _ i _ _ n t A c hnone (fun j i' x hx => (hAF _ hx j i' _ x rfl).2.2) h
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hE : ∀ n cand u, Early st.msgs st.leaders st.ledLog n cand u →
      Early st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
        (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n cand u := by
    intro n cand u he t A c ha htu li lt hr
    have ha' := hack n t A c ha
    rcases he t A c ha' htu li lt hr with h1 | h1
    · exact Or.inl (Covers.grows _ _ _ _ _ _ hg (hlen n t A c ha') h1)
    · exact Or.inr (LostIn.grows _ _ _ _ _ _ hg (hlen n t A c ha') (hLS t A ha'.1).2 h1)
  intro n t A c h
  have h' := hack n t A c h
  rcases hAH n t A c h' with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (LostIn.grows _ _ _ _ _ _ hg (hlen n t A c h') (hLS t A h'.1).2 h1)

prove_veil_invariant_goal BecomeLeader AckVote using wp by
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLHL := hinv.2.2.2.2.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hTP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAV := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (v : Vote server) hrole hnone hq hone hcb | intro hrole hnone hq hone hcb (v : Vote server)
  have key := winner_none st.leaders st.ledLog i (st.currentTerm i) hLHL hnone
  have hsame : ∀ L, st.ledLog (st.currentTerm i) = some L → L = st.log i := fun L hL => by rw [hnone] at hL; cases hL
  have hg := ledGrows_set (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) hsame
  have hack : ∀ n t A c, Acked st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
      (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n t A c →
      Acked st.msgs st.leaders st.ledLog n t A c :=
    fun n t A c h => Acked.of_becomeLeader _ _ _ i _ _ n t A c hnone (fun j i' x hx => (hAF _ hx j i' _ x rfl).2.2) h
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hE : ∀ n cand u, Early st.msgs st.leaders st.ledLog n cand u →
      Early st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
        (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n cand u := by
    intro n cand u he t A c ha htu li lt hr
    have ha' := hack n t A c ha
    rcases he t A c ha' htu li lt hr with h1 | h1
    · exact Or.inl (Covers.grows _ _ _ _ _ _ hg (hlen n t A c ha') h1)
    · exact Or.inr (LostIn.grows _ _ _ _ _ _ hg (hlen n t A c ha') (hLS t A ha'.1).2 h1)
  intro n t A c h hv hvn htv li lt hreq
  have h' := hack n t A c h
  rcases hAV v n t A c h' hv hvn htv li lt hreq with h1 | h1
  · exact Or.inl (Covers.grows _ _ _ _ _ _ hg (hlen n t A c h') h1)
  · exact Or.inr (LostIn.grows _ _ _ _ _ _ hg (hlen n t A c h') (hLS t A h'.1).2 h1)

prove_veil_invariant_goal BecomeLeader EarlyQuorum using wp by
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLHL := hinv.2.2.2.2.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hTP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAV := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSMS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCC := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (ld : Elected server) hrole hnone hq hone hcb | intro hrole hnone hq hone hcb (ld : Elected server)
  have key := winner_none st.leaders st.ledLog i (st.currentTerm i) hLHL hnone
  have hsame : ∀ L, st.ledLog (st.currentTerm i) = some L → L = st.log i := fun L hL => by rw [hnone] at hL; cases hL
  have hg := ledGrows_set (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) hsame
  have hack : ∀ n t A c, Acked st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
      (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n t A c →
      Acked st.msgs st.leaders st.ledLog n t A c :=
    fun n t A c h => Acked.of_becomeLeader _ _ _ i _ _ n t A c hnone (fun j i' x hx => (hAF _ hx j i' _ x rfl).2.2) h
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hE : ∀ n cand u, Early st.msgs st.leaders st.ledLog n cand u →
      Early st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
        (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n cand u := by
    intro n cand u he t A c ha htu li lt hr
    have ha' := hack n t A c ha
    rcases he t A c ha' htu li lt hr with h1 | h1
    · exact Or.inl (Covers.grows _ _ _ _ _ _ hg (hlen n t A c ha') h1)
    · exact Or.inr (LostIn.grows _ _ _ _ _ _ hg (hlen n t A c ha') (hLS t A ha'.1).2 h1)
  intro hld B hB
  rw [EtcdRaftVeil.Lemmas.mem_insert] at hld
  rcases hld with rfl | hld
  · simp only [↓reduceIte] at hB ⊢
    cases hB
    obtain ⟨hcl, hceq, hcov⟩ := cand_facts th.initV th.chAdd th.chRemove th.chJoint th.chLeave st.commits (st.currentTerm i) (st.confAt i) (st.log i)
      (st.cIn i) (st.cOut i) hSMS (hCC i) hcb
    rw [← hceq]
    refine MemberCore.IsQ.mono _ _ _ ?_ hq
    intro n hn
    simp only [decide_eq_true_eq]
    have hvote : TSet.contains ({ voter := n, term := st.currentTerm i, cand := i } : Vote server) st.votes = true := by
      by_cases hni : n = i
      · subst hni; simpa using hn
      · simp only [hni, ite_false] at hn
        simpa using hGV _ hn
    refine ⟨hvote, ?_⟩
    intro t A c ha htu li lt hr
    have ha' := hack n t A c ha
    rcases hAV ⟨n, st.currentTerm i, i⟩ n t A c ha' hvote rfl htu li lt hr with h1 | ⟨w, h1, h2, B, hB, h3⟩
    · exact Or.inl (Covers.grows _ _ _ _ _ _ hg (hlen n t A c ha') h1)
    · have hw : w ≠ st.currentTerm i := by intro h; rw [h, hnone] at hB; cases hB
      exact Or.inr (LostIn.grows _ _ _ _ _ _ hg (hlen n t A c ha') (hLS t A ha'.1).2
        ⟨w, h1, by simp only at h2; omega, B, hB, h3⟩)
  · have hne : ¬ st.currentTerm i = ld.term := fun h => absurd (by rw [← h]; exact hnone) (hLHL ld hld)
    rw [EtcdRaftVeil.Lemmas.ifNeg hne] at hB
    rw [EtcdRaftVeil.Lemmas.ifNeg hne]
    refine MemberCore.IsQ.mono _ _ _ ?_ (hEQ ld hld B hB)
    intro n hn
    simp only [decide_eq_true_eq] at hn ⊢
    exact ⟨hn.1, hE n _ _ hn.2⟩

prove_veil_invariant_goal BecomeLeader ConfirmedIsLed using wp by
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLHL := hinv.2.2.2.2.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hTP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCIL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hnone hq hone hcb
  have key := winner_none st.leaders st.ledLog i (st.currentTerm i) hLHL hnone
  have hsame : ∀ L, st.ledLog (st.currentTerm i) = some L → L = st.log i := fun L hL => by rw [hnone] at hL; cases hL
  have hg := ledGrows_set (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) hsame
  have hack : ∀ n t A c, Acked st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
      (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n t A c →
      Acked st.msgs st.leaders st.ledLog n t A c :=
    fun n t A c h => Acked.of_becomeLeader _ _ _ i _ _ n t A c hnone (fun j i' x hx => (hAF _ hx j i' _ x rfl).2.2) h
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hE : ∀ n cand u, Early st.msgs st.leaders st.ledLog n cand u →
      Early st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
        (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n cand u := by
    intro n cand u he t A c ha htu li lt hr
    have ha' := hack n t A c ha
    rcases he t A c ha' htu li lt hr with h1 | h1
    · exact Or.inl (Covers.grows _ _ _ _ _ _ hg (hlen n t A c ha') h1)
    · exact Or.inr (LostIn.grows _ _ _ _ _ _ hg (hlen n t A c ha') (hLS t A ha'.1).2 h1)
  intro j
  rcases hCIL j with h | ⟨L, hL, h1, h2⟩
  · exact Or.inl h
  · obtain ⟨es, hL', _⟩ := hg _ L hL
    have hlL : st.confirmedIndex j ≤ L.length := by
      have := congrArg List.length h2; simp at this; omega
    exact Or.inr ⟨L ++ es, hL', h1, by rw [List.take_append_of_le_length hlL]; exact h2⟩

prove_veil_invariant_goal BecomeLeader CommitRoot using wp by
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLHL := hinv.2.2.2.2.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hTP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (k : Commit server value) hrole hnone hq hone hcb | intro hrole hnone hq hone hcb (k : Commit server value)
  have key := winner_none st.leaders st.ledLog i (st.currentTerm i) hLHL hnone
  have hsame : ∀ L, st.ledLog (st.currentTerm i) = some L → L = st.log i := fun L hL => by rw [hnone] at hL; cases hL
  have hg := ledGrows_set (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) hsame
  have hack : ∀ n t A c, Acked st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
      (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n t A c →
      Acked st.msgs st.leaders st.ledLog n t A c :=
    fun n t A c h => Acked.of_becomeLeader _ _ _ i _ _ n t A c hnone (fun j i' x hx => (hAF _ hx j i' _ x rfl).2.2) h
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hE : ∀ n cand u, Early st.msgs st.leaders st.ledLog n cand u →
      Early st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
        (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n cand u := by
    intro n cand u he t A c ha htu li lt hr
    have ha' := hack n t A c ha
    rcases he t A c ha' htu li lt hr with h1 | h1
    · exact Or.inl (Covers.grows _ _ _ _ _ _ hg (hlen n t A c ha') h1)
    · exact Or.inr (LostIn.grows _ _ _ _ _ _ hg (hlen n t A c ha') (hLS t A ha'.1).2 h1)
  intro hk
  obtain ⟨h1, r, h2, h3, h4, h5⟩ := hCR k hk
  exact ⟨h1, r, h2, Root.mono _ _ _ _ _ _ _ _ _ _ _ _ (fun a ha => ha)
    (fun a ha => ha) hg h3, h4, h5⟩

prove_veil_invariant_goal BecomeLeader CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader CommitWithinLog using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader LeaderCompleteness using wp by
  have hGV := hinv.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hVHR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLER := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAV := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLC := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSMS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hFR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLG := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLCf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCC := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro (cc : Commit server value) hrole hnone hq hone hcb t hc hlt
  by_cases hd : st.currentTerm i = t
  · subst hd
    rw [EtcdRaftVeil.Lemmas.ifPos rfl, allPrefix_iff]
    intro L hL
    cases hL
    obtain ⟨-, r, hcr, ⟨d, A, hroot, hrA⟩, hr, hrt⟩ := hCR cc hc
    refine hcr.trans ?_
    obtain ⟨hcl, hceq, hcov⟩ := cand_facts th.initV th.chAdd th.chRemove th.chJoint th.chLeave st.commits
      (st.currentTerm i) (st.confAt i) (st.log i) (st.cIn i) (st.cOut i) hSMS (hCC i) hcb
    have hrA' : r.entries = A.take r.entries.length := by
      obtain ⟨s, rfl⟩ := hrA; simp
    rw [hceq] at hq
    rw [hrA']
    refine cand_complete _ _ _ _ _ st.msgs st.leaders st.votes st.ledLog st.commits st.elAt
      (world_inv _ _ _ _ _ st.msgs st.ledLog st.commits hSMS hFR hLG hLS)
      hEQ (fun u B hB => (hLCf u B hB).2.2.2.2.2)
      (fun u B hB p q h1 h2 hp hq ht1 ht2 => by have := hLOld u B hB p q h1 h2 hp hq ht1; omega)
      hLHas hVHR hLER (fun t L h => (optAll_iff _ _).1 (hLedFL t) L h)
      i (st.currentTerm i) (st.confAt i) (st.log i) _ ?_
      (fun n t A c ha hv htu li lt hr => hAV ⟨n, st.currentTerm i, i⟩ n t A c ha hv rfl htu li lt hr)
      hnone hq (fun li lt hm => hCL _ hm i (st.currentTerm i) li lt rfl rfl hnone) (hLFL i) hcov
      (fun p q h1 h2 hp hq' => confsAfter_one _ _ hone p q h1 h2 (MemberCore.isC_le _ _ _ hq').2 hp hq')
      r.term r.entries.length d A hroot (by omega)
    intro n hn
    by_cases hni : n = i
    · subst hni; simpa using hn
    · simp only [hni, ite_false] at hn
      simpa using hGV _ hn
  · rw [EtcdRaftVeil.Lemmas.ifNeg hd]; exact hLC cc t hc hlt

prove_veil_invariant_goal BecomeLeader ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader ConfIsCommitted using wp by
  have hConfIsCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader LeaderConf using wp by
  have hSMS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCC := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLCf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hnone hq hone hcb t A hA
  by_cases hc : st.currentTerm i = t
  · subst hc
    simp only [↓reduceIte] at hA ⊢
    cases hA
    obtain ⟨hcl, hceq, hcov⟩ := cand_facts th.initV th.chAdd th.chRemove th.chJoint th.chLeave st.commits (st.currentTerm i) (st.confAt i) (st.log i)
      (st.cIn i) (st.cOut i) hSMS (hCC i) hcb
    refine ⟨hcl, Nat.le_refl _, ?_, confsAfter_one _ _ hone, ?_, hcov⟩
    · intro s
      rw [← hceq]; exact ⟨rfl, rfl⟩
    · rcases hcov with h0 | ⟨k, tk, hk, h1, h2, h3⟩
      · exact Or.inl h0
      · exact Or.inr ⟨k, tk, hk, by omega, h2, h3⟩
  · simp only [hc, ite_false] at hA ⊢
    exact hLCf t A hA

prove_veil_invariant_goal BecomeLeader FirstRoot using wp by
  have hLHL := hinv.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hFR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (k : Commit server value) hrole hnone hq hone hcb | intro hrole hnone hq hone hcb (k : Commit server value)
  have key := winner_none st.leaders st.ledLog i (st.currentTerm i) hLHL hnone
  have hsame : ∀ L, st.ledLog (st.currentTerm i) = some L → L = st.log i := fun L hL => by rw [hnone] at hL; cases hL
  have hg := ledGrows_set (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) hsame
  have hack : ∀ n t A c, Acked st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
      (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n t A c →
      Acked st.msgs st.leaders st.ledLog n t A c :=
    fun n t A c h => Acked.of_becomeLeader _ _ _ i _ _ n t A c hnone (fun j i' x hx => (hAF _ hx j i' _ x rfl).2.2) h
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hE : ∀ n cand u, Early st.msgs st.leaders st.ledLog n cand u →
      Early st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
        (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n cand u := by
    intro n cand u he t A c ha htu li lt hr
    have ha' := hack n t A c ha
    rcases he t A c ha' htu li lt hr with h1 | h1
    · exact Or.inl (Covers.grows _ _ _ _ _ _ hg (hlen n t A c ha') h1)
    · exact Or.inr (LostIn.grows _ _ _ _ _ _ hg (hlen n t A c ha') (hLS t A ha'.1).2 h1)
  intro hk p hp
  exact firstRoot_mono _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a ha => ha) (fun a ha => ha) hg (hFR k hk p hp)

prove_veil_invariant_goal BecomeLeader LedOld using wp by
  have hLOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hnone hq hone hcb u B hB p q hp1 hpq hcp hcq htp
  by_cases hc : st.currentTerm i = u
  · subst hc
    simp only [↓reduceIte] at hB hp1
    cases hB
    exact absurd (confsAfter_one _ _ hone p q hp1 hpq (MemberCore.isC_le _ _ _ hcq).2 hcp hcq) id
  · simp only [hc, ite_false] at hB hp1
    exact hLOld u B hB p q hp1 hpq hcp hcq htp

prove_veil_invariant_goal BecomeLeader LegalChain using wp by
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLG := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (e' : Entry value) hrole hnone hq hone hcb t A hA p hp hce | intro hrole hnone hq hone hcb (e' : Entry value) t A hA p hp hce
  by_cases hc : st.currentTerm i = t
  · subst hc
    simp only [↓reduceIte] at hA
    cases hA
    exact legal_of_fromLed _ _ _ _ _ st.ledLog (st.log i) (hLFL i) hLG p e' hp hce
  · simp only [hc, ite_false] at hA
    exact hLG e' t A hA p hp hce

prove_veil_invariant_goal BecomeLeader ReadMsgsOld using wp by
  have hReadMsgsOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader ReadFloorOld using wp by
  have hReadFloorOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader ReadFloorBound using wp by
  have hReadFloorBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader ReadIndexSafety using wp by
  have hReadIndexSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader ReadTermLed using wp by
  have hReadTermLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader ReadFloorRooted using wp by
  have hRFR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (k : Commit server value) hrole hnone hq hone hcb | intro hrole hnone hq hone hcb (k : Commit server value)
  have hsame : ∀ L, st.ledLog (st.currentTerm i) = some L → L = st.log i := fun L hL => by rw [hnone] at hL; cases hL
  have hg := ledGrows_set (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) hsame
  intro hon hk
  obtain ⟨r, h1, h2, h3⟩ := hRFR k hon hk
  exact ⟨r, h1, h2, Root.mono _ _ _ _ _ _ _ _ _ _ _ _ (fun a ha => ha) (fun a ha => ha) hg h3⟩

prove_veil_invariant_goal BecomeLeader ReadFirstRoot using wp by
  have hRF1 := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (k : Commit server value) hrole hnone hq hone hcb | intro hrole hnone hq hone hcb (k : Commit server value)
  have hsame : ∀ L, st.ledLog (st.currentTerm i) = some L → L = st.log i := fun L hL => by rw [hnone] at hL; cases hL
  have hg := ledGrows_set (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) hsame
  intro hon hk p hp
  exact firstRoot_mono _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a ha => ha) (fun a ha => ha) hg (hRF1 k hon hk p hp)

prove_veil_invariant_goal BecomeLeader ReadRespBound using wp by
  have hReadRespBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- LeaderAppend

prove_veil_invariant_goal LeaderAppend ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend LeaderSync using wp by
  have hLeaderSync := hinv.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend LedOwner using wp by
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intro x hrole hsome hconf hx hxt
  obtain ⟨l, hled⟩ : ∃ l, st.ledLog (st.currentTerm i) = some l := by
    cases h : st.ledLog (st.currentTerm i) with
    | none => exact absurd h hsome
    | some l => exact ⟨l, rfl⟩
  have hgd : (st.ledLog (st.currentTerm i)).getD [] = l := by rw [hled]; rfl
  rw [hgd]
  have := hLO x hx hxt
  rw [anyPrefix_iff] at this ⊢
  obtain ⟨L, hL, hp⟩ := this
  by_cases hc : st.currentTerm i = x.term
  · rw [EtcdRaftVeil.Lemmas.ifPos hc]
    rw [← hc, hled] at hL; cases hL
    exact ⟨_, rfl, hp.trans (List.prefix_append _ _)⟩
  · rw [EtcdRaftVeil.Lemmas.ifNeg hc]; exact ⟨L, hL, hp⟩

prove_veil_invariant_goal LeaderAppend LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend LeaderLogIsLed using wp by
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hsome hconf j hjrole
  obtain ⟨l, hled⟩ : ∃ l, st.ledLog (st.currentTerm i) = some l := by
    cases h : st.ledLog (st.currentTerm i) with
    | none => exact absurd h hsome
    | some l => exact ⟨l, rfl⟩
  have hgd : (st.ledLog (st.currentTerm i)).getD [] = l := by rw [hled]; rfl
  rw [hgd]
  have := hLLL j hjrole
  rw [anyPrefix_iff] at this ⊢
  obtain ⟨L, hL, hp⟩ := this
  by_cases hc : st.currentTerm i = st.currentTerm j
  · rw [EtcdRaftVeil.Lemmas.ifPos hc]
    rw [← hc, hled] at hL; cases hL
    exact ⟨_, rfl, hp.trans (List.prefix_append _ _)⟩
  · rw [EtcdRaftVeil.Lemmas.ifNeg hc]; exact ⟨L, hL, hp⟩

prove_veil_invariant_goal LeaderAppend RequestsFromLed using wp by
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hsome hconf
  obtain ⟨l, hled⟩ : ∃ l, st.ledLog (st.currentTerm i) = some l := by
    cases h : st.ledLog (st.currentTerm i) with
    | none => exact absurd h hsome
    | some l => exact ⟨l, rfl⟩
  have hgd : (st.ledLog (st.currentTerm i)).getD [] = l := by rw [hled]; rfl
  rw [hgd]
  intro m hm
  refine req_mono st.ledLog _ _ _ m (hRFL m hm) ?_ ?_
  · exact led_ext_set st.ledLog (st.currentTerm i) _
      (fun L hL => by rw [hled] at hL; cases hL; exact List.prefix_append _ _)
  · intro t l l' c hp hx
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
    exact commitPart_mono st.commits _ (fun k hk => hk) l l' c t hp hx

prove_veil_invariant_goal LeaderAppend LogFromLed using wp by
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hsome hconf
  obtain ⟨l, hled⟩ : ∃ l, st.ledLog (st.currentTerm i) = some l := by
    cases h : st.ledLog (st.currentTerm i) with
    | none => exact absurd h hsome
    | some l => exact ⟨l, rfl⟩
  have hgd : (st.ledLog (st.currentTerm i)).getD [] = l := by rw [hled]; rfl
  rw [hgd]
  intro j
  refine (leaderAppend_fromLed st.ledLog l _ _ ?_ hled).1 _ (hLFL j); rfl

prove_veil_invariant_goal LeaderAppend LedFromLed using wp by
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hsome hconf
  obtain ⟨l, hled⟩ : ∃ l, st.ledLog (st.currentTerm i) = some l := by
    cases h : st.ledLog (st.currentTerm i) with
    | none => exact absurd h hsome
    | some l => exact ⟨l, rfl⟩
  have hgd : (st.ledLog (st.currentTerm i)).getD [] = l := by rw [hled]; rfl
  rw [hgd]
  intro t
  refine (optAll_iff _ _).2 ?_
  intro L hL
  by_cases hc : st.currentTerm i = t
  · rw [EtcdRaftVeil.Lemmas.ifPos hc] at hL; cases hL
    refine (leaderAppend_fromLed st.ledLog l _ _ ?_ hled).2 ((optAll_iff _ _).1 (hLedFL _) l hled); rfl
  · rw [EtcdRaftVeil.Lemmas.ifNeg hc] at hL
    refine (leaderAppend_fromLed st.ledLog (l) _ _ ?_ hled).1 _ ((optAll_iff _ _).1 (hLedFL t) L hL); rfl

prove_veil_invariant_goal LeaderAppend LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend LedSorted using wp by
  have hES := hinv.1
  have hLE := hinv.2.2.2.2.2.2.1
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hsome hconf
  obtain ⟨l, hled⟩ : ∃ l, st.ledLog (st.currentTerm i) = some l := by
    cases h : st.ledLog (st.currentTerm i) with
    | none => exact absurd h hsome
    | some l => exact ⟨l, rfl⟩
  have hgd : (st.ledLog (st.currentTerm i)).getD [] = l := by rw [hled]; rfl
  rw [hgd]
  generalize hE : ({ term := st.currentTerm i, kind := ty, value := _ } : Entry value) = e
  have he : e.term = st.currentTerm i := by rw [← hE]
  have hg := ledGrows_append (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (l) e hled he
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hold : ∀ n t A c, Acked st.msgs st.leaders (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (l ++ [e])) (st.ledLog x)) n t A c →
      ∃ A0, Acked st.msgs st.leaders st.ledLog n t A0 c ∧ A0.take c = A.take c := by
    intro n t A c h
    rcases Acked.of_leaderAppend (d := fun _ => Classical.propDecidable _) _ _ _ _ _ e n t A c hled
      (fun i' x' hx' => by
        obtain ⟨_, _, L, hL, hxL⟩ := hAF _ hx' n i' _ x' rfl
        rw [hled] at hL; cases hL; exact hxL) h with ⟨_, h'⟩ | ⟨rfl, rfl, hc, h'⟩
    · exact ⟨A, h', rfl⟩
    · exact ⟨l, h', by rw [List.take_append_of_le_length hc]⟩
  intro t L hL
  by_cases hc : st.currentTerm i = t
  · rw [EtcdRaftVeil.Lemmas.ifPos hc] at hL; cases hL
    rw [← hc]
    exact Sorted.append (l) [e] (st.currentTerm i) (hLS _ _ hled) (by intro e' he'; simp at he'; rw [he', he])
  · rw [EtcdRaftVeil.Lemmas.ifNeg hc] at hL; exact hLS t L hL

prove_veil_invariant_goal LeaderAppend ReqFacts using wp by
  have hES := hinv.1
  have hLE := hinv.2.2.2.2.2.2.1
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (a : Msg server value) hrole hsome hconf | intro hrole hsome hconf (a : Msg server value)
  obtain ⟨l, hled⟩ : ∃ l, st.ledLog (st.currentTerm i) = some l := by
    cases h : st.ledLog (st.currentTerm i) with
    | none => exact absurd h hsome
    | some l => exact ⟨l, rfl⟩
  have hgd : (st.ledLog (st.currentTerm i)).getD [] = l := by rw [hled]; rfl
  rw [hgd]
  generalize hE : ({ term := st.currentTerm i, kind := ty, value := _ } : Entry value) = e
  have he : e.term = st.currentTerm i := by rw [← hE]
  have hg := ledGrows_append (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (l) e hled he
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hold : ∀ n t A c, Acked st.msgs st.leaders (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (l ++ [e])) (st.ledLog x)) n t A c →
      ∃ A0, Acked st.msgs st.leaders st.ledLog n t A0 c ∧ A0.take c = A.take c := by
    intro n t A c h
    rcases Acked.of_leaderAppend (d := fun _ => Classical.propDecidable _) _ _ _ _ _ e n t A c hled
      (fun i' x' hx' => by
        obtain ⟨_, _, L, hL, hxL⟩ := hAF _ hx' n i' _ x' rfl
        rw [hled] at hL; cases hL; exact hxL) h with ⟨_, h'⟩ | ⟨rfl, rfl, hc, h'⟩
    · exact ⟨A, h', rfl⟩
    · exact ⟨l, h', by rw [List.take_append_of_le_length hc]⟩
  intro ha c u li lt heq
  obtain ⟨h1, h2⟩ := hRF a ha c u li lt heq
  exact ⟨h1, ReqOk.grows _ _ _ _ _ hg h2⟩

prove_veil_invariant_goal LeaderAppend ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend LedExtendsReq using wp by
  have hES := hinv.1
  have hLE := hinv.2.2.2.2.2.2.1
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLER := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (ld : Elected server) hrole hsome hconf | intro hrole hsome hconf (ld : Elected server)
  obtain ⟨l, hled⟩ : ∃ l, st.ledLog (st.currentTerm i) = some l := by
    cases h : st.ledLog (st.currentTerm i) with
    | none => exact absurd h hsome
    | some l => exact ⟨l, rfl⟩
  have hgd : (st.ledLog (st.currentTerm i)).getD [] = l := by rw [hled]; rfl
  rw [hgd]
  generalize hE : ({ term := st.currentTerm i, kind := ty, value := _ } : Entry value) = e
  have he : e.term = st.currentTerm i := by rw [← hE]
  have hg := ledGrows_append (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (l) e hled he
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hold : ∀ n t A c, Acked st.msgs st.leaders (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (l ++ [e])) (st.ledLog x)) n t A c →
      ∃ A0, Acked st.msgs st.leaders st.ledLog n t A0 c ∧ A0.take c = A.take c := by
    intro n t A c h
    rcases Acked.of_leaderAppend (d := fun _ => Classical.propDecidable _) _ _ _ _ _ e n t A c hled
      (fun i' x' hx' => by
        obtain ⟨_, _, L, hL, hxL⟩ := hAF _ hx' n i' _ x' rfl
        rw [hled] at hL; cases hL; exact hxL) h with ⟨_, h'⟩ | ⟨rfl, rfl, hc, h'⟩
    · exact ⟨A, h', rfl⟩
    · exact ⟨l, h', by rw [List.take_append_of_le_length hc]⟩
  intro hld m hm li lt heq L hL
  by_cases hc : st.currentTerm i = ld.term
  · rw [EtcdRaftVeil.Lemmas.ifPos hc] at hL; cases hL
    obtain ⟨h1, h2⟩ := hLER ld hld m hm li lt heq (l) (by rw [← hc]; exact hled)
    show li ≤ (l ++ [e]).length ∧ TermAt (l ++ [e]) li = lt
    exact ⟨by simp; omega, by rw [termAt_append_left _ _ _ h1]; exact h2⟩
  · rw [EtcdRaftVeil.Lemmas.ifNeg hc] at hL; exact hLER ld hld m hm li lt heq L hL

prove_veil_invariant_goal LeaderAppend AckFacts using wp by
  have hES := hinv.1
  have hLE := hinv.2.2.2.2.2.2.1
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (a : Msg server value) hrole hsome hconf | intro hrole hsome hconf (a : Msg server value)
  obtain ⟨l, hled⟩ : ∃ l, st.ledLog (st.currentTerm i) = some l := by
    cases h : st.ledLog (st.currentTerm i) with
    | none => exact absurd h hsome
    | some l => exact ⟨l, rfl⟩
  have hgd : (st.ledLog (st.currentTerm i)).getD [] = l := by rw [hled]; rfl
  rw [hgd]
  generalize hE : ({ term := st.currentTerm i, kind := ty, value := _ } : Entry value) = e
  have he : e.term = st.currentTerm i := by rw [← hE]
  have hg := ledGrows_append (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (l) e hled he
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hold : ∀ n t A c, Acked st.msgs st.leaders (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (l ++ [e])) (st.ledLog x)) n t A c →
      ∃ A0, Acked st.msgs st.leaders st.ledLog n t A0 c ∧ A0.take c = A.take c := by
    intro n t A c h
    rcases Acked.of_leaderAppend (d := fun _ => Classical.propDecidable _) _ _ _ _ _ e n t A c hled
      (fun i' x' hx' => by
        obtain ⟨_, _, L, hL, hxL⟩ := hAF _ hx' n i' _ x' rfl
        rw [hled] at hL; cases hL; exact hxL) h with ⟨_, h'⟩ | ⟨rfl, rfl, hc, h'⟩
    · exact ⟨A, h', rfl⟩
    · exact ⟨l, h', by rw [List.take_append_of_le_length hc]⟩
  intro ha j i' t x heq
  obtain ⟨h1, h2, L, hL, hx⟩ := hAF a ha j i' t x heq
  obtain ⟨es, hL', _⟩ := hg t L hL
  exact ⟨h1, h2, L ++ es, hL', by simp; omega⟩

prove_veil_invariant_goal LeaderAppend AckedHeld using wp by
  have hES := hinv.1
  have hLE := hinv.2.2.2.2.2.2.1
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAH := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hsome hconf
  obtain ⟨l, hled⟩ : ∃ l, st.ledLog (st.currentTerm i) = some l := by
    cases h : st.ledLog (st.currentTerm i) with
    | none => exact absurd h hsome
    | some l => exact ⟨l, rfl⟩
  have hgd : (st.ledLog (st.currentTerm i)).getD [] = l := by rw [hled]; rfl
  rw [hgd]
  generalize hE : ({ term := st.currentTerm i, kind := ty, value := _ } : Entry value) = e
  have he : e.term = st.currentTerm i := by rw [← hE]
  have hg := ledGrows_append (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (l) e hled he
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hold : ∀ n t A c, Acked st.msgs st.leaders (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (l ++ [e])) (st.ledLog x)) n t A c →
      ∃ A0, Acked st.msgs st.leaders st.ledLog n t A0 c ∧ A0.take c = A.take c := by
    intro n t A c h
    rcases Acked.of_leaderAppend (d := fun _ => Classical.propDecidable _) _ _ _ _ _ e n t A c hled
      (fun i' x' hx' => by
        obtain ⟨_, _, L, hL, hxL⟩ := hAF _ hx' n i' _ x' rfl
        rw [hled] at hL; cases hL; exact hxL) h with ⟨_, h'⟩ | ⟨rfl, rfl, hc, h'⟩
    · exact ⟨A, h', rfl⟩
    · exact ⟨l, h', by rw [List.take_append_of_le_length hc]⟩
  intro n t A c h
  obtain ⟨A0, h', heq⟩ := hold n t A c h
  rcases hAH n t A0 c h' with h1 | h1
  · left
    rw [← heq]; exact h1
  · exact Or.inr (LostIn.congr _ _ _ _ _ _ heq
      (LostIn.grows _ _ _ _ _ _ hg (hlen n t A0 c h') (hLS t A0 h'.1).2 h1))

prove_veil_invariant_goal LeaderAppend AckVote using wp by
  have hES := hinv.1
  have hVT := hinv.2.2.1
  have hVB := hinv.2.2.2.1
  have hLE := hinv.2.2.2.2.2.2.1
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAV := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (v : Vote server) hrole hsome hconf | intro hrole hsome hconf (v : Vote server)
  obtain ⟨l, hled⟩ : ∃ l, st.ledLog (st.currentTerm i) = some l := by
    cases h : st.ledLog (st.currentTerm i) with
    | none => exact absurd h hsome
    | some l => exact ⟨l, rfl⟩
  have hgd : (st.ledLog (st.currentTerm i)).getD [] = l := by rw [hled]; rfl
  rw [hgd]
  generalize hE : ({ term := st.currentTerm i, kind := ty, value := _ } : Entry value) = e
  have he : e.term = st.currentTerm i := by rw [← hE]
  have hg := ledGrows_append (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (l) e hled he
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hold : ∀ n t A c, Acked st.msgs st.leaders (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (l ++ [e])) (st.ledLog x)) n t A c →
      ∃ A0, Acked st.msgs st.leaders st.ledLog n t A0 c ∧ A0.take c = A.take c := by
    intro n t A c h
    rcases Acked.of_leaderAppend (d := fun _ => Classical.propDecidable _) _ _ _ _ _ e n t A c hled
      (fun i' x' hx' => by
        obtain ⟨_, _, L, hL, hxL⟩ := hAF _ hx' n i' _ x' rfl
        rw [hled] at hL; cases hL; exact hxL) h with ⟨_, h'⟩ | ⟨rfl, rfl, hc, h'⟩
    · exact ⟨A, h', rfl⟩
    · exact ⟨l, h', by rw [List.take_append_of_le_length hc]⟩
  intro n t A c h hv hvn htv li lt hreq
  obtain ⟨A0, h', heq⟩ := hold n t A c h
  rcases hAV v n t A0 c h' hv hvn htv li lt hreq with h1 | h1
  · exact Or.inl (Covers.congr _ _ _ _ _ _ heq (Covers.grows _ _ _ _ _ _ hg (hlen n t A0 c h') h1))
  · exact Or.inr (LostIn.congr _ _ _ _ _ _ heq
      (LostIn.grows _ _ _ _ _ _ hg (hlen n t A0 c h') (hLS t A0 h'.1).2 h1))

prove_veil_invariant_goal LeaderAppend EarlyQuorum using wp by
  have hES := hinv.1
  have hVT := hinv.2.2.1
  have hVB := hinv.2.2.2.1
  have hLE := hinv.2.2.2.2.2.2.1
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLCf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (ld : Elected server) hrole hsome hconf | intro hrole hsome hconf (ld : Elected server)
  obtain ⟨l, hled⟩ : ∃ l, st.ledLog (st.currentTerm i) = some l := by
    cases h : st.ledLog (st.currentTerm i) with
    | none => exact absurd h hsome
    | some l => exact ⟨l, rfl⟩
  have hgd : (st.ledLog (st.currentTerm i)).getD [] = l := by rw [hled]; rfl
  rw [hgd]
  generalize hE : ({ term := st.currentTerm i, kind := ty, value := _ } : Entry value) = e
  have he : e.term = st.currentTerm i := by rw [← hE]
  have hg := ledGrows_append (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (l) e hled he
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hold : ∀ n t A c, Acked st.msgs st.leaders (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (l ++ [e])) (st.ledLog x)) n t A c →
      ∃ A0, Acked st.msgs st.leaders st.ledLog n t A0 c ∧ A0.take c = A.take c := by
    intro n t A c h
    rcases Acked.of_leaderAppend (d := fun _ => Classical.propDecidable _) _ _ _ _ _ e n t A c hled
      (fun i' x' hx' => by
        obtain ⟨_, _, L, hL, hxL⟩ := hAF _ hx' n i' _ x' rfl
        rw [hled] at hL; cases hL; exact hxL) h with ⟨_, h'⟩ | ⟨rfl, rfl, hc, h'⟩
    · exact ⟨A, h', rfl⟩
    · exact ⟨l, h', by rw [List.take_append_of_le_length hc]⟩
  intro hld B hB
  obtain ⟨B0, hB0, hcB⟩ : ∃ B0, st.ledLog ld.term = some B0 ∧
      cOf th.initV th.chAdd th.chRemove th.chJoint th.chLeave B (st.elAt ld.term) = cOf th.initV th.chAdd th.chRemove th.chJoint th.chLeave B0 (st.elAt ld.term) := by
    by_cases hc : st.currentTerm i = ld.term
    · rw [EtcdRaftVeil.Lemmas.ifPos hc] at hB
      rw [show Append.append l [e] = l ++ [e] from rfl] at hB; cases hB
      refine ⟨l, by rw [← hc]; exact hled, ?_⟩
      have hle := hLCf _ l hled
      have : st.elAt ld.term ≤ l.length := by rw [← hc]; omega
      exact MemberCore.confOf_congr _ _ _ _ _ _ (List.take_append_of_le_length this)
    · rw [EtcdRaftVeil.Lemmas.ifNeg hc] at hB; exact ⟨B, hB, rfl⟩
  rw [hcB]
  refine MemberCore.IsQ.mono _ _ _ ?_ (hEQ ld hld B0 hB0)
  intro n hn
  simp only [decide_eq_true_eq] at hn ⊢
  refine ⟨hn.1, ?_⟩
  intro t A c ha htu li lt hr
  obtain ⟨A0, h', heq⟩ := hold n t A c ha
  rcases hn.2 t A0 c h' htu li lt hr with h1 | h1
  · exact Or.inl (Covers.congr _ _ _ _ _ _ heq (Covers.grows _ _ _ _ _ _ hg (hlen n t A0 c h') h1))
  · exact Or.inr (LostIn.congr _ _ _ _ _ _ heq
      (LostIn.grows _ _ _ _ _ _ hg (hlen n t A0 c h') (hLS t A0 h'.1).2 h1))

prove_veil_invariant_goal LeaderAppend ConfirmedIsLed using wp by
  have hES := hinv.1
  have hLE := hinv.2.2.2.2.2.2.1
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCIL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hsome hconf
  obtain ⟨l, hled⟩ : ∃ l, st.ledLog (st.currentTerm i) = some l := by
    cases h : st.ledLog (st.currentTerm i) with
    | none => exact absurd h hsome
    | some l => exact ⟨l, rfl⟩
  have hgd : (st.ledLog (st.currentTerm i)).getD [] = l := by rw [hled]; rfl
  rw [hgd]
  generalize hE : ({ term := st.currentTerm i, kind := ty, value := _ } : Entry value) = e
  have he : e.term = st.currentTerm i := by rw [← hE]
  have hg := ledGrows_append (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (l) e hled he
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hold : ∀ n t A c, Acked st.msgs st.leaders (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (l ++ [e])) (st.ledLog x)) n t A c →
      ∃ A0, Acked st.msgs st.leaders st.ledLog n t A0 c ∧ A0.take c = A.take c := by
    intro n t A c h
    rcases Acked.of_leaderAppend (d := fun _ => Classical.propDecidable _) _ _ _ _ _ e n t A c hled
      (fun i' x' hx' => by
        obtain ⟨_, _, L, hL, hxL⟩ := hAF _ hx' n i' _ x' rfl
        rw [hled] at hL; cases hL; exact hxL) h with ⟨_, h'⟩ | ⟨rfl, rfl, hc, h'⟩
    · exact ⟨A, h', rfl⟩
    · exact ⟨l, h', by rw [List.take_append_of_le_length hc]⟩
  intro j
  rcases hCIL j with h | ⟨L, hL, h1, h2⟩
  · exact Or.inl h
  · obtain ⟨es, hL', _⟩ := hg _ L hL
    have hlL : st.confirmedIndex j ≤ L.length := by
      have := congrArg List.length h2; simp at this; omega
    refine Or.inr ⟨L ++ es, hL', h1, ?_⟩
    rw [List.take_append_of_le_length hlL]; exact h2

prove_veil_invariant_goal LeaderAppend CommitRoot using wp by
  have hES := hinv.1
  have hLE := hinv.2.2.2.2.2.2.1
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (k : Commit server value) hrole hsome hconf | intro hrole hsome hconf (k : Commit server value)
  obtain ⟨l, hled⟩ : ∃ l, st.ledLog (st.currentTerm i) = some l := by
    cases h : st.ledLog (st.currentTerm i) with
    | none => exact absurd h hsome
    | some l => exact ⟨l, rfl⟩
  have hgd : (st.ledLog (st.currentTerm i)).getD [] = l := by rw [hled]; rfl
  rw [hgd]
  generalize hE : ({ term := st.currentTerm i, kind := ty, value := _ } : Entry value) = e
  have he : e.term = st.currentTerm i := by rw [← hE]
  have hg := ledGrows_append (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (l) e hled he
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hold : ∀ n t A c, Acked st.msgs st.leaders (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (l ++ [e])) (st.ledLog x)) n t A c →
      ∃ A0, Acked st.msgs st.leaders st.ledLog n t A0 c ∧ A0.take c = A.take c := by
    intro n t A c h
    rcases Acked.of_leaderAppend (d := fun _ => Classical.propDecidable _) _ _ _ _ _ e n t A c hled
      (fun i' x' hx' => by
        obtain ⟨_, _, L, hL, hxL⟩ := hAF _ hx' n i' _ x' rfl
        rw [hled] at hL; cases hL; exact hxL) h with ⟨_, h'⟩ | ⟨rfl, rfl, hc, h'⟩
    · exact ⟨A, h', rfl⟩
    · exact ⟨l, h', by rw [List.take_append_of_le_length hc]⟩
  intro hk
  obtain ⟨h1, r, h2, h3, h4, h5⟩ := hCR k hk
  exact ⟨h1, r, h2, Root.mono _ _ _ _ _ _ _ _ _ _ _ _ (fun a ha => ha) (fun a ha => ha) hg h3, h4, h5⟩

prove_veil_invariant_goal LeaderAppend CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend CommitWithinLog using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend LeaderCompleteness using wp by
  have hLC := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro (cc : Commit server value) hrole hsome hconf t hc hlt
  obtain ⟨l, hled⟩ : ∃ l, st.ledLog (st.currentTerm i) = some l := by
    cases h : st.ledLog (st.currentTerm i) with
    | none => exact absurd h hsome
    | some l => exact ⟨l, rfl⟩
  have hgd : (st.ledLog (st.currentTerm i)).getD [] = l := by rw [hled]; rfl
  rw [hgd]
  have := hLC cc t hc hlt
  rw [allPrefix_iff] at this ⊢
  intro L hL
  by_cases hd : st.currentTerm i = t
  · rw [EtcdRaftVeil.Lemmas.ifPos hd] at hL; cases hL
    exact (this l (hd ▸ hled)).trans (List.prefix_append _ _)
  · rw [EtcdRaftVeil.Lemmas.ifNeg hd] at hL; exact this L hL

prove_veil_invariant_goal LeaderAppend ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend ConfIsCommitted using wp by
  have hConfIsCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend LeaderConf using wp by
  have hLSy := hinv.2.2.2.2.2.1
  have hLCf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hsome hconf t A hA
  obtain ⟨l, hled⟩ : ∃ l, st.ledLog (st.currentTerm i) = some l := by
    cases h : st.ledLog (st.currentTerm i) with
    | none => exact absurd h hsome
    | some l => exact ⟨l, rfl⟩
  have hgd : (st.ledLog (st.currentTerm i)).getD [] = l := by rw [hled]; rfl
  rw [hgd] at hconf hA
  generalize hE : ({ term := st.currentTerm i, kind := ty, value := _ } : Entry value) = e at hA
  have he : e.term = st.currentTerm i := by rw [← hE]
  have hty : e.isConf = true → ty = EntryType.conf := by
    intro h
    have hk : e.kind = ty := by rw [← hE]
    unfold Entry.isConf at h
    rw [hk] at h
    cases ty <;> simp_all
  by_cases hc : st.currentTerm i = t
  · subst hc
    rw [EtcdRaftVeil.Lemmas.ifPos rfl] at hA
    rw [show Append.append l [e] = l ++ [e] from rfl] at hA; cases hA
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hLCf _ l hled
    have htk : ∀ d, d ≤ l.length → (l ++ [e]).take d = l.take d := fun d hd => List.take_append_of_le_length hd
    refine ⟨by simp; omega, h2, ?_, ?_, ?_, ?_⟩
    · intro s
      rw [show cOf th.initV th.chAdd th.chRemove th.chJoint th.chLeave (l ++ [e]) (st.ledAt (st.currentTerm i)) =
          cOf th.initV th.chAdd th.chRemove th.chJoint th.chLeave l (st.ledAt (st.currentTerm i)) from
        MemberCore.confOf_congr _ _ _ _ _ _ (htk _ h1)]
      exact h3 s
    · intro p q hp1 hpq hq hcp hcq
      rcases Nat.lt_or_ge q (l.length + 1) with hql | hql
      · rw [isC_append _ _ _ (by omega)] at hcp hcq
        exact h4 p q hp1 hpq (by omega) hcp hcq
      · have hqe : q = l.length + 1 := by simp at hq; omega
        subst hqe
        rw [isC_last] at hcq
        have hno := confsAfter_zero l _ (hconf (hty hcq)).1
        rw [isC_append _ _ _ (by omega)] at hcp
        have hsync := (hLSy i hrole).1
        have := hno p (by omega) (by omega)
        rw [this] at hcp; cases hcp
    · rcases h5 with h0 | ⟨k, tk, hk, r1, r2, r3⟩
      · exact Or.inl h0
      · exact Or.inr ⟨k, tk, hk, r1, r2, by rw [htk _ h1]; exact r3⟩
    · rcases h6 with h0 | ⟨k, tk, hk, r1, r2, r3⟩
      · exact Or.inl h0
      · exact Or.inr ⟨k, tk, hk, r1, r2, by rw [htk _ (by omega)]; exact r3⟩
  · rw [EtcdRaftVeil.Lemmas.ifNeg hc] at hA
    exact hLCf t A hA

prove_veil_invariant_goal LeaderAppend FirstRoot using wp by
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hFR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (k : Commit server value) hrole hsome hconf | intro hrole hsome hconf (k : Commit server value)
  obtain ⟨l, hled⟩ : ∃ l, st.ledLog (st.currentTerm i) = some l := by
    cases h : st.ledLog (st.currentTerm i) with
    | none => exact absurd h hsome
    | some l => exact ⟨l, rfl⟩
  have hgd : (st.ledLog (st.currentTerm i)).getD [] = l := by rw [hled]; rfl
  rw [hgd]
  generalize hE : ({ term := st.currentTerm i, kind := ty, value := _ } : Entry value) = e
  have he : e.term = st.currentTerm i := by rw [← hE]
  have hg := ledGrows_append (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (l) e hled he
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hold : ∀ n t A c, Acked st.msgs st.leaders (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (l ++ [e])) (st.ledLog x)) n t A c →
      ∃ A0, Acked st.msgs st.leaders st.ledLog n t A0 c ∧ A0.take c = A.take c := by
    intro n t A c h
    rcases Acked.of_leaderAppend (d := fun _ => Classical.propDecidable _) _ _ _ _ _ e n t A c hled
      (fun i' x' hx' => by
        obtain ⟨_, _, L, hL, hxL⟩ := hAF _ hx' n i' _ x' rfl
        rw [hled] at hL; cases hL; exact hxL) h with ⟨_, h'⟩ | ⟨rfl, rfl, hc, h'⟩
    · exact ⟨A, h', rfl⟩
    · exact ⟨l, h', by rw [List.take_append_of_le_length hc]⟩
  intro hk p hp
  exact firstRoot_mono _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a ha => ha) (fun a ha => ha) hg (hFR k hk p hp)

prove_veil_invariant_goal LeaderAppend LedOld using wp by
  have hLOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hsome hconf u B hB p q hp1 hpq hcp hcq htp
  obtain ⟨l, hled⟩ : ∃ l, st.ledLog (st.currentTerm i) = some l := by
    cases h : st.ledLog (st.currentTerm i) with
    | none => exact absurd h hsome
    | some l => exact ⟨l, rfl⟩
  have hgd : (st.ledLog (st.currentTerm i)).getD [] = l := by rw [hled]; rfl
  rw [hgd] at hconf hB
  generalize hE : ({ term := st.currentTerm i, kind := ty, value := _ } : Entry value) = e at hB
  have he : e.term = st.currentTerm i := by rw [← hE]
  have hty : e.isConf = true → ty = EntryType.conf := by
    intro h
    have hk : e.kind = ty := by rw [← hE]
    unfold Entry.isConf at h
    rw [hk] at h
    cases ty <;> simp_all
  by_cases hc : st.currentTerm i = u
  · subst hc
    rw [EtcdRaftVeil.Lemmas.ifPos rfl] at hB
    rw [show Append.append l [e] = l ++ [e] from rfl] at hB; cases hB
    rcases Nat.lt_or_ge q (l.length + 1) with hql | hql
    · rw [isC_append _ _ _ (by omega)] at hcp hcq
      rw [termAt_append_left _ _ _ (by omega)] at htp ⊢
      exact hLOld _ l hled p q hp1 hpq hcp hcq htp
    · have hqe : q = l.length + 1 := by
        have := (MemberCore.isC_le _ _ _ hcq).2
        simp at this; omega
      subst hqe
      have : TermAt (l ++ [e]) (l.length + 1) = e.term := by simp [TermAt]
      rw [this, he]; exact Nat.le_refl _
  · rw [EtcdRaftVeil.Lemmas.ifNeg hc] at hB
    exact hLOld u B hB p q hp1 hpq hcp hcq htp

prove_veil_invariant_goal LeaderAppend LegalChain using wp by
  have hLSy := hinv.2.2.2.2.2.1
  have hLCf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLG := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (e' : Entry value) hrole hsome hconf t A hA p hp hce | intro hrole hsome hconf (e' : Entry value) t A hA p hp hce
  obtain ⟨l, hled⟩ : ∃ l, st.ledLog (st.currentTerm i) = some l := by
    cases h : st.ledLog (st.currentTerm i) with
    | none => exact absurd h hsome
    | some l => exact ⟨l, rfl⟩
  have hgd : (st.ledLog (st.currentTerm i)).getD [] = l := by rw [hled]; rfl
  rw [hgd] at hconf hA
  generalize hE : ({ term := st.currentTerm i, kind := ty, value := _ } : Entry value) = e at hA
  have he : e.term = st.currentTerm i := by rw [← hE]
  have hty : e.isConf = true → ty = EntryType.conf := by
    intro h
    have hk : e.kind = ty := by rw [← hE]
    unfold Entry.isConf at h
    rw [hk] at h
    cases ty <;> simp_all
  by_cases hc : st.currentTerm i = t
  · subst hc
    rw [EtcdRaftVeil.Lemmas.ifPos rfl] at hA
    rw [show Append.append l [e] = l ++ [e] from rfl] at hA; cases hA
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hLCf _ l hled
    rcases Nat.lt_or_ge p l.length with hpl | hpl
    · rw [List.getElem?_append_left hpl] at hp
      have := hLG e' _ l hled p hp hce
      rwa [show cOf th.initV th.chAdd th.chRemove th.chJoint th.chLeave (l ++ [e]) p = cOf th.initV th.chAdd th.chRemove th.chJoint th.chLeave l p from
        MemberCore.confOf_congr _ _ _ _ _ _ (List.take_append_of_le_length (by omega))]
    · have hpe : p = l.length := by
        have := (List.getElem?_eq_some_iff.1 hp).1
        simp at this; omega
      subst hpe
      have hee : e = e' := by simpa using hp
      subst hee
      obtain ⟨hno, hleg⟩ := hconf (hty hce)
      have hsync := hLSy i hrole
      have hC : cOf th.initV th.chAdd th.chRemove th.chJoint th.chLeave (l ++ [e]) l.length = { inn := st.cIn i, out := st.cOut i } := by
        rw [show cOf th.initV th.chAdd th.chRemove th.chJoint th.chLeave (l ++ [e]) l.length = cOf th.initV th.chAdd th.chRemove th.chJoint th.chLeave l l.length from
          MemberCore.confOf_congr _ _ _ _ _ _ (List.take_append_of_le_length (Nat.le_refl _))]
        unfold cOf
        rw [MemberCore.confOf_skip _ _ _ l (st.ledAt (st.currentTerm i)) l.length h1
          (by rw [← hsync.1]; exact confsAfter_zero l _ hno)]
        symm; apply conf_ext; intro s
        exact ⟨(hsync.2 s).1.trans (h3 s).1, (hsync.2 s).2.trans (h3 s).2⟩
      rw [hC]
      have hv : chgOf th.chAdd th.chRemove th.chJoint th.chLeave e =
          { add := th.chAdd v, remove := th.chRemove v, joint := th.chJoint v, leave := th.chLeave v } := by
        rw [← hE]; simp [chgOf, hty hce]
      rw [hv]; exact hleg
  · rw [EtcdRaftVeil.Lemmas.ifNeg hc] at hA
    exact hLG e' t A hA p hp hce

prove_veil_invariant_goal LeaderAppend ReadMsgsOld using wp by
  have hReadMsgsOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend ReadFloorOld using wp by
  have hReadFloorOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend ReadFloorBound using wp by
  have hReadFloorBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend ReadIndexSafety using wp by
  have hReadIndexSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend ReadTermLed using wp by
  have hReadTermLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend ReadFloorRooted using wp by
  have hRFR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (k : Commit server value) hrole hsome hconf | intro hrole hsome hconf (k : Commit server value)
  obtain ⟨l, hled⟩ : ∃ l, st.ledLog (st.currentTerm i) = some l := by
    cases h : st.ledLog (st.currentTerm i) with
    | none => exact absurd h hsome
    | some l => exact ⟨l, rfl⟩
  have hgd : (st.ledLog (st.currentTerm i)).getD [] = l := by rw [hled]; rfl
  rw [hgd]
  generalize hE : ({ term := st.currentTerm i, kind := ty, value := _ } : Entry value) = e
  have he : e.term = st.currentTerm i := by rw [← hE]
  have hg := ledGrows_append (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (l) e hled he
  intro hon hk
  obtain ⟨r, h1, h2, h3⟩ := hRFR k hon hk
  exact ⟨r, h1, h2, Root.mono _ _ _ _ _ _ _ _ _ _ _ _ (fun a ha => ha) (fun a ha => ha) hg h3⟩

prove_veil_invariant_goal LeaderAppend ReadFirstRoot using wp by
  have hRF1 := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (k : Commit server value) hrole hsome hconf | intro hrole hsome hconf (k : Commit server value)
  obtain ⟨l, hled⟩ : ∃ l, st.ledLog (st.currentTerm i) = some l := by
    cases h : st.ledLog (st.currentTerm i) with
    | none => exact absurd h hsome
    | some l => exact ⟨l, rfl⟩
  have hgd : (st.ledLog (st.currentTerm i)).getD [] = l := by rw [hled]; rfl
  rw [hgd]
  generalize hE : ({ term := st.currentTerm i, kind := ty, value := _ } : Entry value) = e
  have he : e.term = st.currentTerm i := by rw [← hE]
  have hg := ledGrows_append (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (l) e hled he
  intro hon hk p hp
  exact firstRoot_mono _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a ha => ha) (fun a ha => ha) hg (hRF1 k hon hk p hp)

prove_veil_invariant_goal LeaderAppend ReadRespBound using wp by
  have hReadRespBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- SendAppend

prove_veil_invariant_goal SendAppend ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend GrantsAreVotes using wp by
  have hGV := hinv.2.2.2.2.1
  clear hinv
  intros
  simp only [EtcdRaftVeil.Lemmas.mem_iff, EtcdRaftVeil.Lemmas.contains_insert_iff] at *
  repeat' split
  all_goals grind only

prove_veil_invariant_goal SendAppend LeaderSync using wp by
  have hLeaderSync := hinv.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend AppendFromLeader using wp by
  have hAFL := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  rename_i ld p
  intro hld hsrv hpn hcm m hm
  rw [EtcdRaftVeil.Lemmas.mem_insert] at hm
  rcases hm with rfl | hm
  · subst hsrv
    exact hld
  · exact hAFL m hm

prove_veil_invariant_goal SendAppend LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend RequestsFromLed using wp by
  have hLHL := hinv.2.2.2.2.2.2.2.2.2.1
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  rename_i ld p
  obtain ⟨p, hp⟩ := p
  obtain ⟨n, hn⟩ := a
  obtain ⟨c, hc⟩ := b
  intro hld hsrv hpn hcm m hm
  rw [EtcdRaftVeil.Lemmas.mem_insert] at hm
  rcases hm with rfl | hm
  · obtain ⟨l, hL⟩ := Option.ne_none_iff_exists'.1 (hLHL ld hld)
    simp only [hL, Option.getD_some, List.mem_range] at hc hpn hcm ⊢
    have hlen := subSeq_length l p n hpn
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, hlen]
    refine ⟨hpn, trivial, trivial, ?_⟩
    rcases hcm with h0 | ⟨k, hk1, hk2, hk3, hk4⟩
    · exact Or.inl h0
    · exact Or.inr ⟨by omega, ⟨k, hk3⟩, hk1, hk2, hk4⟩
  · exact hRFL m hm

prove_veil_invariant_goal SendAppend LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend AckedHeld using wp by
  have hAH := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  rename_i n t A c hack
  exact hAH n t A c (Acked.of_insert _ _ _ _ _ _ _ _ (fun _ _ _ _ h => by cases h) hack)

prove_veil_invariant_goal SendAppend AckVote using wp by
  have hAV := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro v
  intros
  rename_i n t A c hack hv hvn htv li lt hreq
  rcases (EtcdRaftVeil.Lemmas.contains_insert_iff _ _ _).1 hreq with h | h
  · cases h
  · exact hAV v n t A c (Acked.of_insert _ _ _ _ _ _ _ _ (fun _ _ _ _ h => by cases h) hack) hv hvn htv li lt h

prove_veil_invariant_goal SendAppend EarlyQuorum using wp by
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ld
  intros
  rename_i hld B hB
  refine MemberCore.IsQ.mono _ _ _ ?_ (hEQ ld hld B hB)
  intro n hn
  simp only [decide_eq_true_eq] at hn ⊢
  exact ⟨hn.1, Early.of_insert _ _ _ _ _ _ _ (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h) hn.2⟩

prove_veil_invariant_goal SendAppend ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend CommitRoot using wp by
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro k
  intros
  rename_i hk
  obtain ⟨h1, r, h2, h3, h4, h5⟩ := hCR k hk
  exact ⟨h1, r, h2, Root.mono _ _ _ _ _ _ _ _ _ _ _ _ (fun a ha => (EtcdRaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr ha))
    (fun a ha => ha) (LedGrows.refl _) h3, h4, h5⟩

prove_veil_invariant_goal SendAppend CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend CommitWithinLog using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend ConfIsCommitted using wp by
  have hConfIsCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend LeaderConf using wp by
  have hLeaderConf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend FirstRoot using wp by
  have hFR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro k
  intros
  rename_i hk p hp
  exact firstRoot_mono _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a ha => (EtcdRaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr ha))
    (fun a ha => ha) (LedGrows.refl _) (hFR k hk p hp)

prove_veil_invariant_goal SendAppend LedOld using wp by
  have hLedOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend LegalChain using wp by
  have hLegalChain := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend ReadMsgsOld using wp by
  have hReadMsgsOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend ReadFloorOld using wp by
  have hReadFloorOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend ReadFloorBound using wp by
  have hReadFloorBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend ReadIndexSafety using wp by
  have hReadIndexSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend ReadTermLed using wp by
  have hReadTermLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend ReadFloorRooted using wp by
  have hReadFloorRooted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend ReadFirstRoot using wp by
  have hReadFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend ReadRespBound using wp by
  have hReadRespBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- LeaderCommit

prove_veil_invariant_goal LeaderCommit ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LeaderSync using wp by
  have hLeaderSync := hinv.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit RequestsFromLed using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro _ _ c _ _ _ _ m hm
  refine req_mono st.ledLog st.ledLog _ _ m (hRFL m hm) (fun t l h => ⟨l, h, List.prefix_refl _⟩) ?_
  · intro t l l' c hp hx
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
    exact commitPart_mono st.commits _ (fun k hk => (EtcdRaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr hk)) l l' c t hp hx

prove_veil_invariant_goal LeaderCommit LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit AckedHeld using wp by
  have hAckedHeld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit CommitRoot using wp by
  have hLHL := hinv.2.2.2.2.2.2.2.2.2.1
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLCf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro k hld hsrv c hc1 hc2 hct hq hk
  subst hsrv
  obtain ⟨A, hA⟩ := Option.ne_none_iff_exists'.1 (hLHL a hld)
  have hgd : (st.ledLog a.term).getD [] = A := by rw [hA]; rfl
  rw [hgd] at hc2 hct
  try rw [hgd]
  have hlenK : (SubSeq A 1 c).length = c := by
    rw [subSeq_one, List.length_take, Nat.min_eq_left (by omega)]
  have hM : MRoot th.initV th.chAdd th.chRemove th.chJoint th.chLeave st.msgs st.ledLog st.commits a.term c
      (st.ledAt a.term) A := by
    refine mroot_of_commit _ _ _ _ _ st.msgs st.ledLog st.commits st.ledAt st.elAt st.lIn st.lOut hLCf a.term c A hA
      (by omega) (by omega) hct _ ?_ hq
    intro j hj
    simp only [ackedBy, decide_eq_true_eq] at hj ⊢
    obtain ⟨⟨m, hm⟩, hmm⟩ := hj
    cases m with
    | ack src dst term index =>
      simp only [decide_eq_true_eq] at hmm
      obtain ⟨rfl, rfl, rfl, hidx⟩ := hmm
      exact ⟨_, index, hm, hidx⟩
    | _ => simp at hmm
  have hRoot : Root th.initV th.chAdd th.chRemove th.chJoint th.chLeave st.msgs st.ledLog st.commits
      { server := a.server, term := a.term, entries := SubSeq A 1 c } := by
    refine ⟨st.ledAt a.term, A, ?_, by rw [subSeq_one]; exact List.take_prefix _ _⟩
    show MRoot _ _ _ _ _ _ _ _ a.term (SubSeq A 1 c).length _ A
    rw [hlenK]; exact hM
  have lift : ∀ r : Commit server value,
      Root th.initV th.chAdd th.chRemove th.chJoint th.chLeave st.msgs st.ledLog st.commits r →
      Root th.initV th.chAdd th.chRemove th.chJoint th.chLeave st.msgs st.ledLog
        (TSet.insert { server := a.server, term := a.term, entries := SubSeq A 1 c } st.commits) r :=
    fun r h => Root.mono _ _ _ _ _ _ _ _ _ _ _ _ (fun a ha => ha)
      (fun k hk => (EtcdRaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr hk)) (LedGrows.refl _) h
  rw [hgd] at hk
  rw [EtcdRaftVeil.Lemmas.mem_insert] at hk
  rcases hk with rfl | hk
  · refine ⟨?_, _, List.prefix_refl _, lift _ hRoot, (EtcdRaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inl rfl), Nat.le_refl _⟩
    intro h
    have := congrArg List.length h
    rw [hlenK] at this
    simp at this; omega
  · obtain ⟨h1, r, h2, h3, h4, h5⟩ := hCR k hk
    exact ⟨h1, r, h2, lift r h3, (EtcdRaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr h4), h5⟩

prove_veil_invariant_goal LeaderCommit CommitSafety using wp by
  have hLHL := hinv.2.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hVHR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLER := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSMS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hFR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLG := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLCf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro r1 r2 hld hsrv c hc1 hc2 hct hq h1 h2
  subst hsrv
  obtain ⟨A, hA⟩ := Option.ne_none_iff_exists'.1 (hLHL a hld)
  have hgd : (st.ledLog a.term).getD [] = A := by rw [hA]; rfl
  rw [hgd] at hc2 hct
  try rw [hgd]
  have hlenK : (SubSeq A 1 c).length = c := by
    rw [subSeq_one, List.length_take, Nat.min_eq_left (by omega)]
  have hM : MRoot th.initV th.chAdd th.chRemove th.chJoint th.chLeave st.msgs st.ledLog st.commits a.term c
      (st.ledAt a.term) A := by
    refine mroot_of_commit _ _ _ _ _ st.msgs st.ledLog st.commits st.ledAt st.elAt st.lIn st.lOut hLCf a.term c A hA
      (by omega) (by omega) hct _ ?_ hq
    intro j hj
    simp only [ackedBy, decide_eq_true_eq] at hj ⊢
    obtain ⟨⟨m, hm⟩, hmm⟩ := hj
    cases m with
    | ack src dst term index =>
      simp only [decide_eq_true_eq] at hmm
      obtain ⟨rfl, rfl, rfl, hidx⟩ := hmm
      exact ⟨_, index, hm, hidx⟩
    | _ => simp at hmm
  have hRoot : Root th.initV th.chAdd th.chRemove th.chJoint th.chLeave st.msgs st.ledLog st.commits
      { server := a.server, term := a.term, entries := SubSeq A 1 c } := by
    refine ⟨st.ledAt a.term, A, ?_, by rw [subSeq_one]; exact List.take_prefix _ _⟩
    show MRoot _ _ _ _ _ _ _ _ a.term (SubSeq A 1 c).length _ A
    rw [hlenK]; exact hM
  have cmp : ∀ b : Commit server value, b ∈ st.commits →
      SubSeq A 1 c <+: b.entries ∨ b.entries <+: SubSeq A 1 c := by
    intro b hb
    obtain ⟨_, r, hbr, hroot, hr, -⟩ := hCR b hb
    exact prefix_cmp_of_roots _ _ _ _ (List.prefix_refl _) hbr
      (roots_cmp _ _ _ _ _ st.msgs st.leaders st.votes st.ledLog st.commits st.ledAt st.elAt st.lIn st.lOut
        hSMS hFR hLG hLS hEQ hLCf hLOld hLHas hVHR hLER
        (fun t L h => (optAll_iff _ _).1 (hLedFL t) L h) _ r hRoot hroot)
  rw [hgd] at h1 h2
  rw [EtcdRaftVeil.Lemmas.mem_insert] at h1 h2
  simp only [isPrefix_iff]
  rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
  · exact Or.inl (List.prefix_refl _)
  · exact cmp r2 h2
  · exact (cmp r1 h1).symm
  · have := hSMS r1 r2 h1 h2
    simpa only [isPrefix_iff] using this

prove_veil_invariant_goal LeaderCommit ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit CommitTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit CommittedEntriesPreserved using wp by
  have hCEP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hld hsrv c hc1 hc2 hct hq j
  rcases hCEP j with h0 | ⟨k, h1, hk, h2⟩
  · exact Or.inl h0
  · exact Or.inr ⟨k, h1, (EtcdRaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr hk), h2⟩

prove_veil_invariant_goal LeaderCommit CommitWithinLog using wp by
  have hCommitWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LeaderCompleteness using wp by
  have hLHL := hinv.2.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hVHR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLER := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSMS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hFR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLG := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLCf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLC := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro (cc : Commit server value) hld hsrv c hc1 hc2 hct hq t hk hlt
  subst hsrv
  rw [EtcdRaftVeil.Lemmas.mem_insert] at hk
  rcases hk with rfl | hk
  · skip
    obtain ⟨A, hA⟩ := Option.ne_none_iff_exists'.1 (hLHL a hld)
    have hgd : (st.ledLog a.term).getD [] = A := by rw [hA]; rfl
    rw [hgd] at hc2 hct
    try rw [hgd]
    have hlenK : (SubSeq A 1 c).length = c := by
      rw [subSeq_one, List.length_take, Nat.min_eq_left (by omega)]
    have hM : MRoot th.initV th.chAdd th.chRemove th.chJoint th.chLeave st.msgs st.ledLog st.commits a.term c
        (st.ledAt a.term) A := by
      refine mroot_of_commit _ _ _ _ _ st.msgs st.ledLog st.commits st.ledAt st.elAt st.lIn st.lOut hLCf a.term c A hA
        (by omega) (by omega) hct _ ?_ hq
      intro j hj
      simp only [ackedBy, decide_eq_true_eq] at hj ⊢
      obtain ⟨⟨m, hm⟩, hmm⟩ := hj
      cases m with
      | ack src dst term index =>
        simp only [decide_eq_true_eq] at hmm
        obtain ⟨rfl, rfl, rfl, hidx⟩ := hmm
        exact ⟨_, index, hm, hidx⟩
      | _ => simp at hmm
    have hRoot : Root th.initV th.chAdd th.chRemove th.chJoint th.chLeave st.msgs st.ledLog st.commits
        { server := a.server, term := a.term, entries := SubSeq A 1 c } := by
      refine ⟨st.ledAt a.term, A, ?_, by rw [subSeq_one]; exact List.take_prefix _ _⟩
      show MRoot _ _ _ _ _ _ _ _ a.term (SubSeq A 1 c).length _ A
      rw [hlenK]; exact hM
    rw [allPrefix_iff]
    intro B hB
    exact root_in_later _ _ _ _ _ st.msgs st.leaders st.votes st.ledLog st.commits st.ledAt st.elAt st.lIn st.lOut
      hSMS hFR hLG hLS hEQ hLCf hLOld hLHas hVHR hLER
      (fun t L h => (optAll_iff _ _).1 (hLedFL t) L h) _ hRoot t (Nat.le_of_lt hlt) B hB
  · exact hLC cc t hk hlt

prove_veil_invariant_goal LeaderCommit ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit ConfIsCommitted using wp by
  have hConfIsCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LeaderConf using wp by
  have hLCf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hld hsrv c hc1 hc2 hct hq t A hA
  subst hsrv
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hLCf t A hA
  have hK := fun k tk => Kof.mono st.commits (TSet.insert
      { server := a.server, term := a.term, entries := SubSeq ((st.ledLog a.term).getD []) 1 c } st.commits)
    (fun k hk => (EtcdRaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr hk)) k tk
  exact ⟨h1, h2, h3, h4, h5.imp id (fun ⟨k, tk, hk, r⟩ => ⟨k, tk, hK k tk hk, r⟩),
    h6.imp id (fun ⟨k, tk, hk, r⟩ => ⟨k, tk, hK k tk hk, r⟩)⟩

prove_veil_invariant_goal LeaderCommit FirstRoot using wp by
  have hLHL := hinv.2.2.2.2.2.2.2.2.2.1
  have hFR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLCf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro k hld hsrv c hc1 hc2 hct hq hk p hp
  subst hsrv
  obtain ⟨A, hA⟩ := Option.ne_none_iff_exists'.1 (hLHL a hld)
  have hgd : (st.ledLog a.term).getD [] = A := by rw [hA]; rfl
  rw [hgd] at hc2 hct
  try rw [hgd]
  have hlenK : (SubSeq A 1 c).length = c := by
    rw [subSeq_one, List.length_take, Nat.min_eq_left (by omega)]
  have hM : MRoot th.initV th.chAdd th.chRemove th.chJoint th.chLeave st.msgs st.ledLog st.commits a.term c
      (st.ledAt a.term) A := by
    refine mroot_of_commit _ _ _ _ _ st.msgs st.ledLog st.commits st.ledAt st.elAt st.lIn st.lOut hLCf a.term c A hA
      (by omega) (by omega) hct _ ?_ hq
    intro j hj
    simp only [ackedBy, decide_eq_true_eq] at hj ⊢
    obtain ⟨⟨m, hm⟩, hmm⟩ := hj
    cases m with
    | ack src dst term index =>
      simp only [decide_eq_true_eq] at hmm
      obtain ⟨rfl, rfl, rfl, hidx⟩ := hmm
      exact ⟨_, index, hm, hidx⟩
    | _ => simp at hmm
  have hRoot : Root th.initV th.chAdd th.chRemove th.chJoint th.chLeave st.msgs st.ledLog st.commits
      { server := a.server, term := a.term, entries := SubSeq A 1 c } := by
    refine ⟨st.ledAt a.term, A, ?_, by rw [subSeq_one]; exact List.take_prefix _ _⟩
    show MRoot _ _ _ _ _ _ _ _ a.term (SubSeq A 1 c).length _ A
    rw [hlenK]; exact hM
  have lift := fun kt h => firstRoot_mono th.initV th.chAdd th.chRemove th.chJoint th.chLeave st.msgs st.msgs
    st.ledLog st.ledLog st.commits
    (TSet.insert { server := a.server, term := a.term, entries := SubSeq A 1 c } st.commits) kt p
    (fun a ha => ha) (fun k hk => (EtcdRaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr hk)) (LedGrows.refl _) h
  rw [hgd] at hk
  rw [EtcdRaftVeil.Lemmas.mem_insert] at hk
  rcases hk with rfl | hk
  · have hpc : 1 ≤ p ∧ p ≤ c := by
      have := MemberCore.isC_le _ _ _ hp
      simp only at this
      rw [hlenK] at this; exact this
    have hpA : MemberCore.isC Entry.isConf A p = true := by
      simp only [subSeq_one] at hp
      rw [← MemberCore.isC_take Entry.isConf A c p hpc.2]; exact hp
    rcases Nat.lt_or_ge (st.ledAt a.term) p with hlt | hge
    · -- the leader does not count with this change yet: this commit is its first
      obtain ⟨es, _, hM'⟩ := MRoot.mono th.initV th.chAdd th.chRemove th.chJoint th.chLeave st.msgs st.msgs
        st.ledLog st.ledLog st.commits
        (TSet.insert { server := a.server, term := a.term, entries := SubSeq A 1 c } st.commits) _ _ _ A
        (fun a ha => ha) (fun k hk => (EtcdRaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr hk)) (LedGrows.refl _) hM
      refine ⟨_, Nat.le_refl _, by simp only [hlenK]; exact hpc.2,
        (EtcdRaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inl rfl), st.ledAt a.term, hlt, A ++ es, ?_, ?_⟩
      · show MRoot _ _ _ _ _ _ _ _ a.term (SubSeq A 1 c).length _ _
        rw [hlenK]; exact hM'
      · rw [subSeq_one]; exact (List.take_prefix _ _).trans (List.prefix_append _ _)
    · -- it does: the change was committed before, under this term or an earlier one
      obtain ⟨_, _, _, _, h5, _⟩ := hLCf a.term A hA
      rcases h5 with h0 | ⟨k0, tk0, ⟨r0, hr0, rfl, rfl⟩, htk, hlk, htake⟩
      · omega
      · have hp0 : MemberCore.isC Entry.isConf r0.entries p = true := by
          rw [MemberCore.isC_congr Entry.isConf r0.entries A (st.ledAt a.term) p htake hge]; exact hpA
        obtain ⟨r, h1, h2, h3⟩ := lift r0.term (hFR r0 hr0 p hp0)
        exact ⟨r, Nat.le_trans h1 htk, h2, h3⟩
  · exact lift k.term (hFR k hk p hp)

prove_veil_invariant_goal LeaderCommit LedOld using wp by
  have hLedOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LegalChain using wp by
  have hLegalChain := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit ReadMsgsOld using wp by
  have hReadMsgsOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit ReadFloorOld using wp by
  have hReadFloorOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit ReadFloorBound using wp by
  have hReadFloorBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit ReadIndexSafety using wp by
  have hReadIndexSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit ReadTermLed using wp by
  have hReadTermLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit ReadFloorRooted using wp by
  have hReadFloorRooted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit ReadFirstRoot using wp by
  have hReadFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit ReadRespBound using wp by
  have hReadRespBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- DeleteSuffix

prove_veil_invariant_goal DeleteSuffix ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix LeaderSync using wp by
  have hLeaderSync := hinv.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix LedOwner using wp by
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intro x
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen hne
  intro hx hxt
  by_cases hj : a.dst = x.server
  · rw [EtcdRaftVeil.Lemmas.ifPos hj]
    have := hLO x hx hxt
    rw [anyPrefix_iff] at this ⊢
    obtain ⟨L, hL, hp⟩ := this
    refine ⟨L, hL, ?_⟩
    rw [subSeq_one, hj]; exact (List.take_prefix _ _).trans hp
  · rw [EtcdRaftVeil.Lemmas.ifNeg hj]; exact hLO x hx hxt

prove_veil_invariant_goal DeleteSuffix LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix LeaderLogIsLed using wp by
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen hne
  intro j hj
  by_cases hd : a.dst = j
  · subst hd
    rw [EtcdRaftVeil.Lemmas.ifPos rfl]
    have := hLLL _ hj
    rw [anyPrefix_iff] at this ⊢
    obtain ⟨L, hL, hp⟩ := this
    exact ⟨L, hL, by rw [subSeq_one]; exact (List.take_prefix _ _).trans hp⟩
  · rw [EtcdRaftVeil.Lemmas.ifNeg hd]; exact hLLL j hj

prove_veil_invariant_goal DeleteSuffix RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix LogFromLed using wp by
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen hne j
  by_cases hj : a.dst = j
  · rw [EtcdRaftVeil.Lemmas.ifPos hj, subSeq_one]; exact FromLed.take _ _ _ (hLFL a.dst)
  · rw [EtcdRaftVeil.Lemmas.ifNeg hj]; exact hLFL j

prove_veil_invariant_goal DeleteSuffix LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix LogMatching using wp by
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen hne
  have hf : FromLed st.ledLog (SubSeq (st.log a.dst) 1 (a.prevLogIndex + k - 1)) := by
    rw [subSeq_one]; exact FromLed.take _ _ _ (hLFL a.dst)
  intro x y k' hk1' hk2'
  refine FromLed.matching st.ledLog _ _ ?_ ?_ k' (List.mem_range'_1.2 ⟨hk1', hk2'⟩)
  · by_cases hj : a.dst = x
    · rw [EtcdRaftVeil.Lemmas.ifPos hj]; exact hf
    · rw [EtcdRaftVeil.Lemmas.ifNeg hj]; exact hLFL x
  · by_cases hj : a.dst = y
    · rw [EtcdRaftVeil.Lemmas.ifPos hj]; exact hf
    · rw [EtcdRaftVeil.Lemmas.ifNeg hj]; exact hLFL y

prove_veil_invariant_goal DeleteSuffix TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix LogTermsBound using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLogTB := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen hne
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hLedL := (optAll_iff _ _).1 (hLedFL a.term) L hL
  intro j k'
  by_cases hj : a.dst = j
  · subst hj; rw [EtcdRaftVeil.Lemmas.ifPos rfl, subSeq_one]
    rcases Nat.lt_or_ge (a.prevLogIndex + k - 1) k' with h | h
    · rw [termAt_le_of_gt _ _ (by simp; omega)]; omega
    · rw [termAt_take _ _ _ h]; exact hLogTB _ _
  · rw [EtcdRaftVeil.Lemmas.ifNeg hj]; exact hLogTB j k'

prove_veil_invariant_goal DeleteSuffix LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix CandLog using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen hne
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hLedL := (optAll_iff _ _).1 (hLedFL a.term) L hL
  intro m hm c u li lt heq hcu hnone
  by_cases hj : a.dst = c
  · subst hj; rw [← hcu, ← hterm, hL] at hnone; cases hnone
  · repeat rw [EtcdRaftVeil.Lemmas.ifNeg hj]
    exact hCL m hm c u li lt heq hcu hnone

prove_veil_invariant_goal DeleteSuffix LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix AckedHeld using wp by
  have hLTB := hinv.2.2.2.2.2.2.2.1
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAH := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen hne
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hLedL := (optAll_iff _ _).1 (hLedFL a.term) L hL
  intro n t A c h
  rcases hAH n t A c h with h1 | h1
  · by_cases hj : a.dst = n
    · subst hj; rw [EtcdRaftVeil.Lemmas.ifPos rfl]
      have hcA := Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' a.dst i' t x' rfl).2.2) h
      rcases delete_held A (st.log a.dst) L c a.prevLogIndex k a.entries hcA h1 hpn hes hk1 (by omega) hlen hne with h2 | h2
      · exact Or.inl h2
      · right
        have hle : t ≤ st.currentTerm a.dst := by
          obtain ⟨i', x, hx, _⟩ := h.2.2.2
          exact (hAF _ hx _ i' t x rfl).2.1
        have hne' : t ≠ a.term := by
          intro heq; subst heq
          have hA := h.1; rw [hL] at hA; cases hA
          exact h2 (List.take_prefix _ _)
        exact ⟨a.term, by omega, by omega, L, hL, h2⟩
    · rw [EtcdRaftVeil.Lemmas.ifNeg hj]; exact Or.inl h1
  · exact Or.inr h1

prove_veil_invariant_goal DeleteSuffix AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix ConfirmedIsLed using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCIL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen hne
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hLedL := (optAll_iff _ _).1 (hLedFL a.term) L hL
  intro j
  by_cases hj : a.dst = j
  · subst hj
    repeat rw [EtcdRaftVeil.Lemmas.ifPos rfl]
    right
    refine ⟨L, hL, ?_⟩
    obtain ⟨h1, h2⟩ := checked_prefix st.ledLog (st.log a.dst) L a.prevLogIndex (k - 1) a.entries (hLFL a.dst) hLedL
      hpn hes hprev (by omega) hfirst
    rw [subSeq_one, show a.prevLogIndex + k - 1 = a.prevLogIndex + (k - 1) by omega]
    exact ⟨by simp; omega, by rw [List.take_take]; simpa using h2⟩
  · repeat rw [EtcdRaftVeil.Lemmas.ifNeg hj]
    exact hCIL j

prove_veil_invariant_goal DeleteSuffix CommitRoot using wp by
  have hCommitRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix CommittedEntriesPreserved using wp by
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hVHR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLER := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCmT := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCEP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCWL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSMS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hFR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLG := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLCf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen hne j
  by_cases hd : a.dst = j
  · subst hd
    rw [EtcdRaftVeil.Lemmas.ifPos rfl]
    rcases hCEP a.dst with h0 | ⟨cc, hsrv, hc, hpre⟩
    · exact Or.inl h0
    · right
      refine ⟨cc, hsrv, hc, ?_⟩
      obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
      obtain ⟨-, r, hcr, hroot, hr, hrt⟩ := hCR cc hc
      have hle : r.term ≤ a.term := by
        have := hCmT cc hc
        rw [hterm, ← hsrv]; omega
      have hB := root_in_later _ _ _ _ _ st.msgs st.leaders st.votes st.ledLog st.commits st.ledAt st.elAt st.lIn st.lOut
        hSMS hFR hLG hLS hEQ hLCf hLOld hLHas hVHR hLER
        (fun t L h => (optAll_iff _ _).1 (hLedFL t) L h) r hroot a.term hle L hL
      rw [isPrefix_iff] at hpre
      have hcut := delete_keeps (st.log a.dst) L (st.commitIndex a.dst) a.prevLogIndex k a.entries
        (hCWL a.dst) ((hpre.trans hcr).trans hB) hpn hes hk1 (by omega) hlen hne
      rw [isPrefix_iff, subSeq_one, List.take_take, Nat.min_eq_left hcut]
      exact hpre
  · rw [EtcdRaftVeil.Lemmas.ifNeg hd]; exact hCEP j

prove_veil_invariant_goal DeleteSuffix CommitWithinLog using wp by
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hVHR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLER := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCmT := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCEP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCWL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSMS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hFR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLG := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLCf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen hne j
  by_cases hd : a.dst = j
  · subst hd
    rw [EtcdRaftVeil.Lemmas.ifPos rfl]
    rcases hCEP a.dst with h0 | ⟨cc, hsrv, hc, hpre⟩
    · rw [h0]; exact Nat.zero_le _
    · skip
      obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
      obtain ⟨-, r, hcr, hroot, hr, hrt⟩ := hCR cc hc
      have hle : r.term ≤ a.term := by
        have := hCmT cc hc
        rw [hterm, ← hsrv]; omega
      have hB := root_in_later _ _ _ _ _ st.msgs st.leaders st.votes st.ledLog st.commits st.ledAt st.elAt st.lIn st.lOut
        hSMS hFR hLG hLS hEQ hLCf hLOld hLHas hVHR hLER
        (fun t L h => (optAll_iff _ _).1 (hLedFL t) L h) r hroot a.term hle L hL
      rw [isPrefix_iff] at hpre
      have hcut := delete_keeps (st.log a.dst) L (st.commitIndex a.dst) a.prevLogIndex k a.entries
        (hCWL a.dst) ((hpre.trans hcr).trans hB) hpn hes hk1 (by omega) hlen hne
      rw [subSeq_one, List.length_take]
      have := hCWL a.dst
      omega
  · rw [EtcdRaftVeil.Lemmas.ifNeg hd]; exact hCWL j

prove_veil_invariant_goal DeleteSuffix AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix ConfirmedWithinLog using wp by
  have hCfWL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen hne i
  by_cases hd : a.dst = i
  · rw [EtcdRaftVeil.Lemmas.ifPos hd, EtcdRaftVeil.Lemmas.ifPos hd, subSeq_one, List.length_take]; omega
  · rw [EtcdRaftVeil.Lemmas.ifNeg hd, EtcdRaftVeil.Lemmas.ifNeg hd]; exact hCfWL i

prove_veil_invariant_goal DeleteSuffix ConfIsCommitted using wp by
  have hConfIsCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix LeaderConf using wp by
  have hLeaderConf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix FirstRoot using wp by
  have hFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix LedOld using wp by
  have hLedOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix LegalChain using wp by
  have hLegalChain := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix ReadMsgsOld using wp by
  have hReadMsgsOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix ReadFloorOld using wp by
  have hReadFloorOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix ReadFloorBound using wp by
  have hReadFloorBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix ReadIndexSafety using wp by
  have hReadIndexSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix ReadTermLed using wp by
  have hReadTermLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix ReadFloorRooted using wp by
  have hReadFloorRooted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix ReadFirstRoot using wp by
  have hReadFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix ReadRespBound using wp by
  have hReadRespBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- StoreEntries

prove_veil_invariant_goal StoreEntries ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries LeaderSync using wp by
  have hLeaderSync := hinv.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries LedOwner using wp by
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro x
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hstore := store_eq st.ledLog (st.log a.dst) L a.prevLogIndex k a.entries (hLFL a.dst)
    ((optAll_iff _ _).1 (hLedFL a.term) L hL) hpn hes hprev (List.mem_range'_1.2 ⟨hk1, hk2⟩) hfirst hlen
  intro hx hxt
  by_cases hj : a.dst = x.server
  · rw [EtcdRaftVeil.Lemmas.ifPos hj, anyPrefix_iff]
    have hxa : x.term = a.term := by rw [hxt, ← hj, hterm]
    refine ⟨L, by rw [hxa]; exact hL, ?_⟩
    show (st.log a.dst ++ SubSeq a.entries k a.entries.length) <+: L
    rw [hstore]; exact List.take_prefix _ _
  · rw [EtcdRaftVeil.Lemmas.ifNeg hj]; exact hLO x hx hxt

prove_veil_invariant_goal StoreEntries LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries LeaderLogIsLed using wp by
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hstore := store_eq st.ledLog (st.log a.dst) L a.prevLogIndex k a.entries (hLFL a.dst)
    ((optAll_iff _ _).1 (hLedFL a.term) L hL) hpn hes hprev (List.mem_range'_1.2 ⟨hk1, hk2⟩) hfirst hlen
  intro j hj
  by_cases hd : a.dst = j
  · subst hd
    rw [EtcdRaftVeil.Lemmas.ifPos rfl, anyPrefix_iff]
    refine ⟨L, by rw [← hterm]; exact hL, ?_⟩
    show (st.log a.dst ++ SubSeq a.entries k a.entries.length) <+: L
    rw [hstore]; exact List.take_prefix _ _
  · rw [EtcdRaftVeil.Lemmas.ifNeg hd]; exact hLLL j hj

prove_veil_invariant_goal StoreEntries RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries LogFromLed using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hnew := store_fromLed st.ledLog (st.log a.dst) L a.prevLogIndex k a.entries (hLFL a.dst)
    ((optAll_iff _ _).1 (hLedFL a.term) L hL) hpn hes hprev
    (List.mem_range'_1.2 ⟨hk1, hk2⟩) hfirst hlen
  intro j
  by_cases hj : a.dst = j
  · rw [EtcdRaftVeil.Lemmas.ifPos hj]; exact hnew
  · rw [EtcdRaftVeil.Lemmas.ifNeg hj]; exact hLFL j

prove_veil_invariant_goal StoreEntries LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries LogMatching using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hnew := store_fromLed st.ledLog (st.log a.dst) L a.prevLogIndex k a.entries (hLFL a.dst)
    ((optAll_iff _ _).1 (hLedFL a.term) L hL) hpn hes hprev
    (List.mem_range'_1.2 ⟨hk1, hk2⟩) hfirst hlen
  intro x y k' hk1' hk2'
  refine FromLed.matching st.ledLog _ _ ?_ ?_ k' (List.mem_range'_1.2 ⟨hk1', hk2'⟩)
  · by_cases hj : a.dst = x
    · rw [EtcdRaftVeil.Lemmas.ifPos hj]; exact hnew
    · rw [EtcdRaftVeil.Lemmas.ifNeg hj]; exact hLFL x
  · by_cases hj : a.dst = y
    · rw [EtcdRaftVeil.Lemmas.ifPos hj]; exact hnew
    · rw [EtcdRaftVeil.Lemmas.ifNeg hj]; exact hLFL y

prove_veil_invariant_goal StoreEntries TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries LogTermsBound using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLogTB := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hLedL := (optAll_iff _ _).1 (hLedFL a.term) L hL
  have hstore := store_eq st.ledLog (st.log a.dst) L a.prevLogIndex k a.entries (hLFL a.dst) hLedL
    hpn hes hprev (List.mem_range'_1.2 ⟨hk1, hk2⟩) hfirst hlen
  intro j k'
  by_cases hj : a.dst = j
  · subst hj; rw [EtcdRaftVeil.Lemmas.ifPos rfl]
    show TermAt (st.log a.dst ++ SubSeq a.entries k a.entries.length) k' ≤ _
    rw [hstore, ← hterm]; exact (Sorted.take L a.term _ (hLS _ L hL)).2 k'
  · rw [EtcdRaftVeil.Lemmas.ifNeg hj]; exact hLogTB j k'

prove_veil_invariant_goal StoreEntries LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries CandLog using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hLedL := (optAll_iff _ _).1 (hLedFL a.term) L hL
  have hstore := store_eq st.ledLog (st.log a.dst) L a.prevLogIndex k a.entries (hLFL a.dst) hLedL
    hpn hes hprev (List.mem_range'_1.2 ⟨hk1, hk2⟩) hfirst hlen
  intro m hm c u li lt heq hcu hnone
  by_cases hj : a.dst = c
  · subst hj; rw [← hcu, ← hterm, hL] at hnone; cases hnone
  · repeat rw [EtcdRaftVeil.Lemmas.ifNeg hj]
    exact hCL m hm c u li lt heq hcu hnone

prove_veil_invariant_goal StoreEntries LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries AckedHeld using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAH := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hLedL := (optAll_iff _ _).1 (hLedFL a.term) L hL
  have hstore := store_eq st.ledLog (st.log a.dst) L a.prevLogIndex k a.entries (hLFL a.dst) hLedL
    hpn hes hprev (List.mem_range'_1.2 ⟨hk1, hk2⟩) hfirst hlen
  intro n t A c h
  rcases hAH n t A c h with h1 | h1
  · left
    by_cases hj : a.dst = n
    · subst hj; rw [EtcdRaftVeil.Lemmas.ifPos rfl]; exact h1.trans (List.prefix_append _ _)
    · rw [EtcdRaftVeil.Lemmas.ifNeg hj]; exact h1
  · exact Or.inr h1

prove_veil_invariant_goal StoreEntries AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries ConfirmedIsLed using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCIL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hLedL := (optAll_iff _ _).1 (hLedFL a.term) L hL
  have hstore := store_eq st.ledLog (st.log a.dst) L a.prevLogIndex k a.entries (hLFL a.dst) hLedL
    hpn hes hprev (List.mem_range'_1.2 ⟨hk1, hk2⟩) hfirst hlen
  intro j
  by_cases hj : a.dst = j
  · subst hj
    repeat rw [EtcdRaftVeil.Lemmas.ifPos rfl]
    right
    refine ⟨L, hL, ?_⟩
    show _ ≤ (st.log a.dst ++ SubSeq a.entries k a.entries.length).length ∧
      List.take _ (st.log a.dst ++ SubSeq a.entries k a.entries.length) = _
    rw [hstore]
    exact ⟨by simp; omega, by rw [List.take_take]; simp⟩
  · repeat rw [EtcdRaftVeil.Lemmas.ifNeg hj]
    exact hCIL j

prove_veil_invariant_goal StoreEntries CommitRoot using wp by
  have hCommitRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries CommittedEntriesPreserved using wp by
  have hCEP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCWL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen j
  by_cases hd : a.dst = j
  · subst hd
    rw [EtcdRaftVeil.Lemmas.ifPos rfl]
    rcases hCEP a.dst with h0 | ⟨cc, h1, hc, h2⟩
    · exact Or.inl h0
    · refine Or.inr ⟨cc, h1, hc, ?_⟩
      show IsPrefix (List.take (st.commitIndex a.dst) (st.log a.dst ++ SubSeq a.entries k a.entries.length)) cc.entries = true
      rw [List.take_append_of_le_length (hCWL a.dst)]; exact h2
  · rw [EtcdRaftVeil.Lemmas.ifNeg hd]; exact hCEP j

prove_veil_invariant_goal StoreEntries CommitWithinLog using wp by
  have hCWL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen j
  by_cases hd : a.dst = j
  · subst hd
    rw [EtcdRaftVeil.Lemmas.ifPos rfl]
    have := hCWL a.dst
    show st.commitIndex a.dst ≤ (st.log a.dst ++ SubSeq a.entries k a.entries.length).length
    rw [List.length_append]
    omega
  · rw [EtcdRaftVeil.Lemmas.ifNeg hd]; exact hCWL j

prove_veil_invariant_goal StoreEntries AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries ConfirmedWithinLog using wp by
  have hCfWL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen i
  by_cases hd : a.dst = i
  · rw [EtcdRaftVeil.Lemmas.ifPos hd, EtcdRaftVeil.Lemmas.ifPos hd]
    show _ ≤ (st.log a.dst ++ SubSeq a.entries k a.entries.length).length
    simp only [SubSeq, List.length_append, List.length_take, List.length_drop]; omega
  · rw [EtcdRaftVeil.Lemmas.ifNeg hd, EtcdRaftVeil.Lemmas.ifNeg hd]; exact hCfWL i

prove_veil_invariant_goal StoreEntries ConfIsCommitted using wp by
  have hConfIsCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries LeaderConf using wp by
  have hLeaderConf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries FirstRoot using wp by
  have hFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries LedOld using wp by
  have hLedOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries LegalChain using wp by
  have hLegalChain := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries ReadMsgsOld using wp by
  have hReadMsgsOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries ReadFloorOld using wp by
  have hReadFloorOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries ReadFloorBound using wp by
  have hReadFloorBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries ReadIndexSafety using wp by
  have hReadIndexSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries ReadTermLed using wp by
  have hReadTermLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries ReadFloorRooted using wp by
  have hReadFloorRooted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries ReadFirstRoot using wp by
  have hReadFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries ReadRespBound using wp by
  have hReadRespBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- Ack

prove_veil_invariant_goal Ack ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack GrantsAreVotes using wp by
  have hGV := hinv.2.2.2.2.1
  clear hinv
  intros
  simp only [EtcdRaftVeil.Lemmas.mem_iff, EtcdRaftVeil.Lemmas.contains_insert_iff] at *
  repeat' split
  all_goals grind only

prove_veil_invariant_goal Ack LeaderSync using wp by
  have hLeaderSync := hinv.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack AckFacts using wp by
  have hAFL := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (m : Msg server value) ha hisA hterm hprev hfirst | intro ha hisA hterm hprev hfirst (m : Msg server value)
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hLedL := (optAll_iff _ _).1 (hLedFL a.term) L hL
  have hchk := checked_prefix st.ledLog (st.log a.dst) L a.prevLogIndex a.entries.length a.entries (hLFL a.dst) hLedL
    hpn hes hprev (Nat.le_refl _) hfirst
  have hldr : TSet.contains ({ server := a.src, term := a.term } : Elected server) st.leaders = true := by
    have h := hAFL a ha
    cases a with
    | append src dst term p pt es c =>
      exact h
    | _ => simp [Msg.isAppend] at hisA
  intro hm j i' t x heq
  rw [EtcdRaftVeil.Lemmas.mem_insert] at hm
  rcases hm with rfl | hm
  · injection heq with h1 h2 h3 h4
    subst h1 h2 h3 h4
    exact ⟨hldr, by omega, L, hL, hpn⟩
  · exact hAF m hm j i' t x heq

prove_veil_invariant_goal Ack AckedHeld using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAH := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev hfirst
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hLedL := (optAll_iff _ _).1 (hLedFL a.term) L hL
  have hchk := checked_prefix st.ledLog (st.log a.dst) L a.prevLogIndex a.entries.length a.entries (hLFL a.dst) hLedL
    hpn hes hprev (Nat.le_refl _) hfirst
  intro n t A c h
  rcases Acked.of_insert_ack _ _ _ _ _ _ _ _ _ _ _ h with h' | ⟨rfl, rfl, hc, hA, hc2, hct⟩
  · exact hAH n t A c h'
  · left
    rw [hL] at hA; cases hA
    rw [take_prefix_iff _ _ _ (by omega)]
    refine ⟨by omega, ?_⟩
    have := congrArg (List.take c) hchk.2
    rw [List.take_take, List.take_take, Nat.min_eq_left hc] at this
    exact this.symm

prove_veil_invariant_goal Ack AckVote using wp by
  have hVT := hinv.2.2.1
  have hVB := hinv.2.2.2.1
  have hAV := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (v : Vote server) ha hisA hterm hprev hfirst | intro ha hisA hterm hprev hfirst (v : Vote server)
  intro n t A c h hv hvn htv li lt hreq
  rcases (EtcdRaftVeil.Lemmas.contains_insert_iff _ _ _).1 hreq with hh | hreq'
  · cases hh
  · rcases Acked.of_insert_ack _ _ _ _ _ _ _ _ _ _ _ h with h' | ⟨rfl, rfl, _⟩
    · exact hAV v n t A c h' hv hvn htv li lt hreq'
    · have h1 := hVB v hv
      have h2 := hVT v.voter
      rw [hvn] at h1 h2
      omega

prove_veil_invariant_goal Ack EarlyQuorum using wp by
  have hVT := hinv.2.2.1
  have hVB := hinv.2.2.2.1
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (ld : Elected server) ha hisA hterm hprev hfirst | intro ha hisA hterm hprev hfirst (ld : Elected server)
  intro hld B hB
  refine MemberCore.IsQ.mono _ _ _ ?_ (hEQ ld hld B hB)
  intro n hn
  simp only [decide_eq_true_eq] at hn ⊢
  refine ⟨hn.1, ?_⟩
  intro t A c ha' htu li lt hr
  rw [EtcdRaftVeil.Lemmas.mem_insert] at hr
  rcases hr with hh | hr
  · cases hh
  · rcases Acked.of_insert_ack _ _ _ _ _ _ _ _ _ _ _ ha' with h' | ⟨rfl, rfl, _⟩
    · exact hn.2 t A c h' htu li lt hr
    · have h1 := hVB _ hn.1
      have h2 := hVT a.dst
      simp only at h1
      omega

prove_veil_invariant_goal Ack ConfirmedIsLed using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCIL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev hfirst
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hLedL := (optAll_iff _ _).1 (hLedFL a.term) L hL
  have hchk := checked_prefix st.ledLog (st.log a.dst) L a.prevLogIndex a.entries.length a.entries (hLFL a.dst) hLedL
    hpn hes hprev (Nat.le_refl _) hfirst
  intro j
  by_cases hj : a.dst = j
  · subst hj
    repeat rw [EtcdRaftVeil.Lemmas.ifPos rfl]
    by_cases hct' : st.confirmedTerm a.dst = a.term
    · repeat rw [EtcdRaftVeil.Lemmas.ifPos hct']
      rcases Nat.le_total (st.confirmedIndex a.dst) (a.prevLogIndex + a.entries.length) with hle | hle
      · rw [Nat.max_eq_right hle]; exact Or.inr ⟨L, hL, hchk.1, hchk.2⟩
      · rw [Nat.max_eq_left hle]
        rcases hCIL a.dst with h0 | ⟨L0, hL0, h1, h2⟩
        · exact Or.inl h0
        · rw [hct', hL] at hL0; cases hL0; exact Or.inr ⟨L, hL, h1, h2⟩
    · repeat rw [EtcdRaftVeil.Lemmas.ifNeg hct']
      exact Or.inr ⟨L, hL, hchk.1, hchk.2⟩
  · repeat rw [EtcdRaftVeil.Lemmas.ifNeg hj]
    exact hCIL j

prove_veil_invariant_goal Ack CommitRoot using wp by
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro k
  intros
  rename_i hk
  obtain ⟨h1, r, h2, h3, h4, h5⟩ := hCR k hk
  exact ⟨h1, r, h2, Root.mono _ _ _ _ _ _ _ _ _ _ _ _ (fun a ha => (EtcdRaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr ha))
    (fun a ha => ha) (LedGrows.refl _) h3, h4, h5⟩

prove_veil_invariant_goal Ack CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack CommitWithinLog using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack ConfirmedWithinLog using wp by
  have hCfWL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev hfirst i
  by_cases hd : a.dst = i
  · subst hd
    rw [EtcdRaftVeil.Lemmas.ifPos rfl]
    have hlast := ack_within _ _ _ _ hprev hfirst
    have := hCfWL a.dst
    split <;> omega
  · rw [EtcdRaftVeil.Lemmas.ifNeg hd]; exact hCfWL i

prove_veil_invariant_goal Ack ConfIsCommitted using wp by
  have hConfIsCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LeaderConf using wp by
  have hLeaderConf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack FirstRoot using wp by
  have hFR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro k
  intros
  rename_i hk p hp
  exact firstRoot_mono _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a ha => (EtcdRaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr ha))
    (fun a ha => ha) (LedGrows.refl _) (hFR k hk p hp)

prove_veil_invariant_goal Ack LedOld using wp by
  have hLedOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LegalChain using wp by
  have hLegalChain := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack ReadMsgsOld using wp by
  have hReadMsgsOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack ReadFloorOld using wp by
  have hReadFloorOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack ReadFloorBound using wp by
  have hReadFloorBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack ReadIndexSafety using wp by
  have hReadIndexSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack ReadTermLed using wp by
  have hReadTermLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack ReadFloorRooted using wp by
  have hReadFloorRooted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack ReadFirstRoot using wp by
  have hReadFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack ReadRespBound using wp by
  have hReadRespBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- AckCommitted

prove_veil_invariant_goal AckCommitted ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted GrantsAreVotes using wp by
  have hGV := hinv.2.2.2.2.1
  clear hinv
  intros
  simp only [EtcdRaftVeil.Lemmas.mem_iff, EtcdRaftVeil.Lemmas.contains_insert_iff] at *
  repeat' split
  all_goals grind only

prove_veil_invariant_goal AckCommitted LeaderSync using wp by
  have hLeaderSync := hinv.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted AckFacts using wp by
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hAFL := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hVHR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLER := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAH := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCmT := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCEP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCWL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSMS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hFR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLG := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLCf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (m : Msg server value) ha hisA hterm hlt | intro ha hisA hterm hlt (m : Msg server value)
  obtain ⟨L, hL, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  -- a.dst's committed prefix is in its term's leader log (leader completeness, or its own log).
  have hpre : st.commitIndex a.dst ≤ L.length ∧ st.commitIndex a.dst ≤ (st.log a.dst).length ∧
      (st.log a.dst).take (st.commitIndex a.dst) = L.take (st.commitIndex a.dst) := by
    rcases hCEP a.dst with h0 | ⟨k, hk1, hk2, hk3⟩
    · exact absurd hlt (by omega)
    · obtain ⟨-, r, hkr, hroot, hrm, hrt⟩ := hCR k hk2
      have hkt := hCmT k hk2
      rw [hk1] at hkt
      have hB := root_in_later _ _ _ _ _ st.msgs st.leaders st.votes st.ledLog st.commits st.ledAt st.elAt st.lIn st.lOut
        hSMS hFR hLG hLS hEQ hLCf hLOld hLHas hVHR hLER
        (fun t L h => (optAll_iff _ _).1 (hLedFL t) L h) r hroot a.term (by omega) L hL
      rw [isPrefix_iff] at hk3
      have hcL := (hk3.trans hkr).trans hB
      have hcw := hCWL a.dst
      rw [take_prefix_iff _ _ _ hcw] at hcL
      exact ⟨hcL.1, hcw, hcL.2⟩
  have hldr : TSet.contains ({ server := a.src, term := a.term } : Elected server) st.leaders = true := by
    have h := hAFL a ha
    cases a with
    | append src dst term p pt es c =>
      exact h
    | _ => simp [Msg.isAppend] at hisA
  intro hm j i' t x heq
  rw [EtcdRaftVeil.Lemmas.mem_insert] at hm
  rcases hm with rfl | hm
  · injection heq with h1 h2 h3 h4
    subst h1 h2 h3 h4
    exact ⟨hldr, by omega, L, hL, hpre.1⟩
  · exact hAF m hm j i' t x heq

prove_veil_invariant_goal AckCommitted AckedHeld using wp by
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hAFL := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hVHR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLER := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAH := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCmT := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCEP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCWL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSMS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hFR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLG := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLCf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hlt
  obtain ⟨L, hL, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  -- a.dst's committed prefix is in its term's leader log (leader completeness, or its own log).
  have hpre : st.commitIndex a.dst ≤ L.length ∧ st.commitIndex a.dst ≤ (st.log a.dst).length ∧
      (st.log a.dst).take (st.commitIndex a.dst) = L.take (st.commitIndex a.dst) := by
    rcases hCEP a.dst with h0 | ⟨k, hk1, hk2, hk3⟩
    · exact absurd hlt (by omega)
    · obtain ⟨-, r, hkr, hroot, hrm, hrt⟩ := hCR k hk2
      have hkt := hCmT k hk2
      rw [hk1] at hkt
      have hB := root_in_later _ _ _ _ _ st.msgs st.leaders st.votes st.ledLog st.commits st.ledAt st.elAt st.lIn st.lOut
        hSMS hFR hLG hLS hEQ hLCf hLOld hLHas hVHR hLER
        (fun t L h => (optAll_iff _ _).1 (hLedFL t) L h) r hroot a.term (by omega) L hL
      rw [isPrefix_iff] at hk3
      have hcL := (hk3.trans hkr).trans hB
      have hcw := hCWL a.dst
      rw [take_prefix_iff _ _ _ hcw] at hcL
      exact ⟨hcL.1, hcw, hcL.2⟩
  intro n t A c h
  rcases Acked.of_insert_ack _ _ _ _ _ _ _ _ _ _ _ h with h' | ⟨rfl, rfl, hc, hA, hc2, hct⟩
  · exact hAH n t A c h'
  · left
    rw [hL] at hA; cases hA
    rw [take_prefix_iff _ _ _ (by omega)]
    refine ⟨by omega, ?_⟩
    have := congrArg (List.take c) hpre.2.2
    rw [List.take_take, List.take_take, Nat.min_eq_left hc] at this
    exact this.symm

prove_veil_invariant_goal AckCommitted AckVote using wp by
  have hVT := hinv.2.2.1
  have hVB := hinv.2.2.2.1
  have hAV := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (v : Vote server) ha hisA hterm hlt | intro ha hisA hterm hlt (v : Vote server)
  intro n t A c h hv hvn htv li lt hreq
  rcases (EtcdRaftVeil.Lemmas.contains_insert_iff _ _ _).1 hreq with hh | hreq'
  · cases hh
  · rcases Acked.of_insert_ack _ _ _ _ _ _ _ _ _ _ _ h with h' | ⟨rfl, rfl, _⟩
    · exact hAV v n t A c h' hv hvn htv li lt hreq'
    · have h1 := hVB v hv
      have h2 := hVT v.voter
      rw [hvn] at h1 h2
      omega

prove_veil_invariant_goal AckCommitted EarlyQuorum using wp by
  have hVT := hinv.2.2.1
  have hVB := hinv.2.2.2.1
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (ld : Elected server) ha hisA hterm hlt | intro ha hisA hterm hlt (ld : Elected server)
  intro hld B hB
  refine MemberCore.IsQ.mono _ _ _ ?_ (hEQ ld hld B hB)
  intro n hn
  simp only [decide_eq_true_eq] at hn ⊢
  refine ⟨hn.1, ?_⟩
  intro t A c ha' htu li lt hr
  rw [EtcdRaftVeil.Lemmas.mem_insert] at hr
  rcases hr with hh | hr
  · cases hh
  · rcases Acked.of_insert_ack _ _ _ _ _ _ _ _ _ _ _ ha' with h' | ⟨rfl, rfl, _⟩
    · exact hn.2 t A c h' htu li lt hr
    · have h1 := hVB _ hn.1
      have h2 := hVT a.dst
      simp only at h1
      omega

prove_veil_invariant_goal AckCommitted ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted CommitRoot using wp by
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro k
  intros
  rename_i hk
  obtain ⟨h1, r, h2, h3, h4, h5⟩ := hCR k hk
  exact ⟨h1, r, h2, Root.mono _ _ _ _ _ _ _ _ _ _ _ _ (fun a ha => (EtcdRaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr ha))
    (fun a ha => ha) (LedGrows.refl _) h3, h4, h5⟩

prove_veil_invariant_goal AckCommitted CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted CommitWithinLog using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted ConfIsCommitted using wp by
  have hConfIsCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted LeaderConf using wp by
  have hLeaderConf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted FirstRoot using wp by
  have hFR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro k
  intros
  rename_i hk p hp
  exact firstRoot_mono _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a ha => (EtcdRaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr ha))
    (fun a ha => ha) (LedGrows.refl _) (hFR k hk p hp)

prove_veil_invariant_goal AckCommitted LedOld using wp by
  have hLedOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted LegalChain using wp by
  have hLegalChain := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted ReadMsgsOld using wp by
  have hReadMsgsOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted ReadFloorOld using wp by
  have hReadFloorOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted ReadFloorBound using wp by
  have hReadFloorBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted ReadIndexSafety using wp by
  have hReadIndexSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted ReadTermLed using wp by
  have hReadTermLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted ReadFloorRooted using wp by
  have hReadFloorRooted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted ReadFirstRoot using wp by
  have hReadFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AckCommitted ReadRespBound using wp by
  have hReadRespBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- FollowerCommit

prove_veil_invariant_goal FollowerCommit ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LeaderSync using wp by
  have hLeaderSync := hinv.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit RequestsFromLed using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  rename_i m hm
  refine req_mono st.ledLog st.ledLog _ _ m (hRFL m hm) (fun t l h => ⟨l, h, List.prefix_refl _⟩) ?_
  · intro t l l' c hp hx
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
    exact commitPart_mono st.commits _ (fun k hk => (EtcdRaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr hk)) l l' c t hp hx

prove_veil_invariant_goal FollowerCommit LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit AckedHeld using wp by
  have hAckedHeld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit CommitRoot using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCIL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro k ha hisA hct c hc1 hc2 hci hcm hk
  obtain ⟨L, hL, hpn, hpt, hes, hX⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hX
  have hcmin : c ≤ a.commit ∧ c ≤ st.confirmedIndex a.dst := by omega
  rcases hX with h0 | ⟨hcl, ⟨kk, hkk⟩, hkt, hk1, hk2⟩
  · omega
  rcases hCIL a.dst with h0 | ⟨L0, hL0, hc1', hc2'⟩
  · omega
  rw [← hct, hL] at hL0; cases hL0
  have hlenK : (SubSeq (st.log a.dst) 1 c).length = c := by
    rw [subSeq_one, List.length_take, Nat.min_eq_left (by omega)]
  have hK : SubSeq (st.log a.dst) 1 c <+: kk.entries := by
    rw [subSeq_one]
    have e1 : (st.log a.dst).take c = L.take c := by
      have := congrArg (List.take c) hc2'
      rwa [List.take_take, List.take_take, Nat.min_eq_left hcmin.2] at this
    have e2 : kk.entries.take c = L.take c := by
      rw [subSeq_one, subSeq_one] at hk2
      have := congrArg (List.take c) hk2
      rwa [List.take_take, List.take_take, Nat.min_eq_left hcmin.1] at this
    rw [e1, ← e2]; exact List.take_prefix _ _
  have lift : ∀ r : Commit server value,
      Root th.initV th.chAdd th.chRemove th.chJoint th.chLeave st.msgs st.ledLog st.commits r →
      Root th.initV th.chAdd th.chRemove th.chJoint th.chLeave st.msgs st.ledLog
        (TSet.insert { server := a.dst, term := a.term, entries := SubSeq (st.log a.dst) 1 c } st.commits) r :=
    fun r h => Root.mono _ _ _ _ _ _ _ _ _ _ _ _ (fun a ha => ha)
      (fun k hk => (EtcdRaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr hk)) (LedGrows.refl _) h
  rw [EtcdRaftVeil.Lemmas.mem_insert] at hk
  rcases hk with rfl | hk
  · obtain ⟨_, r, hkr, hroot, hr, hrt⟩ := hCR kk hkk
    refine ⟨?_, r, hK.trans hkr, lift r hroot, (EtcdRaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr hr), Nat.le_trans hrt hkt⟩
    intro h
    have := congrArg List.length h
    rw [hlenK] at this
    simp at this; omega
  · obtain ⟨h1, r, h2, h3, h4, h5⟩ := hCR k hk
    exact ⟨h1, r, h2, lift r h3, (EtcdRaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr h4), h5⟩

prove_veil_invariant_goal FollowerCommit CommitSafety using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCIL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSMS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro r1 r2 ha hisA hct c hc1 hc2 hci hcm h1 h2
  obtain ⟨L, hL, hpn, hpt, hes, hX⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hX
  have hcmin : c ≤ a.commit ∧ c ≤ st.confirmedIndex a.dst := by omega
  rcases hX with h0 | ⟨hcl, ⟨kk, hkk⟩, hkt, hk1, hk2⟩
  · omega
  rcases hCIL a.dst with h0 | ⟨L0, hL0, hc1', hc2'⟩
  · omega
  rw [← hct, hL] at hL0; cases hL0
  have hlenK : (SubSeq (st.log a.dst) 1 c).length = c := by
    rw [subSeq_one, List.length_take, Nat.min_eq_left (by omega)]
  have hK : SubSeq (st.log a.dst) 1 c <+: kk.entries := by
    rw [subSeq_one]
    have e1 : (st.log a.dst).take c = L.take c := by
      have := congrArg (List.take c) hc2'
      rwa [List.take_take, List.take_take, Nat.min_eq_left hcmin.2] at this
    have e2 : kk.entries.take c = L.take c := by
      rw [subSeq_one, subSeq_one] at hk2
      have := congrArg (List.take c) hk2
      rwa [List.take_take, List.take_take, Nat.min_eq_left hcmin.1] at this
    rw [e1, ← e2]; exact List.take_prefix _ _
  have cmp : ∀ b : Commit server value, b ∈ st.commits →
      SubSeq (st.log a.dst) 1 c <+: b.entries ∨ b.entries <+: SubSeq (st.log a.dst) 1 c := by
    intro b hb
    have := hSMS kk b hkk hb
    simp only [isPrefix_iff] at this
    rcases this with h | h
    · exact Or.inl (hK.trans h)
    · exact prefix_cmp_of_prefix _ _ kk.entries hK h
  rw [EtcdRaftVeil.Lemmas.mem_insert] at h1 h2
  simp only [isPrefix_iff]
  rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
  · exact Or.inl (List.prefix_refl _)
  · exact cmp r2 h2
  · exact (cmp r1 h1).symm
  · have := hSMS r1 r2 h1 h2
    simpa only [isPrefix_iff] using this

prove_veil_invariant_goal FollowerCommit ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit CommitTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit CommittedEntriesPreserved using wp by
  have hCEP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hct c hc1 hc2 hci hcm j
  by_cases hd : a.dst = j
  · subst hd
    rw [EtcdRaftVeil.Lemmas.ifPos rfl]
    refine Or.inr ⟨{ server := a.dst, term := a.term, entries := SubSeq (st.log a.dst) 1 c }, rfl,
      (EtcdRaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inl rfl), ?_⟩
    show IsPrefix ((st.log a.dst).take c) (SubSeq (st.log a.dst) 1 c) = true
    rw [isPrefix_iff, subSeq_one]; exact List.prefix_refl _
  · rw [EtcdRaftVeil.Lemmas.ifNeg hd]
    rcases hCEP j with h0 | ⟨k, hk1, hk2, hk3⟩
    · exact Or.inl h0
    · exact Or.inr ⟨k, hk1, (EtcdRaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr hk2), hk3⟩

prove_veil_invariant_goal FollowerCommit CommitWithinLog using wp by
  have hCWL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCfWL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hct c hc1 hc2 hci hcm j
  by_cases hd : a.dst = j
  · subst hd
    rw [EtcdRaftVeil.Lemmas.ifPos rfl]
    have := hCfWL a.dst
    omega
  · rw [EtcdRaftVeil.Lemmas.ifNeg hd]; exact hCWL j

prove_veil_invariant_goal FollowerCommit AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LeaderCompleteness using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCIL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLC := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro (cc : Commit server value) ha hisA hct c hc1 hc2 hci hcm t hk hlt
  rw [EtcdRaftVeil.Lemmas.mem_insert] at hk
  rcases hk with rfl | hk
  · obtain ⟨L, hL, hpn, hpt, hes, hX⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hX
    have hcmin : c ≤ a.commit ∧ c ≤ st.confirmedIndex a.dst := by omega
    rcases hX with h0 | ⟨hcl, ⟨kk, hkk⟩, hkt, hk1, hk2⟩
    · omega
    rcases hCIL a.dst with h0 | ⟨L0, hL0, hc1', hc2'⟩
    · omega
    rw [← hct, hL] at hL0; cases hL0
    have hK : SubSeq (st.log a.dst) 1 c <+: kk.entries := by
      rw [subSeq_one]
      have e1 : (st.log a.dst).take c = L.take c := by
        have := congrArg (List.take c) hc2'
        rwa [List.take_take, List.take_take, Nat.min_eq_left hcmin.2] at this
      have e2 : kk.entries.take c = L.take c := by
        rw [subSeq_one, subSeq_one] at hk2
        have := congrArg (List.take c) hk2
        rwa [List.take_take, List.take_take, Nat.min_eq_left hcmin.1] at this
      rw [e1, ← e2]; exact List.take_prefix _ _
    have := hLC kk t hkk (Nat.lt_of_le_of_lt hkt hlt)
    rw [allPrefix_iff] at this ⊢
    intro B hB
    exact hK.trans (this B hB)
  · exact hLC cc t hk hlt

prove_veil_invariant_goal FollowerCommit ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit ConfIsCommitted using wp by
  have hConfIsCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LeaderConf using wp by
  have hLCf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hct c hc1 hc2 hci hcm t A hA
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hLCf t A hA
  have hK : ∀ k tk, Kof st.commits k tk →
      Kof (TSet.insert { server := a.dst, term := a.term, entries := SubSeq (st.log a.dst) 1 c } st.commits) k tk :=
    fun k tk ⟨r, hr, e1, e2⟩ => ⟨r, (EtcdRaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr hr), e1, e2⟩
  exact ⟨h1, h2, h3, h4, h5.imp id (fun ⟨k, tk, hk, r⟩ => ⟨k, tk, hK k tk hk, r⟩),
    h6.imp id (fun ⟨k, tk, hk, r⟩ => ⟨k, tk, hK k tk hk, r⟩)⟩

prove_veil_invariant_goal FollowerCommit FirstRoot using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCIL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hFR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro k ha hisA hct c hc1 hc2 hci hcm hk p hp
  obtain ⟨L, hL, hpn, hpt, hes, hX⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hX
  have hcmin : c ≤ a.commit ∧ c ≤ st.confirmedIndex a.dst := by omega
  rcases hX with h0 | ⟨hcl, ⟨kk, hkk⟩, hkt, hk1, hk2⟩
  · omega
  rcases hCIL a.dst with h0 | ⟨L0, hL0, hc1', hc2'⟩
  · omega
  rw [← hct, hL] at hL0; cases hL0
  have hlenK : (SubSeq (st.log a.dst) 1 c).length = c := by
    rw [subSeq_one, List.length_take, Nat.min_eq_left (by omega)]
  have hK : SubSeq (st.log a.dst) 1 c <+: kk.entries := by
    rw [subSeq_one]
    have e1 : (st.log a.dst).take c = L.take c := by
      have := congrArg (List.take c) hc2'
      rwa [List.take_take, List.take_take, Nat.min_eq_left hcmin.2] at this
    have e2 : kk.entries.take c = L.take c := by
      rw [subSeq_one, subSeq_one] at hk2
      have := congrArg (List.take c) hk2
      rwa [List.take_take, List.take_take, Nat.min_eq_left hcmin.1] at this
    rw [e1, ← e2]; exact List.take_prefix _ _
  have lift := fun kt h => firstRoot_mono th.initV th.chAdd th.chRemove th.chJoint th.chLeave st.msgs st.msgs
    st.ledLog st.ledLog st.commits
    (TSet.insert { server := a.dst, term := a.term, entries := SubSeq (st.log a.dst) 1 c } st.commits) kt p
    (fun a ha => ha) (fun k hk => (EtcdRaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr hk)) (LedGrows.refl _) h
  rw [EtcdRaftVeil.Lemmas.mem_insert] at hk
  rcases hk with rfl | hk
  · have hp' : MemberCore.isC Entry.isConf kk.entries p = true := by
      have hple := (MemberCore.isC_le _ _ _ hp).2
      simp only at hple
      rw [hlenK] at hple
      obtain ⟨s, hs⟩ := hK
      rw [← hs, isC_append _ _ _ (by rw [hlenK]; exact hple)]; exact hp
    obtain ⟨r, h1, h2, h3⟩ := lift kk.term (hFR kk hkk p hp')
    exact ⟨r, Nat.le_trans h1 hkt, h2, h3⟩
  · exact lift k.term (hFR k hk p hp)

prove_veil_invariant_goal FollowerCommit LedOld using wp by
  have hLedOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LegalChain using wp by
  have hLegalChain := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit ReadMsgsOld using wp by
  have hReadMsgsOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit ReadFloorOld using wp by
  have hReadFloorOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit ReadFloorBound using wp by
  have hReadFloorBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit ReadIndexSafety using wp by
  have hReadIndexSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit ReadTermLed using wp by
  have hReadTermLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit ReadFloorRooted using wp by
  have hReadFloorRooted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit ReadFirstRoot using wp by
  have hReadFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit ReadRespBound using wp by
  have hReadRespBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- Apply

prove_veil_invariant_goal Apply ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LeaderSync using wp by
  have hLeaderSync := hinv.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply AckedHeld using wp by
  have hAckedHeld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply CommitRoot using wp by
  have hCommitRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply CommitWithinLog using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply AppliedCommitted using wp by
  have hAC := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro (cc : Commit server value) (x : Applied server value) h1 hle hcc heq hx
  rw [EtcdRaftVeil.Lemmas.mem_insert] at hx
  rcases hx with rfl | hx
  · refine ⟨Nat.le_add_left 1 _, cc, hcc, ?_⟩
    show cc.entries[st.lastApplied i + 1 - 1]? = some _
    rw [Nat.add_sub_cancel]
    exact applied_entry _ _ _ _ h1 hle heq
  · exact hAC x hx

prove_veil_invariant_goal Apply StateMachineSafety using wp by
  have hSMS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCEP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCWL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAC := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSM := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro (cc : Commit server value) (x : Applied server value) (y : Applied server value) h1 hle hcc heq hx hy hxy
  have hnew : ∃ k : Commit server value, k ∈ st.commits ∧
      k.entries[st.lastApplied i]? = some ((st.log i)[st.lastApplied i]?.getD noEntry) :=
    ⟨cc, hcc, applied_entry _ _ _ _ h1 hle heq⟩
  have cmp : ∀ k k' : Commit server value, k ∈ st.commits → k' ∈ st.commits →
      k.entries <+: k'.entries ∨ k'.entries <+: k.entries := by
    intro k k' hk hk'
    have := hSMS k k' hk hk'
    simpa only [isPrefix_iff] using this
  rw [EtcdRaftVeil.Lemmas.mem_insert] at hx hy
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · rfl
  · obtain ⟨k, hk, hke⟩ := hnew
    obtain ⟨hy1, k', hk', hke'⟩ := hAC y hy
    simp only at hxy
    rw [← hxy] at hke'
    exact prefix_get_eq _ _ _ _ _ (cmp k k' hk hk') hke hke'
  · obtain ⟨k, hk, hke⟩ := hnew
    obtain ⟨hx1, k', hk', hke'⟩ := hAC x hx
    simp only at hxy
    rw [hxy] at hke'
    exact prefix_get_eq _ _ _ _ _ (cmp k' k hk' hk) hke' hke
  · exact hSM x y hx hy hxy

prove_veil_invariant_goal Apply LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply ConfIsCommitted using wp by
  have hConfIsCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LeaderConf using wp by
  have hLeaderConf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply FirstRoot using wp by
  have hFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LedOld using wp by
  have hLedOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LegalChain using wp by
  have hLegalChain := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply ReadMsgsOld using wp by
  have hReadMsgsOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply ReadFloorOld using wp by
  have hReadFloorOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply ReadFloorBound using wp by
  have hReadFloorBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply ReadIndexSafety using wp by
  have hReadIndexSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply ReadTermLed using wp by
  have hReadTermLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply ReadFloorRooted using wp by
  have hReadFloorRooted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply ReadFirstRoot using wp by
  have hReadFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply ReadRespBound using wp by
  have hReadRespBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- Restart

prove_veil_invariant_goal Restart ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LeaderSync using wp by
  have hLeaderSync := hinv.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart AckedHeld using wp by
  have hAckedHeld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart CommitRoot using wp by
  have hCommitRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart CommitWithinLog using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart ConfIsCommitted using wp by
  have hConfIsCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LeaderConf using wp by
  have hLeaderConf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart FirstRoot using wp by
  have hFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LedOld using wp by
  have hLedOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LegalChain using wp by
  have hLegalChain := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart ReadMsgsOld using wp by
  have hReadMsgsOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart ReadFloorOld using wp by
  have hReadFloorOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart ReadFloorBound using wp by
  have hReadFloorBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart ReadIndexSafety using wp by
  have hReadIndexSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart ReadTermLed using wp by
  have hReadTermLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart ReadFloorRooted using wp by
  have hReadFloorRooted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart ReadFirstRoot using wp by
  have hReadFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart ReadRespBound using wp by
  have hReadRespBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- Restore

prove_veil_invariant_goal Restore ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore LeaderSync using wp by
  have hLeaderSync := hinv.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore AckedHeld using wp by
  have hAckedHeld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore CommitRoot using wp by
  have hCommitRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore CommitWithinLog using wp by
  have hCommitWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore ConfIsCommitted using wp by
  have hConfIsCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore LeaderConf using wp by
  have hLeaderConf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore FirstRoot using wp by
  have hFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore LedOld using wp by
  have hLedOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore LegalChain using wp by
  have hLegalChain := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore ReadMsgsOld using wp by
  have hReadMsgsOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore ReadFloorOld using wp by
  have hReadFloorOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore ReadFloorBound using wp by
  have hReadFloorBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore ReadIndexSafety using wp by
  have hReadIndexSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore ReadTermLed using wp by
  have hReadTermLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore ReadFloorRooted using wp by
  have hReadFloorRooted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore ReadFirstRoot using wp by
  have hReadFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restore ReadRespBound using wp by
  have hReadRespBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- RestoreConf

prove_veil_invariant_goal RestoreConf ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf LeaderSync using wp by
  have hLeaderSync := hinv.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf AckedHeld using wp by
  have hAckedHeld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf CommitRoot using wp by
  have hCommitRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf CommitWithinLog using wp by
  have hCommitWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf ConfIsCommitted using wp by
  have hCC := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hc x hx j
  by_cases hij : i = j
  · subst hij
    simp only [if_true]
    right
    have h1 := lastConf_le a.entries x
    refine ⟨a, by omega, hc, fun s => ?_⟩
    unfold cOf
    rw [confOf_lastConf]
    exact ⟨rfl, rfl⟩
  · simp only [hij, if_false]
    exact hCC j

prove_veil_invariant_goal RestoreConf LeaderConf using wp by
  have hLeaderConf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf FirstRoot using wp by
  have hFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf LedOld using wp by
  have hLedOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf LegalChain using wp by
  have hLegalChain := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf ReadMsgsOld using wp by
  have hReadMsgsOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf ReadFloorOld using wp by
  have hReadFloorOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf ReadFloorBound using wp by
  have hReadFloorBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf ReadIndexSafety using wp by
  have hReadIndexSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf ReadTermLed using wp by
  have hReadTermLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf ReadFloorRooted using wp by
  have hReadFloorRooted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf ReadFirstRoot using wp by
  have hReadFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal RestoreConf ReadRespBound using wp by
  have hReadRespBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- ReadRequest

prove_veil_invariant_goal ReadRequest ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest LeaderSync using wp by
  have hLeaderSync := hinv.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest AckedHeld using wp by
  have hAckedHeld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest CommitRoot using wp by
  have hCommitRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest CommitWithinLog using wp by
  have hCommitWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest ConfIsCommitted using wp by
  have hConfIsCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest LeaderConf using wp by
  have hLeaderConf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest FirstRoot using wp by
  have hFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest LedOld using wp by
  have hLedOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest LegalChain using wp by
  have hLegalChain := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadRequest ReadMsgsOld using wp by
  clear hinv
  intros
  rename_i hm
  exact hm

prove_veil_invariant_goal ReadRequest ReadFloorOld using wp by
  clear hinv
  intros
  rename_i hm
  exact hm

prove_veil_invariant_goal ReadRequest ReadFloorBound using wp by
  all_goals (clear hinv; intros; simp_all)

prove_veil_invariant_goal ReadRequest ReadIndexSafety using wp by
  all_goals (clear hinv; intros; simp_all)

prove_veil_invariant_goal ReadRequest ReadTermLed using wp by
  have hLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro x hrole _ _ a _ _ hnone
  have := hLL i hrole
  rw [hnone] at this
  simp at this

prove_veil_invariant_goal ReadRequest ReadFloorRooted using wp by
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro x a hrole _ _ c _ _ ha
  obtain ⟨_, r, hkr, hroot, hr, _⟩ := hCR a ha
  exact ⟨r, hkr, hr, hroot⟩

prove_veil_invariant_goal ReadRequest ReadFirstRoot using wp by
  have hFR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro x a hrole _ _ c _ _ ha p hp
  exact hFR a ha p hp

prove_veil_invariant_goal ReadRequest ReadRespBound using wp by
  all_goals (clear hinv; intros; simp_all)

-- ReadAck

prove_veil_invariant_goal ReadAck ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck LeaderSync using wp by
  have hLeaderSync := hinv.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck AckedHeld using wp by
  have hAckedHeld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck CommitRoot using wp by
  have hCommitRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck CommitWithinLog using wp by
  have hCommitWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck ConfIsCommitted using wp by
  have hConfIsCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck LeaderConf using wp by
  have hLeaderConf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck FirstRoot using wp by
  have hFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck LedOld using wp by
  have hLedOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck LegalChain using wp by
  have hLegalChain := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck ReadMsgsOld using wp by
  have hReadMsgsOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck ReadFloorOld using wp by
  have hReadFloorOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck ReadFloorBound using wp by
  have hReadFloorBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck ReadIndexSafety using wp by
  have hReadIndexSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck ReadTermLed using wp by
  have hReadTermLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck ReadFloorRooted using wp by
  have hReadFloorRooted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck ReadFirstRoot using wp by
  have hReadFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadAck ReadRespBound using wp by
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRMO := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRRB := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intro hon hle _ j' hj' m hm i' t x heq
  by_cases hd : j = j'
  · subst hd
    have hin : m ∈ st.msgs := hRMO hon m hm
    have := (hAF m hin j i' t x heq).2.1
    omega
  · exact hRRB hon j' (hj' hd) m hm i' t x heq

-- ReadConfirm

prove_veil_invariant_goal ReadConfirm ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm LeaderSync using wp by
  have hLeaderSync := hinv.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm AckedHeld using wp by
  have hAckedHeld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm CommitRoot using wp by
  have hCommitRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm CommitWithinLog using wp by
  have hCommitWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm ConfIsCommitted using wp by
  have hConfIsCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm LeaderConf using wp by
  have hLeaderConf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm FirstRoot using wp by
  have hFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm LedOld using wp by
  have hLedOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm LegalChain using wp by
  have hLegalChain := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm ReadMsgsOld using wp by
  have hReadMsgsOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm ReadFloorOld using wp by
  have hReadFloorOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm ReadFloorBound using wp by
  have hReadFloorBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm ReadIndexSafety using wp by
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hVHR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLER := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSMS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hFR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLG := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLCf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLOld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRMO := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRFO := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRFB := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRTL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRFR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRF1 := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRRB := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intro (k : Commit server value) hon hq hk
  obtain ⟨AT, hAT⟩ := Option.ne_none_iff_exists'.1 (hRTL hon)
  obtain ⟨r, hkr, hr, hroot⟩ := hRFR k hon hk
  have ht : r.term ≤ st.readTerm :=
    read_safe _ _ _ _ _ st.msgs st.leaders st.votes st.ledLog st.commits st.ledAt st.elAt st.lIn st.lOut
      hSMS hFR hLG hLS hEQ hLCf hLOld hLHas hVHR hLER
      (fun t L h => (optAll_iff _ _).1 (hLedFL t) L h)
      (fun k hk => by
        obtain ⟨_, r, h2, h3, h4, h5⟩ := hCR k hk
        exact ⟨r, h4, h2, h3, h5⟩)
      st.readMsgs st.readFloor (fun a ha => hRMO hon a ha) (fun k hk => hRFO k hon hk)
      (fun a ha p hp => hRF1 a hon ha p hp)
      st.readTerm AT hAT (fun j => st.readResp j) hq
      (fun n hn i t x hx => hRRB hon n hn _ hx i t x rfl)
      r hroot
  have h1 := hRFB r hon hr ht
  have h2 := hkr.length_le
  omega

prove_veil_invariant_goal ReadConfirm ReadTermLed using wp by
  have hReadTermLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm ReadFloorRooted using wp by
  have hReadFloorRooted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm ReadFirstRoot using wp by
  have hReadFirstRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal ReadConfirm ReadRespBound using wp by
  have hReadRespBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  try simp only [EtcdRaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

end EtcdRaftVeil
