---- MODULE EtcdChange ----
\* What is known of a change in ConfChanges(Server), the only module that
\* expands it. Its set constructor has three bound variables, which Zenon and
\* Isabelle do not support and on which tlapm's SMT set-extensionality axiom
\* crashes: checked with `tlapm --debug no_smt_set_extensionality` (flags.sh).
EXTENDS EtcdInv, TLAPS

\* What is known of a change.
ChangeOK(d) == /\ d.leave \in BOOLEAN /\ d.joint \in BOOLEAN
               /\ Range(d.add) \subseteq Server /\ Range(d.remove) \subseteq Server

LEMMA ChangeFacts ==
  ASSUME NEW d \in ConfChanges(Server)
  PROVE  ChangeOK(d)
<1>1. ASSUME NEW a \in Seqs(Server) PROVE Range(a) \subseteq Server
  <2>1. PICK n : a \in [1..n -> Server] BY DEF Seqs
  <2> QED BY <2>1 DEF Range
<1>2. Range(<< >>) = {} BY DEF Range
<1>3. CASE d = [add |-> <<>>, remove |-> <<>>, joint |-> FALSE, leave |-> TRUE]
  BY <1>2, <1>3 DEF ChangeOK
<1>4. CASE \E a \in Seqs(Server), r \in Seqs(Server), j \in BOOLEAN : d = [add |-> a, remove |-> r, joint |-> j, leave |-> FALSE]
  <2>1. PICK a \in Seqs(Server), r \in Seqs(Server), j \in BOOLEAN : d = [add |-> a, remove |-> r, joint |-> j, leave |-> FALSE] BY <1>4
  <2>2. d.add = a /\ d.remove = r /\ d.joint = j /\ d.leave = FALSE BY <2>1
  <2> QED BY <2>2, <1>1 DEF ChangeOK
<1> QED BY <1>3, <1>4 DEF ConfChanges

====
