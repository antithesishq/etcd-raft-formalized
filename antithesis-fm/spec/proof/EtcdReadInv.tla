---- MODULE EtcdReadInv ----
\* Invariants for read indexes (definitions only; TLC-checkable via MCInv).
EXTENDS EtcdInv

\* AckedBy, Cover, MRoot with the messages M and the committed prefixes K as
\* parameters: what was acknowledged and committed when the read was asked for.
AckedByS(M, t, c) ==
    {n \in Server : \E a \in M : a.type = "ack" /\ a.src = n /\ a.term = t /\ a.index >= c}
CoverS(K, l, d, t) == d = 0 \/ \E k \in K : k.term <= t /\ Agree(k.entries, l, d)
MRootS(M, K, t, c, d) ==
    /\ Good(t, c)
    /\ d <= Len(ledLog[t])
    /\ CoverS(K, ledLog[t], d, t)
    /\ AtMostOne(ledLog[t], d, c)
    /\ IsQuorum(AckedByS(M, t, c), ConfOf(ledLog[t], d))

ReadTermLed == read.on => read.term \in DOMAIN ledLog
ReadFloorRooted ==
    read.on => \A k \in read.floor : \E r \in read.floor :
        /\ Pre(k.entries, r.entries)
        /\ r.term \in DOMAIN ledLog
        /\ Pre(r.entries, ledLog[r.term])
        /\ \E d \in 0..Len(ledLog[r.term]) : MRootS(read.msgs, read.floor, r.term, Len(r.entries), d)
ReadFirstRoot ==
    read.on => \A k \in read.floor : \A p \in 1..Len(k.entries) : IsConf(k.entries[p]) =>
        \E r \in read.floor :
            /\ r.term <= k.term /\ p <= Len(r.entries)
            /\ r.term \in DOMAIN ledLog
            /\ Pre(r.entries, ledLog[r.term])
            /\ \E d \in 0..(p - 1) : MRootS(read.msgs, read.floor, r.term, Len(r.entries), d)
ReadRespBound ==
    read.on => \A j \in read.resp : \A m \in read.msgs :
        m.type = "ack" /\ m.src = j => m.term <= read.term

RInv ==
    /\ ReadMsgsOld /\ ReadFloorOld /\ ReadFloorBound /\ ReadIndexSafety
    /\ ReadTermLed /\ ReadFloorRooted /\ ReadFirstRoot /\ ReadRespBound

\* What ReadConfirm needs (theorem ReadSafe of EtcdReadCore.tla): a consequence
\* of Inv and RInv in one state.
ReadSafeP ==
    read.on /\ IsQuorum(read.resp, ledConf[read.term]) =>
        \A k \in read.floor : Len(k.entries) <= read.index
====
