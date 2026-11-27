module

public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Reordering a block of AArch64 code

`schedule ks l` is the block `l` in another order: each `k` of `ks` takes the
next instruction from the `k`th place of those that remain. The order is data
(a search over the dependences finds it); where every instruction taken is
independent of those it overtakes, the block runs as `l` does
(`Proof/Framework/AArch64/Schedule.lean`).
-/

@[expose] public section

namespace VG.Impl.AArch64Schedule

open VG.AArch64

def schedule : List Nat → List Instr → List Instr
  | [], l => l
  | k :: ks, l =>
    match l[k]? with
    | some i => i :: schedule ks (l.eraseIdx k)
    | none => l

end VG.Impl.AArch64Schedule
