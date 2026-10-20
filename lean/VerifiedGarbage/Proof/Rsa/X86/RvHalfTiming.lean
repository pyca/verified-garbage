module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Rsa.X86.RvHalfStep

import VerifiedGarbage.Proof.Rsa.X86.RvLoopTiming

/-! # The halving schedule depends on the public exponent lengths -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86
open VG.Impl.Rsa.X86.Recover

theorem halfLoop_relCT (g : Geo) (s0 t0 : State) (A B : Nat → Nat) (m r c : Nat)
    (positive : 0 < c) (bound : c ≤ 16384) :
    RelCT isa (fun s t => HI g s0 A m c 0 s ∧ HI g t0 B r c 0 t)
      (.loop (halfBody g.n) .ne) (fun s t => HI g s0 A m c c s ∧ HI g t0 B r c c t) := by
  apply fixedLoop_relCT (fun k s => HI g s0 A m c k s) (fun k t => HI g t0 B r c k t)
    positive (halfBody_workspace g.n)
  · intro k s t hs ht
    exact ks_agree hs ht
  · intro k s hk hs
    exact halfBody_ok hs hk bound
  · intro k t hk ht
    exact halfBody_ok ht hk bound

end VG.Proof.Rsa.X86.Recover
