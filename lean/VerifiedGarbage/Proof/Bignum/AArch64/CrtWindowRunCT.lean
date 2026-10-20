module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRunContext

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailsCT
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRunPost
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowGroupsCT

/-! Constant time for the complete exponent, including both tails. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.WindowFive (expRun)

theorem expRun_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two fun p => RunInv p 0 0) (expRun W.code M.mm S.code) (fun _ _ => True) := by
  unfold expRun
  refine RelCT.seq (two_post (Ψ := fun p => RunInv p (5*(p.len/5)) 0)
    (expGroups_ct W) (fun _ _ h => h.groups W)) ?_
  refine RelCT.seq (two_post (Ψ := fun p => RunInv p p.len ((8*(p.len-5*(p.len/5)))%5))
    (two_map (fun p : RunPub => (p,5*(p.len/5)))
      (fun _ _ h => ⟨by dsimp; omega,h⟩) (expTail_ct W))
    (fun _ _ h => h.tails W (by omega))) ?_
  exact two_map (fun p : RunPub => (p.ws,(8*(p.len-5*(p.len/5)))%5))
    (fun _ _ h => h.finish) (finish_ct M S)

end VG.Proof.Bignum.AArch64.WindowFive
