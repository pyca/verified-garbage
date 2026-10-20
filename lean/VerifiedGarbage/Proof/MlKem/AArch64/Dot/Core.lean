module

import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Setup
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Result
import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Loop

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64 VG.Spec.MlKem

theorem dot_ok {s : State} {out : Nat} (ho : out < 65536) (terms : List (Nat × Nat))
    {F G : (Nat × Nat) → Poly}
    (hd : LoopData s (s.gpr .x28 + BitVec.ofNat 64 out) (s.syms "VG_MLKEM_GAMMA") terms
      (polyValues F) (polyValues G) gammaValues) :
    WP isa (Impl.MlKem.AArch64.Dot.dot out terms) s fun s' =>
      Keep clob s s' ∧ Frame [polyRegion (s.gpr .x28 + BitVec.ofNat 64 out)] s.mem s'.mem ∧
      PolyIs s'.mem (s.gpr .x28 + BitVec.ofNat 64 out) (polySum terms F G) := by
  rw [dot_partition]
  refine WP.seq (WP.mono (setup_ok ho (result terms (polyValues F) (polyValues G) gammaValues))
    fun s₁ h₁ => ?_)
  refine WP.mono (loop_ok hd h₁) fun s₂ h₂ => ?_
  exact ⟨h₂.keep,h₂.frame,h₂.out.polyIs (fun i hi => result_field terms F G hi)⟩

end VG.Proof.MlKem.AArch64.Dot
