module

public import VerifiedGarbage.Proof.Dsa.AArch64.SignificantCT
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # Constant-time public width scans through the saved field bindings -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG VG.AArch64 VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def ScanFieldPre (fp fl : Field) (p : ScanPublic) (s : State) : Prop :=
  Scr s p.base p.extent ∧ s.gpr .x0 = p.base ∧ pWorkspace ≤ p.extent ∧
  word s.mem p.base fp.offset = p.pointer ∧ word s.mem p.base fl.offset = BitVec.ofNat 64 p.bytes.length ∧
  Src s p.base p.extent p.pointer p.bytes ∧ 0 < p.bytes.length ∧ p.bytes.length < 2 ^ 64

theorem scanField_ct (fp fl : Field) {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0])
      (.block [Core.field .x1 fp, Core.field .x9 fl]) hint).isSome = true) :
    RelCT isa (Two (ScanFieldPre fp fl))
      (.seq (.block [Core.field .x1 fp, Core.field .x9 fl]) Checks.significant)
      (fun _ _ => True) := by
  refine RelCT.seq (two_piece (Ψ := ScanPre) [.x0] (pins_of (fun p _ => p.base) (by
    intro p s h r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.2.1)) hT ?_) significant_ct
  intro p s ⟨hs, hdi, hZ, hp, hl, hsrc, h1, h64⟩
  refine WP.mono (WP.keep [.x1, .x9] (Q := fun t =>
    t.gpr .x1 = p.pointer ∧ t.gpr .x9 = BitVec.ofNat 64 p.bytes.length ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨htp, htl, hmem⟩, hk⟩ => ⟨htp, htl, hsrc.congrK ?_ hk, h1, h64⟩
  · brun [field_enc fp, field_enc fl, Core.field, hdi, fieldAddress, hp, hl,
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds fp).2 hZ),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds fl).2 hZ)]
  · rw [hmem]
    exact InScr.refl _ _ _

end VG.Proof.Dsa.AArch64
