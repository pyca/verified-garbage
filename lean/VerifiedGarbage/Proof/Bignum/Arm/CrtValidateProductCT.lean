module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtValidateProduct
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtFactorProductCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtCheckProductCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT

/-! # Complete factor-product validation is constant-time -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_validateProduct_ct {base : BitVec 32} {size len product cmp pad a b cp cq w : Nat}
    (fit : 244 ≤ size) :
    RelCT isa (fun s t => CrtValidateInput base size len product cmp pad a b cp cq w s ∧
      CrtValidateInput base size len product cmp pad a b cp cq w t ∧ s.sp = t.sp)
      validateProduct (fun _ _ => True) := by
  let P := CrtValidateInput base size len product cmp pad a b cp cq w
  have multiply : RelCT isa (fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
      factorProduct (fun _ _ => True) :=
    (crt_factorProduct_ct (size := size) (by omega)).mono (fun _ _ h => ⟨h.1.multiplication, h.2.1.multiplication, h.2.2⟩)
      (fun _ _ _ => trivial)
  have ready := (relCT_keep_sp multiply (fun _ _ h => h.2.2)).wp (fun s t h =>
    ⟨(crt_validationProduct_ready s h.1).mono (fun _ j => j.1),
      (crt_validationProduct_ready t h.2.1).mono (fun _ j => j.1)⟩)
  exact ready.seq ((crt_checkProduct_ct fit).mono
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial))

end VG.Proof.Bignum.Arm
