module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtCheckProduct
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPadModulusCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtCompareProductCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Combined modulus padding and product validation are constant-time -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_checkProduct_ct {base : BitVec 32} {size len o a d w : Nat}
    (fit : 244 ≤ size) :
    RelCT isa (fun s t => CrtCheckProductInput base size len o a d w s ∧
      CrtCheckProductInput base size len o a d w t ∧ s.sp = t.sp) checkProduct (fun _ _ => True) := by
  let P := CrtCheckProductInput base size len o a d w
  have pad : RelCT isa (fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp) padModulus (fun _ _ => True) :=
    (crt_padModulus_ct (base := base) (size := size) (len := len) (w := w) (d := d) fit).mono
      (fun _ _ h => ⟨h.1.padding, h.2.1.padding, h.2.2⟩) (fun _ _ _ => trivial)
  have ready := (relCT_keep_sp pad (fun _ _ h => h.2.2)).wp (fun s t h =>
    ⟨(crt_padComparison_ready s h.1).mono (fun _ j => j.1),
      (crt_padComparison_ready t h.2.1).mono (fun _ j => j.1)⟩)
  exact ready.seq (crt_compareProduct_ct.mono
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial))

end VG.Proof.Bignum.Arm
