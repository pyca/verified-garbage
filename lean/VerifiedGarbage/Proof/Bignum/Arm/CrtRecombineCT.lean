module
public import VerifiedGarbage.Impl.Bignum.Arm.CrtRecombine
public import VerifiedGarbage.Proof.Bignum.Arm.CrtRecombineProduct
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.Arm.CrtFactorProductCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtFinishRecombineCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT

/-! # Full CRT reconstruction conceals both factors and residues -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_recombine_ct {base : BitVec 32} {size len w o a b cp cq d : Nat} (fit : 244 ≤ size) :
    RelCT isa (fun s t => CrtRecombineInput base size len w o a b cp cq d s ∧
      CrtRecombineInput base size len w o a b cp cq d t ∧ s.sp = t.sp) recombine (fun _ _ => True) := by
  let P := CrtRecombineInput base size len w o a b cp cq d
  have product : RelCT isa (fun s t => P s ∧ P t ∧ s.sp = t.sp) (factorProduct true) (fun _ _ => True) :=
    (crt_factorProduct_ct (by omega : 236 ≤ size)).mono
      (fun _ _ h => ⟨h.1.multiplication, h.2.1.multiplication, h.2.2⟩) (fun _ _ _ => trivial)
  have wp (s : State) (h : P s) : WP isa (factorProduct true) s (CrtFinishInput base size len w o d) :=
    WP.mono (crt_recombineProduct_ready s h) (fun _ j => j.1)
  have first := (relCT_keep_sp product (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  exact first.seq ((crt_finishRecombine_ct fit).mono
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial))

end VG.Proof.Bignum.Arm
