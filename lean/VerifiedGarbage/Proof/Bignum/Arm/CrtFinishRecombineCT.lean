module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtFinishRecombine
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPadModulusCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtAddWideCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Final CRT reconstruction hides the product and residue -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_finishRecombine_ct {base : BitVec 32} {size len w o d : Nat} (fit : 244 ≤ size) :
    RelCT isa (fun s t => CrtFinishInput base size len w o d s ∧
      CrtFinishInput base size len w o d t ∧ s.sp = t.sp) finishRecombine (fun _ _ => True) := by
  let P := CrtFinishInput base size len w o d
  have pad : RelCT isa (fun s t => P s ∧ P t ∧ s.sp = t.sp) (padModulus 1) (fun _ _ => True) :=
    (crt_padModulus_ct fit 1).mono (fun _ _ h => ⟨h.1.padding, h.2.1.padding, h.2.2⟩) (fun _ _ _ => trivial)
  have wp (s : State) (h : P s) : WP isa (padModulus 1) s (CrtAddWideInput base size o d w) :=
    WP.mono (crt_finishPad_ready s h) (fun _ j => j.1)
  have first := (relCT_keep_sp pad (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  exact first.seq (crt_addWide_ct.mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial))

end VG.Proof.Bignum.Arm
