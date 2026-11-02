module

public import VerifiedGarbage.Proof.Ffdh.Arm.Power
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.ExpControlsCT
import VerifiedGarbage.Proof.Bignum.Arm.ImportOperandCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowPhaseCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT

/-! FFDH power processes every exponent byte and scans every window entry,
even when the modulus, base and secret exponent differ between executions. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)

theorem power_ct {base src ep : BitVec 32} {len w M1 M2 : Nat} {bb1 bb2 eb1 eb2 : List Byte}
    (fit : arrAt w 3 + 32 ≤ 8 * len) (fits : arrAt w 16 ≤ 8 * len)
    (positive : 0 < eb1.length) (baseLength : bb1.length = bb2.length) (length : eb1.length = eb2.length) :
    RelCT isa (fun s t => PowerInput base src ep len w M1 bb1 eb1 s ∧
      PowerInput base src ep len w M2 bb2 eb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.power (fun _ _ => True) := by
  have controls := expControls_ct.mono
    (P' := fun (s t : State) => PowerInput base src ep len w M1 bb1 eb1 s ∧
      PowerInput base src ep len w M2 bb2 eb2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.1.ready.ptr.trans h.2.1.ready.ptr.symm) (fun _ _ h => h)
  have importCT := (importOperand_ct (base := base) (src := src) (len := len) (w := w) (k := bb1.length)
    (by decide : 1 < 8)).mono
    (P' := fun (s t : State) => PowerPrepared base src ep len w M1 bb1 eb1 s ∧
      PowerPrepared base src ep len w M2 bb2 eb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.input.ready, h.2.1.input.ready, h.1.input.source,
      h.2.1.input.source, h.1.input.count, by rw [baseLength]; exact h.2.1.input.count, h.2.2⟩)
    (fun _ _ h => h)
  have importAll : RelCT isa (fun s t => PowerInput base src ep len w M1 bb1 eb1 s ∧
      PowerInput base src ep len w M2 bb2 eb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.powerImport (fun _ _ => True) := by
    unfold VG.Impl.Ffdh.Arm.powerImport
    exact relCT_chain controls
      (fun s h => WP.mono (powerControls_ok s h) fun _ k => k.1)
      (fun s h => WP.mono (powerControls_ok s h) fun _ k => k.1) importCT
  unfold VG.Impl.Ffdh.Arm.power VG.Impl.Ffdh.Arm.pow
  exact relCT_chain importAll
    (fun s h => WP.mono (powerImport_ok s h) fun _ k => k.1)
    (fun s h => WP.mono (powerImport_ok s h) fun _ k => k.1)
    (windowExpPhase_ct fit fits positive length)

end VG.Proof.Ffdh.Arm
