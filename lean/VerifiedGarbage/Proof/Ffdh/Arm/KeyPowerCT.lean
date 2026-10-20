module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerPhase
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPower
import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerPhaseCT
import VerifiedGarbage.Proof.Bignum.Arm.ExpControlsCT
import VerifiedGarbage.Proof.Bignum.Arm.ImportOperandCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT

/-! # Imported public-generator dispatch retains private-scalar timing -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeyPower
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (arrAt)

theorem import_ct {base src ep : BitVec 32} {len w M1 M2 : Nat} {bb eb1 eb2 : List Byte}
    (_length : eb1.length = eb2.length) :
    RelCT isa (fun s t => PowerInput base src ep len w M1 bb eb1 s ∧
      PowerInput base src ep len w M2 bb eb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.powerImport (fun _ _ => True) := by
  have controls := expControls_ct.mono
    (P' := fun (s t : State) => PowerInput base src ep len w M1 bb eb1 s ∧
      PowerInput base src ep len w M2 bb eb2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.1.ready.ptr.trans h.2.1.ready.ptr.symm) (fun _ _ h => h)
  have importCT := (importOperand_ct (base := base) (src := src) (len := len) (w := w) (k := bb.length)
    (by decide : 1 < 8)).mono
    (P' := fun (s t : State) => PowerPrepared base src ep len w M1 bb eb1 s ∧
      PowerPrepared base src ep len w M2 bb eb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.input.ready, h.2.1.input.ready, h.1.input.source,
      h.2.1.input.source, h.1.input.count, h.2.1.input.count, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.powerImport
  exact relCT_chain controls
    (fun s h => WP.mono (powerControls_ok s h) fun _ k => k.1)
    (fun s h => WP.mono (powerControls_ok s h) fun _ k => k.1) importCT

theorem power_ct {base src ep : BitVec 32} {len w M1 M2 : Nat} {P : State → Prop}
    {regions : List Region} {bb eb1 eb2 : List Byte}
    (A : TwoExp.Montgomery base len w P regions) (ct : TwoExp.MontgomeryTiming A)
    (fallback : Fallback base len w P regions)
    (fit : arrAt w 3 + 32 ≤ 8 * len) (hn : 0 < 2 * w) (positive : 0 < eb1.length)
    (length : eb1.length = eb2.length) :
    RelCT isa (fun s t => Input base src ep len w M1 P regions bb eb1 s ∧
      Input base src ep len w M2 P regions bb eb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.KeyPower.power A.phase fallback.code) (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.KeyPower.power
  exact relCT_chain
    ((import_ct length).mono (fun _ _ h => ⟨h.1.power, h.2.1.power, h.2.2⟩) (fun _ _ h => h))
    (fun s h => WP.mono (import_ok A s h) fun _ k => k.1)
    (fun s h => WP.mono (import_ok A s h) fun _ k => k.1)
    (phase_ct A ct fallback fit hn positive length)

end VG.Proof.Ffdh.Arm.KeyPower
