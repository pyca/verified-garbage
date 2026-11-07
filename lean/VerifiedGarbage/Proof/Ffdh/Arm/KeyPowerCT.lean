module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerPhase
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPower

import VerifiedGarbage.Proof.Bignum.Arm.ExpControlsCT
import VerifiedGarbage.Proof.Bignum.Arm.ImportOperandCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpStep
import VerifiedGarbage.Proof.Bignum.Arm.ExpByteHeadCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.EqualCT
import VerifiedGarbage.Proof.Ffdh.Arm.FlagCT
import VerifiedGarbage.Impl.Bignum.Arm.DoubleFnBody
import VerifiedGarbage.Impl.Bignum.Arm.Exp
import VerifiedGarbage.Impl.Bignum.Arm.SelectArray
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.Arm.ExpControl
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.SelectArrayCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.HeaderStore
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.ExpByteLoad
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
import VerifiedGarbage.Proof.Bignum.Arm.ExpPhaseInput
import VerifiedGarbage.Proof.Bignum.FoldedPublic
import VerifiedGarbage.Proof.Bignum.Math
/-! # Imported public-generator dispatch retains private-scalar timing -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeyPower
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)

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

end VG.Proof.Ffdh.Arm.KeyPower
