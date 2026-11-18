module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
public import VerifiedGarbage.Proof.Ffdh.Arm.Power
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.ExpControlsCT
import VerifiedGarbage.Proof.Bignum.Arm.ImportOperandCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Proof.Bignum.Arm.WindowPhase
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.EqualCT
import VerifiedGarbage.Proof.Ffdh.Arm.FlagCT
public import VerifiedGarbage.Impl.Bignum.Arm.DoubleFnBody
public import VerifiedGarbage.Impl.Bignum.Arm.Exp
public import VerifiedGarbage.Impl.Bignum.Arm.SelectArray
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.Arm.ExpControl
import VerifiedGarbage.Proof.Bignum.Arm.SelectArrayCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.HeaderStore
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.ExpByteLoad
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Bignum.FoldedPublic
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Ffdh.Arm.Branch

/-! ### `Ffdh.Arm.KeyPowerPhase`, which only this module used -/

section

/-! # Public generator dispatch with a full-width secret exponent

The fallback is supplied with its verified arithmetic and timing behavior.
Both paths use the original imported exponent bytes without shortening.
-/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeyPower
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand)
open VG.Proof.X25519.Arm (Rest)

structure PhaseInput (base ep : BitVec 32) (len w M x : Nat) (P : State → Prop)
    (regions : List Region) (eb : List Byte) (s : State) : Prop where
  phase : ExpPhaseInput base ep len w M x eb s
  persistent : P s
  separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb.length⟩ r

end VG.Proof.Ffdh.Arm.KeyPower

end

end

/-! ### `Ffdh.Arm.KeyPower`, which only this module used -/

section

/-! # Generator-specialized key-generation power after exponent and base import -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeyPower
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

structure Input (base src ep : BitVec 32) (len w M : Nat) (P : State → Prop)
    (regions : List Region) (bb eb : List Byte) (s : State) : Prop where
  power : PowerInput base src ep len w M bb eb s
  persistent : P s
  separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb.length⟩ r

theorem import_ok {base src ep : BitVec 32} {len w M : Nat} {P : State → Prop}
    {regions : List Region} {bb eb : List Byte}
    (A : TwoExp.Montgomery base len w P regions) (s : State)
    (h : Input base src ep len w M P regions bb eb s) :
    WP isa VG.Impl.Ffdh.Arm.powerImport s fun t =>
      PhaseInput base ep len w M (Spec.Rsa.os2ip bb) P regions eb t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (powerImport_ok s h.power) ?_
  rintro t ⟨input, frame, rest⟩
  exact ⟨⟨input, A.stable frame rest h.persistent, h.separate⟩, frame, rest⟩

end VG.Proof.Ffdh.Arm.KeyPower

end

end

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
