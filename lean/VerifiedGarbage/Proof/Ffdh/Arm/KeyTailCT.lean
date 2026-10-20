module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyFinishCT
public import VerifiedGarbage.Proof.Ffdh.Arm.PowerAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyTail
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeometry
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyOutputs
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeMain

/-! Generated-public-value exponentiation, checking, export and masking have
the same trace for different secret scalars of the public significant width. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (numAt Operand)

structure KeyPowerInput (p : Inputs) (slots : List Nat) (eb : List Byte) (s : State) : Prop extends
    PowerAtInput p slots 56 16 p.P ((p.dom.drop p.k).take p.k) eb s where
  outputs : KeyOutputs p s

structure KeyRangeInput (p : Inputs) (slots : List Nat) (s : State) : Prop extends KeyExportInput p slots s where
  modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P

theorem keyPower_next (s : State) {p : Inputs} {slots : List Nat} {eb : List Byte}
    (stable : stableSlots slots = true) (h16 : 16 ∈ slots) (h20 : 20 ∈ slots) (h32 : 32 ∈ slots) (h56 : 56 ∈ slots)
    (size : eb.length = p.scalarWidth) (odd : p.P % 2 = 1) (h : KeyPowerInput p slots eb s) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.powerAt 56 16 20) s (KeyRangeInput p slots) := by
  refine WP.mono (powerAt_ok s 56 16 20 h.context stable h56 h16 h20 h32 h.ready h.modulus odd h.r2
    h.source p.gLength h.exponent (by rw [size]; exact p.scalarWidthBounds.1)
    (by rw [size]; have := p.scalarWidthBounds; have := p.maxLength; omega)
    (by change BitVec.ofNat 32 p.scalarWidth = _; rw [size])) ?_
  rintro t ⟨context, ready, power, modulus, _, _, _, rest⟩
  refine ⟨⟨context, ready, h.outputs.after rest, ?_⟩, modulus⟩
  rw [power, VG.Proof.Bignum.powMod_eq]
  have large := h.ready.modulus
  rw [h.modulus] at large
  exact Nat.lt_trans (Nat.mod_lt _ (by omega)) p.modulusBound

theorem keyRange_next (s : State) {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (odd : p.P % 2 = 1) (h : KeyRangeInput p slots s) :
    WP isa (VG.Impl.Ffdh.Arm.inRange 6) s (KeyExportInput p slots) := by
  refine WP.mono (inRange_ok s h.ready (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp] : Operand 6)
    (by decide) (by rw [h.modulus]; exact odd)) ?_
  rintro t ⟨ready, _, arrays, frame, rest⟩
  exact ⟨h.context.after_workspace frame rest ready.ptr (fun d hd => (stableSlots_at stable hd).1), ready,
    h.outputs.after rest, by rw [arrays 6 (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]) (by decide)]; exact h.valueFit⟩

theorem keyTail_ct {p : Inputs} {slots : List Nat} {eb1 eb2 : List Byte}
    (stable : stableSlots slots = true) (h4 : 4 ∈ slots) (h16 : 16 ∈ slots) (h20 : 20 ∈ slots) (h32 : 32 ∈ slots)
    (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h56 : 56 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (size1 : eb1.length = p.scalarWidth) (size2 : eb2.length = p.scalarWidth)
    (odd : p.P % 2 = 1) (outputY : p.output = p.publicValue) :
    RelCT isa (fun s t => KeyPowerInput p slots eb1 s ∧ KeyPowerInput p slots eb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.GenerateKey.tail (fun _ _ => True) := by
  have power := (powerAt_ct stable h56 h16 h20 h32 p.gLength
    (by rw [size1]; exact p.scalarWidthBounds.1)
    (by rw [size1]; have := p.scalarWidthBounds; have := p.maxLength; omega)
    (by change BitVec.ofNat 32 p.scalarWidth = _; rw [size1]) (size1.trans size2.symm) odd).mono
    (P' := fun (s t : State) => KeyPowerInput p slots eb1 s ∧ KeyPowerInput p slots eb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.toPowerAtInput, h.2.1.toPowerAtInput, h.2.2⟩) (fun _ _ h => h)
  have range := (inRange_ct (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp] : Operand 6) (by decide)).mono
    (P' := fun (s t : State) => KeyRangeInput p slots s ∧ KeyRangeInput p slots t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.tail
  exact relCT_chain power (keyPower_next · stable h16 h20 h32 h56 size1 odd) (keyPower_next · stable h16 h20 h32 h56 size2 odd)
    (relCT_chain range (keyRange_next · stable odd) (keyRange_next · stable odd)
      (keyExportFinish_ct stable h4 h32 h36 h40 saved outputY))

end VG.Proof.Ffdh.Arm
