module

import VerifiedGarbage.Proof.Ffdh.Arm.PrivateMatch
public import VerifiedGarbage.Proof.Ffdh.Arm.PrivateState
import VerifiedGarbage.Proof.Ffdh.Arm.PowerAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.EqualCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Framework.RelCT

/-! Computing g^x and comparing it with the imported public value is constant time in x. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (Operand)

theorem privateMatch_ct {p : Inputs} {slots : List Nat} {yb xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots)
    (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h56 : 56 ∈ slots)
    (peerLength : yb.length = p.k) (positive : 0 < xb1.length) (fits : xb1.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => PrivateReady p slots yb xb1 s ∧ PrivateReady p slots yb xb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.CheckPrivate.matchPublic (fun _ _ => True) := by
  have powers := (powerAt_ct (p := p) (bs := 56) (es := 40) (ec := 44)
    stable h56 h40 h44 h32 p.gLength positive fits count length odd).mono
    (P' := fun (s t : State) => PrivateReady p slots yb xb1 s ∧ PrivateReady p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready, h.1.modulus, h.1.r2, h.1.context.gBytes, h.1.scalar⟩,
      ⟨h.2.1.context, h.2.1.ready, h.2.1.modulus, h.2.1.r2, h.2.1.context.gBytes, h.2.1.scalar⟩, h.2.2⟩) (fun _ _ h => h)
  have wpPower (s : State) {xb : List Byte} (h : PrivateReady p slots yb xb s)
      (positive : 0 < xb.length) (fits : xb.length < 2 ^ 32) (count : p.slotValue 44 = BitVec.ofNat 32 xb.length) :
      WP isa (VG.Impl.Ffdh.Arm.Domain.powerAt 56 40 44) s (PrivateReady p slots yb xb) := by
    refine WP.mono (powerAt_ok s 56 40 44 h.context stable h56 h40 h44 h32 h.ready h.modulus odd h.r2
      h.context.gBytes p.gLength h.scalar positive fits count) ?_
    rintro u ⟨context, ready, _, modulus, r2, _, frame, rest⟩
    exact ⟨context, ready, modulus, r2, h.value.after_workspace frame rest, h.scalar.after_workspace frame rest⟩
  have imports := (importAt_ct (p := p) (a := 1) (slot := 36) (k := p.k)
    stable h36 h32 rfl (by decide)).mono
    (P' := fun (s t : State) => PrivateReady p slots yb xb1 s ∧ PrivateReady p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready⟩, ⟨h.2.1.context, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  have wpImport (s : State) {xb : List Byte} (h : PrivateReady p slots yb xb s) :
      WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 36 32) s (ArithmeticReady p.base p.len p.w) :=
    WP.mono (importAt_ok s 1 36 32 h.context stable h36 h32 h.ready (by decide) (by decide) h.value
      (by rw [peerLength]; have := p.minLength; omega) (by rw [peerLength]; exact p.width.2.2.2.1)
      (by change BitVec.ofNat 32 p.k = _; rw [peerLength])) fun _ j => j.2.1
  have equal := equal_ct (base := p.base) (len := p.len) (w := p.w)
    (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp] : Operand 6)
    (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp] : Operand 1)
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPrivate.matchPublic
  exact relCT_chain powers (fun s h => wpPower s h positive fits count)
    (fun s h => wpPower s h (by rw [← length]; exact positive)
      (by rw [← length]; exact fits) (by rw [← length]; exact count))
    (relCT_chain imports (fun s h => wpImport s h) (fun s h => wpImport s h) (equal.seq finishFlag_ct))

end VG.Proof.Ffdh.Arm
