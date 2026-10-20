module

import VerifiedGarbage.Proof.Ffdh.Arm.PrivatePublic
import VerifiedGarbage.Proof.Ffdh.Arm.PrivateTailCT
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Ffdh.Arm.FlagCT
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Ffdh.Arm.PrivateState
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT

/-! The public half of private-key checking reveals no private scalar data. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (numAt Operand arrAt)

structure PrivateImported (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop extends
    PrivateReady p slots yb xb s where
  imported : numAt s.mem (State.addr p.base) p.w 1 = Spec.Rsa.os2ip yb

structure PrivateRanged (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop extends
    PrivateReady p slots yb xb s where
  flag : s.gpr .r11 = if 1 < Spec.Rsa.os2ip yb ∧ Spec.Rsa.os2ip yb < p.P - 1 then 1 else 0

theorem PrivateRanged.after_mem {p : Inputs} {slots : List Nat} {yb xb : List Byte} {s t : State}
    (h : PrivateRanged p slots yb xb s) (mem : t.mem = s.mem) (rest : VG.Proof.X25519.Arm.Rest [] s t) :
    PrivateRanged p slots yb xb t :=
  ⟨h.toPrivateReady.after_mem mem rest ((rest.gpr .r0 (by simp)).trans h.context.ptr),
    (rest.gpr .r11 (by simp)).trans h.flag⟩

theorem privateImport_public (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : PrivateReady p slots yb xb s) (stable : stableSlots slots = true) (h36 : 36 ∈ slots) (h32 : 32 ∈ slots)
    (length : yb.length = p.k) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 36 32) s (PrivateImported p slots yb xb) := by
  have op0 : Operand 0 := by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  refine WP.mono (importAt_ok s 1 36 32 h.context stable h36 h32 h.ready (by decide) (by decide) h.value
    (by rw [length]; have := p.minLength; omega) (by rw [length]; exact p.width.2.2.2.1)
    (by change BitVec.ofNat 32 p.k = _; rw [length])) ?_
  rintro u ⟨context, ready, value, keeps, frame, rest⟩
  have fits : arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
  exact ⟨⟨context, ready, (keeps_array_num keeps fits op0 (by decide)).trans h.modulus,
    (keeps_array_num keeps fits op4 (by decide)).trans h.r2,
    h.value.after_workspace frame rest, h.scalar.after_workspace frame rest⟩, value⟩

theorem privateRange_public (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : PrivateImported p slots yb xb s) (stable : stableSlots slots = true) (odd : p.P % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.inRange 1) s (PrivateRanged p slots yb xb) := by
  have op0 : Operand 0 := by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  refine WP.mono (inRange_ok s h.ready op1 (by decide) (by rw [h.modulus]; exact odd)) ?_
  rintro u ⟨ready, flag, arrays, frame, rest⟩
  rw [h.imported, h.modulus] at flag
  exact ⟨h.toPrivateReady.after_workspace stable frame rest ready
    ((arrays 0 op0 (by decide)).trans h.modulus) ((arrays 4 op4 (by decide)).trans h.r2), flag⟩

theorem privatePublic_ct {p : Inputs} {slots : List Nat} {yb xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots)
    (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (peerLength : yb.length = p.k) (positive : 0 < xb1.length) (fits : xb1.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => PrivateReady p slots yb xb1 s ∧ PrivateReady p slots yb xb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.CheckPrivate.publicCheck (fun _ _ => True) := by
  have imports := (importAt_ct (p := p) (a := 1) (slot := 36) (k := p.k)
    stable h36 h32 rfl (by decide)).mono
    (P' := fun (s t : State) => PrivateReady p slots yb xb1 s ∧ PrivateReady p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready⟩, ⟨h.2.1.context, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  have ranges := (inRange_ct (base := p.base) (len := p.len) (w := p.w)
    (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp] : Operand 1) (by decide)).mono
    (P' := fun (s t : State) => PrivateImported p slots yb xb1 s ∧ PrivateImported p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.2.2⟩) (fun _ _ h => h)
  have branches : RelCT isa (fun s t => PrivateRanged p slots yb xb1 s ∧ PrivateRanged p slots yb xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.ifFlag VG.Impl.Ffdh.Arm.Domain.CheckPrivate.tail (VG.Impl.Ffdh.Arm.Domain.ret 0))
      (fun _ _ => True) := by
    apply ifFlag_pair_ct (decide (1 < Spec.Rsa.os2ip yb ∧ Spec.Rsa.os2ip yb < p.P - 1))
      (fun _ h => by simpa only [decide_eq_true_eq] using h.flag)
      (fun _ h => by simpa only [decide_eq_true_eq] using h.flag)
      (fun _ _ h mem rest => h.after_mem mem rest) (fun _ _ h mem rest => h.after_mem mem rest)
    · intro _
      exact (privateTail_ct stable h28 h32 h36 h40 h44 h56 h60 peerLength positive fits count length odd).mono
        (fun _ _ h => ⟨h.1.toPrivateReady, h.2.1.toPrivateReady, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPrivate.publicCheck
  exact relCT_chain imports (fun s h => privateImport_public s h stable h36 h32 peerLength)
    (fun s h => privateImport_public s h stable h36 h32 peerLength)
    (relCT_chain ranges (fun s h => privateRange_public s h stable odd)
      (fun s h => privateRange_public s h stable odd) branches)

end VG.Proof.Ffdh.Arm
