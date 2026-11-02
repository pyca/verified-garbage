module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.KeySample
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyTail
import VerifiedGarbage.Proof.Ffdh.Arm.KeyFail
import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRange
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAt
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyOutputs
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalarSpec
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarUpper
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicMain
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt

/-! One key-generation attempt runs sampling, scalar validation, windowed
exponentiation, and output rejection entirely in native ARMv7 code. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand arrAt)

def keyScalarValid (p : Inputs) (rb : List Byte) : Prop :=
  0 < Spec.Rsa.os2ip (scalarOctets p rb) ∧ Spec.Rsa.os2ip (scalarOctets p rb) < scalarBound p

instance (p : Inputs) (rb : List Byte) : Decidable (keyScalarValid p rb) := inferInstanceAs (Decidable (_ ∧ _))

def keySuccess (p : Inputs) (rb : List Byte) : Bool := decide (keyScalarValid p rb) && keyAccepted p (scalarOctets p rb)

def keyMainFlag (p : Inputs) (rb : List Byte) : BitVec 32 :=
  if keyScalarValid p rb then (if keyAccepted p (scalarOctets p rb) then 1 else 3) else 2

theorem keyMain_ok (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h48 : 48 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (large : 1 < p.P) (odd : p.P % 2 = 1)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr s.sp, 72⟩)
    (outputs : KeyOutputs p s)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (privateLength : p.privateLength = p.k) (outputY : p.output = p.publicValue) :
    WP isa VG.Impl.Ffdh.Arm.Domain.GenerateKey.main s fun t =>
      t.gpr .r0 = keyMainFlag p rb ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.k =
        (if keySuccess p rb then scalarOctets p rb else List.replicate p.k 0) ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.publicValue) p.k =
        (if keySuccess p rb then Spec.Rsa.i2osp (keyPower p (scalarOctets p rb)) p.k else List.replicate p.k 0) ∧
      Frame (keyWrites p s) s.mem t.mem := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have extend {m m' : Mem} (f : Frame [⟨State.addr p.base, 8 * p.len⟩] m m') : Frame (keyWrites p s) m m' :=
    f.mono (by simp [keyWrites])
  have pStack : Region.Disjoint ⟨State.addr p.domain, p.k⟩ ⟨State.addr s.sp, 72⟩ :=
    h.domainStack.sub_left (Region.sub_prefix (by rw [p.domainLength]; split <;> omega))
  rw [VG.Impl.Ffdh.Arm.Domain.GenerateKey.main, WP.seq_iff]
  refine WP.mono (prepareAt_ok s 24 h stable h24 h32 h0 h.pBytes p.pLength pStack large odd) ?_
  rintro u ⟨contextU, readyU, modU, r2U, frameU, restU⟩
  have entropyU := entropy.after_frame frameU restU (by
    intro r hr
    simp only [prepareAtWrites, prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact entropy.separate
    · rw [size]; exact entropyStack.sub_right (Offset.sub_base _ (by decide))
    · rw [size]; exact entropyStack.sub_right (Offset.sub_base _ (by decide)))
  rw [WP.seq_iff]
  refine WP.mono (keySample_ok u contextU stable h0 h24 h28 h32 h40 h48 h60 readyU modU r2U entropyU size
    (by rw [restU.sp]; exact entropyStack) (outputs.after restU) entropySep) ?_
  rintro v ⟨contextV, readyV, modV, r2V, scalarV, significantV, frameV, restV⟩
  have stableV : stableSlots (16 :: 68 :: 20 :: slots) = true := by
    change (true && (true && (true && stableSlots slots))) = true
    rw [Bool.true_and, Bool.true_and, Bool.true_and, stable]
  have savedV : ∀ d ∈ 16 :: 68 :: 20 :: slots, d + 4 ≤ 64 ∨ 68 ≤ d := by
    intro d hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | rfl | rfl | hd
    · left; decide
    · right; decide
    · left; decide
    · exact saved d hd
  have scalarSize := scalarOctets_length (p := p) size
  have count : p.slotValue 44 = BitVec.ofNat 32 (scalarOctets p rb).length := by
    change BitVec.ofNat 32 p.privateLength = _
    rw [privateLength, scalarSize]
  rw [WP.seq_iff]
  refine WP.mono (importAt_ok v 1 40 44 contextV stableV (by simp [h40]) (by simp [h44]) readyV (by decide) (by decide)
    scalarV (by rw [scalarSize]; have := p.minLength; omega) (by rw [scalarSize]; exact p.width.2.2.2.1) count) ?_
  rintro w ⟨contextW, readyW, x, keepsW, frameW, restW⟩
  have fits : arrAt p.w 8 ≤ 8 * p.len := readyW.width ▸ readyW.layout.2.2.1
  have modW := (keeps_array_num keepsW fits op0 (by decide)).trans modV
  have r2W := (keeps_array_num keepsW fits op4 (by decide)).trans r2V
  rw [WP.seq_iff]
  refine WP.mono (scalarRange_ok w contextW stableV (by simp [h28]) (by simp [h32]) (by simp [h60]) readyW modW odd) ?_
  rintro a ⟨contextA, readyA, flag, arraysA, frameA, restA⟩
  rw [x] at flag
  have modA := (arraysA 0 (by simp)).trans modW
  have r2A := (arraysA 4 (by simp)).trans r2W
  have scalarA := (scalarV.after_workspace frameW restW).after_workspace frameA restA
  have significantA := (significantV.after_workspace frameW restW).after_workspace frameA restA
  have outA := (((outputs.after restU).after restV).after restW).after restA
  have fullU : Frame (keyWrites p s) s.mem u.mem := frameU.sub (by
    intro r hr
    simp only [prepareAtWrites, prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨State.addr p.base, 8 * p.len⟩, by simp [keyWrites], by intro a ha; exact ha⟩
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyWrites], Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyWrites], Offset.sub_base _ (by decide)⟩)
  have fullV : Frame (keyWrites p s) u.mem v.mem := frameV.sub (by
    intro r hr
    simp only [keyScalarWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyWrites], by rw [restU.sp]; exact Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyWrites], by rw [restU.sp]; exact Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyWrites], by rw [restU.sp]; exact Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr p.privateValue, p.k⟩, by simp [keyWrites], by intro a ha; exact ha⟩)
  have fullA := ((fullU.trans fullV).trans (extend frameW)).trans (extend frameA)
  rw [VG.Impl.Ffdh.Arm.Domain.ifFlag, WP.seq_iff]
  refine WP.mono (testFlag_ok a) ?_
  rintro z ⟨⟨zeroZ, memZ⟩, restZ⟩
  have ptrZ := (restZ.gpr .r0 (by simp)).trans contextA.ptr
  have contextZ := contextA.of_mem memZ restZ ptrZ
  have readyZ := readyA.of_mem memZ restZ ptrZ
  have frameZ : Frame [⟨State.addr p.base, 8 * p.len⟩] a.mem z.mem := by rw [memZ]; exact Frame.refl _ _
  have scalarZ := scalarA.after_workspace frameZ restZ
  have significantZ := significantA.after_workspace frameZ restZ
  have outZ := outA.after restZ
  by_cases valid : keyScalarValid p rb
  · refine WP.ite true (by change some (!z.z) = some true; rw [zeroZ, flag, scalarValidFlag, ite_eq_left (show 0 < Spec.Rsa.os2ip (scalarOctets p rb) ∧ Spec.Rsa.os2ip (scalarOctets p rb) < scalarBound p from valid)]; rfl) ?_ (by intro hf; cases hf)
    intro _
    refine WP.mono (keyTail_ok z contextZ stableV (by simp [h4]) (by simp) (by simp) (by simp [h32])
      (by simp [h36]) (by simp [h40]) (by simp [h56]) savedV readyZ (by rw [memZ]; exact modA) odd
      (by rw [memZ]; exact r2A) scalarZ scalarSize significantZ
      (by rw [List.length_drop, scalarSize]; rfl) scalarOctets_significant outZ outputY) ?_
    rintro t ⟨status, privateT, publicT, frameT⟩
    refine ⟨by rw [keyMainFlag, ite_eq_left valid]; exact status,
      by simpa only [keySuccess, decide_eq_true valid, Bool.true_and] using privateT,
      by simpa only [keySuccess, decide_eq_true valid, Bool.true_and] using publicT, ?_⟩
    have same : Frame (keyWrites p s) z.mem t.mem := by
      simpa only [keyWrites, restZ.sp, restA.sp, restW.sp, restV.sp, restU.sp] using frameT
    exact (fullA.trans (extend frameZ)).trans same
  · refine WP.ite false (by change some (!z.z) = some false; rw [zeroZ, flag, scalarValidFlag, ite_eq_right (show ¬(0 < Spec.Rsa.os2ip (scalarOctets p rb) ∧ Spec.Rsa.os2ip (scalarOctets p rb) < scalarBound p) from valid)]; rfl) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (keyFail_ok z contextZ.toArgumentMemory (fun d hd => (stableSlots_at stableV hd).1)
      (by simp [h32]) (by simp [h36]) (by simp [h40]) outZ) ?_
    rintro t ⟨status, privateT, publicT, frameT⟩
    refine ⟨by rw [keyMainFlag, ite_eq_right valid]; exact status,
      by simpa only [keySuccess, decide_eq_false valid, Bool.false_and, Bool.false_eq_true, ite_false] using privateT,
      by simpa only [keySuccess, decide_eq_false valid, Bool.false_and, Bool.false_eq_true, ite_false] using publicT, ?_⟩
    exact (fullA.trans (extend frameZ)).trans (frameT.mono (by simp [keyWrites]))

end VG.Proof.Ffdh.Arm
