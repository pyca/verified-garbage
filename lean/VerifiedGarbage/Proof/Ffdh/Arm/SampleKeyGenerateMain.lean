module

import VerifiedGarbage.Impl.Ffdh.Arm.KeyGenerate
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrepareLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleTailLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleResult
import VerifiedGarbage.Proof.Ffdh.Arm.SampleMemory
public import VerifiedGarbage.Impl.Ffdh.Arm.SampleKeyGenerate
import VerifiedGarbage.Proof.Ffdh.Arm.KeyMain
import VerifiedGarbage.Proof.Ffdh.Arm.KeySample
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyTail
import VerifiedGarbage.Proof.Ffdh.Arm.KeyFail
import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRange
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyOutputs
import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalarSpec
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarUpper
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicMain
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
import VerifiedGarbage.Proof.Framework.Arm.Syms

/-! Generic key-generation sampling, validation and result handling for a supplied verified exponentiator. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt Operand arrAt)

theorem sampleKeyGenerateMain_ok (prepare sample tail : Prog isa) (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p)
    (prep : KeyPrepareLaw prepare) (sampler : SampleLaw env layout sample) (law : SampleTailLaw tail) (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (h : Context p slots s) (environment : env.holds p s) (calls : KeyCallMemory p s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h48 : 48 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (special : sampleSlots slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1) (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr s.sp, 72⟩)
    (outputs : KeyOutputs p s)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (privateLength : p.privateLength = p.k) (outputY : p.output = p.publicValue) :
    WP isa (VG.Impl.Ffdh.Arm.SampleKeyGenerate.main prepare sample tail) s fun t =>
      t.gpr .r0 = sampleMainFlag p (layout p) rb ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.k =
        (if sampleSuccess p (layout p) rb then (layout p).encode rb else List.replicate p.k 0) ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.publicValue) p.k =
        (if sampleSuccess p (layout p) rb then Spec.Rsa.i2osp (keyPower p ((layout p).encode rb)) p.k else List.replicate p.k 0) ∧
      Frame (keyCallWrites p s) s.mem t.mem := by
  have op0 : Operand 0 := by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  have extend {m m' : Mem} (f : Frame [⟨State.addr p.base, 8 * p.len⟩] m m') : Frame (keyCallWrites p s) m m' :=
    f.mono (by simp [keyCallWrites, keyWrites])
  rw [VG.Impl.Ffdh.Arm.SampleKeyGenerate.main, WP.seq_iff]
  refine WP.mono_syms (prep.correct s h calls stable h0 h24 h32 large odd normalized) ?_
  rintro u ⟨contextU, readyU, modU, r2U, frameU, restU⟩ symsU
  have fullU : Frame (keyCallWrites p s) s.mem u.mem := frameU.sub (by
    intro r hr
    simp only [keyPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact ⟨⟨State.addr p.base, 8 * p.len⟩, by simp [keyCallWrites, keyWrites], by intro a ha; exact ha⟩
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], Offset.sub_base _ (by decide)⟩
    · exact ⟨_, by simp [keyCallWrites], fun _ hx => hx⟩)
  have environmentU := env.stable environment fullU restU symsU
  have entropyU := entropy.after_frame frameU restU (by
    intro r hr
    simp only [keyPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact entropy.separate
    · rw [size]; exact entropyStack.sub_right (Offset.sub_base _ (by decide))
    · rw [size]; exact entropyStack.sub_right (Offset.sub_base _ (by decide))
    · rw [size]; exact calls.entropy)
  rw [WP.seq_iff]
  refine WP.mono (sampler.correct u contextU environmentU normalized odd stable special h0 h24 h28 h32 h40 h48 h60 readyU modU r2U entropyU size
    (by rw [restU.sp]; exact entropyStack) (outputs.after restU) entropySep) ?_
  rintro v ⟨contextV, readyV, modV, r2V, scalarV, significantV, frameV, restV⟩
  have scalarSize := (layout p).encode_length size
  have count : p.slotValue 44 = BitVec.ofNat 32 ((layout p).encode rb).length := by
    change BitVec.ofNat 32 p.privateLength = _
    rw [privateLength, scalarSize]
  rw [WP.seq_iff]
  refine WP.mono (importAt_ok v 1 40 44 contextV.toContext stable (by simp [h40]) (by simp [h44]) readyV (by decide) (by decide)
    scalarV (by rw [scalarSize]; have := p.minLength; omega) (by rw [scalarSize]; exact p.width.2.2.2.1) count) ?_
  rintro w ⟨contextW0, readyW, x, keepsW, frameW, restW⟩
  have contextW := contextV.after_workspace frameW restW contextW0.ptr (fun d hd => (stableSlots_at stable hd).1)
  have fits : arrAt p.w 8 ≤ 8 * p.len := readyW.width ▸ readyW.layout.2.2.1
  have modW := (keeps_array_num keepsW fits op0 (by decide)).trans modV
  have r2W := (keeps_array_num keepsW fits op4 (by decide)).trans r2V
  rw [WP.seq_iff]
  refine WP.mono (scalarRange_ok w contextW.toContext stable (by simp [h28]) (by simp [h32]) (by simp [h60]) readyW modW odd) ?_
  rintro a ⟨contextA0, readyA, flag, arraysA, frameA, restA⟩
  have contextA := contextW.after_workspace frameA restA contextA0.ptr (fun d hd => (stableSlots_at stable hd).1)
  rw [x] at flag
  have modA := (arraysA 0 (by simp)).trans modW
  have r2A := (arraysA 4 (by simp)).trans r2W
  have scalarA := (scalarV.after_workspace frameW restW).after_workspace frameA restA
  have significantA := (significantV.after_workspace frameW restW).after_workspace frameA restA
  have outA := (((outputs.after restU).after restV).after restW).after restA
  have fullV : Frame (keyCallWrites p s) u.mem v.mem := frameV.sub (by
    intro r hr
    simp only [keyScalarWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], by rw [restU.sp]; exact Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], by rw [restU.sp]; exact Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], by rw [restU.sp]; exact Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr p.privateValue, p.k⟩, by simp [keyCallWrites, keyWrites], by intro a ha; exact ha⟩)
  have fullA := ((fullU.trans fullV).trans (extend frameW)).trans (extend frameA)
  rw [VG.Impl.Ffdh.Arm.Domain.ifFlag, WP.seq_iff]
  refine WP.mono (testFlag_ok a) ?_
  rintro z ⟨⟨zeroZ, memZ⟩, restZ⟩
  have ptrZ := (restZ.gpr .r0 (by simp)).trans contextA.ptr

  have readyZ := readyA.of_mem memZ restZ ptrZ
  have frameZ : Frame [⟨State.addr p.base, 8 * p.len⟩] a.mem z.mem := by rw [memZ]; exact Frame.refl _ _
  have contextZ := contextA.after_workspace frameZ restZ ptrZ (fun d hd => (stableSlots_at stable hd).1)
  have scalarZ := scalarA.after_workspace frameZ restZ
  have significantZ := significantA.after_workspace frameZ restZ
  have outZ := outA.after restZ
  by_cases valid : sampleScalarValid p (layout p) rb
  · refine WP.ite true (by change some (!z.z) = some true; rw [zeroZ, flag, scalarValidFlag, ite_eq_left (show 0 < Spec.Rsa.os2ip ((layout p).encode rb) ∧ Spec.Rsa.os2ip ((layout p).encode rb) < scalarBound p from valid)]; rfl) ?_ (by intro hf; cases hf)
    intro _
    refine WP.mono (law.correct z contextZ
      (((((calls.after restU).after restV).after restW).after restA).after restZ) stable h4 h32
      h36 h40 h56 saved readyZ (by rw [memZ]; exact modA) odd
      (by rw [memZ]; exact r2A) scalarZ scalarSize significantZ
      (by rw [List.length_drop, scalarSize]; rfl) ((layout p).encode_significant rb) outZ outputY) ?_
    rintro t ⟨status, privateT, publicT, frameT⟩
    refine ⟨by rw [sampleMainFlag, ite_eq_left valid]; exact status,
      by simpa only [sampleSuccess, decide_eq_true valid, Bool.true_and] using privateT,
      by simpa only [sampleSuccess, decide_eq_true valid, Bool.true_and] using publicT, ?_⟩
    have same : Frame (keyCallWrites p s) z.mem t.mem := by
      simpa only [keyCallWrites, keyWrites, restZ.sp, restA.sp, restW.sp, restV.sp, restU.sp] using frameT
    exact (fullA.trans (extend frameZ)).trans same
  · refine WP.ite false (by change some (!z.z) = some false; rw [zeroZ, flag, scalarValidFlag, ite_eq_right (show ¬(0 < Spec.Rsa.os2ip ((layout p).encode rb) ∧ Spec.Rsa.os2ip ((layout p).encode rb) < scalarBound p) from valid)]; rfl) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (keyFail_ok z contextZ.toArgumentMemory (fun d hd => (stableSlots_at stable hd).1)
      (by simp [h32]) (by simp [h36]) (by simp [h40]) outZ) ?_
    rintro t ⟨status, privateT, publicT, frameT⟩
    refine ⟨by rw [sampleMainFlag, ite_eq_right valid]; exact status,
      by simpa only [sampleSuccess, decide_eq_false valid, Bool.false_and, Bool.false_eq_true, ite_false] using privateT,
      by simpa only [sampleSuccess, decide_eq_false valid, Bool.false_and, Bool.false_eq_true, ite_false] using publicT, ?_⟩
    exact (fullA.trans (extend frameZ)).trans (frameT.mono (by simp [keyCallWrites, keyWrites]))

end VG.Proof.Ffdh.Arm
