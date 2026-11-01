module

public import VerifiedGarbage.Proof.Ffdh.Arm.SharedDeriveTail
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarUpper
import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRange
import VerifiedGarbage.Proof.Ffdh.Arm.DomainNormalizedPrepareAt
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset

/-! Modulus preparation, the scalar's range, and the derivation's two paths. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedDerive
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand arrAt)

/-- The scalar is in range and its public value is accepted. -/
def accepted (p : Inputs) (xb : List Byte) : Prop :=
  (0 < Spec.Rsa.os2ip xb ∧ Spec.Rsa.os2ip xb < scalarBound p) ∧ sharedAccepted p (gOctets p) xb = true

/-- The status returned: 2 for a scalar out of range, then 1 or 3 by y's range. -/
def status (p : Inputs) (xb : List Byte) : BitVec 32 :=
  if 0 < Spec.Rsa.os2ip xb ∧ Spec.Rsa.os2ip xb < scalarBound p then
    (if sharedAccepted p (gOctets p) xb then 1 else 3) else 2

def result (p : Inputs) (xb : List Byte) (s : State) : Prop :=
  s.gpr .r0 = status p xb ∧ Spec.Rsa.bytesAt s.mem (State.addr p.output) p.k =
    (open Classical in if accepted p xb then Spec.Rsa.i2osp (sharedValue p (gOctets p) xb) p.k
      else List.replicate p.k 0)

theorem main_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} {xb : List Byte}
    (h : Context p slots s) (calls : SharedExchange.CallMemory p xb.length s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (large : 1 < p.P) (odd : p.P % 2 = 1) (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length)
    (scalarLength : xb.length ≤ p.k) (scalarCount : p.slotValue 44 = BitVec.ofNat 32 xb.length)
    (scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr s.sp, 72⟩)
    (output : OutputBuffer p.output p.k s)
    (workspaceSep : Region.Disjoint ⟨State.addr p.base, 8 * p.len⟩ ⟨State.addr p.output, p.k⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.output, p.k⟩) :
    WP isa (VG.Impl.Ffdh.Arm.SharedDerive.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s
      fun t => result p xb t ∧ Frame (SharedExchange.writes p s) s.mem t.mem := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have extend {m m' : Mem} (f : Frame [⟨State.addr p.base, 8 * p.len⟩] m m') :
      Frame (SharedExchange.writes p s) m m' :=
    f.mono (by simp [SharedExchange.writes, exchangeWrites])
  rw [VG.Impl.Ffdh.Arm.SharedDerive.main, WP.seq_iff]
  refine WP.mono (domainNormalizedPrepareAt24_ok backend s h calls.toDomainCallMemory stable h0 h24 h32
    large odd normalized) ?_
  rintro u ⟨contextU, readyU, modU, r2U, frameU, restU⟩
  have scalarU := scalar.after_frame frameU restU (by
    intro r hr
    simp only [domainPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact scalar.separate
    · exact scalarStack.sub_right (Offset.sub_base _ (by decide))
    · exact scalarStack.sub_right (Offset.sub_base _ (by decide))
    · exact calls.scalarBelow)
  have fU : Frame (SharedExchange.writes p s) s.mem u.mem := frameU.sub (by
    intro r hr
    simp only [domainPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact ⟨⟨State.addr p.base, 8 * p.len⟩, by simp [SharedExchange.writes, exchangeWrites],
        by intro a ha; exact ha⟩
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [SharedExchange.writes, exchangeWrites], Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [SharedExchange.writes, exchangeWrites], Offset.sub_base _ (by decide)⟩
    · exact ⟨FrameStack.belowA s.sp 48, by simp [SharedExchange.writes], by intro a ha; exact ha⟩)
  rw [WP.seq_iff]
  refine WP.mono (importAt_ok u 1 40 44 contextU stable h40 h44 readyU (by decide) (by decide)
    scalarU positive (Nat.le_trans scalarLength p.width.2.2.2.1) scalarCount) ?_
  rintro v ⟨contextV, readyV, x, keepsV, frameV, restV⟩
  have fits : arrAt p.w 8 ≤ 8 * p.len := readyV.width ▸ readyV.layout.2.2.1
  have modV := (keeps_array_num keepsV fits op0 (by decide)).trans modU
  have r2V := (keeps_array_num keepsV fits op4 (by decide)).trans r2U
  rw [WP.seq_iff]
  refine WP.mono (scalarRange_ok v contextV stable h28 h32 h60 readyV modV odd) ?_
  rintro w ⟨contextW, readyW, flag, arraysW, frameW, restW⟩
  rw [x] at flag
  have modW := (arraysW 0 (by simp)).trans modV
  have r2W := (arraysW 4 (by simp)).trans r2V
  have scalarW := (scalarU.after_workspace frameV restV).after_workspace frameW restW
  have fUW := (fU.trans (extend frameV)).trans (extend frameW)
  have restUW := (restU.trans restV).trans restW
  rw [VG.Impl.Ffdh.Arm.Domain.ifFlag, WP.seq_iff]
  refine WP.mono (testFlag_ok w) ?_
  rintro z ⟨⟨zeroZ, memZ⟩, restZ⟩
  have ptrZ := (restZ.gpr .r0 (by simp)).trans contextW.ptr
  have contextZ := contextW.of_mem memZ restZ ptrZ
  have restSZ := restUW.trans (restZ.mono (by simp))
  by_cases valid : 0 < Spec.Rsa.os2ip xb ∧ Spec.Rsa.os2ip xb < scalarBound p
  · refine WP.ite true (by change some (!z.z) = some true; rw [zeroZ, flag, scalarValidFlag, ite_eq_left valid]; rfl) ?_ (by intro hf; cases hf)
    intro _
    have frameZ : Frame [⟨State.addr p.base, 8 * p.len⟩] w.mem z.mem := by rw [memZ]; exact Frame.refl _ _
    refine WP.mono (tail_ok backend z contextZ ⟨calls.toDomainCallMemory.after restSZ,
        by rw [restSZ.sp]; exact calls.scalarBelow, by rw [restSZ.sp]; exact calls.outputBelow⟩
      stable h4 h32 h40 h44 h56 saved odd
      (readyW.of_mem memZ restZ ptrZ) (by rw [memZ]; exact modW) (by rw [memZ]; exact r2W)
      (scalarW.after_workspace frameZ restZ) positive (by have := p.maxLength; omega) scalarCount
      (output.after restSZ) workspaceSep (by rw [restSZ.sp]; exact stackSep)) ?_
    rintro t ⟨status_t, bytes, frameT⟩
    refine ⟨⟨by rw [status, ite_eq_left valid]; exact status_t, ?_⟩, ?_⟩
    · rw [bytes]
      by_cases acc : sharedAccepted p (gOctets p) xb = true
      · rw [ite_eq_left acc, ite_eq_left ⟨valid, acc⟩]
      · rw [ite_eq_right acc, ite_eq_right (fun h => acc h.2)]
    · have fT := frameT
      simp only [SharedExchange.writes, exchangeWrites, restSZ.sp] at fT
      exact (fUW.trans (by rw [memZ]; exact Frame.refl _ _)).trans fT
  · refine WP.ite false (by change some (!z.z) = some false; rw [zeroZ, flag, scalarValidFlag, ite_eq_right valid]; rfl) (by intro ht; cases ht) ?_
    intro _
    have flagZ : z.gpr .r11 = 0 := by
      rw [restZ.gpr .r11 (by simp), flag, scalarValidFlag, ite_eq_right valid]
    refine WP.mono (fail_ok z contextZ h4 h32 flagZ (output.after restSZ) (by rw [restSZ.sp]; exact stackSep)) ?_
    rintro t ⟨status_t, bytes, frameT⟩
    refine ⟨⟨by rw [status, ite_eq_right valid]; exact status_t, ?_⟩, ?_⟩
    · rw [bytes, ite_eq_right (fun h => valid h.1)]
    · have fT : Frame (SharedExchange.writes p s) z.mem t.mem := frameT.mono (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp [SharedExchange.writes, exchangeWrites, restSZ.sp])
      exact (fUW.trans (by rw [memZ]; exact Frame.refl _ _)).trans fT

end VG.Proof.Ffdh.Arm.SharedDerive
