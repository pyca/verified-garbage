module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.PrivatePublic
import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRange
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAt
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarUpper
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt

/-! Imported private-key validation keeps scalar validity and public-key consistency in native code. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand arrAt)

def privateMainFlag (p : Inputs) (yb xb : List Byte) : BitVec 32 :=
  if 0 < Spec.Rsa.os2ip xb ∧ Spec.Rsa.os2ip xb < scalarBound p then privatePublicFlag p yb xb else 2

theorem privateMain_ok (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1)
    (value : Octets p.base p.publicValue p.len yb s) (length : yb.length = p.k)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length)
    (scalarLength : xb.length ≤ p.k) (count : p.slotValue 44 = BitVec.ofNat 32 xb.length)
    (valueStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr s.sp, 72⟩)
    (scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr s.sp, 72⟩) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckPrivate.main s fun t =>
      t.gpr .r0 = privateMainFlag p yb xb ∧ Frame (prepareAtWrites p s) s.mem t.mem := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have extend {m m' : Mem} (f : Frame [⟨State.addr p.base, 8 * p.len⟩] m m') : Frame (prepareAtWrites p s) m m' :=
    f.mono (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact List.mem_cons_self)
  have pStack : Region.Disjoint ⟨State.addr p.domain, p.k⟩ ⟨State.addr s.sp, 72⟩ :=
    h.domainStack.sub_left (Region.sub_prefix (by rw [p.domainLength]; split <;> omega))
  rw [VG.Impl.Ffdh.Arm.Domain.CheckPrivate.main, WP.seq_iff]
  refine WP.mono (prepareAt_ok s 24 h stable h24 h32 h0 h.pBytes p.pLength pStack large odd) ?_
  rintro u ⟨contextU, readyU, modU, r2U, frameU, restU⟩
  have sourceSep {src : BitVec 32} {bs : List Byte} (source : Octets p.base src p.len bs s)
      (stack : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr s.sp, 72⟩)
      (r : Region) (hr : r ∈ prepareAtWrites p s) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
    simp only [prepareAtWrites, prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact source.separate
    · exact stack.sub_right (Offset.sub_base _ (by decide))
    · exact stack.sub_right (Offset.sub_base _ (by decide))
  have valueU := value.after_frame frameU restU (sourceSep value valueStack)
  have scalarU := scalar.after_frame frameU restU (sourceSep scalar scalarStack)
  rw [WP.seq_iff]
  refine WP.mono (importAt_ok u 1 40 44 contextU stable h40 h44 readyU (by decide) (by decide)
    scalarU positive (Nat.le_trans scalarLength p.width.2.2.2.1) count) ?_
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
  have valueW := (valueU.after_workspace frameV restV).after_workspace frameW restW
  have scalarW := (scalarU.after_workspace frameV restV).after_workspace frameW restW
  have fullW := (frameU.trans (extend frameV)).trans (extend frameW)
  rw [VG.Impl.Ffdh.Arm.Domain.ifFlag, WP.seq_iff]
  refine WP.mono (testFlag_ok w) ?_
  rintro z ⟨⟨zeroZ, memZ⟩, restZ⟩
  by_cases valid : 0 < Spec.Rsa.os2ip xb ∧ Spec.Rsa.os2ip xb < scalarBound p
  · refine WP.ite true (by change some (!z.z) = some true; rw [zeroZ, flag, scalarValidFlag, ite_eq_left valid]; rfl) ?_ (by intro hf; cases hf)
    intro _
    have ptrZ := (restZ.gpr .r0 (by simp)).trans contextW.ptr
    have contextZ := contextW.of_mem memZ restZ ptrZ
    have readyZ := readyW.of_mem memZ restZ ptrZ
    have frameZ : Frame [⟨State.addr p.base, 8 * p.len⟩] w.mem z.mem := by rw [memZ]; exact Frame.refl _ _
    refine WP.mono (privatePublic_ok z contextZ stable h28 h32 h36 h40 h44 h56 h60 readyZ
      (by rw [memZ]; exact modW) odd (by rw [memZ]; exact r2W)
      (valueW.after_workspace frameZ restZ) length (scalarW.after_workspace frameZ restZ) positive
      (by have := p.maxLength; omega) count) ?_
    rintro t ⟨result, frameT⟩
    exact ⟨by rw [privateMainFlag, ite_eq_left valid]; exact result,
      (fullW.trans (extend frameZ)).trans (extend frameT)⟩
  · refine WP.ite false (by change some (!z.z) = some false; rw [zeroZ, flag, scalarValidFlag, ite_eq_right valid]; rfl) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (ret_ok z 2 (by decide)) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    exact ⟨by rw [result, privateMainFlag, ite_eq_right valid], by rw [memT, memZ]; exact fullW⟩

end VG.Proof.Ffdh.Arm
