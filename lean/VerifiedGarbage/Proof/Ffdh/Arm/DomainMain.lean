module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.DomainTail
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAt
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Framework.Block

/-! Native generator range and optional subgroup-order validation. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand arrAt)

def domainMainFlag (p : Inputs) (y : Nat) : BitVec 32 :=
  if 1 < y ∧ y < p.P - 1 then domainTailFlag p else 0

theorem domainMain_ok (s : State) {p : Inputs} {slots : List Nat} {yb : List Byte}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1)
    (value : Octets p.base p.g p.len yb s) (length : yb.length = p.k)
    (valueStack : Region.Disjoint ⟨State.addr p.g, yb.length⟩ ⟨State.addr s.sp, 72⟩) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckDomain.main s fun t =>
      t.gpr .r0 = domainMainFlag p (Spec.Rsa.os2ip yb) ∧ Frame (prepareAtWrites p s) s.mem t.mem := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have extend {m m' : Mem} (f : Frame [⟨State.addr p.base, 8 * p.len⟩] m m') : Frame (prepareAtWrites p s) m m' :=
    f.mono (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact List.mem_cons_self)
  have pStack : Region.Disjoint ⟨State.addr p.domain, p.k⟩ ⟨State.addr s.sp, 72⟩ :=
    h.domainStack.sub_left (Region.sub_prefix (by rw [p.domainLength]; split <;> omega))
  rw [VG.Impl.Ffdh.Arm.Domain.CheckDomain.main, WP.seq_iff]
  refine WP.mono (prepareAt_ok s 24 h stable h24 h32 h0 h.pBytes p.pLength pStack large odd) ?_
  rintro u ⟨contextU, readyU, modU, r2U, frameU, restU⟩
  have valueU := value.after_frame frameU restU (by
    intro r hr
    simp only [prepareAtWrites, prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact value.separate
    · exact valueStack.sub_right (Offset.sub_base _ (by decide))
    · exact valueStack.sub_right (Offset.sub_base _ (by decide)))
  rw [WP.seq_iff]
  refine WP.mono (importAt_ok u 1 56 32 contextU stable h56 h32 readyU (by decide) (by decide)
    valueU (by rw [length]; have := p.minLength; omega) (by rw [length]; exact p.width.2.2.2.1)
    (by change BitVec.ofNat 32 p.k = _; rw [length])) ?_
  rintro v ⟨contextV, readyV, y, keepsV, frameV, restV⟩
  have bound : arrAt p.w 8 ≤ 8 * p.len := readyV.width ▸ readyV.layout.2.2.1
  have modV := (keeps_array_num keepsV bound op0 (by decide : 0 ≠ 1)).trans modU
  have r2V := (keeps_array_num keepsV bound op4 (by decide : 4 ≠ 1)).trans r2U
  rw [WP.seq_iff]
  refine WP.mono (inRange_ok v readyV op1 (by decide) (by rw [modV]; exact odd)) ?_
  rintro w ⟨readyW, flag, arraysW, frameW, restW⟩
  rw [y, modV] at flag
  change w.gpr .r11 = (if 1 < Spec.Rsa.os2ip yb ∧ Spec.Rsa.os2ip yb < p.P - 1 then 1 else 0) at flag
  have contextW := contextV.after_workspace frameW restW readyW.ptr (fun d hd => (stableSlots_at stable hd).1)
  have modW := (arraysW 0 op0 (by decide)).trans modV
  have r2W := (arraysW 4 op4 (by decide)).trans r2V
  have frameW' := (frameU.trans (extend frameV)).trans (extend frameW)
  rw [VG.Impl.Ffdh.Arm.Domain.ifFlag, WP.seq_iff]
  refine WP.mono (testFlag_ok w) ?_
  rintro z ⟨⟨zero, memZ⟩, restZ⟩
  by_cases valid : 1 < Spec.Rsa.os2ip yb ∧ Spec.Rsa.os2ip yb < p.P - 1
  · refine WP.ite true (by change some (!z.z) = some true; rw [zero, flag, ite_eq_left valid]; rfl) ?_ (by intro hf; cases hf)
    intro _
    have frameZ : Frame [⟨State.addr p.base, 8 * p.len⟩] w.mem z.mem := by rw [memZ]; exact Frame.refl _ _
    have ptrZ := (restZ.gpr .r0 (by simp)).trans readyW.ptr
    have contextZ := contextW.after_workspace frameZ restZ ptrZ (fun d hd => (stableSlots_at stable hd).1)
    have readyZ := readyW.of_mem memZ restZ ptrZ
    refine WP.mono (domainTail_ok z contextZ stable h0 h24 h28 h32 h56 h60 readyZ
      (by rw [memZ]; exact modW) large odd (by rw [memZ]; exact r2W)) ?_
    rintro t ⟨result, frameT⟩
    refine ⟨?_, ?_⟩
    · rw [domainMainFlag, ite_eq_left valid]; exact result
    · rw [memZ] at frameT
      have frameT' : Frame (prepareAtWrites p s) w.mem t.mem := by
        simpa only [prepareAtWrites, prepareWrites, restZ.sp, restW.sp, restV.sp, restU.sp] using frameT
      exact frameW'.trans frameT'
  · refine WP.ite false (by change some (!z.z) = some false; rw [zero, flag, ite_eq_right valid]; rfl) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (ret_ok z 0 (by decide)) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    refine ⟨?_, ?_⟩
    · rw [domainMainFlag, ite_eq_right valid]; exact result
    · rw [memT, memZ]; exact frameW'

end VG.Proof.Ffdh.Arm
