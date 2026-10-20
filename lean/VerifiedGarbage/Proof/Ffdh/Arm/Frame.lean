module

public import VerifiedGarbage.Impl.Ffdh.Arm.Arithmetic
public import VerifiedGarbage.Proof.Bignum.Arm.PcPush
public import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.AddrArith

/-! The FFDH wrapper reserves 72 bytes of locals inside RSA's AAPCS frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

def entered (s : State) : State := allocated 72 (pcPushed s)

theorem framed_ok (body : Prog isa) (s : State) (stackFit : 128 ≤ s.sp.toNat)
    (written : List Region) (Q : Mem → BitVec 32 → Prop)
    (saved : ∀ (u : State), Frame written (entered s).mem u.mem →
      Spill.Saved u.mem (State.addr (pcPushed s).sp) s.gpr pcCalleeSaved)
    (body_ok : WP isa body (entered s) fun u => Frame written (entered s).mem u.mem ∧ Q u.mem (u.gpr .r0)) :
    WP isa (VG.Impl.Ffdh.Arm.framed body) s fun t => abiPreserved s t ∧ Q t.mem (t.gpr .r0) := by
  have pushFit : 56 ≤ s.sp.toNat := by omega
  have allocFit : 72 ≤ (pcPushed s).sp.toNat := by
    change 72 ≤ (s.sp - BitVec.ofNat 32 56).toNat
    rw [FrameStack.sub_toNat' pushFit]
    omega
  obtain ⟨tr, u, run, frame, result⟩ := body_ok
  have perms := VG.Arm.Exec.rdwr run
  unfold VG.Impl.Ffdh.Arm.framed
  refine WP.frame (by decide) pushFit (by decide) ?_
  rw [WP.seq_iff]
  refine WP.alloc (by decide) allocFit ?_
  refine ⟨tr, u, run, ?_⟩
  have spU : (freed 72 u).sp = (pcPushed s).sp := by
    change u.sp + BitVec.ofNat 32 72 = _
    rw [perms.2.2]
    exact BitVec.sub_add_cancel _ _
  have wrU : (freed 72 u).wr = (pcPushed s).wr := by
    change u.wr.tail = _
    rw [perms.2.1]
    rfl
  have fit : (freed 72 u).sp.toNat + 56 ≤ 2 ^ 32 := by
    rw [spU]
    change (s.sp - BitVec.ofNat 32 56).toNat + 56 ≤ 2 ^ 32
    rw [FrameStack.sub_toNat' pushFit]
    have := s.sp.isLt
    omega
  have read : InRegions ((freed 72 u).rd ++ (freed 72 u).wr) (State.addr (freed 72 u).sp) 56 := by
    refine ⟨⟨State.addr (freed 72 u).sp, 56⟩, List.mem_append_right _ ?_, Region.contains_self _ _⟩
    rw [wrU, spU]
    exact List.mem_cons_self
  have savedU : Spill.Saved (freed 72 u).mem (State.addr (freed 72 u).sp) s.gpr pcCalleeSaved := by
    rw [spU]
    exact saved u frame
  refine WP.mono (pc_restore_ok (freed 72 u) s.gpr fit read savedU) ?_
  rintro t ⟨restored, memT, restT⟩
  have ret : t.gpr .r0 = u.gpr .r0 := restT.gpr .r0 (by simp [pcCalleeSaved])
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    have ne : r ≠ .r12 := by intro he; subst r; simp [preserved] at hr
    rw [popped_gpr ne]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact restored (.r4, 16) (by simp [pcCalleeSaved])
    · exact restored (.r5, 20) (by simp [pcCalleeSaved])
    · exact restored (.r6, 24) (by simp [pcCalleeSaved])
    · exact restored (.r7, 28) (by simp [pcCalleeSaved])
    · exact restored (.r8, 32) (by simp [pcCalleeSaved])
    · exact restored (.r9, 36) (by simp [pcCalleeSaved])
    · exact restored (.r10, 40) (by simp [pcCalleeSaved])
    · exact restored (.r11, 44) (by simp [pcCalleeSaved])
    · exact restored (.lr, 52) (by simp [pcCalleeSaved])
  · rw [popped_sp, restT.sp, spU]
    exact BitVec.sub_add_cancel _ _
  · simp only [popped_gpr (by decide : Reg.r0 ≠ .r12), popped_mem, memT, ret]
    exact result

theorem framed_of_separate (body : Prog isa) (s : State) (stackFit : 128 ≤ s.sp.toNat)
    (written : List Region) (Q : Mem → BitVec 32 → Prop)
    (separate : ∀ r ∈ written, (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint r)
    (body_ok : WP isa body (entered s) fun u => Frame written (entered s).mem u.mem ∧ Q u.mem (u.gpr .r0)) :
    WP isa (VG.Impl.Ffdh.Arm.framed body) s fun t => abiPreserved s t ∧ Q t.mem (t.gpr .r0) := by
  refine framed_ok body s stackFit written Q ?_ body_ok
  intro u frame
  have initial := pc_push_callee_saved s (by omega)
  apply initial.frame (lo := 0) (hi := 56) (by decide) frame
  intro r hr
  change (⟨State.addr (pcPushed s).sp + BitVec.ofNat 64 0, 56 - 0⟩ : Region).Disjoint r
  simpa only [BitVec.add_zero, Nat.sub_zero] using separate r hr

end VG.Proof.Ffdh.Arm
