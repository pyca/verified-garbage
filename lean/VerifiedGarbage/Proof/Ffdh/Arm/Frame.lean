module

public import VerifiedGarbage.Impl.Ffdh.Arm.Arithmetic
public import VerifiedGarbage.Proof.Bignum.Arm.PcPush
public import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! The FFDH wrapper reserves 72 bytes of locals inside RSA's AAPCS frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

def entered (s : State) : State := allocated 72 (pcPushed s)

/-- The two frames `framed` releases: the saved registers' and the locals'. -/
abbrev released (s : State) : List Region :=
  [⟨State.addr (pcPushed s).sp, 56⟩, ⟨State.addr (entered s).sp, 72⟩]

theorem framed_ok (body : Prog isa) (s : State) (stackFit : 128 ≤ s.sp.toNat)
    (written : List Region) (Q : Mem → BitVec 32 → Prop)
    (saved : ∀ (u : State), Frame written (entered s).mem u.mem →
      Spill.Saved u.mem (State.addr (pcPushed s).sp) s.gpr pcCalleeSaved)
    (body_ok : WP isa body (entered s) fun u => Frame written (entered s).mem u.mem ∧ Q u.mem (u.gpr .r0))
    (hQ : ∀ m₁ m₂ v, Frame (released s) m₁ m₂ → Q m₁ v → Q m₂ v := by intro _ _ _ _ h; exact h) :
    WP isa (VG.Impl.Ffdh.Arm.framed body) s fun t => abiPreserved s t ∧ Q t.mem (t.gpr .r0) := by
  have pushFit : 56 ≤ s.sp.toNat := by omega_using [stackFit]
  have allocFit : 72 ≤ (pcPushed s).sp.toNat := by
    change 72 ≤ (s.sp - BitVec.ofNat 32 56).toNat
    rw [FrameStack.sub_toNat' pushFit]
    omega_using [stackFit]
  obtain ⟨tr, u, run, frame, result⟩ := body_ok
  have perms := VG.Arm.Exec.rdwr run
  unfold VG.Impl.Ffdh.Arm.framed
  refine WP.frame (by decide) pushFit (by decide) ?_
  rw [WP.seq_iff]
  refine WP.alloc (by decide) allocFit ?_
  refine ⟨tr, u, run, ?_⟩
  intro m₁ u₁ hfl₁
  generalize ha : ({ freed 72 u with mem := m₁, unknowns := u₁ } : State) = a
  have spU : a.sp = (pcPushed s).sp := by
    rw [← ha]
    change u.sp + BitVec.ofNat 32 72 = _
    rw [perms.2.2]
    exact BitVec.sub_add_cancel _ _
  have wrU : a.wr = (pcPushed s).wr := by
    rw [← ha]
    change u.wr.tail = _
    rw [perms.2.1]
    rfl
  have fit : a.sp.toNat + 56 ≤ 2 ^ 32 := by
    rw [spU]
    change (s.sp - BitVec.ofNat 32 56).toNat + 56 ≤ 2 ^ 32
    rw [FrameStack.sub_toNat' pushFit]
    have := s.sp.isLt
    omega_using []
  have read : InRegions (a.rd ++ a.wr) (State.addr a.sp) 56 := by
    refine ⟨⟨State.addr a.sp, 56⟩, List.mem_append_right _ ?_, Region.contains_self _ _⟩
    rw [wrU, spU]
    exact List.mem_cons_self
  have savedU : Spill.Saved a.mem (State.addr a.sp) s.gpr pcCalleeSaved := by
    rw [spU, ← ha]
    refine (saved u frame).frame (lo := 0) (hi := 56) (by decide) hfl₁ fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    rw [FrameStack.addr_sub' allocFit]
    exact Offset.disjoint_below _ (by omega_using [])
  refine WP.mono (pc_restore_ok a s.gpr fit read savedU) ?_
  rintro t ⟨restored, memT, restT⟩ m₂ u₂ hfl₂
  have ret : t.gpr .r0 = u.gpr .r0 := by rw [restT.gpr .r0 (by simp [pcCalleeSaved]), ← ha]; rfl
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    have ne : r ≠ .r12 := by intro he; subst r; simp [preserved] at hr
    dsimp only
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
  · dsimp only
    rw [popped_sp, restT.sp, spU]
    exact BitVec.sub_add_cancel _ _
  · dsimp only
    rw [popped_gpr (by decide : Reg.r0 ≠ .r12), ret]
    rw [memT, ← ha] at hfl₂
    refine hQ u.mem m₂ _ ((hfl₁.mono fun r hr => ?_).trans (hfl₂.mono fun r hr => ?_)) result
    · simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ List.mem_cons_self
    · simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self

theorem framed_of_separate (body : Prog isa) (s : State) (stackFit : 128 ≤ s.sp.toNat)
    (written : List Region) (Q : Mem → BitVec 32 → Prop)
    (separate : ∀ r ∈ written, (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint r)
    (body_ok : WP isa body (entered s) fun u => Frame written (entered s).mem u.mem ∧ Q u.mem (u.gpr .r0))
    (hQ : ∀ m₁ m₂ v, Frame (released s) m₁ m₂ → Q m₁ v → Q m₂ v := by intro _ _ _ _ h; exact h) :
    WP isa (VG.Impl.Ffdh.Arm.framed body) s fun t => abiPreserved s t ∧ Q t.mem (t.gpr .r0) := by
  refine framed_ok body s stackFit written Q ?_ body_ok hQ
  intro u frame
  have initial := pc_push_callee_saved s (by omega_using [stackFit])
  apply initial.frame (lo := 0) (hi := 56) (by decide) frame
  intro r hr
  change (⟨State.addr (pcPushed s).sp + BitVec.ofNat 64 0, 56 - 0⟩ : Region).Disjoint r
  simpa only [BitVec.add_zero, Nat.sub_zero] using separate r hr

end VG.Proof.Ffdh.Arm
