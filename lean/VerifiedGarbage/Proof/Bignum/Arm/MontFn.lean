module

public import VerifiedGarbage.Proof.Bignum.Arm.Entry
import VerifiedGarbage.Proof.Bignum.Arm.MontFnBody
import VerifiedGarbage.Proof.Bignum.Arm.Restore
import VerifiedGarbage.Proof.Framework.Block

/-! # Callable Montgomery multiplication preserves the ARM procedure-call ABI -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (arrAt wOf numAt Operand Keeps)

theorem montFn_ok (s : State) {base : BitVec 32} {len w o a b : Nat}
    (h : FnInput base len w o a b s) (ho : Operand o) (ha : Operand a) (hb : Operand b) :
    WP isa MontFn.mul s fun t => abiPreserved s t ∧
      numAt t.mem (State.addr base) w o < numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o * 2 ^ (64 * w) % numAt s.mem (State.addr base) w 0 =
        numAt s.mem (State.addr base) w a * numAt s.mem (State.addr base) w b % numAt s.mem (State.addr base) w 0 ∧
      Keeps (State.addr base) len w o s.mem t.mem := by
  have nowrap := h.workspace.nowrap
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have eq := h.pushed_eq
  have framePush := FrameStack.pushed_frameA (rs := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]) h.stackFit
  unfold MontFn.mul
  refine WP.frame (by decide) h.stackFit (by decide) ?_
  rw [WP.seq_iff]
  refine WP.mono (mont_entry_ok s h hb.1) ?_
  rintro u ⟨ready, memU, restU⟩
  rw [WP.seq_iff]
  have body := montFnBody_ok u ready.workspace ready.layout ho ha hb ready.ptr ready.outIndex ready.aIndex ready.bIndex
    (by rw [ready.width]; exact ready.inverse) (by rw [ready.width]; exact ready.operand)
  simp only [ready.width] at body
  refine WP.mono body ?_
  rintro v ⟨lt, value, keeps, frameBody, restV⟩
  have spV : v.sp = s.sp - BitVec.ofNat 32 36 := restV.sp.trans restU.sp
  have wrV : v.wr = (montPushed s).wr := restV.wr.trans restU.wr
  rw [memU] at lt value keeps frameBody
  have saved : Spill.Saved v.mem (State.addr v.sp) s.gpr montSaved := by
    rw [spV]
    have savedPush : Spill.Saved (montPushed s).mem (State.addr (s.sp - BitVec.ofNat 32 36)) s.gpr montSaved :=
      mont_push_saved s h.stackFit
    exact savedPush.frame (lo := 0) (hi := 36) (by decide) frameBody (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      simpa only [FrameStack.belowA, BitVec.add_zero, Nat.sub_zero] using h.stackWorkspace)
  have stackFit : v.sp.toNat + 36 ≤ 2 ^ 32 := by
    rw [spV, FrameStack.sub_toNat' h.stackFit]
    have := s.sp.isLt
    omega
  have writable : (⟨State.addr v.sp, 36⟩ : Region) ∈ v.wr := by
    rw [wrV, spV]
    exact List.mem_cons_self
  refine WP.mono (mont_restore_ok v s.gpr stackFit writable saved) ?_
  rintro t ⟨restored, memT, restT⟩
  have spT : t.sp = s.sp - BitVec.ofNat 32 36 := restT.sp.trans spV
  have saved4 : t.mem.readW (State.addr t.sp) 32 = s.gpr .r4 := by
    rw [memT, restT.sp]
    simpa only [BitVec.add_zero] using saved (.r4, 0) (by simp [montSaved])
  have oldM := eq.number fits (by decide : 0 < 8)
  have oldA := eq.number fits ha.1
  have oldB := eq.number fits hb.1
  rw [oldM] at lt
  rw [oldM, oldA, oldB] at value
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro r hr
    by_cases he : r = .r4
    · subst r
      change (t.setReg .r4 (t.mem.readW (State.addr t.sp) 32)).gpr .r4 = _
      simpa only [State.setReg, ite_true] using saved4
    · rw [popped_gpr he]
      apply restored
      simpa only [preserved, List.mem_cons, he, false_or] using hr
  · rw [popped_sp, spT]
    exact BitVec.sub_add_cancel _ _
  · rw [popped_mem, memT]; exact lt
  · rw [popped_mem, memT]; exact value
  · intro i hi separate
    rw [popped_mem, memT, keeps i hi separate]
    exact framePush.bytes (R := ⟨State.addr base, 8 * len⟩)
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.stackWorkspace.symm)
      (by change 8 * len ≤ 2 ^ 64; omega) hi

end VG.Proof.Bignum.Arm
