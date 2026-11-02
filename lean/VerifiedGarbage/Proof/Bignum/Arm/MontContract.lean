module

public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Bignum.Arm.Entry

import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Impl.Bignum.Arm.MontFn
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Arm.MontFnBody
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
/-! # The shared RSA Montgomery contract under AAPCS -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/Restore.lean`, which only this module imported.
section

/-! # Restore the saved registers before the frame pops its first word -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem mont_restore_ok (s : State) (g : Reg → BitVec 32)
    (fit : s.sp.toNat + 36 ≤ 2 ^ 32) (frame : (⟨State.addr s.sp, 36⟩ : Region) ∈ s.wr)
    (saved : Spill.Saved s.mem (State.addr s.sp) g montSaved) :
    WP isa (.block MontFn.restore) s fun t =>
      (∀ r ∈ [.r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr], t.gpr r = g r) ∧
      t.mem = s.mem ∧ Rest roundClobbers s t := by
  have read (t : State) (wr : t.wr = s.wr) (d : Nat) (hd : d + 4 ≤ 36) :
      InRegions (t.rd ++ t.wr) (off (State.addr s.sp) d) 4 := by
    refine ⟨⟨State.addr s.sp, 36⟩, List.mem_append_right _ ?_, Offset.contains_base _ hd (by omega)⟩
    rw [wr]; exact frame
  unfold MontFn.restore
  refine wp_loadStack (a := off (State.addr s.sp) 4) (by decide) ?_ (read s rfl 4 (by decide)) fun s1 u1 => ?_
  · exact addr_add (by omega)
  have sp1 := u1.sp
  have wr1 := u1.wr
  refine wp_loadStack (a := off (State.addr s.sp) 8) (by decide) ?_ (read s1 wr1 8 (by decide)) fun s2 u2 => ?_
  · rw [sp1]; exact addr_add (by omega)
  have sp2 := u2.sp.trans sp1
  have wr2 := u2.wr.trans wr1
  refine wp_loadStack (a := off (State.addr s.sp) 12) (by decide) ?_ (read s2 wr2 12 (by decide)) fun s3 u3 => ?_
  · rw [sp2]; exact addr_add (by omega)
  have sp3 := u3.sp.trans sp2
  have wr3 := u3.wr.trans wr2
  refine wp_loadStack (a := off (State.addr s.sp) 16) (by decide) ?_ (read s3 wr3 16 (by decide)) fun s4 u4 => ?_
  · rw [sp3]; exact addr_add (by omega)
  have sp4 := u4.sp.trans sp3
  have wr4 := u4.wr.trans wr3
  refine wp_loadStack (a := off (State.addr s.sp) 20) (by decide) ?_ (read s4 wr4 20 (by decide)) fun s5 u5 => ?_
  · rw [sp4]; exact addr_add (by omega)
  have sp5 := u5.sp.trans sp4
  have wr5 := u5.wr.trans wr4
  refine wp_loadStack (a := off (State.addr s.sp) 24) (by decide) ?_ (read s5 wr5 24 (by decide)) fun s6 u6 => ?_
  · rw [sp5]; exact addr_add (by omega)
  have sp6 := u6.sp.trans sp5
  have wr6 := u6.wr.trans wr5
  refine wp_loadStack (a := off (State.addr s.sp) 28) (by decide) ?_ (read s6 wr6 28 (by decide)) fun s7 u7 => ?_
  · rw [sp6]; exact addr_add (by omega)
  have sp7 := u7.sp.trans sp6
  have wr7 := u7.wr.trans wr6
  refine wp_loadStack (a := off (State.addr s.sp) 32) (by decide) ?_ (read s7 wr7 32 (by decide)) fun s8 u8 => WP.block_nil ?_
  · rw [sp7]; exact addr_add (by omega)
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u8.other .r5 (by decide), u7.other .r5 (by decide), u6.other .r5 (by decide), u5.other .r5 (by decide), u4.other .r5 (by decide), u3.other .r5 (by decide), u2.other .r5 (by decide), u1.gpr]
      exact saved (.r5, 4) (by decide)
    · rw [u8.other .r6 (by decide), u7.other .r6 (by decide), u6.other .r6 (by decide), u5.other .r6 (by decide), u4.other .r6 (by decide), u3.other .r6 (by decide), u2.gpr, u1.mem]
      exact saved (.r6, 8) (by decide)
    · rw [u8.other .r7 (by decide), u7.other .r7 (by decide), u6.other .r7 (by decide), u5.other .r7 (by decide), u4.other .r7 (by decide), u3.gpr, u2.mem, u1.mem]
      exact saved (.r7, 12) (by decide)
    · rw [u8.other .r8 (by decide), u7.other .r8 (by decide), u6.other .r8 (by decide), u5.other .r8 (by decide), u4.gpr, u3.mem, u2.mem, u1.mem]
      exact saved (.r8, 16) (by decide)
    · rw [u8.other .r9 (by decide), u7.other .r9 (by decide), u6.other .r9 (by decide), u5.gpr, u4.mem, u3.mem, u2.mem, u1.mem]
      exact saved (.r9, 20) (by decide)
    · rw [u8.other .r10 (by decide), u7.other .r10 (by decide), u6.gpr, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
      exact saved (.r10, 24) (by decide)
    · rw [u8.other .r11 (by decide), u7.gpr, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
      exact saved (.r11, 28) (by decide)
    · rw [u8.gpr, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
      exact saved (.lr, 32) (by decide)
  · rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans ((u7.rest (by decide)).trans ((u8.rest (by decide)))))))))

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/MontFn.lean`, which only this module imported.
section

/-! # Callable Montgomery multiplication preserves the ARM procedure-call ABI -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wOf numAt Operand Keeps)

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
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/MontFnCT.lean`, which only this module imported.
section

/-! # The complete callable Montgomery function is constant time -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt Operand)

theorem montFn_ct {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b) :
    RelCT isa (fun s t => FnInput base len w o a b s ∧ FnInput base len w o a b t ∧ s.sp = t.sp)
      MontFn.mul (fun _ _ => True) := by
  unfold MontFn.mul
  apply RelCT.frame (fun _ _ h => h.2.2)
  intro s t tr1 tr2 u v hp e1 e2
  obtain ⟨s0, t0, ⟨hs, ht, sp⟩, ps, pt⟩ := hp
  have ps' := push_pushed (rs := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]) (by decide) hs.stackFit
  have pt' := push_pushed (rs := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]) (by decide) ht.stackFit
  have es : montPushed s0 = s := Option.some.inj (ps'.symm.trans ps)
  have et : montPushed t0 = t := Option.some.inj (pt'.symm.trans pt)
  subst s; subst t
  cases e1 with
  | seq entry1 tail1 =>
    cases e2 with
    | seq entry2 tail2 =>
      obtain ⟨trace, sp'⟩ := loadStack_ct .r12 36 _ _ _ _ _ _ (by simp only [montPushed, pushed_sp, sp]) entry1 entry2
      obtain ⟨_, s1, run1, ready1, _, _⟩ := mont_entry_ok s0 hs hb.1
      obtain ⟨_, t1, run2, ready2, _, _⟩ := mont_entry_ok t0 ht hb.1
      obtain ⟨-, rfl⟩ := Exec.det entry1 run1
      obtain ⟨-, rfl⟩ := Exec.det entry2 run2
      have hw : 2 ≤ w := hs.width ▸ hs.layout.1
      have fit : arrAt w 8 ≤ 8 * len := hs.width ▸ hs.layout.2.2.1
      have tmpFits : arrAt w 3 + 32 ≤ 8 * len := by
        have := array_end_le (w := w) (j := 3) (k := 8) (by decide)
        omega
      have body := relCT_keep_sp
        ((montFnBody_ct ho ha hb tmpFits).mono
          (P' := fun (s t : State) => FnBodyReady base len w o a b s ∧ FnBodyReady base len w o a b t ∧ s.sp = t.sp)
          (fun _ _ h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)) (fun _ _ h => h.2.2)
      obtain ⟨tailTrace, _⟩ := body.seq montRestore_ct _ _ _ _ _ _ ⟨ready1, ready2, sp'⟩ tail1 tail2
      exact ⟨by rw [trace, tailTrace], trivial⟩

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (wOf Operand)

abbrev stackB (s : State) : BitVec 32 := s.mem.readW (State.addr s.sp) 32

theorem mont_contract_pre (s : State) (h : (Proof.Rsa.Mont.mulContract abi 36).pre s) :
    FnInput (s.gpr .r0) (s.gpr .r1).toNat (wOf s.mem (State.addr (s.gpr .r0)))
      (s.gpr .r2).toNat (s.gpr .r3).toNat (stackB s).toNat s ∧
      Operand (s.gpr .r2).toNat ∧ Operand (s.gpr .r3).toNat ∧ Operand (stackB s).toNat := by
  sig_pre [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
  have argAddr : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  have argValue : stackArg s 0 = stackB s := by simp [stackArg, argAddr]
  rw [argAddr, argValue] at h
  obtain ⟨stackFit, _, rd, wr, _, stackWs, stackArgSep, nowrap, layout, ho, ha, hb, inverse, operand⟩ := h
  refine ⟨⟨⟨?_, ?_⟩, layout, rfl, rfl, ?_, ?_, ?_, inverse, operand, stackFit, ?_, ?_, ?_⟩, ho, ha, hb⟩
  · simpa only [Nat.mul_comm] using nowrap
  · rw [wr]; simp only [List.mem_singleton, State.addr, Nat.mul_comm]
  · simp
  · simp
  · simp
  · refine ⟨⟨State.addr s.sp, 4⟩, List.mem_append_left _ ?_, ?_⟩
    · rw [rd]; simp
    · simp [Region.Contains]
  · unfold FrameStack.belowA
    rw [FrameStack.addr_sub' stackFit]
    simpa only [State.addr, Nat.mul_comm] using stackWs
  · unfold FrameStack.belowA
    rw [FrameStack.addr_sub' stackFit]
    exact stackArgSep


theorem mont_contract_correct (s : State) (h : (Proof.Rsa.Mont.mulContract abi 36).pre s) :
    ∃ tr t, Exec isa MontFn.mul s tr t ∧ abiPreserved s t ∧
      (Proof.Rsa.Mont.mulContract abi 36).post s t := by
  obtain ⟨input, ho, ha, hb⟩ := mont_contract_pre s h
  obtain ⟨tr, t, run, preserved, post⟩ := montFn_ok s input ho ha hb
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  have argValue : stackArg s 0 = stackB s := by simp [stackArg, stackArgAddr, stackB]
  rw [argValue]
  exact post

theorem mont_contract_ct : ConstantTime isa (Proof.Rsa.Mont.mulContract abi 36).pre
    (Proof.Rsa.Mont.mulContract abi 36).pub MontFn.mul := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨is, ho, ha, hb⟩ := mont_contract_pre s hs
  obtain ⟨it, _, _, _⟩ := mont_contract_pre t ht
  sig_pub [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, width, p0, p1, p2, p3, pb⟩ := hp
  change [wOf s.mem (State.addr (s.gpr .r0))] = [wOf t.mem (State.addr (t.gpr .r0))] at width
  have wb := List.singleton_inj.mp width
  have bb : stackB s = stackB t := by simpa only [stackArg, stackArgAddr, Nat.mul_zero, BitVec.add_zero, stackB] using pb
  rw [← wb, ← p0, ← p1, ← p2, ← p3, ← bb] at it
  exact (montFn_ct ho ha hb s t tr1 tr2 u v ⟨is, it, sp⟩ e1 e2).1

end VG.Proof.Bignum.Arm
