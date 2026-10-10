import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc2.Contract
import VerifiedGarbage.Proof.Rc2.Arm.Cbc.StepCT
import VerifiedGarbage.Proof.Rc2.Arm.KeyIO
import VerifiedGarbage.Proof.Rc2.Arm.Cbc.Body

section

section

/-! # Frames for successive CBC blocks -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm

def loopWrites (s : State) (n : Nat) : List Region := [ivR s, dataR s n, ⟨State.addr (s.gpr .r2), 264⟩]

theorem loopFrame_slice {s s' : State} {n m i : Nat} {a b : Mem}
    (h : Frame (loopWrites s' m) a b) (bound : i + m ≤ n)
    (iv : s'.gpr .r4 = s.gpr .r4) (buf : s'.gpr .r2 = s.gpr .r2)
    (ptr : State.addr (s'.gpr .r1) = State.addr (s.gpr .r1) + BitVec.ofNat 64 (8 * i)) :
    Frame (loopWrites s n) a b := by
  apply h.sub
  intro r hr
  simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · refine ⟨ivR s, by simp [loopWrites], ?_⟩
    change Region.Sub ⟨State.addr (s'.gpr .r4), 8⟩ ⟨State.addr (s.gpr .r4), 8⟩
    rw [iv]; exact fun _ h => h
  · refine ⟨dataR s n, by simp [loopWrites], ?_⟩
    change Region.Sub ⟨State.addr (s'.gpr .r1), 8 * m⟩ ⟨State.addr (s.gpr .r1), 8 * n⟩
    rw [ptr]
    exact Offset.sub_base _ (by omega_arith)
  · refine ⟨⟨State.addr (s.gpr .r2), 264⟩, by simp [loopWrites], ?_⟩
    rw [buf]; exact fun _ h => h

theorem BodyPost.frame {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s n s') (hn : 1 ≤ n) : Frame (loopWrites s n) s.mem s'.mem :=
  loopFrame_slice (m := 1) (i := 0) h.mem hn rfl rfl (by simp)

theorem BodyPost.schedule {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s n s') (hp : StepPre s) :
    Spec.Rc2.scheduleAt s'.mem (State.addr (s.gpr .r0)) = Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0)) := by
  apply scheduleAt_frame h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.keyIv (And.intro hp.keyData
      (hp.keyBuf.sub_right (Region.sub_prefix (by decide : 264 ≤ 512))))

theorem BodyPost.tailData {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64) :
    Spec.Rc2.blocksAt s'.mem (State.addr (s.gpr .r1) + 8) n = Spec.Rc2.blocksAt s.mem (State.addr (s.gpr .r1) + 8) n := by
  have sub : Region.Sub ⟨State.addr (s.gpr .r1) + 8, 8 * n⟩ (dataR s (n + 1)) :=
    Offset.sub_base _ (by change 8 + 8 * n ≤ 8 * (n + 1); omega_arith)
  have sep : (Region.mk (State.addr (s.gpr .r1) + 8) (8 * n)).Disjoint (dataR s) :=
    Offset.disjoint_base _ (d := 8) (n := 8 * n) (k := 8) (by decide) (by omega_arith)
  apply blocksAt_frame h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.ivData.sub_right sub).symm) (And.intro sep
      ((hp.dataBuf.sub_left sub).sub_right (Region.sub_prefix (by decide : 264 ≤ 512))))

theorem firstBlock_frame {d : Spec.Rc2.Direction} {s s' : State} {n : Nat} {m : Mem}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64)
    (hn : 1 ≤ n)
    (frame : Frame (loopWrites s' n) s'.mem m) :
    Spec.Rc2.blockAt m (State.addr (s.gpr .r1)) = Spec.Rc2.blockAt s'.mem (State.addr (s.gpr .r1)) := by
  have first : Region.Sub (dataR s) (dataR s (n + 1)) := Region.sub_prefix (by change 8 ≤ 8 * (n + 1); omega_arith)
  have sep : (dataR s).Disjoint ⟨State.addr (s.gpr .r1) + 8, 8 * n⟩ :=
    Offset.base_disjoint _ (e := 8) (n := 8 * n) (k := 8) (by decide) (by omega_arith)
  have ptr : State.addr (s'.gpr .r1) = State.addr (s.gpr .r1) + 8 := by
    rw [h.ptr]
    exact addr_add (k := 8) (by have := hp.dataFit; omega_arith)
  apply blockAt_frame frame
  have iv := h.reg .r4 (by decide) (by decide) (by decide)
  have buf := h.reg .r2 (by decide) (by decide) (by decide)
  simpa only [loopWrites, ivR, dataR, iv, buf, ptr,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.ivData.sub_right first).symm) (And.intro sep
      ((hp.dataBuf.sub_left first).sub_right (Region.sub_prefix (by decide : 264 ≤ 512))))

end VG.Proof.Rc2.Arm.Cbc

end

/-! # Correctness of the CBC loop on complete blocks -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm

structure LoopPost (d : Spec.Rc2.Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .r1 = s.gpr .r1 + BitVec.ofNat 32 (8 * n)
  count : s'.gpr .r5 = 0
  reg : ∀ r ∈ kept, r ≠ .r1 → r ≠ .r5 → s'.gpr r = s.gpr r
  callee : ∀ r ∈ savedAcrossCall, r ≠ .r5 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (loopWrites s n) s.mem s'.mem
  data : Spec.Rc2.blocksAt s'.mem (State.addr (s.gpr .r1)) n =
    (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) d
      (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r4))) (Spec.Rc2.blocksAt s.mem (State.addr (s.gpr .r1)) n)).1
  iv : Spec.Rc2.blockAt s'.mem (State.addr (s.gpr .r4)) =
    (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) d
      (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r4))) (Spec.Rc2.blocksAt s.mem (State.addr (s.gpr .r1)) n)).2

theorem loop_ok (d : Spec.Rc2.Direction) (n : Nat) :
    ∀ s : State, 1 ≤ n → 8 * n ≤ 2 ^ 32 → StepPre s n → s.gpr .r5 = BitVec.ofNat 32 n →
      WP isa (.loop (Impl.Rc2.Arm.Cbc.body d) .ne) s (LoopPost d s n) := by
  induction n with
  | zero => intro s hn; omega_arith
  | succ n ih =>
    intro s hn bound hp count
    obtain ⟨t₁, s₁, exec₁, h₁⟩ := body_ok d s (n + 1) hn (by omega_arith) count (hp.head hn)
    by_cases hz : n = 0
    · subst n
      refine ⟨_, s₁, Exec.loopExit exec₁ ?_, ?_⟩
      · simp only [eval_nonzeroCount, h₁.flag, decide_true, Option.map_some, Bool.not_true]
      · refine ⟨h₁.ptr, h₁.count, h₁.reg, h₁.callee, h₁.rd, h₁.wr, h₁.frame (by decide), ?_, ?_⟩
        · rw [blocksAt_cons, blocksAt_cons]
          simp only [Spec.Rc2.blocksAt, List.range_zero, List.map_nil, Spec.Rc2.cbc]
          exact congrArg (· :: []) h₁.data
        · rw [blocksAt_cons]
          simp only [Spec.Rc2.blocksAt, List.range_zero, List.map_nil, Spec.Rc2.cbc]
          exact h₁.iv
    · have hp₁ := h₁.tail hp (by omega_arith)
      obtain ⟨t₂, s₂, exec₂, h₂⟩ := ih s₁ (by omega_arith) (by omega_arith) hp₁ (by simpa using h₁.count)
      refine ⟨_, s₂, Exec.loopNext exec₁ ?_ exec₂, ?_⟩
      · have he : n + 1 ≠ 1 := by omega_arith
        simp only [eval_nonzeroCount, h₁.flag, he, decide_false, Option.map_some, Bool.not_false]
      · have key := h₁.schedule (hp.head hn)
        have tail := h₁.tailData hp (by omega_arith)
        have data := h₂.data
        have iv := h₂.iv
        have ki := h₁.reg .r0 (by decide) (by decide) (by decide)
        have vi := h₁.reg .r4 (by decide) (by decide) (by decide)
        have bi := h₁.reg .r2 (by decide) (by decide) (by decide)
        have ptr : State.addr (s₁.gpr .r1) = State.addr (s.gpr .r1) + 8 := by
          rw [h₁.ptr]; exact addr_add (k := 8) (by have := hp.dataFit; omega_arith)
        rw [ki, vi, ptr, key, tail, h₁.iv] at data
        rw [ki, vi, ptr, key, tail, h₁.iv] at iv
        refine ⟨?_, h₂.count, ?_, ?_, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, ?_, ?_, ?_⟩
        · rw [h₂.ptr, h₁.ptr, BitVec.add_assoc]
          exact congrArg (s.gpr .r1 + ·) (by
            change BitVec.ofNat 32 8 + BitVec.ofNat 32 (8 * n) = _
            rw [← BitVec.ofNat_add]
            exact congrArg (BitVec.ofNat 32) (by omega_arith))
        · intro r hr hs hb
          exact (h₂.reg r hr hs hb).trans (h₁.reg r hr hs hb)
        · intro r hr hb
          exact (h₂.callee r hr hb).trans (h₁.callee r hr hb)
        · exact (h₁.frame hn).trans (loopFrame_slice (i := 1) h₂.mem (by omega_arith) vi bi ptr)
        · have first := firstBlock_frame h₁ hp (by omega_arith) (by omega_arith) h₂.mem
          rw [blocksAt_cons, first, h₁.data, data, blocksAt_cons]
          rfl
        · rw [blocksAt_cons]
          exact iv

theorem maybeLoop_ok (d : Spec.Rc2.Direction) (s : State) (n : Nat) (bound : 8 * n ≤ 2 ^ 32)
    (hp : StepPre s n) (count : s.gpr .r5 = BitVec.ofNat 32 n)
    (flag : zeroCount s = some (s.gpr .r5 == 0)) :
    WP isa (.ite .eq (.block []) (.loop (Impl.Rc2.Arm.Cbc.body d) .ne)) s (LoopPost d s n) := by
  have eqZero := counter_eq n 0 (by omega_arith) (by decide)
  simp only [BitVec.sub_zero] at eqZero
  have flag' : zeroCount s = some (decide (n = 0)) := by
    rw [flag, count]
    exact congrArg some eqZero
  by_cases hz : n = 0
  · subst n
    apply WP.ite true (by simp only [eval_zeroCount, flag', decide_true])
    · intro _
      apply WP.block_nil
      refine ⟨by simp, count, fun _ _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, Frame.refl _ _, ?_, ?_⟩
      · rfl
      · rfl
    · simp
  · apply WP.ite false (by simp only [eval_zeroCount, flag', hz, decide_false])
    · simp
    · intro _
      exact loop_ok d n s (by omega_arith) bound hp count

theorem LoopPost.scratchRead {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : LoopPost d s n s') (hp : StepPre s n) (i : Nat) (lo : 264 ≤ i) (hi : i + 4 ≤ 512) :
    s'.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 i) 32 = s.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 i) 32 := by
  have sub : Region.Sub ⟨State.addr (s.gpr .r2) + BitVec.ofNat 64 i, 4⟩ (bufR s) := Offset.sub_base _ hi
  have sep : (Region.mk (State.addr (s.gpr .r2) + BitVec.ofNat 64 i) 4).Disjoint ⟨State.addr (s.gpr .r2), 264⟩ :=
    Offset.disjoint_base _ lo (by omega_arith)
  apply h.mem.readW (r := ⟨State.addr (s.gpr .r2) + BitVec.ofNat 64 i, 4⟩) (Region.contains_self _ _)
    (hn := by decide)
  simpa only [loopWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.ivBuf.sub_right sub).symm) (And.intro ((hp.dataBuf.sub_right sub).symm)
      sep)

end VG.Proof.Rc2.Arm.Cbc

end

section

/-! # CBC register saves, setup, and restoration -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm

def callerSaved : List Reg := [.r4, .r5, .r6, .r7, .lr]

def savedMem (s : State) : Mem :=
  (((((s.mem.writeW (State.addr (s.gpr .r12) + BitVec.ofNat 64 264) (s.gpr .r4)).writeW (State.addr (s.gpr .r12) + BitVec.ofNat 64 268) (s.gpr .r5)).writeW (State.addr (s.gpr .r12) + BitVec.ofNat 64 272) (s.gpr .r6)).writeW (State.addr (s.gpr .r12) + BitVec.ofNat 64 276) (s.gpr .r7)).writeW (State.addr (s.gpr .r12) + BitVec.ofNat 64 280) (s.gpr .lr))

theorem save_ok (s : State)
    (fit : (s.gpr .r12).toNat + 512 ≤ 2 ^ 32)
    (w0 : InRegions s.wr (State.addr (s.gpr .r12) + BitVec.ofNat 64 264) 4)
    (w1 : InRegions s.wr (State.addr (s.gpr .r12) + BitVec.ofNat 64 268) 4)
    (w2 : InRegions s.wr (State.addr (s.gpr .r12) + BitVec.ofNat 64 272) 4)
    (w3 : InRegions s.wr (State.addr (s.gpr .r12) + BitVec.ofNat 64 276) 4)
    (w4 : InRegions s.wr (State.addr (s.gpr .r12) + BitVec.ofNat 64 280) 4)
    : ∃ s', runBlock isa Impl.Rc2.Arm.Cbc.save s = some s' ∧ Keep [] {s with mem := savedMem s} s' := by
  have a264 : State.addr (s.gpr .r12 + BitVec.ofNat 32 264) = State.addr (s.gpr .r12) + BitVec.ofNat 64 264 := addr_add (by omega_arith)
  have a268 : State.addr (s.gpr .r12 + BitVec.ofNat 32 268) = State.addr (s.gpr .r12) + BitVec.ofNat 64 268 := addr_add (by omega_arith)
  have a272 : State.addr (s.gpr .r12 + BitVec.ofNat 32 272) = State.addr (s.gpr .r12) + BitVec.ofNat 64 272 := addr_add (by omega_arith)
  have a276 : State.addr (s.gpr .r12 + BitVec.ofNat 32 276) = State.addr (s.gpr .r12) + BitVec.ofNat 64 276 := addr_add (by omega_arith)
  have a280 : State.addr (s.gpr .r12 + BitVec.ofNat 32 280) = State.addr (s.gpr .r12) + BitVec.ofNat 64 280 := addr_add (by omega_arith)
  refine ⟨_, by
    simp only [Impl.Rc2.Arm.Cbc.save, runBlock_cons, runStep_some, runBlock_nil,
      exec, Nat.reduceLT, ite_true, State.store32,
      a264, a268, a272, a276, a280, w0, w1, w2, w3, w4]
    rfl, ?_⟩
  exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem savedMem_frame (s : State) : Frame [⟨State.addr (s.gpr .r12), 512⟩] s.mem (savedMem s) := by
  unfold savedMem
  apply Frame.writeW (r := ⟨State.addr (s.gpr .r12), 512⟩) (hr := List.mem_cons_self) (hb := Offset.contains_base _ (by decide : 280 + 4 ≤ 512) (by decide))
  apply Frame.writeW (r := ⟨State.addr (s.gpr .r12), 512⟩) (hr := List.mem_cons_self) (hb := Offset.contains_base _ (by decide : 276 + 4 ≤ 512) (by decide))
  apply Frame.writeW (r := ⟨State.addr (s.gpr .r12), 512⟩) (hr := List.mem_cons_self) (hb := Offset.contains_base _ (by decide : 272 + 4 ≤ 512) (by decide))
  apply Frame.writeW (r := ⟨State.addr (s.gpr .r12), 512⟩) (hr := List.mem_cons_self) (hb := Offset.contains_base _ (by decide : 268 + 4 ≤ 512) (by decide))
  apply Frame.writeW (r := ⟨State.addr (s.gpr .r12), 512⟩) (hr := List.mem_cons_self) (hb := Offset.contains_base _ (by decide : 264 + 4 ≤ 512) (by decide))
  exact Frame.refl _ _

theorem savedMem_r4 (s : State) : (savedMem s).readW (State.addr (s.gpr .r12) + BitVec.ofNat 64 264) 32 = s.gpr .r4 := by
  rw [savedMem, Mem.readW_writeW_sep (Offset.sep _ (by decide : 264 + 4 ≤ 280 ∨ 280 + 4 ≤ 264) (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 264 + 4 ≤ 276 ∨ 276 + 4 ≤ 264) (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 264 + 4 ≤ 272 ∨ 272 + 4 ≤ 264) (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 264 + 4 ≤ 268 ∨ 268 + 4 ≤ 264) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]

theorem savedMem_r5 (s : State) : (savedMem s).readW (State.addr (s.gpr .r12) + BitVec.ofNat 64 268) 32 = s.gpr .r5 := by
  rw [savedMem, Mem.readW_writeW_sep (Offset.sep _ (by decide : 268 + 4 ≤ 280 ∨ 280 + 4 ≤ 268) (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 268 + 4 ≤ 276 ∨ 276 + 4 ≤ 268) (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 268 + 4 ≤ 272 ∨ 272 + 4 ≤ 268) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]

theorem savedMem_r6 (s : State) : (savedMem s).readW (State.addr (s.gpr .r12) + BitVec.ofNat 64 272) 32 = s.gpr .r6 := by
  rw [savedMem, Mem.readW_writeW_sep (Offset.sep _ (by decide : 272 + 4 ≤ 280 ∨ 280 + 4 ≤ 272) (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 272 + 4 ≤ 276 ∨ 276 + 4 ≤ 272) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]

theorem savedMem_r7 (s : State) : (savedMem s).readW (State.addr (s.gpr .r12) + BitVec.ofNat 64 276) 32 = s.gpr .r7 := by
  rw [savedMem, Mem.readW_writeW_sep (Offset.sep _ (by decide : 276 + 4 ≤ 280 ∨ 280 + 4 ≤ 276) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]

theorem savedMem_lr (s : State) : (savedMem s).readW (State.addr (s.gpr .r12) + BitVec.ofNat 64 280) 32 = s.gpr .lr := by
  rw [savedMem, Mem.readW_writeW_self32]

theorem setup_ok (s : State) :
    ∃ s', runBlock isa Impl.Rc2.Arm.Cbc.setup s = some s' ∧
      s'.gpr .r4 = s.gpr .r1 ∧ s'.gpr .r5 = s.gpr .r3 ∧
      s'.gpr .r1 = s.gpr .r2 ∧ s'.gpr .r2 = s.gpr .r12 ∧
      zeroCount s' = some (s.gpr .r3 == 0) ∧ Keep [.r4, .r5, .r1, .r2] s s' := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Impl.Rc2.Arm.Cbc.setup, rr, runBlock_cons,
      runStep_some, exec, Op2.eval, Option.map_some, gpr_setReg]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_subFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · simp only [gpr_subFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · simp only [gpr_subFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · simp only [gpr_subFlags, gpr_setReg_self]
  · change some ((s.gpr .r3 - 0) == 0) = _
    exact congrArg (fun x : BitVec 32 => some (x == 0)) (by bv_omega)
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_subFlags, gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem restore_ok (s : State) (values : Reg → BitVec 32)
    (fit : (s.gpr .r2).toNat + 512 ≤ 2 ^ 32)
    (r0 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 264) 4)
    (v0 : s.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 264) 32 = values .r4)
    (r1 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 268) 4)
    (v1 : s.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 268) 32 = values .r5)
    (r2 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 272) 4)
    (v2 : s.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 272) 32 = values .r6)
    (r3 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 276) 4)
    (v3 : s.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 276) 32 = values .r7)
    (r4 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 280) 4)
    (v4 : s.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 280) 32 = values .lr)
    : ∃ s', runBlock isa Impl.Rc2.Arm.Cbc.restore s = some s' ∧
      (∀ r ∈ callerSaved, s'.gpr r = values r) ∧ Keep callerSaved s s' := by
  have a264 : State.addr (s.gpr .r2 + BitVec.ofNat 32 264) = State.addr (s.gpr .r2) + BitVec.ofNat 64 264 := addr_add (by omega_arith)
  have a268 : State.addr (s.gpr .r2 + BitVec.ofNat 32 268) = State.addr (s.gpr .r2) + BitVec.ofNat 64 268 := addr_add (by omega_arith)
  have a272 : State.addr (s.gpr .r2 + BitVec.ofNat 32 272) = State.addr (s.gpr .r2) + BitVec.ofNat 64 272 := addr_add (by omega_arith)
  have a276 : State.addr (s.gpr .r2 + BitVec.ofNat 32 276) = State.addr (s.gpr .r2) + BitVec.ofNat 64 276 := addr_add (by omega_arith)
  have a280 : State.addr (s.gpr .r2 + BitVec.ofNat 32 280) = State.addr (s.gpr .r2) + BitVec.ofNat 64 280 := addr_add (by omega_arith)
  refine ⟨_, by
    simp only [Impl.Rc2.Arm.Cbc.restore, runBlock_cons, runStep_some, runBlock_nil,
      exec, Nat.reduceLT, ite_true, State.load32, gpr_setReg, reduceCtorEq, ite_false,
      mem_setReg, rd_setReg, wr_setReg, Option.map_some,
      a264, a268, a272, a276, a280, r0, r1, r2, r3, r4, v0, v1, v2, v3, v4]
    rfl, ?_⟩
  constructor
  · intro r hr
    simp only [callerSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [callerSaved, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

end VG.Proof.Rc2.Arm.Cbc

end

section

section

/-! # Constant-time CBC loops -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm VG.Impl.Rc2.Arm

def LoopRel (n : Nat) (s₁ s₂ : State) : Prop :=
  StepPre s₁ n ∧ StepPre s₂ n ∧ EqKept s₁ s₂ ∧
    s₁.gpr .r5 = BitVec.ofNat 32 n ∧ s₂.gpr .r5 = BitVec.ofNat 32 n ∧ 1 ≤ n

theorem bodyRel (d : Spec.Rc2.Direction) (n : Nat) :
    RelCT isa (LoopRel n) (Impl.Rc2.Arm.Cbc.body d) (fun s₁ s₂ =>
      EqKept s₁ s₂ ∧ eval .ne s₁ = eval .ne s₂ ∧
        (eval .ne s₁ = some true → ∃ m < n, LoopRel m s₁ s₂)) := by
  have ct : RelCT isa (LoopRel n) (Impl.Rc2.Arm.Cbc.body d) (fun _ _ => True) :=
    (body_ct d).mono (fun _ _ h => ⟨h.1.head h.2.2.2.2.2, h.2.1.head h.2.2.2.2.2, h.2.2.1⟩)
      (fun _ _ _ => trivial)
  have correct (s₁ s₂ : State) (h : LoopRel n s₁ s₂) :=
    And.intro (body_ok d s₁ n h.2.2.2.2.2 (by have := h.1.dataFit; omega_arith) h.2.2.2.1 (h.1.head h.2.2.2.2.2))
      (body_ok d s₂ n h.2.2.2.2.2 (by have := h.2.1.dataFit; omega_arith) h.2.2.2.2.1 (h.2.1.head h.2.2.2.2.2))
  apply (ct.wpDep correct).mono (fun _ _ h => h)
  rintro s₁' s₂' ⟨_, s₁, s₂, hp, h₁, h₂⟩
  have eq : EqKept s₁' s₂' := by
    intro r hr
    by_cases hptr : r = .r1
    · subst r; rw [h₁.ptr, h₂.ptr, hp.2.2.1 .r1 (by decide)]
    · by_cases hcount : r = .r5
      · subst r; rw [h₁.count, h₂.count]
      · rw [h₁.reg r hr hptr hcount, h₂.reg r hr hptr hcount]
        exact hp.2.2.1 r hr
  refine ⟨eq, by rw [eval_nonzeroCount, eval_nonzeroCount, h₁.flag, h₂.flag], ?_⟩
  intro hcontinue
  have hn : 1 ≤ n := hp.2.2.2.2.2
  have hm : 1 ≤ n - 1 := by
    rw [eval_nonzeroCount, h₁.flag] at hcontinue
    by_contra h
    have e : n = 1 := by omega_arith
    simp only [e, decide_true, Option.map_some, Bool.not_true, Option.some.injEq, Bool.false_eq_true] at hcontinue
  refine ⟨n - 1, by omega_arith, ?_, ?_, eq, h₁.count, h₂.count, hm⟩
  · have e : n = (n - 1) + 1 := by omega_arith
    rw [e] at h₁ hp
    exact h₁.tail hp.1 hm
  · have e : n = (n - 1) + 1 := by omega_arith
    rw [e] at h₂ hp
    exact h₂.tail hp.2.1 hm

theorem loop_ct (d : Spec.Rc2.Direction) (n : Nat) :
    RelCT isa (LoopRel n) (.loop (Impl.Rc2.Arm.Cbc.body d) .ne) EqKept := by
  refine RelCT.loop (M := isa) (body := Impl.Rc2.Arm.Cbc.body d) (c := .ne) (Q := EqKept) LoopRel ?_ n
  intro m
  exact (bodyRel d m).mono (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, fun _ => h.1, h.2.2⟩)

def MaybeRel (s₁ s₂ : State) : Prop :=
  ∃ n, StepPre s₁ n ∧ StepPre s₂ n ∧ EqKept s₁ s₂ ∧
    s₁.gpr .r5 = BitVec.ofNat 32 n ∧ s₂.gpr .r5 = BitVec.ofNat 32 n ∧
    zeroCount s₁ = some (decide (n = 0)) ∧ zeroCount s₂ = some (decide (n = 0))

theorem maybeLoop_ct (d : Spec.Rc2.Direction) :
    RelCT isa MaybeRel (.ite .eq (.block []) (.loop (Impl.Rc2.Arm.Cbc.body d) .ne)) EqKept := by
  apply RelCT.ite
  · rintro s₁ s₂ ⟨n, _, _, _, _, _, h₁, h₂⟩
    change zeroCount s₁ = zeroCount s₂
    rw [h₁, h₂]
  · apply RelCT.block_nil
    rintro s₁ s₂ ⟨⟨n, _, _, eq, _⟩, _⟩
    exact eq
  · apply RelCT.exists_ (fun n => loop_ct d n) |>.mono
    · rintro s₁ s₂ ⟨⟨n, h₁, h₂, eq, c₁, c₂, z₁, _⟩, branch⟩
      refine ⟨n, h₁, h₂, eq, c₁, c₂, ?_⟩
      change zeroCount s₁ = some false at branch
      rw [z₁] at branch
      have hn : n ≠ 0 := by intro hz; simp [hz] at branch
      omega_arith
    · exact fun _ _ h => h

end VG.Proof.Rc2.Arm.Cbc

end

section

/-! # CBC's function-level contract -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm

def contract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let iv : Region := ⟨State.addr (s.gpr .r1), 8⟩
    let data : Region := ⟨State.addr (s.gpr .r2), 8 * (s.gpr .r3).toNat⟩
    let buf : Region := ⟨State.addr (stackArg s 0), 512⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [key, args] ∧ s.wr = [iv, data, buf] ∧ key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      iv.Disjoint data ∧ iv.Disjoint buf ∧ data.Disjoint buf ∧ iv.Disjoint args ∧ data.Disjoint args ∧ buf.Disjoint args ∧
      (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 8 ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat + 512 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 8 * (s.gpr .r3).toNat ≤ 2 ^ 32
  post s s' :=
    let out := Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) d
      (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1))) (Spec.Rc2.blocksAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
    Spec.Rc2.blocksAt s'.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat = out.1 ∧
      Spec.Rc2.blockAt s'.mem (State.addr (s.gpr .r1)) = out.2
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

end VG.Proof.Rc2.Arm.Cbc

end

/-! # CBC's public prologue and stack argument -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm VG.Impl.Rc2.Arm

def startCode : Prog isa := .seq (.block [.ldrSp .r12 0])
  (.block (Impl.Rc2.Arm.Cbc.save ++ Impl.Rc2.Arm.Cbc.setup))

structure StartPost (s s' : State) : Prop where
  pre : StepPre s' (s.gpr .r3).toNat
  key : s'.gpr .r0 = s.gpr .r0
  iv : s'.gpr .r4 = s.gpr .r1
  data : s'.gpr .r1 = s.gpr .r2
  buf : s'.gpr .r2 = stackArg s 0
  count : s'.gpr .r5 = s.gpr .r3
  flag : zeroCount s' = some (s.gpr .r3 == 0)

theorem start_ok (d : Spec.Rc2.Direction) (s : State) (hs : (contract d).pre s) :
    WP isa startCode s (StartPost s) := by
  obtain ⟨hrd, hwr, keyIv, keyData, keyBuf, ivData, ivBuf, dataBuf,
    _ivArgs, _dataArgs, _bufArgs, keyFit, ivFit, bufFit, _spFit, fit⟩ := hs
  have writes (i : Nat) (hi : i + 4 ≤ 512) : InRegions s.wr (State.addr (stackArg s 0) + BitVec.ofNat 64 i) 4 := by
    rw [hwr]
    exact ⟨⟨State.addr (stackArg s 0), 512⟩, by simp, Offset.contains_base _ hi (by omega_arith)⟩
  rw [startCode]
  apply WP.seq
  obtain ⟨s₀, run₀, buf₀, keep₀⟩ := loadScratch_ok s (by
    rw [hrd, hwr]
    exact ⟨⟨stackArgAddr s 0, 4⟩, by simp, Region.contains_self _ _⟩)
  refine WP.of_runBlock ⟨s₀, run₀, ?_⟩
  have g₀ (r : Reg) (hr : r ≠ .r12) := keep₀.reg r (by simpa using hr)
  have writes₀ (i : Nat) (hi : i + 4 ≤ 512) :
      InRegions s₀.wr (State.addr (s₀.gpr .r12) + BitVec.ofNat 64 i) 4 := by
    rw [keep₀.wr, buf₀]; exact writes i hi
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, keep₁⟩ := save_ok s₀ (by rw [buf₀]; exact bufFit)
    (writes₀ 264 (by decide)) (writes₀ 268 (by decide)) (writes₀ 272 (by decide))
    (writes₀ 276 (by decide)) (writes₀ 280 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, iv₂, count₂, data₂, buf₂, flag₂, keep₂⟩ := setup_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have g₁ (r : Reg) : s₁.gpr r = s₀.gpr r := keep₁.reg r (by simp)
  rw [g₁, g₀ .r1 (by decide)] at iv₂
  rw [g₁, g₀ .r3 (by decide)] at count₂ flag₂
  rw [g₁, g₀ .r2 (by decide)] at data₂
  rw [g₁, buf₀] at buf₂
  have key₂ := (keep₂.reg .r0 (by decide)).trans ((g₁ .r0).trans (g₀ .r0 (by decide)))
  have rd₂ := keep₂.rd.trans (keep₁.rd.trans keep₀.rd)
  have wr₂ := keep₂.wr.trans (keep₁.wr.trans keep₀.wr)
  have hp₂ : StepPre s₂ (s.gpr .r3).toNat := by
    constructor
    · rw [key₂]; exact keyFit
    · rw [iv₂]; exact ivFit
    · rw [data₂]; exact fit
    · rw [buf₂]; exact bufFit
    · simp only [Covers, keyR, ivR, dataR, bufR, key₂, iv₂, data₂, buf₂, rd₂, wr₂, hrd, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, by simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; grind, hc⟩
    · simp only [Covers, ivR, dataR, bufR, iv₂, data₂, buf₂, wr₂, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; grind, hc⟩
    · simpa only [keyR, ivR, key₂, iv₂] using keyIv
    · simpa only [keyR, dataR, key₂, data₂] using keyData
    · simpa only [keyR, bufR, key₂, buf₂] using keyBuf
    · simpa only [ivR, dataR, iv₂, data₂] using ivData
    · simpa only [ivR, bufR, iv₂, buf₂] using ivBuf
    · simpa only [dataR, bufR, data₂, buf₂] using dataBuf
  exact ⟨hp₂, key₂, iv₂, data₂, buf₂, count₂, flag₂⟩

def InitialRel (d : Spec.Rc2.Direction) (s₁ s₂ : State) : Prop :=
  (contract d).pre s₁ ∧ (contract d).pre s₂ ∧ (contract d).pub s₁ s₂

def EqArgs (s₁ s₂ : State) : Prop := ∀ r ∈ ([.r0, .r1, .r2, .r3, .r12] : List Reg), s₁.gpr r = s₂.gpr r

theorem load_trace {s s' : State} {t : List Leak} (h : Exec isa (.block [.ldrSp .r12 0]) s t s') :
    t = [.addr (State.addr s.sp)] := by
  cases h with
  | block h =>
    simp only [execBlock, isa] at h
    cases he : exec (.ldrSp .r12 0) s with
    | none => simp only [he] at h; cases h
    | some u =>
      simp only [he, Option.map_some, List.append_nil, Option.some.injEq, Prod.mk.injEq] at h
      simpa only [addrs, BitVec.add_zero, List.map_cons, List.map_nil] using h.2.symm

theorem load_ct (d : Spec.Rc2.Direction) :
    RelCT isa (InitialRel d) (.block [.ldrSp .r12 0]) EqArgs := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  have read₁ : InRegions (s₁.rd ++ s₁.wr) (stackArgAddr s₁ 0) 4 := by
    rw [hp.1.1, hp.1.2.1]
    exact ⟨⟨stackArgAddr s₁ 0, 4⟩, by simp, Region.contains_self _ _⟩
  have read₂ : InRegions (s₂.rd ++ s₂.wr) (stackArgAddr s₂ 0) 4 := by
    rw [hp.2.1.1, hp.2.1.2.1]
    exact ⟨⟨stackArgAddr s₂ 0, 4⟩, by simp, Region.contains_self _ _⟩
  obtain ⟨u₁, run₁, buf₁, keep₁⟩ := loadScratch_ok s₁ read₁
  obtain ⟨u₂, run₂, buf₂, keep₂⟩ := loadScratch_ok s₂ read₂
  obtain ⟨_, v₁, ev₁, hv₁⟩ := WP.of_runBlock (Q := fun s => s = u₁) ⟨u₁, run₁, rfl⟩
  obtain ⟨_, v₂, ev₂, hv₂⟩ := WP.of_runBlock (Q := fun s => s = u₂) ⟨u₂, run₂, rfl⟩
  have eu₁ : s₁' = u₁ := (Exec.det e₁ ev₁).2.trans hv₁
  have eu₂ : s₂' = u₂ := (Exec.det e₂ ev₂).2.trans hv₂
  obtain ⟨sp, p0, p1, p2, p3, bp⟩ := hp.2.2
  constructor
  · rw [load_trace e₁, load_trace e₂, sp]
  · rw [eu₁, eu₂]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [keep₁.reg .r0 (by decide), keep₂.reg .r0 (by decide)]; exact p0
    · rw [keep₁.reg .r1 (by decide), keep₂.reg .r1 (by decide)]; exact p1
    · rw [keep₁.reg .r2 (by decide), keep₂.reg .r2 (by decide)]; exact p2
    · rw [keep₁.reg .r3 (by decide), keep₂.reg .r3 (by decide)]; exact p3
    · rw [buf₁, buf₂]; exact bp

theorem start_ct (d : Spec.Rc2.Direction) : RelCT isa (InitialRel d) startCode MaybeRel := by
  have ct : RelCT isa (InitialRel d) startCode (fun _ _ => True) := by
    apply (load_ct d).seq
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3, .r12])
      (fun _ _ h => Taint.agree_ofRegs h)
    taint_decide
  apply (ct.wpDep (fun s₁ s₂ h => ⟨start_ok d s₁ h.1, start_ok d s₂ h.2.1⟩)).mono (fun _ _ h => h)
  rintro s₁' s₂' ⟨_, s₁, s₂, hp, h₁, h₂⟩
  obtain ⟨_, p0, p1, p2, p3, bp⟩ := hp.2.2
  refine ⟨(s₁.gpr .r3).toNat, h₁.pre, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p3]; exact h₂.pre
  · intro r hr
    simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h₁.key, h₂.key, p0]
    · rw [h₁.data, h₂.data, p2]
    · rw [h₁.buf, h₂.buf, bp]
    · rw [h₁.iv, h₂.iv, p1]
    · rw [h₁.count, h₂.count, p3]
  · simpa using h₁.count
  · rw [p3]; simpa using h₂.count
  · rw [h₁.flag]
    apply congrArg some
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact BitVec.eq_of_toNat_eq h
  · rw [h₂.flag, p3]
    apply congrArg some
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact BitVec.eq_of_toNat_eq h

end VG.Proof.Rc2.Arm.Cbc

end

section

/-! # Constant-time CBC callers -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm

theorem cbc_constantTime (d : Spec.Rc2.Direction) :
    ConstantTime isa (contract d).pre (contract d).pub (Impl.Rc2.Arm.Cbc.cbc d) := by
  apply RelCT.constantTime
  apply RelCT.assoc
  apply (start_ct d).seq
  apply (maybeLoop_ct d).seq
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r2])
    (fun _ _ h => Taint.agree_ofRegs (fun r hr => h r (by have e := List.mem_singleton.mp hr; rw [e]; decide)))
  taint_decide

end VG.Proof.Rc2.Arm.Cbc

end

/-! # Verified RC2-CBC encryption and decryption -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm VG.Impl.Rc2.Arm

theorem cbc_body_correct (d : Spec.Rc2.Direction) (s : State) (hs : (contract d).pre s) :
    WP isa (Impl.Rc2.Arm.Cbc.cbc d) s (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (contract d).post s s') := by
  obtain ⟨hrd, hwr, keyIv, keyData, keyBuf, ivData, ivBuf, dataBuf,
    _ivArgs, _dataArgs, _bufArgs, keyFit, ivFit, bufFit, _spFit, fit⟩ := hs
  have writes (i : Nat) (hi : i + 4 ≤ 512) : InRegions s.wr (State.addr (stackArg s 0) + BitVec.ofNat 64 i) 4 := by
    rw [hwr]
    exact ⟨⟨State.addr (stackArg s 0), 512⟩, by simp, Offset.contains_base _ hi (by omega_arith)⟩
  rw [Impl.Rc2.Arm.Cbc.cbc]
  apply WP.seq
  obtain ⟨s₀, run₀, buf₀, keep₀⟩ := loadScratch_ok s (by
    rw [hrd, hwr]
    exact ⟨⟨stackArgAddr s 0, 4⟩, by simp, Region.contains_self _ _⟩)
  refine WP.of_runBlock ⟨s₀, run₀, ?_⟩
  have g₀ (r : Reg) (hr : r ≠ .r12) := keep₀.reg r (by simpa using hr)
  have writes₀ (i : Nat) (hi : i + 4 ≤ 512) :
      InRegions s₀.wr (State.addr (s₀.gpr .r12) + BitVec.ofNat 64 i) 4 := by
    rw [keep₀.wr, buf₀]; exact writes i hi
  apply WP.seq
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, keep₁⟩ := save_ok s₀ (by rw [buf₀]; exact bufFit)
    (writes₀ 264 (by decide)) (writes₀ 268 (by decide)) (writes₀ 272 (by decide))
    (writes₀ 276 (by decide)) (writes₀ 280 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, iv₂, count₂, data₂, buf₂, flag₂, keep₂⟩ := setup_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have g₁ (r : Reg) : s₁.gpr r = s₀.gpr r := keep₁.reg r (by simp)
  rw [g₁, g₀ .r1 (by decide)] at iv₂
  rw [g₁, g₀ .r3 (by decide)] at count₂ flag₂
  rw [g₁, g₀ .r2 (by decide)] at data₂
  rw [g₁, buf₀] at buf₂
  have key₂ := (keep₂.reg .r0 (by decide)).trans ((g₁ .r0).trans (g₀ .r0 (by decide)))
  have rd₂ := keep₂.rd.trans (keep₁.rd.trans keep₀.rd)
  have wr₂ := keep₂.wr.trans (keep₁.wr.trans keep₀.wr)
  have mem₂ : s₂.mem = savedMem s₀ := keep₂.mem.trans keep₁.mem
  have scratchFrame : Frame [⟨State.addr (stackArg s 0), 512⟩] s.mem s₂.mem := by
    rw [mem₂, ← keep₀.mem, ← buf₀]; exact savedMem_frame s₀
  have initialKey := scheduleAt_frame scratchFrame (State.addr (s.gpr .r0)) (by simpa using keyBuf)
  have initialIv := blockAt_frame scratchFrame (State.addr (s.gpr .r1)) (by simpa using ivBuf)
  have initialData := blocksAt_frame scratchFrame (State.addr (s.gpr .r2)) (s.gpr .r3).toNat (by simpa using dataBuf)
  have hp₂ : StepPre s₂ (s.gpr .r3).toNat := by
    constructor
    · rw [key₂]; exact keyFit
    · rw [iv₂]; exact ivFit
    · rw [data₂]; exact fit
    · rw [buf₂]; exact bufFit
    · simp only [Covers, keyR, ivR, dataR, bufR, key₂, iv₂, data₂, buf₂, rd₂, wr₂, hrd, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, by simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; grind, hc⟩
    · simp only [Covers, ivR, dataR, bufR, iv₂, data₂, buf₂, wr₂, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; grind, hc⟩
    · simpa only [keyR, ivR, key₂, iv₂] using keyIv
    · simpa only [keyR, dataR, key₂, data₂] using keyData
    · simpa only [keyR, bufR, key₂, buf₂] using keyBuf
    · simpa only [ivR, dataR, iv₂, data₂] using ivData
    · simpa only [ivR, bufR, iv₂, buf₂] using ivBuf
    · simpa only [dataR, bufR, data₂, buf₂] using dataBuf
  apply WP.seq
  apply WP.mono (maybeLoop_ok d s₂ (s.gpr .r3).toNat (by omega_arith) hp₂
    (by simpa using count₂) (by rw [count₂]; exact flag₂))
  intro s₃ h₃
  have rd₃ := h₃.rd.trans rd₂
  have wr₃ := h₃.wr.trans wr₂
  have buf₃ := (h₃.reg .r2 (by decide) (by decide) (by decide)).trans buf₂
  have reads (i : Nat) (hi : i + 4 ≤ 512) :
      InRegions (s₃.rd ++ s₃.wr) (State.addr (s₃.gpr .r2) + BitVec.ofNat 64 i) 4 := by
    rw [rd₃, wr₃, buf₃]
    obtain ⟨r, hr, hc⟩ := writes i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have v0 : s₃.mem.readW (State.addr (s₃.gpr .r2) + BitVec.ofNat 64 264) 32 = s.gpr .r4 := by
    have h := h₃.scratchRead hp₂ 264 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, savedMem_r4, g₀ .r4 (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  have v1 : s₃.mem.readW (State.addr (s₃.gpr .r2) + BitVec.ofNat 64 268) 32 = s.gpr .r5 := by
    have h := h₃.scratchRead hp₂ 268 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, savedMem_r5, g₀ .r5 (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  have v2 : s₃.mem.readW (State.addr (s₃.gpr .r2) + BitVec.ofNat 64 272) 32 = s.gpr .r6 := by
    have h := h₃.scratchRead hp₂ 272 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, savedMem_r6, g₀ .r6 (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  have v3 : s₃.mem.readW (State.addr (s₃.gpr .r2) + BitVec.ofNat 64 276) 32 = s.gpr .r7 := by
    have h := h₃.scratchRead hp₂ 276 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, savedMem_r7, g₀ .r7 (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  have v4 : s₃.mem.readW (State.addr (s₃.gpr .r2) + BitVec.ofNat 64 280) 32 = s.gpr .lr := by
    have h := h₃.scratchRead hp₂ 280 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, savedMem_lr, g₀ .lr (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  obtain ⟨s₄, run₄, saved₄, keep₄⟩ := restore_ok s₃ s.gpr (by rw [buf₃]; exact bufFit)
    (reads 264 (by decide)) v0    (reads 268 (by decide)) v1    (reads 272 (by decide)) v2    (reads 276 (by decide)) v3    (reads 280 (by decide)) v4
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  constructor
  · intro r hr
    by_cases hs : r ∈ callerSaved
    · exact saved₄ r hs
    · have kept : ∀ r ∈ preserved, r ∉ callerSaved →
          r ∈ savedAcrossCall ∧ r ≠ .r5 ∧ r ∉ [.r4, .r5, .r1, .r2] ∧ r ≠ .r12 := by decide
      obtain ⟨hc, hn, ht, h12⟩ := kept r hr hs
      rw [keep₄.reg r hs, h₃.callee r hc hn, keep₂.reg r ht, g₁ r]
      exact g₀ r h12
  · have out := h₃.data
    have iv := h₃.iv
    rw [key₂, iv₂, data₂, initialKey, initialIv, initialData] at out iv
    constructor
    · rw [keep₄.mem]; exact out
    · rw [keep₄.mem]; exact iv

def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x6000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x6001 then 0x40 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x6000, 4⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 512⟩]

theorem encrypt_correct (s : State) (hs : (contract .encrypt).pre s) :
    ∃ t s', Exec isa Impl.Rc2.Arm.Cbc.encrypt s t s' ∧ abiPreserved s s' ∧
      (contract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := cbc_body_correct .encrypt s hs
  change Exec isa Impl.Rc2.Arm.Cbc.encrypt s t s' at he
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (contract .decrypt).pre s) :
    ∃ t s', Exec isa Impl.Rc2.Arm.Cbc.decrypt s t s' ∧ abiPreserved s s' ∧
      (contract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := cbc_body_correct .decrypt s hs
  change Exec isa Impl.Rc2.Arm.Cbc.decrypt s t s' at he
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

theorem encrypt_verified : Verified target Impl.Rc2.Arm.Cbc.encrypt (Spec.Rc2.cbcEncryptContract abi 0) := by
  refine Verified.of_correct encrypt_correct (cbc_constantTime .encrypt) ?_
  sig_implies [Spec.Rc2.cbcEncryptContract, Spec.Rc2.cbcContract, Spec.Rc2.cbcSig, abi, argRegs,
    Arm.reduceClassify, Arm.Loc.val, State.addr, contract]
    [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

theorem decrypt_verified : Verified target Impl.Rc2.Arm.Cbc.decrypt (Spec.Rc2.cbcDecryptContract abi 0) := by
  refine Verified.of_correct decrypt_correct (cbc_constantTime .decrypt) ?_
  sig_implies [Spec.Rc2.cbcDecryptContract, Spec.Rc2.cbcContract, Spec.Rc2.cbcSig, abi, argRegs,
    Arm.reduceClassify, Arm.Loc.val, State.addr, contract]
    [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

end VG.Proof.Rc2.Arm.Cbc
