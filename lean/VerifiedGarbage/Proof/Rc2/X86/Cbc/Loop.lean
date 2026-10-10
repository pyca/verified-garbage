import VerifiedGarbage.Proof.Rc2.X86.Cbc.Body

section

/-! # Frames for successive CBC blocks -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86

def loopWrites (s : State) (n : Nat) : List Region := [ivR s, dataR s n, ⟨addr32 (s.gpr .ebp), 264⟩, stackR s]

theorem loopFrame_slice {s s' : State} {n m i : Nat} {a b : Mem}
    (h : Frame (loopWrites s' m) a b) (bound : i + m ≤ n)
    (iv : s'.gpr .ecx = s.gpr .ecx) (buf : s'.gpr .ebp = s.gpr .ebp) (sp : s'.gpr .esp = s.gpr .esp)
    (ptr : addr32 (s'.gpr .esi) = addr32 (s.gpr .esi) + BitVec.ofNat 64 (8 * i)) :
    Frame (loopWrites s n) a b := by
  apply h.sub
  intro r hr
  simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · refine ⟨ivR s, by simp [loopWrites], ?_⟩
    change Region.Sub ⟨addr32 (s'.gpr .ecx), 8⟩ ⟨addr32 (s.gpr .ecx), 8⟩
    rw [iv]; exact fun _ h => h
  · refine ⟨dataR s n, by simp [loopWrites], ?_⟩
    change Region.Sub ⟨addr32 (s'.gpr .esi), 8 * m⟩ ⟨addr32 (s.gpr .esi), 8 * n⟩
    rw [ptr]
    exact Offset.sub_base _ (by omega_arith)
  · refine ⟨⟨addr32 (s.gpr .ebp), 264⟩, by simp [loopWrites], ?_⟩
    rw [buf]; exact fun _ h => h
  · refine ⟨stackR s, by simp [loopWrites], ?_⟩
    change Region.Sub (below (s'.gpr .esp) 16) (below (s.gpr .esp) 16)
    rw [sp]; exact fun _ h => h

theorem BodyPost.frame {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s n s') (hn : 1 ≤ n) : Frame (loopWrites s n) s.mem s'.mem :=
  loopFrame_slice (m := 1) (i := 0) h.mem hn rfl rfl rfl (by simp)

theorem BodyPost.schedule {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s n s') (hp : StepPre s) :
    Spec.Rc2.scheduleAt s'.mem (addr32 (s.gpr .ebx)) = Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx)) := by
  apply scheduleAt_frame h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.keyIv (And.intro hp.keyData (And.intro
      (hp.keyBuf.sub_right (Region.sub_prefix (by decide : 264 ≤ 512))) hp.stackKey.symm))

theorem BodyPost.tailData {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64) :
    Spec.Rc2.blocksAt s'.mem (addr32 (s.gpr .esi) + 8) n = Spec.Rc2.blocksAt s.mem (addr32 (s.gpr .esi) + 8) n := by
  have sub : Region.Sub ⟨addr32 (s.gpr .esi) + 8, 8 * n⟩ (dataR s (n + 1)) :=
    Offset.sub_base _ (by change 8 + 8 * n ≤ 8 * (n + 1); omega_arith)
  have sep : (Region.mk (addr32 (s.gpr .esi) + 8) (8 * n)).Disjoint (dataR s) :=
    Offset.disjoint_base _ (d := 8) (n := 8 * n) (k := 8) (by decide) (by omega_arith)
  apply blocksAt_frame h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.ivData.sub_right sub).symm) (And.intro sep (And.intro
      ((hp.dataBuf.sub_left sub).sub_right (Region.sub_prefix (by decide : 264 ≤ 512))) (hp.stackData.sub_right sub).symm))

theorem firstBlock_frame {d : Spec.Rc2.Direction} {s s' : State} {n : Nat} {m : Mem}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64)
    (hn : 1 ≤ n)
    (frame : Frame (loopWrites s' n) s'.mem m) :
    Spec.Rc2.blockAt m (addr32 (s.gpr .esi)) = Spec.Rc2.blockAt s'.mem (addr32 (s.gpr .esi)) := by
  have first : Region.Sub (dataR s) (dataR s (n + 1)) := Region.sub_prefix (by change 8 ≤ 8 * (n + 1); omega_arith)
  have sep : (dataR s).Disjoint ⟨addr32 (s.gpr .esi) + 8, 8 * n⟩ :=
    Offset.base_disjoint _ (e := 8) (n := 8 * n) (k := 8) (by decide) (by omega_arith)
  have ptr : addr32 (s'.gpr .esi) = addr32 (s.gpr .esi) + 8 := by
    rw [h.ptr]
    exact addr_add (k := 8) (by have := hp.dataFit; omega_arith)
  apply blockAt_frame frame
  have iv := h.reg .ecx (by decide) (by decide) (by decide)
  have buf := h.reg .ebp (by decide) (by decide) (by decide)
  have sp := h.reg .esp (by decide) (by decide) (by decide)
  simpa only [loopWrites, ivR, dataR, stackR, iv, buf, ptr, sp,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.ivData.sub_right first).symm) (And.intro sep (And.intro
      ((hp.dataBuf.sub_left first).sub_right (Region.sub_prefix (by decide : 264 ≤ 512))) (hp.stackData.sub_right first).symm))

end VG.Proof.Rc2.X86.Cbc

end

/-! # Correctness of the CBC loop on complete blocks -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86

structure LoopPost (d : Spec.Rc2.Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .esi = s.gpr .esi + BitVec.ofNat 32 (8 * n)
  count : s'.gpr .edi = 0
  reg : ∀ r ∈ kept, r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r
  callee : ∀ r ∈ calleeSaved, r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (loopWrites s n) s.mem s'.mem
  data : Spec.Rc2.blocksAt s'.mem (addr32 (s.gpr .esi)) n =
    (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx))) d
      (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .ecx))) (Spec.Rc2.blocksAt s.mem (addr32 (s.gpr .esi)) n)).1
  iv : Spec.Rc2.blockAt s'.mem (addr32 (s.gpr .ecx)) =
    (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx))) d
      (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .ecx))) (Spec.Rc2.blocksAt s.mem (addr32 (s.gpr .esi)) n)).2

theorem loop_ok (d : Spec.Rc2.Direction) (n : Nat) :
    ∀ s : State, 1 ≤ n → 8 * n ≤ 2 ^ 32 → StepPre s n → s.gpr .edi = BitVec.ofNat 32 n →
      WP isa (.loop (Impl.Rc2.X86.Cbc.body d) .ne) s (LoopPost d s n) := by
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
        have ki := h₁.reg .ebx (by decide) (by decide) (by decide)
        have vi := h₁.reg .ecx (by decide) (by decide) (by decide)
        have bi := h₁.reg .ebp (by decide) (by decide) (by decide)
        have ptr : addr32 (s₁.gpr .esi) = addr32 (s.gpr .esi) + 8 := by
          rw [h₁.ptr]; exact addr_add (k := 8) (by have := hp.dataFit; omega_arith)
        rw [ki, vi, ptr, key, tail, h₁.iv] at data
        rw [ki, vi, ptr, key, tail, h₁.iv] at iv
        refine ⟨?_, h₂.count, ?_, ?_, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, ?_, ?_, ?_⟩
        · rw [h₂.ptr, h₁.ptr, BitVec.add_assoc]
          exact congrArg (s.gpr .esi + ·) (by
            change BitVec.ofNat 32 8 + BitVec.ofNat 32 (8 * n) = _
            rw [← BitVec.ofNat_add]
            exact congrArg (BitVec.ofNat 32) (by omega_arith))
        · intro r hr hs hb
          exact (h₂.reg r hr hs hb).trans (h₁.reg r hr hs hb)
        · intro r hr hs hb
          exact (h₂.callee r hr hs hb).trans (h₁.callee r hr hs hb)
        · exact (h₁.frame hn).trans (loopFrame_slice (i := 1) h₂.mem (by omega_arith) vi bi (h₁.reg .esp (by decide) (by decide) (by decide)) ptr)
        · have first := firstBlock_frame h₁ hp (by omega_arith) (by omega_arith) h₂.mem
          rw [blocksAt_cons, first, h₁.data, data, blocksAt_cons]
          rfl
        · rw [blocksAt_cons]
          exact iv

theorem maybeLoop_ok (d : Spec.Rc2.Direction) (s : State) (n : Nat) (bound : 8 * n ≤ 2 ^ 32)
    (hp : StepPre s n) (count : s.gpr .edi = BitVec.ofNat 32 n)
    (flag : zeroCount s = some (s.gpr .edi == 0)) :
    WP isa (.ite .e (.block []) (.loop (Impl.Rc2.X86.Cbc.body d) .ne)) s (LoopPost d s n) := by
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
      refine ⟨by simp, count, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _, ?_, ?_⟩
      · rfl
      · rfl
    · simp
  · apply WP.ite false (by simp only [eval_zeroCount, flag', hz, decide_false])
    · simp
    · intro _
      exact loop_ok d n s (by omega_arith) bound hp count

theorem LoopPost.scratchRead {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : LoopPost d s n s') (hp : StepPre s n) (i : Nat) (lo : 264 ≤ i) (hi : i + 4 ≤ 512) :
    s'.mem.readW (addr32 (s.gpr .ebp) + BitVec.ofNat 64 i) 32 = s.mem.readW (addr32 (s.gpr .ebp) + BitVec.ofNat 64 i) 32 := by
  have sub : Region.Sub ⟨addr32 (s.gpr .ebp) + BitVec.ofNat 64 i, 4⟩ (bufR s) := Offset.sub_base _ hi
  have sep : (Region.mk (addr32 (s.gpr .ebp) + BitVec.ofNat 64 i) 4).Disjoint ⟨addr32 (s.gpr .ebp), 264⟩ :=
    Offset.disjoint_base _ lo (by omega_arith)
  apply h.mem.readW (r := ⟨addr32 (s.gpr .ebp) + BitVec.ofNat 64 i, 4⟩) (Region.contains_self _ _)
    (hn := by decide)
  simpa only [loopWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.ivBuf.sub_right sub).symm) (And.intro ((hp.dataBuf.sub_right sub).symm)
      (And.intro sep (hp.stackBuf.sub_right sub).symm))

end VG.Proof.Rc2.X86.Cbc
