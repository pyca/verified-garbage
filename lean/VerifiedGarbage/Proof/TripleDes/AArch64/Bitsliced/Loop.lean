import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Ecb

/-!
# The loop

Each iteration of `step` runs one batch: on the next 128 blocks in place
while that many are left, else on the `n mod 128 > 0` blocks left, copied
into the scratch buffer (at `x3`), whose other lanes hold whatever the buffer
held, and copied back; then no blocks are left (`step_ok`). Every block
becomes its encryption or decryption (`ecb_correct`).
-/

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.StraightV VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64.BitsliceNeon
open VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (blockOut wAt wAt_wAt blockAt_frame)

theorem exec_movz_x {s : State} {d : Reg} {imm : BitVec 16} :
    exec (.movz .x d imm 0) s = some (s.write .x d (imm.setWidth 64)) := by
  simp only [exec, Size.bits, Nat.mul_zero, show (0 : Nat) < 64 from by decide, ite_true]
  exact congrArg (fun v => some (s.write .x d v)) (BitVec.shiftLeft_zero _)

theorem wAt_zero (p : Addr) : wAt p 0 = p := by simp [wAt]

theorem scratch_word {B : Addr} {i : Nat} (hi : i < 128) :
    (⟨B, 1024⟩ : Region).Contains (wAt B i) 8 := Offset.contains_base _ (by omega) (by omega)

/-- The registers the loop changes. -/
def EcbRegs (r : Reg) : Prop :=
  r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x4 ∧ r ≠ .x5 ∧ r ≠ .x7 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧
    r ≠ .x13

/-- `m > 0` blocks left, a multiple of 128 fewer than `n`. -/
structure EcbInv (d : Direction) (s₀ : State) (n m : Nat) (s : State) : Prop where
  pos : 0 < m
  le : m ≤ n
  mod : m % 128 = n % 128
  x2 : s.gpr .x2 = BitVec.ofNat 64 m
  x1 : s.gpr .x1 = wAt (s₀.gpr .x1) (n - m)
  gpr : ∀ r, EcbRegs r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  done : ∀ b < n - m, blockAt s.mem (wAt (s₀.gpr .x1) b) =
    blockOut (scheduleAt s₀.mem (s₀.gpr .x0)) d (blockAt s₀.mem (wAt (s₀.gpr .x1) b))
  frame : Frame [⟨s₀.gpr .x1, 8 * (n - m)⟩, ⟨s₀.gpr .x3, 1024⟩] s₀.mem s.mem

/-- Every block done. -/
def EcbPost (d : Direction) (s₀ : State) (n : Nat) (s : State) : Prop :=
  ∀ b < n, blockAt s.mem (wAt (s₀.gpr .x1) b) =
    blockOut (scheduleAt s₀.mem (s₀.gpr .x0)) d (blockAt s₀.mem (wAt (s₀.gpr .x1) b))

theorem step_ok (d : Direction) {s₀ : State} (E : Env s₀) {n : Nat}
    (hn : (s₀.gpr .x2).toNat = n) (m : Nat) (s : State) (h : EcbInv d s₀ n m s) :
    WP isa (step d) s (fun s' =>
      (isa.eval (Cond.nonzero .x .x2) s' = some false ∧ EcbPost d s₀ n s') ∨
      (isa.eval (Cond.nonzero .x .x2) s' = some true ∧ ∃ m' < m, EcbInv d s₀ n m' s')) := by
  have hl := E.len
  have hfit := E.fit
  rw [hn] at hl hfit
  have hpos := h.pos
  have hle := h.le
  let D := s₀.gpr .x1
  let B := s₀.gpr .x3
  let S := s₀.gpr .x0
  have g := h.gpr
  have hx0 : s.gpr .x0 = S := g _ (by simp [EcbRegs])
  have hx3 : s.gpr .x3 = B := g _ (by simp [EcbRegs])
  have keyData : (⟨S, 384⟩ : Region).Disjoint ⟨D, 8 * n⟩ := hn ▸ E.keyData
  have dataB : (⟨D, 8 * n⟩ : Region).Disjoint ⟨B, 1024⟩ := hn ▸ E.dataBuf
  have keyB : (⟨S, 384⟩ : Region).Disjoint ⟨B, 1024⟩ := E.keyBuf
  have dataR : (⟨D, 8 * n⟩ : Region) ∈ s.wr := by rw [h.wr, E.wr, hn]; exact List.mem_cons_self
  have scrR : (⟨B, 1024⟩ : Region) ∈ s.wr := by
    rw [h.wr, E.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  -- the schedule, and the blocks not yet done, as on entry
  have hK : scheduleAt s.mem S = scheduleAt s₀.mem S :=
    VG.Proof.TripleDes.scheduleAt_eq_of_frame S h.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact keyData.sub_right (Region.sub_prefix (by omega))
      · exact keyB
  have hB : ∀ j, j < m → blockAt s.mem (wAt D (n - m + j)) = blockAt s₀.mem (wAt D (n - m + j)) :=
    fun j hj => blockAt_frame h.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base D (by omega) (by omega)
      · exact dataB.sub_left (Offset.sub_base _ (by omega))
  rw [Impl.TripleDes.AArch64.BitsliceNeon.step]
  apply WP.seq
  let s₁ := s.write .x .x10 (s.read .x .x2 >>> 7)
  refine WP.of_runBlock ⟨s₁, by rw [runBlock_cons, wholeLeft, exec_lsr_x (by decide), runStep_some,
    runBlock_nil], ?_⟩
  have x10₁ : s₁.gpr .x10 = BitVec.ofNat 64 (m / 128) := by
    simp only [s₁, State.write, State.read, BitVec.setWidth_eq, ite_true]
    rw [h.x2, lsr7 _ (by omega)]
  have g₁ : ∀ r, r ≠ .x10 → s₁.gpr r = s.gpr r := fun r hr => by simp [s₁, State.write, hr]
  apply WP.seq
  apply WP.ite _ (eval_zero s₁ .x10 x10₁ (by omega))
  · -- the blocks left, through the scratch buffer
    intro hz
    have hm : m < 128 := by simp at hz; omega
    let T := wAt D (n - m)
    have hx1 : s₁.gpr .x1 = T := (g₁ _ (by decide)).trans h.x1
    have dataW : ∀ i < m, InRegions s.wr (wAt T i) 8 := fun i hi =>
      ⟨_, dataR, by rw [wAt_wAt]; exact Offset.contains_base _ (by omega) (by omega)⟩
    have scrIn : ∀ i < 128, InRegions s.wr (wAt B i) 8 := fun i hi => ⟨_, scrR, scratch_word hi⟩
    have subT : Region.Sub ⟨T, 8 * m⟩ ⟨D, 8 * n⟩ := Offset.sub_base _ (by omega)
    have dataSep : (⟨T, 8 * m⟩ : Region).Disjoint ⟨B, 8 * m⟩ :=
      (dataB.sub_left subT).sub_right (Region.sub_prefix (by omega))
    unfold tailIn
    apply WP.seq
    -- x11 := x1, x12 := x3, x13 := x2
    let s₂ := ((s₁.write .x .x11 (s₁.read .x .x1 + BitVec.ofNat _ 0)).write .x .x12
      ((s₁.write .x .x11 (s₁.read .x .x1 + BitVec.ofNat _ 0)).read .x .x3 + BitVec.ofNat _ 0))
    let s₂' := s₂.write .x .x13 (s₂.read .x .x2 + BitVec.ofNat _ 0)
    refine WP.of_runBlock ⟨s₂', by
      rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
        exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_addImm_x (by decide),
        runStep_some, runBlock_nil], ?_⟩
    have g₂ : ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s₂'.gpr r = s.gpr r := by
      intro r a b c e; simp [s₂', s₂, gpr_write, b, c, e]; exact g₁ r a
    have pre₁ : CopyPre T B m s₂' := by
      refine ⟨fun i hi => ?_, fun i hi => scrIn i (by omega), dataSep, by omega⟩
      obtain ⟨r, hr, hc⟩ := dataW i hi
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    have inv₁ : CopyInv T B m s₂' 0 s₂' := by
      refine ⟨by omega, ?_, ?_, ?_, fun j hj => by omega, Frame.refl _ _, fun _ _ => rfl, rfl, rfl,
        rfl, rfl⟩
      · rw [wAt_zero]; simp [s₂', s₂, gpr_write, State.read]; exact hx1
      · rw [wAt_zero]; simp [s₂', s₂, gpr_write, State.read]; exact (g₁ _ (by decide)).trans hx3
      · simp [s₂', s₂, gpr_write, State.read]; rw [g₁ _ (by decide), h.x2]
    apply WP.seq
    apply WP.mono (copy_ok pre₁ s₂' 0 inv₁)
    intro s₃ c₃
    have g₃ : ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s₃.gpr r = s.gpr r :=
      fun r a b c e => (c₃.regs r ⟨a, b, c, e⟩).trans (g₂ r a b c e)
    -- x4 := x3
    let s₄ := s₃.write .x .x4 (s₃.read .x .x3 + BitVec.ofNat _ 0)
    refine WP.of_runBlock ⟨s₄, by rw [runBlock_cons, exec_addImm_x (by decide), runStep_some,
      runBlock_nil], ?_⟩
    have g₄ : ∀ r, r ≠ .x4 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s₄.gpr r = s.gpr r := by
      intro r a b c e f; simp only [s₄, State.write, a, ite_false]; exact g₃ r b c e f
    have x4₄ : s₄.gpr .x4 = B := by
      simp [s₄, gpr_write, State.read]
      exact (g₃ _ (by decide) (by decide) (by decide) (by decide)).trans hx3
    have wr₄ : s₄.wr = s.wr := c₃.wr
    have room₄ : Room s₄ := Ok.of_off (off := 0) (by rw [wr₄]; exact scrR)
      (by show s₄.gpr .x4 = _; rw [x4₄]; simp [B]) (by show 0 + 16 * 64 ≤ 1024; decide)
      (by show 1024 < 2 ^ 64; decide)
    have st₄ : stateR s₄ = ⟨B, 1024⟩ := by simp only [stateR, x4₄]
    have x0₄ : s₄.gpr .x0 = S :=
      (g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx0
    have S₄ : Sched s₄ := by
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [x0₄]
        show InRegions (s₃.rd ++ s₃.wr) _ 8
        rw [c₃.rd, c₃.wr]
        show InRegions (s.rd ++ s.wr) _ 8
        rw [h.rd, h.wr]; exact E.keyIn i hi
      · rw [x0₄, st₄]; exact keyB
    apply WP.seq
    apply WP.mono (batch_ok d room₄ S₄)
    intro s₅ q₅
    have g₅ : ∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x7 → r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 →
        r ≠ .x13 → s₅.gpr r = s.gpr r :=
      fun r a b c e f i j l => (q₅.gpr r b c e f).trans (g₄ r a f i j l)
    apply WP.seq
    let s₆ := s₅.write .x .x10 (s₅.read .x .x2 >>> 7)
    refine WP.of_runBlock ⟨s₆, by rw [runBlock_cons, wholeLeft, exec_lsr_x (by decide), runStep_some,
      runBlock_nil], ?_⟩
    have x2₅ : s₅.gpr .x2 = BitVec.ofNat 64 m :=
      (g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans h.x2
    have x10₆ : s₆.gpr .x10 = BitVec.ofNat 64 (m / 128) := by
      simp only [s₆, State.write, State.read, BitVec.setWidth_eq, ite_true]
      rw [x2₅, lsr7 _ (by omega)]
    have g₆ : ∀ r, r ≠ .x10 → s₆.gpr r = s₅.gpr r := fun r hr => by simp [s₆, State.write, hr]
    apply WP.ite _ (eval_zero s₆ .x10 x10₆ (by omega))
    swap
    · intro hnz; simp at hnz; omega
    intro _
    unfold tailOut
    apply WP.seq
    -- x11 := x3, x12 := x1, x13 := x2
    let s₇ := ((s₆.write .x .x11 (s₆.read .x .x3 + BitVec.ofNat _ 0)).write .x .x12
      ((s₆.write .x .x11 (s₆.read .x .x3 + BitVec.ofNat _ 0)).read .x .x1 + BitVec.ofNat _ 0))
    let s₇' := s₇.write .x .x13 (s₇.read .x .x2 + BitVec.ofNat _ 0)
    refine WP.of_runBlock ⟨s₇', by
      rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
        exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_addImm_x (by decide),
        runStep_some, runBlock_nil], ?_⟩
    have r₆ : ∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x7 → r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 →
        r ≠ .x13 → s₆.gpr r = s.gpr r :=
      fun r a b c e f i j l => (g₆ r f).trans (g₅ r a b c e f i j l)
    have wr₇ : s₇'.wr = s.wr := q₅.wr.trans wr₄
    have rd₇ : s₇'.rd = s.rd := q₅.rd.trans (c₃.rd)
    have pre₂ : CopyPre B T m s₇' := by
      refine ⟨fun i hi => ?_, fun i hi => ?_, dataSep.symm, by omega⟩
      · obtain ⟨r, hr, hc⟩ := scrIn i (by omega)
        rw [wr₇]; exact ⟨r, List.mem_append_right _ hr, hc⟩
      · rw [wr₇]; exact dataW i hi
    have inv₂ : CopyInv B T m s₇' 0 s₇' := by
      refine ⟨by omega, ?_, ?_, ?_, fun j hj => by omega, Frame.refl _ _, fun _ _ => rfl, rfl, rfl,
        rfl, rfl⟩
      · rw [wAt_zero]; simp [s₇', s₇, gpr_write, State.read]
        exact (r₆ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)).trans hx3
      · rw [wAt_zero]; simp [s₇', s₇, gpr_write, State.read]
        exact (r₆ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)).trans ((g₁ _ (by decide)).symm.trans hx1)
      · simp [s₇', s₇, gpr_write, State.read]
        rw [r₆ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h.x2]
    apply WP.seq
    apply WP.mono (copy_ok pre₂ s₇' 0 inv₂)
    intro s₈ c₈
    -- x2 := 0
    let s₉ := s₈.write .x .x2 ((0 : BitVec 16).setWidth 64)
    refine WP.of_runBlock ⟨s₉, by rw [runBlock_cons, exec_movz_x, runStep_some, runBlock_nil], ?_⟩
    left
    refine ⟨eval_nonzero s₉ .x2 (m := 0) (by simp [s₉, State.write]) (by decide), fun b hb => ?_⟩
    have m₉ : s₉.mem = s₈.mem := rfl
    have m₄ : s₄.mem = s₃.mem := rfl
    have m₇ : s₇'.mem = s₆.mem := rfl
    have m₆ : s₆.mem = s₅.mem := rfl
    have m₂ : s₂'.mem = s₁.mem := rfl
    have m₁ : s₁.mem = s.mem := rfl
    show blockAt s₉.mem (wAt D b) = blockOut (scheduleAt s₀.mem S) d (blockAt s₀.mem (wAt D b))
    rw [m₉]
    by_cases hb' : b < n - m
    · -- a block done before: untouched since
      rw [← h.done b hb']
      have f₃ : Frame [⟨B, 8 * m⟩] s.mem s₃.mem := by rw [← m₁, ← m₂]; exact c₃.frame
      have f₅ : Frame [⟨B, 1024⟩] s₃.mem s₅.mem := by rw [← m₄, ← st₄]; exact q₅.frame
      have f₈ : Frame [⟨T, 8 * m⟩] s₅.mem s₈.mem := by rw [← m₆, ← m₇]; exact c₈.frame
      have hT : (⟨wAt D b, 8⟩ : Region).Disjoint ⟨T, 8 * m⟩ :=
        Offset.disjoint D (Or.inl (by omega)) (by omega) (by omega)
      have hS : (⟨wAt D b, 8⟩ : Region).Disjoint ⟨B, 1024⟩ :=
        dataB.sub_left (Offset.sub_base _ (by omega))
      rw [blockAt_frame f₈ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hT),
        blockAt_frame f₅ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hS),
        blockAt_frame f₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hS.sub_right (Region.sub_prefix (by omega)))]
    · obtain ⟨j, rfl⟩ : ∃ j, b = n - m + j := ⟨b - (n - m), by omega⟩
      have hj : j < m := by omega
      -- the block in the data, from the scratch buffer after the batch
      have e₈ : blockAt s₈.mem (wAt D (n - m + j)) = blockAt s₅.mem (wAt B j) := by
        rw [← wAt_wAt, ← m₆, ← m₇]; exact blockAt_eq_of_readW (c₈.copied j hj)
      -- the block in the scratch buffer before the batch, from the data
      have e₃ : blockAt s₃.mem (wAt B j) = blockAt s.mem (wAt D (n - m + j)) := by
        rw [← wAt_wAt, ← m₁, ← m₂]; exact blockAt_eq_of_readW (c₃.copied j hj)
      have K₃ : scheduleAt s₃.mem S = scheduleAt s.mem S := by
        rw [← m₁, ← m₂]
        exact VG.Proof.TripleDes.scheduleAt_eq_of_frame S c₃.frame fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact keyB.sub_right (Region.sub_prefix (by omega))
      have o := q₅.out j (by omega)
      rw [x4₄, x0₄, m₄, e₃, K₃, hK, hB j hj] at o
      rw [e₈, o]
  · -- the next 128 blocks, in place
    intro hnz
    have hm : 128 ≤ m := by simp at hnz; omega
    let s₂ := s₁.write .x .x4 (s₁.read .x .x1 + BitVec.ofNat _ 0)
    refine WP.of_runBlock ⟨s₂, by rw [runBlock_cons, exec_addImm_x (by decide), runStep_some,
      runBlock_nil], ?_⟩
    have g₂ : ∀ r, r ≠ .x4 → r ≠ .x10 → s₂.gpr r = s.gpr r := fun r a b => by
      simp only [s₂, State.write, a, ite_false]; exact g₁ r b
    have x4₂ : s₂.gpr .x4 = wAt D (n - m) := by
      simp [s₂, State.write, State.read]; exact (g₁ _ (by decide)).trans h.x1
    have room₂ : Room s₂ := Ok.of_off (off := 8 * (n - m)) (show _ ∈ s.wr from dataR)
      (by show s₂.gpr .x4 = _; rw [x4₂]) (by show 8 * (n - m) + 16 * 64 ≤ 8 * n; omega) (by omega)
    have st₂ : stateR s₂ = ⟨wAt D (n - m), 1024⟩ := by simp only [stateR, x4₂]
    have stSub : Region.Sub (stateR s₂) ⟨D, 8 * n⟩ := by
      rw [st₂]; exact Offset.sub_base _ (by omega)
    have x0₂ : s₂.gpr .x0 = S := (g₂ _ (by decide) (by decide)).trans hx0
    have S₂ : Sched s₂ := by
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [x0₂]
        show InRegions (s.rd ++ s.wr) _ 8
        rw [h.rd, h.wr]; exact E.keyIn i hi
      · rw [x0₂]; exact keyData.sub_right stSub
    apply WP.seq
    apply WP.mono (batch_ok d room₂ S₂)
    intro s₃ q₃
    have g₃ : ∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x7 → r ≠ .x9 → r ≠ .x10 → s₃.gpr r = s.gpr r :=
      fun r a b c e f => (q₃.gpr r b c e f).trans (g₂ r a f)
    have x2₃ : s₃.gpr .x2 = BitVec.ofNat 64 m :=
      (g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.x2
    apply WP.seq
    let s₄ := s₃.write .x .x10 (s₃.read .x .x2 >>> 7)
    refine WP.of_runBlock ⟨s₄, by rw [runBlock_cons, wholeLeft, exec_lsr_x (by decide), runStep_some,
      runBlock_nil], ?_⟩
    have x10₄ : s₄.gpr .x10 = BitVec.ofNat 64 (m / 128) := by
      simp only [s₄, State.write, State.read, BitVec.setWidth_eq, ite_true]
      rw [x2₃, lsr7 _ (by omega)]
    have g₄ : ∀ r, r ≠ .x10 → s₄.gpr r = s₃.gpr r := fun r hr => by simp [s₄, State.write, hr]
    apply WP.ite _ (eval_zero s₄ .x10 x10₄ (by omega))
    · intro hz; simp at hz; omega
    intro _
    let s₅ := s₄.write .x .x1 (s₄.read .x .x1 + BitVec.ofNat _ 1024)
    let s₆ := s₅.write .x .x2 (s₅.read .x .x2 - BitVec.ofNat _ 128)
    refine WP.of_runBlock ⟨s₆, by
      rw [wideOut, runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
        exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
    have r₄ : ∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x7 → r ≠ .x9 → r ≠ .x10 → s₄.gpr r = s.gpr r :=
      fun r a b c e f => (g₄ r f).trans (g₃ r a b c e f)
    have x2₆ : s₆.gpr .x2 = BitVec.ofNat 64 (m - 128) := by
      simp only [s₆, s₅, State.write, State.read, BitVec.setWidth_eq, reduceCtorEq, ite_false,
        ite_true]
      rw [r₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x2,
        BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) hm]
    have x1₆ : s₆.gpr .x1 = wAt D (n - (m - 128)) := by
      simp only [s₆, s₅, State.write, State.read, BitVec.setWidth_eq, reduceCtorEq, ite_false,
        ite_true]
      rw [r₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x1, wAt,
        BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact congrArg (fun i => D + BitVec.ofNat 64 i) (by omega)
    have g₆ : ∀ r, EcbRegs r → s₆.gpr r = s₀.gpr r := by
      intro r hr
      have ⟨a, b, c, e, f, i, j, _, _, _⟩ := hr
      simp only [s₆, s₅, State.write, b, a, ite_false]
      rw [r₄ r c e f i j, g r hr]
    have mem₆ : s₆.mem = s₃.mem := rfl
    have frame' : Frame [⟨D, 8 * (n - (m - 128))⟩, ⟨B, 1024⟩] s₀.mem s₆.mem := by
      have f₁ : Frame [⟨D, 8 * (n - (m - 128))⟩, ⟨B, 1024⟩] s₀.mem s.mem := h.frame.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by omega)⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      have f₂ : Frame [⟨D, 8 * (n - (m - 128))⟩, ⟨B, 1024⟩] s.mem s₃.mem := q₃.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self, by rw [st₂]; exact Offset.sub_base _ (by omega)⟩
      rw [mem₆]; exact f₁.trans f₂
    have done' : ∀ b < n - (m - 128), blockAt s₆.mem (wAt D b) =
        blockOut (scheduleAt s₀.mem S) d (blockAt s₀.mem (wAt D b)) := by
      intro b hb
      rw [mem₆]
      by_cases hb' : b < n - m
      · rw [← h.done b hb']
        refine blockAt_frame q₃.frame fun r hr => ?_
        simp only [List.mem_singleton] at hr; subst hr
        rw [st₂]
        exact Offset.disjoint D (Or.inl (by omega)) (by omega) (by omega)
      · obtain ⟨j, rfl⟩ : ∃ j, b = n - m + j := ⟨b - (n - m), by omega⟩
        have e := q₃.out j (by omega)
        rw [x4₂, wAt_wAt, x0₂] at e
        rw [e]
        show blockOut (scheduleAt s.mem S) d (blockAt s.mem _) = _
        rw [hK, hB j (by omega)]
    have wr₆ : s₆.wr = s₀.wr := q₃.wr.trans h.wr
    have rd₆ : s₆.rd = s₀.rd := q₃.rd.trans h.rd
    have sp₆ : s₆.sp = s₀.sp := q₃.sp.trans h.sp
    have flag := eval_nonzero s₆ .x2 x2₆ (by omega)
    by_cases hend : m - 128 = 0
    · left
      refine ⟨by rw [flag]; simp [hend], fun b hb => done' b (by omega)⟩
    · right
      refine ⟨by rw [flag]; simp [hend], m - 128, by omega,
        ⟨by omega, by omega, by have := h.mod; omega, x2₆, x1₆, g₆, rd₆, wr₆, sp₆, done', frame'⟩⟩

/-- Every block becomes its encryption or decryption. -/
theorem ecb_correct (d : Direction) {s : State} (E : Env s) :
    WP isa (ecb d) s (fun s' => ∀ b < (s.gpr .x2).toNat, blockAt s'.mem (wAt (s.gpr .x1) b) =
      blockOut (scheduleAt s.mem (s.gpr .x0)) d (blockAt s.mem (wAt (s.gpr .x1) b))) := by
  let n := (s.gpr .x2).toNat
  have hl := E.len
  have hx2 : s.gpr .x2 = BitVec.ofNat 64 n := by simp [n]
  rw [Impl.TripleDes.AArch64.BitsliceNeon.ecb]
  apply WP.ite _ (eval_zero s .x2 hx2 (by omega))
  · intro hz
    apply WP.block_nil
    intro b hb
    simp at hz
    omega
  · intro hnz
    have hn0 : 0 < n := by simp at hnz; omega
    refine WP.loop (M := isa) (EcbInv d s n) (fun m s' h => step_ok d E rfl m s' h) n s ?_
    exact ⟨hn0, Nat.le_refl _, rfl, hx2, by simp [wAt], fun _ _ => rfl, rfl, rfl, rfl,
      fun b hb => by omega, by rw [Nat.sub_self]; exact Frame.refl _ _⟩

end VG.Proof.TripleDes.AArch64.BitslicedNeon
