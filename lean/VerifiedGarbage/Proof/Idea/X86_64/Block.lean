import VerifiedGarbage.Proof.Idea.X86_64.Round
import VerifiedGarbage.Proof.Idea.Memory

/-!
# IDEA on x86-64: a block

`cryptBlock_run`: `Impl.Idea.X86_64.cryptBlock` replaces the block at `rsi`
with `Spec.Idea.cryptBlock` of it under the subkeys at `rdi`: the block's
words are loaded a byte at a time (`load_run`), run through the rounds
(`rounds_run`) and the output transformation (`output_run`), and stored a
byte at a time (`store_run`).
-/

namespace VG.Proof.Idea.X86_64

open VG VG.X86_64 VG.Impl.Idea.X86_64

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, at_, ofInt_natCast]

/-! ## Loading -/

theorem loadWord_run {r : Reg} (hr : r ≠ .rax) (hs : r ≠ .rsi) (k : Nat) (s : State) {a : Addr}
    (ha : s.gpr .rsi = a)
    (h0 : InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 (2 * k)) 1)
    (h1 : InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 (2 * k + 1)) 1) :
    ∃ s', runBlock isa (loadWord r k) s = some s' ∧
      s'.gpr r = (s.mem (a + BitVec.ofNat 64 (2 * k)) ++ s.mem (a + BitVec.ofNat 64 (2 * k + 1))).setWidth 64 ∧
      Keep [.rax, r] s s' := by
  simp only [loadWord, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execShift, readSrc,
    State.load8, isa, Option.map_some, Option.bind_some, ea_at, ha, h0, h1, ↓reduceIte,
    RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setFlags, RegUpd.rd_setFlags,
    RegUpd.wr_setFlags, hr, hs.symm, Nat.reduceLeDiff, and_self,
    Option.some.injEq, exists_eq_left']
  refine ⟨bytes16 _ _, keep_reg_of (fun q hq => ?_) rfl rfl rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hq.1, hq.2, ite_false]

/-- The bytes of the block at `a` can be read. -/
def BlockRead (s : State) (a : Addr) : Prop :=
  ∀ i < 8, InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 i) 1

theorem BlockRead.keep {rs : List Reg} {s s' : State} {a : Addr} (h : BlockRead s a)
    (hk : Keep rs s s') : BlockRead s' a := by
  intro i hi; rw [hk.rd, hk.wr]; exact h i hi

theorem load_run (s : State) {a : Addr} (ha : s.gpr .rsi = a) (hb : BlockRead s a) :
    ∃ s', runBlock isa load s = some s' ∧
      Holds (Spec.Idea.decodeBlock (Spec.Idea.blockAt s.mem a)) s' ∧
      Keep [.rax, .r8, .r9, .r10, .r11] s s' := by
  have w (k : Nat) (hk : k < 4) := decodeBlock_blockAt s.mem a hk
  obtain ⟨s₁, h₁, v₁, e₁⟩ := loadWord_run (r := .r8) (by decide) (by decide) 0 s ha (hb _ (by decide)) (hb _ (by decide))
  obtain ⟨s₂, h₂, v₂, e₂⟩ := loadWord_run (r := .r9) (by decide) (by decide) 1 s₁
    ((e₁.reg .rsi (by decide)).trans ha) ((hb.keep e₁) _ (by decide)) ((hb.keep e₁) _ (by decide))
  obtain ⟨s₃, h₃, v₃, e₃⟩ := loadWord_run (r := .r10) (by decide) (by decide) 2 s₂
    ((e₂.reg .rsi (by decide)).trans ((e₁.reg .rsi (by decide)).trans ha))
    ((hb.keep e₁ |>.keep e₂) _ (by decide)) ((hb.keep e₁ |>.keep e₂) _ (by decide))
  obtain ⟨s₄, h₄, v₄, e₄⟩ := loadWord_run (r := .r11) (by decide) (by decide) 3 s₃
    ((e₃.reg .rsi (by decide)).trans ((e₂.reg .rsi (by decide)).trans ((e₁.reg .rsi (by decide)).trans ha)))
    ((hb.keep e₁ |>.keep e₂ |>.keep e₃) _ (by decide)) ((hb.keep e₁ |>.keep e₂ |>.keep e₃) _ (by decide))
  refine ⟨s₄, run_append (run_append (run_append h₁ h₂) h₃) h₄, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [e₄.reg .r8 (by decide), e₃.reg .r8 (by decide), e₂.reg .r8 (by decide), v₁, w 0 (by decide)]
  · rw [e₄.reg .r9 (by decide), e₃.reg .r9 (by decide), v₂, e₁.mem, w 1 (by decide)]
  · rw [e₄.reg .r10 (by decide), v₃, e₂.mem, e₁.mem, w 2 (by decide)]
  · rw [v₄, e₃.mem, e₂.mem, e₁.mem, w 3 (by decide)]
  · exact (e₁.mono (by decide)).trans ((e₂.mono (by decide)).trans ((e₃.mono (by decide)).trans
      (e₄.mono (by decide))))

/-! ## The rounds -/

theorem rounds_run (z : Spec.Idea.Schedule) (x : Spec.Idea.State) :
    ∀ n ≤ 8, ∀ s : State, Holds x s → KeyOk z s →
      ∃ s', runBlock isa ((List.range n).flatMap round) s = some s' ∧
        Holds (roundsSpec z n x) s' ∧ Keep roundWrites s s'
  | 0, _, s, hx, _ => ⟨s, by simp [runBlock_nil], hx, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | n + 1, hn, s, hx, hk => by
    obtain ⟨s₁, h₁, x₁, e₁⟩ := rounds_run z x n (by omega) s hx hk
    obtain ⟨s₂, h₂, x₂, e₂⟩ := round_run n (by omega) z _ s₁ x₁ (hk.keep e₁ (by decide))
    refine ⟨s₂, ?_, ?_, e₁.trans e₂⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact run_append h₁ h₂
    · simp only [roundsSpec, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact x₂

/-! ## The output transformation -/

/-- The output words: `Y₁` in `r8`, `Y₂` in `r10`, `Y₃` in `r9`, `Y₄` in `r11`. -/
structure OutHolds (y : Spec.Idea.State) (s : State) : Prop where
  r8 : s.gpr .r8 = (y.getD 0 0).setWidth 64
  r10 : s.gpr .r10 = (y.getD 1 0).setWidth 64
  r9 : s.gpr .r9 = (y.getD 2 0).setWidth 64
  r11 : s.gpr .r11 = (y.getD 3 0).setWidth 64

theorem out1_run (s : State) (hk : InRegions (s.rd ++ s.wr) (s.ea (at_ .rdi 96)) 8) :
    ∃ s', runBlock isa [.mov .rax (.reg .r11), .mov .rdx (.mem (at_ .rdi 96)), .shift .shr .rdx 48] s =
        some s' ∧
      s'.gpr .rax = s.gpr .r11 ∧ s'.gpr .rdx = s.mem.readW (s.ea (at_ .rdi 96)) 64 >>> 48 ∧
      Keep [.rax, .rdx] s s' := by
  simp only [State.ea, at_] at hk ⊢
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execShift, readSrc, State.load64,
    isa, Option.map_some, State.ea, hk, ↓reduceIte, Nat.reduceLeDiff, and_self,
    RegUpd.gpr_setReg, RegUpd.gpr_setFlags, reduceCtorEq, Option.some.injEq, exists_eq_left',
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, true_and]
  refine keep_reg_of (fun q hq => ?_) rfl rfl rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hq.1, hq.2, ite_false]

theorem out2_run (s : State) (hk : InRegions (s.rd ++ s.wr) (s.ea (at_ .rdi 96)) 8) :
    ∃ s', runBlock isa [.mov .r11 (.reg .rdx),
        .mov .rdx (.mem (at_ .rdi 96)), .shift .shr .rdx 16, .alu .add .r10 (.reg .rdx),
        .alu .and .r10 (.imm 0xffff),
        .mov .rdx (.mem (at_ .rdi 96)), .shift .shr .rdx 32, .alu .add .r9 (.reg .rdx),
        .alu .and .r9 (.imm 0xffff)] s = some s' ∧
      s'.gpr .r11 = s.gpr .rdx ∧
      s'.gpr .r10 = (s.gpr .r10 + (s.mem.readW (s.ea (at_ .rdi 96)) 64 >>> 16)) &&& 65535 ∧
      s'.gpr .r9 = (s.gpr .r9 + (s.mem.readW (s.ea (at_ .rdi 96)) 64 >>> 32)) &&& 65535 ∧
      Keep [.rdx, .r9, .r10, .r11] s s' := by
  simp only [State.ea, at_] at hk ⊢
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execShift, readSrc,
    State.load64, isa, Option.map_some, Option.bind_some, State.ea, hk, ↓reduceIte,
    Nat.reduceLeDiff, and_self, signExtend_mask,
    RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, reduceCtorEq, Option.some.injEq,
    exists_eq_left', RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setFlags,
    RegUpd.rd_setFlags, RegUpd.wr_setFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, true_and]
  refine keep_reg_of (fun q hq => ?_) rfl rfl rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hq.1, hq.2.1, hq.2.2.1,
    hq.2.2.2, ite_false]

theorem output_run (z : Spec.Idea.Schedule) (x : Spec.Idea.State) (s : State) (hx : Holds x s)
    (hk : KeyOk z s) :
    ∃ s', runBlock isa output s = some s' ∧
      OutHolds (Spec.Idea.output (z.getD 48 0) (z.getD 49 0) (z.getD 50 0) (z.getD 51 0) x) s' ∧
      Keep roundWrites s s' := by
  have k48 := hk.low 48 (by decide)
  simp only [Nat.reduceMul] at k48
  obtain ⟨s₁, h₁, v₁, e₁⟩ := mulKey_run .r8 96 s k48.1
  rw [hx.r8, setWidth_setWidth16, k48.2] at v₁
  have hk₁ := hk.keep e₁ (by decide)
  have k₁ := hk₁.low 48 (by decide)
  simp only [Nat.reduceMul] at k₁
  obtain ⟨s₂, h₂, a₂, d₂, e₂⟩ := out1_run s₁ k₁.1
  obtain ⟨s₃, h₃, v₃, e₃⟩ := mul_run s₂
  have hk₃ := (hk₁.keep e₂ (by decide)).keep e₃ (by decide)
  have k₃ := hk₃.low 48 (by decide)
  simp only [Nat.reduceMul] at k₃
  obtain ⟨s₄, h₄, r11₄, r10₄, r9₄, e₄⟩ := out2_run s₃ k₃.1
  have l1 := hk₃.last 1 (by decide)
  have l2 := hk₃.last 2 (by decide)
  have l3 := hk₁.last 3 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at l1 l2 l3
  refine ⟨s₄, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [output]
    exact run_append (run_append (run_append h₁ h₂) h₃) h₄
  · rw [e₄.reg .r8 (by decide), e₃.reg .r8 (by decide), e₂.reg .r8 (by decide), v₁, output_getD0]
  · rw [r10₄, e₃.reg .r10 (by decide), e₂.reg .r10 (by decide), e₁.reg .r10 (by decide), hx.r10,
      add_mask, l1, output_getD1]
  · rw [r9₄, e₃.reg .r9 (by decide), e₂.reg .r9 (by decide), e₁.reg .r9 (by decide), hx.r9,
      add_mask, l2, output_getD2]
  · rw [r11₄, v₃, a₂, d₂, e₁.reg .r11 (by decide), hx.r11, setWidth_setWidth16, l3, output_getD3]
  · exact (e₁.weaken (by decide)).trans ((e₂.weaken (by decide)).trans ((e₃.weaken (by decide)).trans
      (e₄.weaken (by decide))))

/-! ## Storing -/

theorem storeWord_run (r : Reg) (k : Nat) (s : State) {a : Addr}
    (ha : s.gpr .rsi = a)
    (h1 : InRegions s.wr (a + BitVec.ofNat 64 (2 * k + 1)) 1)
    (h0 : InRegions s.wr (a + BitVec.ofNat 64 (2 * k)) 1) :
    ∃ s', runBlock isa (storeWord r k) s = some s' ∧
      s'.mem = (s.mem.writeW (a + BitVec.ofNat 64 (2 * k + 1)) ((s.gpr r).setWidth 8)).writeW
        (a + BitVec.ofNat 64 (2 * k)) ((s.gpr r >>> 8).setWidth 8) ∧
      (∀ q, q ≠ .rax → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [storeWord, runBlock_cons, runStep_some, runBlock_nil, exec, execShift, readSrc,
    State.store8, isa, Option.map_some, ea_at, ha, h0, h1, ↓reduceIte,
    RegUpd.gpr_setReg, RegUpd.gpr_setFlags, Nat.reduceLeDiff, and_self, reduceCtorEq,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setFlags, RegUpd.rd_setFlags,
    RegUpd.wr_setFlags, Option.some.injEq, exists_eq_left', true_and]
  exact ⟨fun q hq => by simp only [hq, ite_false], trivial⟩

/-- The bytes of the block at `a` can be written. -/
def BlockWrite (s : State) (a : Addr) : Prop :=
  ∀ i < 8, InRegions s.wr (a + BitVec.ofNat 64 i) 1

theorem frame_write8 {a : Addr} {m m' : Mem} {j : Nat} (v : BitVec 8) (hj : j < 8)
    (h : Frame [⟨a, 8⟩] m m') : Frame [⟨a, 8⟩] m (m'.writeW (a + BitVec.ofNat 64 j) v) :=
  h.writeW (List.mem_singleton_self _) v (Offset.contains_base a (by omega) (by omega))

theorem store_run (y : Spec.Idea.State) (s : State) {a : Addr} (ha : s.gpr .rsi = a)
    (hw : BlockWrite s a) (hy : OutHolds y s) :
    ∃ s', runBlock isa store s = some s' ∧
      Spec.Idea.blockAt s'.mem a = Spec.Idea.encodeBlock y ∧
      Frame [⟨a, 8⟩] s.mem s'.mem ∧ (∀ q, q ≠ .rax → s'.gpr q = s.gpr q) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, h₁, m₁, g₁, rd₁, wr₁⟩ := storeWord_run .r8 0 s ha (hw _ (by decide)) (hw _ (by decide))
  have ha₁ : s₁.gpr .rsi = a := (g₁ .rsi (by decide)).trans ha
  have hw₁ : BlockWrite s₁ a := fun i hi => wr₁ ▸ hw i hi
  obtain ⟨s₂, h₂, m₂, g₂, rd₂, wr₂⟩ := storeWord_run .r10 1 s₁ ha₁ (hw₁ _ (by decide)) (hw₁ _ (by decide))
  have ha₂ : s₂.gpr .rsi = a := (g₂ .rsi (by decide)).trans ha₁
  have hw₂ : BlockWrite s₂ a := fun i hi => wr₂ ▸ hw₁ i hi
  obtain ⟨s₃, h₃, m₃, g₃, rd₃, wr₃⟩ := storeWord_run .r9 2 s₂ ha₂ (hw₂ _ (by decide)) (hw₂ _ (by decide))
  have ha₃ : s₃.gpr .rsi = a := (g₃ .rsi (by decide)).trans ha₂
  have hw₃ : BlockWrite s₃ a := fun i hi => wr₃ ▸ hw₂ i hi
  obtain ⟨s₄, h₄, m₄, g₄, rd₄, wr₄⟩ := storeWord_run .r11 3 s₃ ha₃ (hw₃ _ (by decide)) (hw₃ _ (by decide))
  have v10 : s₁.gpr .r10 = (y.getD 1 0).setWidth 64 := (g₁ .r10 (by decide)).trans hy.r10
  have v9 : s₂.gpr .r9 = (y.getD 2 0).setWidth 64 :=
    (g₂ .r9 (by decide)).trans ((g₁ .r9 (by decide)).trans hy.r9)
  have v11 : s₃.gpr .r11 = (y.getD 3 0).setWidth 64 :=
    (g₃ .r11 (by decide)).trans ((g₂ .r11 (by decide)).trans ((g₁ .r11 (by decide)).trans hy.r11))
  rw [v11] at m₄
  rw [v9] at m₃
  rw [v10] at m₂
  rw [hy.r8] at m₁
  rw [m₃, m₂, m₁] at m₄
  refine ⟨s₄, run_append (run_append (run_append h₁ h₂) h₃) h₄, ?_, ?_,
    fun q hq => (g₄ q hq).trans ((g₃ q hq).trans ((g₂ q hq).trans (g₁ q hq))),
    rd₄.trans (rd₃.trans (rd₂.trans rd₁)), wr₄.trans (wr₃.trans (wr₂.trans wr₁))⟩
  · apply Vector.ext
    intro i hi
    simp only [Spec.Idea.blockAt, Vector.getElem_ofFn, m₄, encodeBlock_get _ hi]
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨
        i = 5 ∨ i = 6 ∨ i = 7 := by omega
    all_goals simp (disch := decide) only [write8_apply, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv,
      Nat.reduceMod, Nat.reduceSub, Nat.reduceEqDiff, ↓reduceIte, lo8, hi8, BitVec.ushiftRight_zero]
  · rw [m₄]
    repeat' apply frame_write8 _ (by decide)
    exact Frame.refl _ _

/-! ## A block -/

theorem cryptBlock_run (z : Spec.Idea.Schedule) (s : State) {a : Addr} (ha : s.gpr .rsi = a)
    (hb : BlockRead s a) (hw : BlockWrite s a) (hk : KeyOk z s) :
    ∃ s', runBlock isa cryptBlock s = some s' ∧
      Spec.Idea.blockAt s'.mem a = Spec.Idea.cryptBlock z (Spec.Idea.blockAt s.mem a) ∧
      Frame [⟨a, 8⟩] s.mem s'.mem ∧ (∀ q, q ∉ roundWrites → s'.gpr q = s.gpr q) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, h₁, x₁, e₁⟩ := load_run s ha hb
  have k₁ := hk.keep e₁ (by decide)
  obtain ⟨s₂, h₂, x₂, e₂⟩ := rounds_run z _ 8 (by decide) s₁ x₁ k₁
  obtain ⟨s₃, h₃, x₃, e₃⟩ := output_run z _ s₂ x₂ (k₁.keep e₂ (by decide))
  have e₁₃ := ((e₁.weaken (by decide)).trans e₂).trans e₃
  obtain ⟨s₄, h₄, b₄, f₄, g₄, rd₄, wr₄⟩ := store_run _ s₃ ((e₁₃.reg .rsi (by decide)).trans ha)
    (fun i hi => e₁₃.wr ▸ hw i hi) x₃
  refine ⟨s₄, ?_, ?_, ?_, fun q hq => ?_, rd₄.trans e₁₃.rd, wr₄.trans e₁₃.wr⟩
  · simp only [cryptBlock]
    exact run_append (run_append (run_append h₁ h₂) h₃) h₄
  · rw [b₄, Spec.Idea.cryptBlock, crypt_eq]
  · rw [← e₁₃.mem]; exact f₄
  · rw [g₄ q (by intro h; subst h; exact hq (by decide)), e₁₃.reg q hq]

end VG.Proof.Idea.X86_64
