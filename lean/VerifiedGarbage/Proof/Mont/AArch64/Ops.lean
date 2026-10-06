import VerifiedGarbage.Proof.Mont.AArch64.Chain

/-!
# Montgomery arithmetic on AArch64: the operations

For a modulus `m` in the working space (`ModOk`), at offsets that are
multiples of 8 (`ModA`): `mul o a b` writes `[a] [b] R⁻¹ mod m` to `[o]`
(`mul_ok`), `add` writes `[a] + [b] mod m` (`add_ok`) and `sub` writes
`[a] - [b] mod m` (`sub_ok`), for `[a]`, `[b]` below `m`. Each changes only
the registers `clob n`, the result and the temporary area (`OpKeep`).
-/

namespace VG.Proof.Mont.AArch64

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Proof.Ed25519 (Word64.addCarry Word64.carryOut Word64.addCarry_value Word64.borrow_mask)

/-- The registers the operations change: for `n > 7`, `dRegs n`'s
callee-saved registers too. -/
def clob (n : Nat) : List Reg := [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x16, .x17] ++ acc n ++ (dRegs n).drop 7 ++ (if n = 4 then [.x14,.x15] else [])

/-- Every register the operations may change, for any number of words. -/
abbrev clobAll : List Reg := [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x16, .x17, .x8, .x9, .x10, .x11,
  .x12, .x13, .x14, .x15, .x21, .x22, .x23, .x24, .x25]

theorem mem_clobAll {n : Nat} {r : Reg} (h : r ∈ clob n) : r ∈ clobAll := by
  unfold clob acc dRegs at h
  simp only [List.mem_append] at h
  rcases h with ((h | h) | h) | h
  · revert r; decide
  · exact (by decide : ∀ r ∈ [Reg.x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x21, .x22, .x23],
      r ∈ clobAll) r (List.mem_of_mem_take h)
  · exact (by decide : ∀ r ∈ [Reg.x1, .x3, .x4, .x5, .x6, .x16, .x17, .x24, .x25], r ∈ clobAll) r
      (List.mem_of_mem_take (List.mem_of_mem_drop h))
  · split at h
    · exact (by decide : ∀ r ∈ [Reg.x14,.x15], r ∈ clobAll) r h
    · simp only [List.not_mem_nil] at h

/-- The modulus and the temporary area at offsets that loads and stores can
encode. -/
structure ModA (M : Mod) : Prop where
  mo : M.mo % 8 = 0
  tmp : M.tmp % 8 = 0

/-- What an operation writing `[o]` keeps: the registers but `clob`, the
regions and the stack pointer, and the memory but `[o]` and the temporary
area. -/
structure OpKeep (M : Mod) (base : Addr) (o : Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clob M.n → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  mem : ∀ x, (ofs base x < o ∨ o + 8 * M.n ≤ ofs base x) →
    (ofs base x < M.tmp ∨ M.tmp + 8 * M.n ≤ ofs base x) → s'.mem x = s.mem x

theorem x0_not_clob (n : Nat) : Reg.x0 ∉ clob n := fun h => absurd (mem_clobAll h) (by decide)

theorem acc_not_x7 (n : Nat) (hn : n < 10) : ∀ r ∈ acc n, r ∉ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6,
    .x7, .x16, .x17, .x24, .x25] := acc_regs_lt n hn

theorem fresh_low (n : Nat) (hn : n < 10) :
    Fresh (win n n n :: (List.range n).map (win n n)) := by
  have h := fresh_wins hn n
  rw [wins_split] at h
  refine ⟨?_, fun t ht => h.2 t ?_⟩
  · have hd := h.1
    simp only [List.nodup_append, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false] at hd
    exact List.nodup_cons.mpr ⟨fun hm => hd.2.2 _ hm _ (by simp) rfl, hd.1⟩
  · simp only [List.mem_cons, List.mem_append] at ht ⊢
    grind

theorem fresh_low' (n : Nat) (hn : n < 10) : Fresh ((List.range n).map (win n n)) :=
  (fresh_low n hn).tail

/-- `x7 = 0`. -/
theorem zero7_ok (s : State) :
    WP isa (.block [zero7]) s fun s' => s'.gpr .x7 = 0 ∧ Keeps [.x7] s s' := movz0_ok s .x7

/-- Closes `r ∉ clob n` from `r ∉ rs` for the lists of registers the blocks
change. -/
theorem not_mem_of_clob {n : Nat} {r : Reg} (hr : r ∉ clob n) :
    r ∉ [Reg.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x16, .x17] ∧ r ∉ acc n := by
  simp only [clob, List.mem_append, not_or] at hr
  exact hr.1.1

/-- The words at `a`, loaded into the registers `ts`, each its own. -/
theorem loadsEach_ok {size : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {a : Nat},
    Scr s base size → a + 8 * ts.length ≤ size → a % 8 = 0 → ts.Nodup → Reg.x0 ∉ ts →
    WP isa (.block (loads ts a)) s fun s' =>
      (∀ j (r : Reg), ts[j]? = some r → s'.gpr r = word s.mem base (a + 8 * j)) ∧ Keeps ts s s'
  | [], s, _, _, _, _, _, _, _ => WP.block_nil ⟨fun _ _ h => by simp at h,
      fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | t :: ts, s, base, a, hs, ha, ha8, hd, h0 => by
    simp only [List.length_cons] at ha
    rw [loads, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (ld_ok hs (d := a) (by omega) ha8 t) fun s₁ ⟨e₁, k₁, _⟩ => ?_
    have ht0 : t ≠ .x0 := fun h => h0 (h ▸ List.mem_cons_self ..)
    have hs₁ := hs.of_keeps k₁ (by simpa using Ne.symm ht0)
    refine WP.mono (loadsEach_ok ts hs₁ (a := a + 8) (by omega) (by omega) (List.nodup_cons.mp hd).2
      fun h => h0 (List.mem_cons_of_mem _ h)) fun s₂ ⟨e₂, k₂⟩ => ?_
    refine ⟨fun j r hr => ?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
      subst hr
      rw [k₂.gpr _ (List.nodup_cons.mp hd).1, e₁, Nat.mul_zero, Nat.add_zero]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hr
      rw [e₂ j r hr, k₁.mem, show a + 8 + 8 * j = a + 8 * (j + 1) by omega]

theorem bRegs_take_nodup (n : Nat) : (bRegs.take n).Nodup :=
  (show bRegs.Nodup by decide).sublist (List.take_sublist _ _)

theorem x0_not_bRegs_take (n : Nat) : Reg.x0 ∉ bRegs.take n :=
  fun h => absurd (List.mem_of_mem_take h) (by decide)

theorem mulSetup_eq (M : Mod) (b : Nat) : mulSetup M b = ([zero7] : List Instr) ++
    (loads (bRegs.take M.n) b ++ (mulConst M ++ zeros (acc M.n))) := by
  simp only [mulSetup, List.cons_append, List.nil_append, List.append_assoc]

/-- `x7 = 0`, `[b]`'s words in `bRegs`, the reduction's constant in `x6`, and
the accumulator cleared. -/
theorem setup_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod}
    (hn : M.n < 10) {b : Nat} (hb : b + 8 * M.n ≤ size) (hb8 : b % 8 = 0) :
    WP isa (.block (mulSetup M b)) s fun s' =>
      s'.gpr .x7 = 0 ∧ BRegs s' base b M.n ∧ ConstOk M s' ∧ regsVal s' (wins M.n 0) = 0 ∧
        Keeps (.x4 :: .x5 :: .x6 :: .x7 :: .x16 :: .x17 :: acc M.n) s s' := by
  have hacc := acc_regs_lt _ hn
  have nacc : ∀ r ∈ [Reg.x0, .x4, .x5, .x6, .x7, .x16, .x17], r ∉ acc M.n := fun r hr h => by
    have := hacc r h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at this
  have htake : ∀ r ∈ bRegs.take M.n, r = .x4 ∨ r = .x5 ∨ r = .x16 ∨ r = .x17 :=
    fun r hr => bRegs_regs r (List.mem_of_mem_take hr)
  rw [mulSetup_eq, WP.block_append_iff]
  refine WP.mono (zero7_ok s) fun s₀ ⟨z₀, k₀⟩ => ?_
  have hs₀ := hs.of_keeps k₀ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loadsEach_ok _ hs₀ (a := b) (by
      have := List.length_take_le M.n bRegs; omega) hb8 (bRegs_take_nodup M.n)
      (x0_not_bRegs_take M.n)) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs₀.of_keeps k₁ (x0_not_bRegs_take M.n)
  have z₁ : s₁.gpr .x7 = 0 := by
    rw [k₁.gpr _ (fun h => by rcases htake _ h with h | h | h | h <;> exact absurd h (by decide)), z₀]
  have hBR₁ : BRegs s₁ base b M.n := fun j hj r hr => by
    rw [e₁ j r (by rw [List.getElem?_take_of_lt hj]; exact hr), k₁.mem]
  rw [WP.block_append_iff]
  -- The constant.
  have hC : WP isa (.block (mulConst M)) s₁ fun s₂ => ConstOk M s₂ ∧ Keeps [.x6] s₁ s₂ := by
    cases hr : M.red with
    | general =>
      rw [show mulConst M = const64 .x6 M.minv by simp only [mulConst, hr]]
      refine WP.mono (const64_ok s₁ .x6 M.minv) fun s₂ ⟨e, k⟩ => ⟨?_, k⟩
      unfold ConstOk; rw [hr]; exact e
    | friendly ws =>
      cases hg : firstGen ws with
      | none =>
        rw [show mulConst M = [] by simp only [mulConst, hr, hg]]
        refine WP.block_nil ⟨?_, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
        unfold ConstOk; rw [hr]; intro v hv; rw [hg] at hv; exact absurd hv (by simp)
      | some v =>
        rw [show mulConst M = const64 .x6 (BitVec.ofNat 64 v) by simp only [mulConst, hr, hg]]
        refine WP.mono (const64_ok s₁ .x6 (BitVec.ofNat 64 v)) fun s₂ ⟨e, k⟩ => ⟨?_, k⟩
        unfold ConstOk; rw [hr]; intro v' hv'
        rw [hg, Option.some.injEq] at hv'
        rw [e, hv']
  refine WP.mono hC fun s₂ ⟨c₂, k₂⟩ => ?_
  refine WP.mono (zeros_ok s₂ (acc M.n)) fun s₃ ⟨z₃, k₃⟩ => ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [k₃.gpr _ (nacc .x7 (by simp)), k₂.gpr _ (by decide), z₁]
  · exact (hBR₁.keep k₂.mem fun r hr => k₂.gpr r (by
      rcases bRegs_regs r hr with rfl | rfl | rfl | rfl <;> decide)).keep k₃.mem fun r hr =>
        k₃.gpr r (nacc r (by rcases bRegs_regs r hr with rfl | rfl | rfl | rfl <;> simp))
  · exact c₂.keep (k₃.gpr _ (nacc .x6 (by simp)))
  · exact regsVal_zero fun r hr => z₃ r (wins_sub_acc hn 0 r hr)
  · refine ((k₀.mono (by sub_regs)).trans (k₁.mono fun q hq => ?_)).trans
      ((k₂.mono (by sub_regs)).trans (k₃.mono fun q hq => ?_))
    · rcases htake q hq with rfl | rfl | rfl | rfl <;> simp
    · simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hq)))))

theorem dRegs_clob : ∀ n < 10, ∀ r ∈ dRegs n, r ∈ clob n := by
  unfold clob; decide

/-- What `csubR` changes is in `clob`. -/
theorem csubR_keep {n : Nat} (h7 : n < 10) {ts : List Reg} (hts : ∀ r ∈ ts, r ∈ acc n) :
    ∀ r ∈ (.x2 :: .x17 :: ts ++ dRegs n), r ∈ clob n := by
  intro r hr
  simp only [List.cons_append, List.mem_cons, List.mem_append] at hr
  rcases hr with rfl | rfl | h | h
  · simp [clob]
  · simp [clob]
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (hts r h)))
  · exact dRegs_clob n h7 r h

theorem mul_eq (M : Mod) (o a b : Nat) :
    mul M o a b = mulSetup M b ++ ((List.range M.n).flatMap (round M a b) ++
      (csubR M ((List.range M.n).map (win M.n M.n)) (win M.n M.n M.n) ++
        stores ((List.range M.n).map (win M.n M.n)) o)) := by
  simp only [mul, List.append_assoc]

/-- `[o] = [a] [b] R⁻¹ mod m`. -/
theorem mul_okW {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) (h10 : M.n < 10) (hA : ModA M) {o a b : Nat} (ho : o + 8 * M.n ≤ size)
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hb8 : b % 8 = 0) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (mul M o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  have h7 := h10
  rw [mul_eq, WP.block_append_iff]
  refine WP.mono (setup_ok hs h7 hb hb8) fun s₁ ⟨z₁, hBR₁, h6₁, h0, k₁⟩ => ?_
  have hacc := acc_regs_lt _ h7
  have hs₁ := hs.of_keeps k₁ (fun h => by
    simp only [List.mem_cons] at h
    rcases h with h | h | h | h | h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact (hacc _ h) (by simp))
  have hmem₁ : s₁.mem = s.mem := k₁.mem
  rw [WP.block_append_iff]
  refine WP.mono (rounds_ok h7 ha hb hM.mo ha8 hb8 hA.mo hM.inv hM.red M.n (Nat.le_refl _) hs₁ z₁
    (by rw [hmem₁]; exact hM.val) hBR₁ h6₁ (by rw [hmem₁]; exact hB) h0)
    fun s₂ ⟨⟨U, eU⟩, hT, k₂, _⟩ => ?_
  have nk : ∀ r ∈ [Reg.x0, .x7], r ∉ Reg.x1 :: Reg.x2 :: Reg.x3 :: acc M.n := by
    intro r hr h
    by_cases hr' : r ∈ acc M.n
    · have := hacc _ hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr h
    rcases hr with rfl | rfl <;> simp_all
  have hs₂ := hs₁.of_keeps k₂ (nk .x0 (by simp))
  have hz₂ : s₂.gpr .x7 = 0 := by rw [k₂.gpr .x7 (nk .x7 (by simp)), z₁]
  have hmem₂ : s₂.mem = s.mem := by rw [k₂.mem, hmem₁]
  rw [hmem₁] at eU
  -- The accumulator's value as `csub` sees it: its top word is zero.
  have hsplit := wins_split M.n M.n
  have hmX : m < 2 ^ (64 * M.n) := hM.val ▸ wordsVal_lt _ _ _ _
  have hlowlen : ((List.range M.n).map (win M.n M.n)).length = M.n := by simp
  have hV : regsVal s₂ ((List.range M.n).map (win M.n M.n)) +
      2 ^ (64 * M.n) * (s₂.gpr (win M.n M.n M.n)).toNat = regsVal s₂ (wins M.n M.n) := by
    rw [hsplit, regsVal_append, hlowlen]
    simp only [regsVal, Nat.mul_zero, Nat.add_zero]
    have hT' := hT
    rw [hsplit, regsVal_append, hlowlen] at hT'
    simp only [regsVal, Nat.mul_zero, Nat.add_zero] at hT'
    have : (s₂.gpr (win M.n M.n (M.n + 1))).toNat = 0 := by
      by_contra hne
      have : 2 ^ (64 * M.n) * 2 ^ 64 ≤ 2 ^ (64 * M.n) * ((s₂.gpr (win M.n M.n M.n)).toNat +
          2 ^ 64 * (s₂.gpr (win M.n M.n (M.n + 1))).toNat) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    rw [this, Nat.mul_zero, Nat.add_zero]
  rw [WP.block_append_iff]
  have hlow_acc : ∀ r ∈ (List.range M.n).map (win M.n M.n), r ∈ acc M.n := fun r hr =>
    wins_sub_acc h7 M.n r (by rw [hsplit]; exact List.mem_append_left _ hr)
  refine WP.mono (csubR_ok hs₂ (M := M) (m := m) hlowlen hM.n0 h7 (fresh_low M.n h7) hM.mo
    hA.mo hz₂ (by rw [hmem₂]; exact hM.val) (by rw [hV]; exact hT)) fun s₃ ⟨e₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (fun h => x0_not_clob M.n (csubR_keep h7 hlow_acc _ h))
  refine WP.mono (stores_ok _ hs₃ (o := o) (by rw [hlowlen]; omega) ho8 (fresh_low' M.n h7).1)
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  rw [hlowlen] at e₄ O₄
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_, fun x hx hx' => ?_⟩, ?_, ?_⟩
  · obtain ⟨hr₁, hr₂⟩ := not_mem_of_clob hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr₁
    rw [k₄.gpr r (by simp), k₃.gpr r (fun h => hr (csubR_keep h7 hlow_acc r h)),
      k₂.gpr r (by simp only [List.mem_cons, not_or]; exact ⟨hr₁.1, hr₁.2.1, hr₁.2.2.1, hr₂⟩),
      k₁.gpr r (by simp only [List.mem_cons, not_or]; exact ⟨hr₁.2.2.2.1, hr₁.2.2.2.2.1,
        hr₁.2.2.2.2.2.1, hr₁.2.2.2.2.2.2.1, hr₁.2.2.2.2.2.2.2.1, hr₁.2.2.2.2.2.2.2.2, hr₂⟩)]
  · rw [k₄.rd, k₃.rd, k₂.rd, k₁.rd]
  · rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr]
  · rw [k₄.sp, k₃.sp, k₂.sp, k₁.sp]
  · rw [O₄ x hx, k₃.mem, hmem₂]
  · rw [e₄, e₃, hV]; exact Nat.mod_lt _ (m_pos hB)
  · rw [e₄, e₃, hV, Nat.mod_mul_mod, Nat.mul_comm, eU]
    simp only [Nat.add_mul_mod_self_right]

/-! ## Addition and subtraction -/

theorem low_len_lt : ∀ n < 10, (low n).length = n := by decide

theorem fresh_top_low_lt : ∀ n < 10, Fresh (top n :: low n) := by unfold Fresh; decide

theorem low_sub_acc_lt : ∀ n < 10, ∀ t ∈ top n :: low n, t ∈ acc n := by decide

theorem low_ne_nil {n : Nat} (hn : n < 10) (h0 : 0 < n) : ∃ t ts, low n = t :: ts := by
  have := low_len_lt n hn
  cases h : low n with
  | nil => rw [h] at this; simp at this; omega
  | cons t ts => exact ⟨t, ts, rfl⟩

/-- `t = 0 + 0 + c`: the carry flag as a word. -/
theorem adcZero_ok (s : State) (t : Reg) (hz : s.gpr .x7 = 0) :
    WP isa (.block [.adc .x t .x7 .x7]) s fun s' => (s'.gpr t).toNat = s.c.toNat ∧ Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write_self,
    BitVec.setWidth_eq, hz, Option.some.injEq, exists_eq_left']
  refine ⟨by cases s.c <;> rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

/-- `x17` all ones if the borrow `!c` is set, else zero. -/
theorem sbcMask_ok (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block [.sbc .x .x17 .x7 .x7]) s fun s' =>
      s'.gpr .x17 = (if !s.c then BitVec.allOnes 64 else 0) ∧ Keeps [.x17] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write_self,
    BitVec.setWidth_eq, hz, Option.some.injEq, exists_eq_left']
  refine ⟨by cases s.c <;> decide, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

/-- `[o] = [a] + [b] mod m`. -/
theorem add_okW {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) (h10 : M.n < 10) (hA : ModA M) {o a b : Nat} (ho : o + 8 * M.n ≤ size)
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hb8 : b % 8 = 0)
    (hAB : wordsVal s.mem base a M.n + wordsVal s.mem base b M.n < 2 * m) :
    WP isa (.block (add M o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + wordsVal s.mem base b M.n) % m := by
  have hn := hs.nowrap
  have h7 := h10
  have hf := fresh_top_low_lt M.n h7
  have hl := low_len_lt M.n h7
  obtain ⟨t, ts, hts⟩ := low_ne_nil h7 hM.n0
  have nf : ∀ r ∈ top M.n :: low M.n, r ∉ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x16, .x17, .x24, .x25] :=
    hf.2
  have hsub : ∀ r ∈ top M.n :: low M.n, r ∈ acc M.n := low_sub_acc_lt _ h7
  rw [Impl.Mont.AArch64.add, show zero7 :: loads (low M.n) a = [zero7] ++ loads (low M.n) a from rfl]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero7_ok s) fun s₀ ⟨z₀, k₀⟩ => ?_
  have hs₀ := hs.of_keeps k₀ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok (low M.n) hs₀ (a := a) (by omega) ha8 hf.tail) fun s₁ ⟨e₁, k₁, _⟩ => ?_
  have hs₁ := hs₀.of_keeps k₁ (fun h => nf _ (List.mem_cons_of_mem _ h) (by simp))
  have hz₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr _ (fun h => nf _ (List.mem_cons_of_mem _ h) (by simp)), z₀]
  rw [WP.block_append_iff, hts]
  refine WP.mono (chainAdds_ok hs₁ (b := b) (by rw [← hts]; omega) hb8 (hts ▸ hf.tail))
    fun s₃ ⟨e₃, k₃⟩ => ?_
  rw [← hts] at e₃ k₃ ⊢
  have nk₃ : ∀ r ∈ [Reg.x0, .x7], r ∉ Reg.x2 :: low M.n := by
    intro r hr h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases List.mem_cons.mp h with h | h
    · rcases hr with rfl | rfl <;> exact absurd h (by decide)
    · exact nf _ (List.mem_cons_of_mem _ h) (by rcases hr with rfl | rfl <;> simp)
  have hs₃ := hs₁.of_keeps k₃ (nk₃ .x0 (by simp))
  have hz₃ : s₃.gpr .x7 = 0 := by rw [k₃.gpr _ (nk₃ .x7 (by simp)), hz₁]
  rw [WP.block_append_iff]
  refine WP.mono (adcZero_ok s₃ (top M.n) hz₃) fun s₄ ⟨e₄, k₄⟩ => ?_
  have htop := nf _ (List.mem_cons_self ..)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at htop
  have hs₄ := hs₃.of_keeps k₄ (by simp [Ne.symm htop.1])
  have hz₄ : s₄.gpr .x7 = 0 := by rw [k₄.gpr _ (by simp [Ne.symm htop.2.2.2.2.2.2.2.1]), hz₃]
  have hR₄ : regsVal s₄ (low M.n) = regsVal s₃ (low M.n) :=
    regsVal_congr fun q hq => k₄.gpr q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => (List.nodup_cons.mp hf.1).1 (h ▸ hq))
  have hmem₄ : s₄.mem = s.mem := by rw [k₄.mem, k₃.mem, k₁.mem, k₀.mem]
  rw [hl, e₁, k₀.mem] at e₃
  have hV : regsVal s₄ (low M.n) + 2 ^ (64 * M.n) * (s₄.gpr (top M.n)).toNat =
      wordsVal s.mem base a M.n + wordsVal s.mem base b M.n := by rw [hR₄, e₄, e₃, k₁.mem, k₀.mem, hl]
  rw [WP.block_append_iff]
  have hlow : ∀ r ∈ low M.n, r ∈ acc M.n := fun r h => hsub r (List.mem_cons_of_mem _ h)
  refine WP.mono (csubR_ok hs₄ (M := M) (m := m) hl hM.n0 h7 hf hM.mo hA.mo hz₄
    (by rw [hmem₄]; exact hM.val) (by rw [hV]; exact hAB)) fun s₅ ⟨e₅, k₅⟩ => ?_
  have hs₅ := hs₄.of_keeps k₅ (fun h => x0_not_clob M.n (csubR_keep h7 hlow _ h))
  refine WP.mono (stores_ok _ hs₅ (o := o) (by rw [hl]; omega) ho8 hf.tail.1) fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  rw [hl] at e₆ O₆
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_, fun x hx hx' => ?_⟩, ?_⟩
  · obtain ⟨hr₁, hr₂⟩ := not_mem_of_clob hr
    have hr' : r ∉ top M.n :: low M.n := fun h => hr₂ (hsub r h)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr₁ hr'
    rw [k₆.gpr r (by simp), k₅.gpr r (fun h => hr (csubR_keep h7 hlow r h)),
      k₄.gpr r (by simpa using hr'.1),
      k₃.gpr r (by simp only [List.mem_cons, not_or]; exact ⟨hr₁.2.1, hr'.2⟩),
      k₁.gpr r hr'.2, k₀.gpr r (by simpa using hr₁.2.2.2.2.2.2.1)]
  · rw [k₆.rd, k₅.rd, k₄.rd, k₃.rd, k₁.rd, k₀.rd]
  · rw [k₆.wr, k₅.wr, k₄.wr, k₃.wr, k₁.wr, k₀.wr]
  · rw [k₆.sp, k₅.sp, k₄.sp, k₃.sp, k₁.sp, k₀.sp]
  · rw [O₆ x hx, k₅.mem, hmem₄]
  · rw [e₆, e₅, hV]

/-- `t += ([mo] & x17) + c`: one word of the masked addition. -/
theorem maskStep_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (t : Reg)
    (ht2 : t ≠ .x2) (first : Bool) {c : Bool} (hc : (if first then false else s.c) = c) {k : Bool}
    (hk : s.gpr .x17 = (if k then BitVec.allOnes 64 else 0)) {mo : Nat}
    (hmo : mo + 8 ≤ size) (hmo8 : mo % 8 = 0) :
    WP isa (.block [ld .x2 mo, .logic .and .x .x2 .x2 .x17,
        if first then .adds .x t t .x2 else .adcs .x t t .x2]) s fun s' =>
      (s'.gpr t).toNat + 2 ^ 64 * s'.c.toNat =
        (s.gpr t).toNat + (if k then (word s.mem base mo).toNat else 0) + c.toNat ∧
      Keeps [.x2, t] s s' := by
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (ld_ok hs hmo hmo8 .x2) fun s₁ ⟨l₁, k₁, c₁⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.logic .and .x .x2 .x2 .x17]) s₁ (fun s₂ =>
      s₂.gpr .x2 = (if k then word s.mem base mo else 0) ∧ Keeps [.x2] s₁ s₂ ∧ s₂.c = s₁.c) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write_self,
      BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
    rw [l₁, k₁.gpr .x17 (by decide), hk]
    refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
    · cases k
      · simp
      · simp only [↓reduceIte, BitVec.and_allOnes]
    simp only [List.mem_singleton] at hr
    exact RegUpd.gpr_write_of_ne _ _ _ hr) fun s₂ ⟨a₂, k₂, c₂⟩ => ?_
  refine WP.mono (addc_ok s₂ t t .x2 first (c := c) (by rw [c₂, c₁, hc])) fun s₃ ⟨d₃, c₃, k₃⟩ => ?_
  rw [a₂, k₂.gpr t (by simpa using ht2), k₁.gpr t (by simpa using ht2)] at d₃ c₃
  refine ⟨?_, ((k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))).trans (k₃.mono (by sub_regs))⟩
  rw [d₃, c₃, Word64.addCarry_value]
  cases k <;> rfl

/-- `ts += ([mo] & x17) + c`, `adcs` throughout. -/
theorem addMaskedC_ok {size : Nat} (k : Bool) : ∀ (ts : List Reg) {s : State} {base : Addr} {mo : Nat},
    Scr s base size → mo + 8 * ts.length ≤ size → mo % 8 = 0 → Fresh ts →
    s.gpr .x17 = (if k then BitVec.allOnes 64 else 0) →
    WP isa (.block (addMasked false ts mo)) s fun s' =>
      regsVal s' ts + 2 ^ (64 * ts.length) * s'.c.toNat =
        regsVal s ts + (if k then wordsVal s.mem base mo ts.length else 0) + s.c.toNat ∧
      Keeps (.x2 :: ts) s s'
  | [], s, _, _, _, _, _, _, _ => WP.block_nil ⟨by cases k <;> simp [regsVal, wordsVal],
      fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | t :: ts, s, base, mo, hs, hmo, hmo8, hf, hk => by
    simp only [List.length_cons] at hmo
    have ht2 : t ≠ .x2 := fun h => hf.head.2 (by simp [h])
    have ht17 : t ≠ .x17 := fun h => hf.head.2 (by simp [h])
    rw [addMasked, WP.block_append_iff]
    refine WP.mono (maskStep_ok hs t ht2 false (c := s.c) rfl hk (mo := mo) (by omega) hmo8)
      fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => by rcases h with h | h <;> [exact absurd h (by decide); exact hf.head.2 (by simp [← h])])
    have hk₁ : s₁.gpr .x17 = (if k then BitVec.allOnes 64 else 0) := by
      rw [k₁.gpr _ (by simp [Ne.symm ht17]), hk]
    refine WP.mono (addMaskedC_ok k ts hs₁ (mo := mo + 8) (by omega) (by omega) hf.tail hk₁)
      fun s₂ ⟨e₂, k₂⟩ => ?_
    have ht : s₂.gpr t = s₁.gpr t := k₂.gpr t (by
      simp only [List.mem_cons, not_or]; exact ⟨ht2, hf.head.1⟩)
    have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.gpr q (by
      have := hf.tail.2 q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
      exact ⟨this.2.2.1, fun h => hf.head.1 (h ▸ hq)⟩)
    rw [hR, k₁.mem] at e₂
    refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    simp only [regsVal, wordsVal, List.length_cons, pow64_succ, ht]
    cases k <;> simp only [ite_true, ite_false, Bool.false_eq_true] at e₁ e₂ ⊢ <;> rw [Nat.mul_assoc] <;>
      omega

/-- `ts += [mo] & x17`, with the carry out. -/
theorem addMasked_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (k : Bool)
    {t : Reg} {ts : List Reg} {mo : Nat} (hmo : mo + 8 * (t :: ts).length ≤ size) (hmo8 : mo % 8 = 0)
    (hf : Fresh (t :: ts)) (hk : s.gpr .x17 = (if k then BitVec.allOnes 64 else 0)) :
    WP isa (.block (addMasked true (t :: ts) mo)) s fun s' =>
      regsVal s' (t :: ts) + 2 ^ (64 * (t :: ts).length) * s'.c.toNat =
        regsVal s (t :: ts) + (if k then wordsVal s.mem base mo (t :: ts).length else 0) ∧
      Keeps (.x2 :: t :: ts) s s' := by
  simp only [List.length_cons] at hmo ⊢
  have ht2 : t ≠ .x2 := fun h => hf.head.2 (by simp [h])
  have ht17 : t ≠ .x17 := fun h => hf.head.2 (by simp [h])
  rw [addMasked, WP.block_append_iff]
  refine WP.mono (maskStep_ok hs t ht2 true (c := false) rfl hk (mo := mo) (by omega) hmo8)
    fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact fun h => by rcases h with h | h <;> [exact absurd h (by decide); exact hf.head.2 (by simp [← h])])
  have hk₁ : s₁.gpr .x17 = (if k then BitVec.allOnes 64 else 0) := by
    rw [k₁.gpr _ (by simp [Ne.symm ht17]), hk]
  refine WP.mono (addMaskedC_ok k ts hs₁ (mo := mo + 8) (by omega) (by omega) hf.tail hk₁)
    fun s₂ ⟨e₂, k₂⟩ => ?_
  have ht : s₂.gpr t = s₁.gpr t := k₂.gpr t (by
    simp only [List.mem_cons, not_or]; exact ⟨ht2, hf.head.1⟩)
  have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.gpr q (by
    have := hf.tail.2 q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
    exact ⟨this.2.2.1, fun h => hf.head.1 (h ▸ hq)⟩)
  rw [hR, k₁.mem] at e₂
  refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
  simp only [regsVal, wordsVal, pow64_succ, ht]
  simp only [Bool.toNat_false, Nat.add_zero] at e₁
  cases k <;> simp only [ite_true, ite_false, Bool.false_eq_true] at e₁ e₂ ⊢ <;> rw [Nat.mul_assoc] <;>
    omega

/-- `[o] = [a] - [b] mod m`. -/
theorem sub_okW {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) (h10 : M.n < 10) (hMA : ModA M) {o a b : Nat} (ho : o + 8 * M.n ≤ size)
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hb8 : b % 8 = 0)
    (hA : wordsVal s.mem base a M.n < m) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (sub M o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + m - wordsVal s.mem base b M.n) % m := by
  have hn := hs.nowrap
  have h7 := h10
  have hf := fresh_top_low_lt M.n h7
  have hl := low_len_lt M.n h7
  have hmX : m < 2 ^ (64 * M.n) := hM.val ▸ wordsVal_lt _ _ _ _
  have hmo := hM.mo
  obtain ⟨t, ts, hts⟩ := low_ne_nil h7 hM.n0
  have nf : ∀ r ∈ top M.n :: low M.n, r ∉ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x16, .x17, .x24, .x25] :=
    hf.2
  have hsub : ∀ r ∈ top M.n :: low M.n, r ∈ acc M.n := low_sub_acc_lt _ h7
  have nk : ∀ r ∈ [Reg.x0, .x7, .x17], r ∉ Reg.x2 :: low M.n := by
    intro r hr h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases List.mem_cons.mp h with h | h
    · rcases hr with rfl | rfl | rfl <;> exact absurd h (by decide)
    · exact nf _ (List.mem_cons_of_mem _ h) (by rcases hr with rfl | rfl | rfl <;> simp)
  rw [Impl.Mont.AArch64.sub, show zero7 :: loads (low M.n) a = [zero7] ++ loads (low M.n) a from rfl]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero7_ok s) fun s₀ ⟨z₀, k₀⟩ => ?_
  have hs₀ := hs.of_keeps k₀ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok (low M.n) hs₀ (a := a) (by omega) ha8 hf.tail) fun s₁ ⟨e₁, k₁, _⟩ => ?_
  have hs₁ := hs₀.of_keeps k₁ (fun h => nf _ (List.mem_cons_of_mem _ h) (by simp))
  have hz₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr _ (fun h => nf _ (List.mem_cons_of_mem _ h) (by simp)), z₀]
  rw [WP.block_append_iff, hts]
  refine WP.mono (chainSubs_ok hs₁ (b := b) (by rw [← hts]; omega) hb8 (hts ▸ hf.tail))
    fun s₂ ⟨e₂, k₂⟩ => ?_
  rw [← hts] at e₂ k₂ ⊢
  have hs₂ := hs₁.of_keeps k₂ (nk .x0 (by simp))
  have hz₂ : s₂.gpr .x7 = 0 := by rw [k₂.gpr _ (nk .x7 (by simp)), hz₁]
  rw [WP.block_append_iff]
  refine WP.mono (sbcMask_ok s₂ hz₂) fun s₃ ⟨x₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff, hts]
  refine WP.mono (addMasked_ok hs₃ (!s₂.c) (mo := M.mo) (by rw [← hts]; omega) hMA.mo (hts ▸ hf.tail)
    x₃) fun s₅ ⟨e₅, k₅⟩ => ?_
  rw [← hts] at e₅ k₅ ⊢
  have hs₅ := hs₃.of_keeps k₅ (nk .x0 (by simp))
  refine WP.mono (stores_ok _ hs₅ (o := o) (by rw [hl]; omega) ho8 hf.tail.1) fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  rw [hl] at e₁ e₂ e₅ e₆ O₆
  have hmem₃ : s₃.mem = s.mem := by rw [k₃.mem, k₂.mem, k₁.mem, k₀.mem]
  have hR₃ : regsVal s₃ (low M.n) = regsVal s₂ (low M.n) :=
    regsVal_congr fun q hq => k₃.gpr q (by
      simp only [List.mem_singleton]; exact fun h => nf _ (List.mem_cons_of_mem _ hq) (by simp [h]))
  rw [hR₃, hmem₃, hM.val] at e₅
  rw [e₁, k₁.mem, k₀.mem] at e₂
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_, fun x hx hx' => ?_⟩, ?_⟩
  · obtain ⟨hr₁, hr₂⟩ := not_mem_of_clob hr
    have hr' : r ∉ top M.n :: low M.n := fun h => hr₂ (hsub r h)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr₁ hr'
    rw [k₆.gpr r (by simp), k₅.gpr r (by simp only [List.mem_cons, not_or]; exact ⟨hr₁.2.1, hr'.2⟩),
      k₃.gpr r (by simpa using hr₁.2.2.2.2.2.2.2.2),
      k₂.gpr r (by simp only [List.mem_cons, not_or]; exact ⟨hr₁.2.1, hr'.2⟩),
      k₁.gpr r hr'.2, k₀.gpr r (by simpa using hr₁.2.2.2.2.2.2.1)]
  · rw [k₆.rd, k₅.rd, k₃.rd, k₂.rd, k₁.rd, k₀.rd]
  · rw [k₆.wr, k₅.wr, k₃.wr, k₂.wr, k₁.wr, k₀.wr]
  · rw [k₆.sp, k₅.sp, k₃.sp, k₂.sp, k₁.sp, k₀.sp]
  · rw [O₆ x hx, k₅.mem, hmem₃]
  · rw [e₆]
    have hR₂ := regsVal_lt s₂ (low M.n)
    have hR₅ := regsVal_lt s₅ (low M.n)
    rw [hl] at hR₂ hR₅
    cases hc : s₂.c <;> cases hc' : s₅.c <;> simp only [hc, hc', Bool.toNat_false, Bool.toNat_true,
      Bool.not_false, Bool.not_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Bool.false_eq_true,
      ite_false, ite_true] at e₂ e₅
    · omega
    · rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [show wordsVal s.mem base a M.n + m - wordsVal s.mem base b M.n =
        (wordsVal s.mem base a M.n - wordsVal s.mem base b M.n) + m by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
      omega
    · omega

/-! ## For at most nine words (`ModOkA`) -/

theorem mul_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkA M size m s.mem base) (hA : ModA M) {o a b : Nat} (ho : o + 8 * M.n ≤ size)
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hb8 : b % 8 = 0) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (mul M o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m :=
  mul_okW hs hM.toW hM.n10 hA ho ha hb ho8 ha8 hb8 hB

theorem add_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkA M size m s.mem base) (hA : ModA M) {o a b : Nat} (ho : o + 8 * M.n ≤ size)
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hb8 : b % 8 = 0)
    (hAB : wordsVal s.mem base a M.n + wordsVal s.mem base b M.n < 2 * m) :
    WP isa (.block (add M o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + wordsVal s.mem base b M.n) % m :=
  add_okW hs hM.toW hM.n10 hA ho ha hb ho8 ha8 hb8 hAB

theorem sub_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkA M size m s.mem base) (hMA : ModA M) {o a b : Nat} (ho : o + 8 * M.n ≤ size)
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hb8 : b % 8 = 0)
    (hA : wordsVal s.mem base a M.n < m) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (sub M o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + m - wordsVal s.mem base b M.n) % m :=
  sub_okW hs hM.toW hM.n10 hMA ho ha hb ho8 ha8 hb8 hA hB

end VG.Proof.Mont.AArch64
