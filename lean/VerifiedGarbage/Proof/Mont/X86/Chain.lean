import VerifiedGarbage.Proof.Mont.X86.Step

/-!
# Montgomery arithmetic on x86 (32-bit): chains of additions and subtractions

`chain M op op' acc a b`, word by word through `eax` (`triple`), is
`[acc] = [a] + [b]` with its carry (`op = add`, `op' = adc`:
`chainAdd_ok`) or `[acc] = [a] - [b]` with its borrow (`sub`, `sbb`:
`chainSub_ok`); `csub`'s difference with the modulus (`diffs`) is the
latter.
-/

namespace VG.Proof.Mont.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont

/-- `[acc + 4j] = [a + 4j] op [b + 4j]`, through `eax`. -/
def triple (op : AluOp) (acc a b j : Nat) : List Instr :=
  [.mov .eax (.mem (sc (a + 4 * j))), .alu op .eax (.mem (sc (b + 4 * j))), .store (sc (acc + 4 * j)) .eax]

/-- The first `k` words of a chain. -/
def chainK (op op' : AluOp) (acc a b k : Nat) : List Instr :=
  (List.range k).flatMap fun j => triple (if j = 0 then op else op') acc a b j

theorem chain_eq (M : Mod) (op op' : AluOp) (acc a b : Nat) :
    chain M op op' acc a b = chainK op op' acc a b (words M) := rfl

theorem diffs_eq (M : Mod) (src : Nat) : diffs M src = chainK .sub .sbb M.tmp src M.mo (words M) := rfl

theorem chainK_succ (op op' : AluOp) (acc a b k : Nat) :
    chainK op op' acc a b (k + 1) = chainK op op' acc a b k ++ triple (if k = 0 then op else op') acc a b k := by
  simp only [chainK, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem chainK_one (op op' : AluOp) (acc a b : Nat) : chainK op op' acc a b 1 = triple op acc a b 0 := by
  rw [chainK_succ]; rfl

theorem sub_toNat (a b : BitVec 32) : (a - b).toNat = (a.toNat + 2 ^ 32 * 2 - b.toNat) % 2 ^ 32 := by
  have ha := a.isLt
  have hb := b.isLt
  rw [BitVec.toNat_sub]
  omega

/-- A word of an addition, with the carry in `cin` (none for `add`). -/
theorem tripleAdd_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {op : AluOp} {cin : Bool}
    (hop : (op = .add ∧ cin = false) ∨ (op = .adc ∧ s.cf = some cin)) {acc a b j : Nat}
    (ha : a + 4 * j + 4 ≤ size) (hb : b + 4 * j + 4 ≤ size) (hacc : acc + 4 * j + 4 ≤ size) :
    WP isa (.block (triple op acc a b j)) s fun u =>
      Outside base (acc + 4 * j) 4 s.mem u.mem ∧
      (∃ c, u.cf = some c ∧ w32 u.mem base (acc + 4 * j) + 2 ^ 32 * c.toNat =
        w32 s.mem base (a + 4 * j) + w32 s.mem base (b + 4 * j) + cin.toNat) ∧
      Keeps [.eax] s u := by
  have hn := hs.nowrap
  simp only [triple]
  refine wp_movS (readSrc_sc hs ha) fun s₁ u₁ cf₁ => ?_
  have hs₁ := hs.of_keeps u₁.keeps (by decide)
  have hx := (s.mem.readW (off base (a + 4 * j)) 32).isLt
  have hy := (s.mem.readW (off base (b + 4 * j)) 32).isLt
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, hc⟩
  · refine wp_addS (readSrc_sc hs₁ hb) fun s₂ u₂ c₂ => ?_
    have hs₂ := hs₁.of_keeps u₂.keeps (by decide)
    refine wp_storeS (hs₂.ea (d := acc + 4 * j) (by omega)) (hs₂.write (n := 4) (by omega))
      fun s₃ m₃ => WP.block_nil ⟨?_, ⟨_, by rw [m₃.cf, c₂], ?_⟩, (u₁.keeps.trans (u₂.keeps)).trans (m₃.keeps _)⟩
    · rw [m₃.mem, u₂.mem, u₁.mem]; exact writeW32_outside _ _ _ (by omega)
    · rw [m₃.mem, w32_write_self, u₂.gpr, BitVec.toNat_add, u₁.gpr, u₁.mem]
      simp only [w32]
      by_cases h : 2 ^ 32 ≤ (s.mem.readW (off base (a + 4 * j)) 32).toNat +
          (s.mem.readW (off base (b + 4 * j)) 32).toNat <;>
        simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega
  · refine wp_adcS (readSrc_sc hs₁ hb) (by rw [cf₁]; exact hc) fun s₂ u₂ c₂ => ?_
    have hs₂ := hs₁.of_keeps u₂.keeps (by decide)
    refine wp_storeS (hs₂.ea (d := acc + 4 * j) (by omega)) (hs₂.write (n := 4) (by omega))
      fun s₃ m₃ => WP.block_nil ⟨?_, ⟨_, by rw [m₃.cf, c₂], ?_⟩, (u₁.keeps.trans (u₂.keeps)).trans (m₃.keeps _)⟩
    · rw [m₃.mem, u₂.mem, u₁.mem]; exact writeW32_outside _ _ _ (by omega)
    · rw [m₃.mem, w32_write_self, u₂.gpr, add3_toNat, u₁.gpr, u₁.mem]
      simp only [w32]
      have := Bool.toNat_le cin
      by_cases h : 2 ^ 32 ≤ (s.mem.readW (off base (a + 4 * j)) 32).toNat +
          (s.mem.readW (off base (b + 4 * j)) 32).toNat + cin.toNat <;>
        simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

/-- A word of a subtraction, with the borrow in `cin` (none for `sub`). -/
theorem tripleSub_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {op : AluOp} {cin : Bool}
    (hop : (op = .sub ∧ cin = false) ∨ (op = .sbb ∧ s.cf = some cin)) {acc a b j : Nat}
    (ha : a + 4 * j + 4 ≤ size) (hb : b + 4 * j + 4 ≤ size) (hacc : acc + 4 * j + 4 ≤ size) :
    WP isa (.block (triple op acc a b j)) s fun u =>
      Outside base (acc + 4 * j) 4 s.mem u.mem ∧
      (∃ c, u.cf = some c ∧ w32 u.mem base (acc + 4 * j) + w32 s.mem base (b + 4 * j) + cin.toNat =
        w32 s.mem base (a + 4 * j) + 2 ^ 32 * c.toNat) ∧
      Keeps [.eax] s u := by
  have hn := hs.nowrap
  simp only [triple]
  refine wp_movS (readSrc_sc hs ha) fun s₁ u₁ cf₁ => ?_
  have hs₁ := hs.of_keeps u₁.keeps (by decide)
  have hx := (s.mem.readW (off base (a + 4 * j)) 32).isLt
  have hy := (s.mem.readW (off base (b + 4 * j)) 32).isLt
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, hc⟩
  · refine wp_subS (readSrc_sc hs₁ hb) fun s₂ u₂ c₂ => ?_
    have hs₂ := hs₁.of_keeps u₂.keeps (by decide)
    refine wp_storeS (hs₂.ea (d := acc + 4 * j) (by omega)) (hs₂.write (n := 4) (by omega))
      fun s₃ m₃ => WP.block_nil ⟨?_, ⟨_, by rw [m₃.cf, c₂], ?_⟩, (u₁.keeps.trans (u₂.keeps)).trans (m₃.keeps _)⟩
    · rw [m₃.mem, u₂.mem, u₁.mem]; exact writeW32_outside _ _ _ (by omega)
    · rw [m₃.mem, w32_write_self, u₂.gpr, sub_toNat, u₁.gpr, u₁.mem]
      simp only [w32]
      by_cases h : (s.mem.readW (off base (a + 4 * j)) 32).toNat <
          (s.mem.readW (off base (b + 4 * j)) 32).toNat <;>
        simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega
  · refine wp_sbbS (readSrc_sc hs₁ hb) (by rw [cf₁]; exact hc) fun s₂ u₂ c₂ => ?_
    have hs₂ := hs₁.of_keeps u₂.keeps (by decide)
    refine wp_storeS (hs₂.ea (d := acc + 4 * j) (by omega)) (hs₂.write (n := 4) (by omega))
      fun s₃ m₃ => WP.block_nil ⟨?_, ⟨_, by rw [m₃.cf, c₂], ?_⟩, (u₁.keeps.trans (u₂.keeps)).trans (m₃.keeps _)⟩
    · rw [m₃.mem, u₂.mem, u₁.mem]; exact writeW32_outside _ _ _ (by omega)
    · rw [m₃.mem, w32_write_self, u₂.gpr, sub3_toNat, u₁.gpr, u₁.mem]
      simp only [w32]
      have := Bool.toNat_le cin
      by_cases h : (s.mem.readW (off base (a + 4 * j)) 32).toNat <
          (s.mem.readW (off base (b + 4 * j)) 32).toNat + cin.toNat <;>
        simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

/-- `[acc] = [a] + [b]` (`k + 1` words), and the carry. -/
theorem chainAdd_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {acc a b : Nat} :
    ∀ k, acc + 4 * (k + 1) ≤ size → a + 4 * (k + 1) ≤ size → b + 4 * (k + 1) ≤ size →
    (acc + 4 * (k + 1) ≤ a ∨ a + 4 * (k + 1) ≤ acc) → (acc + 4 * (k + 1) ≤ b ∨ b + 4 * (k + 1) ≤ acc) →
    WP isa (.block (chainK .add .adc acc a b (k + 1))) s fun u =>
      Outside base acc (4 * (k + 1)) s.mem u.mem ∧
      (∃ c, u.cf = some c ∧ val32 u.mem base acc (k + 1) + 2 ^ (32 * (k + 1)) * c.toNat =
        val32 s.mem base a (k + 1) + val32 s.mem base b (k + 1)) ∧
      Keeps [.eax] s u
  | 0, hacc, ha, hb, _, _ => by
    rw [chainK_one]
    refine WP.mono (tripleAdd_ok hs (.inl ⟨rfl, rfl⟩) (j := 0) (by omega) (by omega) (by omega))
      fun u ⟨O, ⟨c, hc, V⟩, K⟩ => ⟨O, ⟨c, hc, ?_⟩, K⟩
    simp only [val32, Nat.mul_zero, Nat.add_zero, Bool.toNat_false] at V ⊢
    exact V
  | k + 1, hacc, ha, hb, hsa, hsb => by
    have hn := hs.nowrap
    rw [chainK_succ, ite_eq_right_of_eq_false _ _ (eq_false (Nat.add_one_ne_zero k))]
    refine WP.block_append (WP.mono (chainAdd_ok hs k (by omega) (by omega) (by omega) (by omega) (by omega))
      fun s₁ ⟨O₁, ⟨c₁, hc₁, V₁⟩, K₁⟩ => ?_)
    have hs₁ := hs.of_keeps K₁ (by decide)
    refine WP.mono (tripleAdd_ok hs₁ (.inr ⟨rfl, hc₁⟩) (j := k + 1) (by omega) (by omega) (by omega))
      fun u ⟨O, ⟨c, hc, V⟩, K⟩ => ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (O.mono (by omega) (by omega)),
        ⟨c, hc, ?_⟩, K₁.trans K⟩
    rw [O₁.w32 (d := a + 4 * (k + 1)) (by omega) (by omega), O₁.w32 (d := b + 4 * (k + 1)) (by omega) (by omega)] at V
    rw [val32_succ u.mem base acc (k + 1), val32_succ s.mem base a (k + 1), val32_succ s.mem base b (k + 1),
      O.val32 (by omega) (by omega), pow32_succ (k + 1)]
    generalize 2 ^ (32 * (k + 1)) = P at *
    grind

/-- `[acc] = [a] - [b]` (`k + 1` words), and the borrow. -/
theorem chainSub_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {acc a b : Nat} :
    ∀ k, acc + 4 * (k + 1) ≤ size → a + 4 * (k + 1) ≤ size → b + 4 * (k + 1) ≤ size →
    (acc + 4 * (k + 1) ≤ a ∨ a + 4 * (k + 1) ≤ acc) → (acc + 4 * (k + 1) ≤ b ∨ b + 4 * (k + 1) ≤ acc) →
    WP isa (.block (chainK .sub .sbb acc a b (k + 1))) s fun u =>
      Outside base acc (4 * (k + 1)) s.mem u.mem ∧
      (∃ c, u.cf = some c ∧ val32 u.mem base acc (k + 1) + val32 s.mem base b (k + 1) =
        val32 s.mem base a (k + 1) + 2 ^ (32 * (k + 1)) * c.toNat) ∧
      Keeps [.eax] s u
  | 0, hacc, ha, hb, _, _ => by
    rw [chainK_one]
    refine WP.mono (tripleSub_ok hs (.inl ⟨rfl, rfl⟩) (j := 0) (by omega) (by omega) (by omega))
      fun u ⟨O, ⟨c, hc, V⟩, K⟩ => ⟨O, ⟨c, hc, ?_⟩, K⟩
    simp only [val32, Nat.mul_zero, Nat.add_zero, Bool.toNat_false] at V ⊢
    exact V
  | k + 1, hacc, ha, hb, hsa, hsb => by
    have hn := hs.nowrap
    rw [chainK_succ, ite_eq_right_of_eq_false _ _ (eq_false (Nat.add_one_ne_zero k))]
    refine WP.block_append (WP.mono (chainSub_ok hs k (by omega) (by omega) (by omega) (by omega) (by omega))
      fun s₁ ⟨O₁, ⟨c₁, hc₁, V₁⟩, K₁⟩ => ?_)
    have hs₁ := hs.of_keeps K₁ (by decide)
    refine WP.mono (tripleSub_ok hs₁ (.inr ⟨rfl, hc₁⟩) (j := k + 1) (by omega) (by omega) (by omega))
      fun u ⟨O, ⟨c, hc, V⟩, K⟩ => ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (O.mono (by omega) (by omega)),
        ⟨c, hc, ?_⟩, K₁.trans K⟩
    rw [O₁.w32 (d := a + 4 * (k + 1)) (by omega) (by omega), O₁.w32 (d := b + 4 * (k + 1)) (by omega) (by omega)] at V
    rw [val32_succ u.mem base acc (k + 1), val32_succ s.mem base a (k + 1), val32_succ s.mem base b (k + 1),
      O.val32 (by omega) (by omega), pow32_succ (k + 1)]
    generalize 2 ^ (32 * (k + 1)) = P at *
    grind

end VG.Proof.Mont.X86
