import VerifiedGarbage.Proof.Mont.X86.Instr

/- Proofs formerly in `VerifiedGarbage.Proof.Mont.X86.Step`. -/
section

/-!
# Montgomery arithmetic on x86 (32-bit): a multiply-accumulate step

`mulStep acc b j` adds `ecx · b_j` and the carry `ebx` to the word of the
accumulator at `[ebp + acc + 4j]`, and leaves the carry word in `ebx`
(`mulStep_ok`): `x = c b_j + k + t` is below `2⁶⁴`, its low word is stored
and its high word is the carry.
-/

namespace VG.Proof.Mont.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont

/-- The sum of a step fits two words. -/
theorem step_lt {c b k t : Nat} (hc : c < 2 ^ 32) (hb : b < 2 ^ 32) (hk : k < 2 ^ 32) (ht : t < 2 ^ 32) :
    c * b + k + t < 2 ^ 64 := by
  have : c * b ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem ofBool_toNat (c : Bool) : ((BitVec.ofBool c).setWidth 32).toNat = c.toNat := by
  cases c <;> rfl

/-- The registers of a step: `edx:eax = A C`, then `+ K` and `+ T` with the
carries into `edx`, are the low and high words of `C A + K + T`. -/
theorem step_regs (A C K T : BitVec 32) (c3 c5 : Bool)
    (hc3 : c3 = decide (2 ^ 32 ≤ (BitVec.ofNat 32 (A.toNat * C.toNat)).toNat + K.toNat))
    (hc5 : c5 = decide (2 ^ 32 ≤ (BitVec.ofNat 32 (A.toNat * C.toNat) + K).toNat + T.toNat)) :
    (BitVec.ofNat 32 (A.toNat * C.toNat) + K + T).toNat = (C.toNat * A.toNat + K.toNat + T.toNat) % 2 ^ 32 ∧
    (BitVec.ofNat 32 (A.toNat * C.toNat / 2 ^ 32) + 0 + (BitVec.ofBool c3).setWidth 32 + 0 +
      (BitVec.ofBool c5).setWidth 32).toNat = (C.toNat * A.toNat + K.toNat + T.toNat) / 2 ^ 32 := by
  obtain ⟨hw, hq⟩ := mul_words A C
  have hx := VG.Proof.Mont.X86.step_lt C.isLt A.isLt K.isLt T.isLt
  have hK := K.isLt
  have hT := T.isLt
  rw [Nat.mul_comm C.toNat] at hx ⊢
  have he2 : (BitVec.ofNat 32 (A.toNat * C.toNat)).toNat = A.toNat * C.toNat % 2 ^ 32 := BitVec.toNat_ofNat _ _
  have hd2 : (BitVec.ofNat 32 (A.toNat * C.toNat / 2 ^ 32)).toNat = A.toNat * C.toNat / 2 ^ 32 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h0 : ∀ x : BitVec 32, x + 0 = x := BitVec.add_zero
  rw [h0, h0]
  rw [add3_toNat, VG.Proof.Mont.X86.ofBool_toNat, BitVec.toNat_add, BitVec.toNat_add, he2, hd2]
  rw [BitVec.toNat_add, he2] at hc5
  rw [he2] at hc3
  subst hc3 hc5
  generalize A.toNat * C.toNat = P at *
  by_cases h1 : 2 ^ 32 ≤ P % 2 ^ 32 + K.toNat <;> by_cases h2 : 2 ^ 32 ≤ (P % 2 ^ 32 + K.toNat) % 2 ^ 32 + T.toNat <;>
    simp only [h1, h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false, Nat.add_zero] <;>
    constructor <;> omega

/-- `[ebp + acc + 4j] += ecx · [edi + b + 4j] + ebx`, the carry word to `ebx`. -/
theorem mulStep_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {acc b i j : Nat}
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (hb : b + 4 * j + 4 ≤ size) (ht : 4 * i + (acc + 4 * j) + 4 ≤ size) :
    WP isa (.block (mulStep acc b j)) s fun u =>
      u.mem = s.mem.writeW (off base (4 * i + (acc + 4 * j))) (BitVec.ofNat 32
        ((s.gpr .ecx).toNat * w32 s.mem base (b + 4 * j) + (s.gpr .ebx).toNat +
          w32 s.mem base (4 * i + (acc + 4 * j)))) ∧
      (u.gpr .ebx).toNat = ((s.gpr .ecx).toNat * w32 s.mem base (b + 4 * j) + (s.gpr .ebx).toNat +
          w32 s.mem base (4 * i + (acc + 4 * j))) / 2 ^ 32 ∧
      Keeps [.eax, .ebx, .edx] s u := by
  simp only [mulStep]
  refine wp_movS (readSrc_sc hs hb) fun s₁ u₁ _ => ?_
  refine wp_mul fun s₂ m₂ => ?_
  refine wp_addS rfl fun s₃ u₃ c₃ => ?_
  refine wp_adcS rfl c₃ fun s₄ u₄ c₄ => ?_
  have hs₄ : Scr s₄ base size := ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), m₂.other _ (by decide)
    (by decide), u₁.other _ (by decide)]; exact hs.edi, by rw [u₄.wr, u₃.wr, m₂.wr, u₁.wr]; exact hs.wr, hs.nowrap⟩
  have hp₄ : s₄.gpr .ebp = s₄.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), m₂.other _ (by decide) (by decide), u₁.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), m₂.other _ (by decide) (by decide), u₁.other _ (by decide)]
    exact hp
  refine wp_addS (readSrc_at hs₄ hp₄ ht) fun s₅ u₅ c₅ => ?_
  refine wp_adcS rfl c₅ fun s₆ u₆ c₆ => ?_
  have hs₆ : Scr s₆ base size := ⟨by rw [u₆.other _ (by decide), u₅.other _ (by decide)]; exact hs₄.edi,
    by rw [u₆.wr, u₅.wr]; exact hs₄.wr, hs.nowrap⟩
  have hp₆ : s₆.gpr .ebp = s₆.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide)]
    exact hp₄
  refine wp_storeS (hs₆.ea_at hp₆ (by omega)) (hs₆.write ht) fun s₇ m₇ => ?_
  refine wp_movS rfl fun s₈ u₈ _ => WP.block_nil ?_
  -- The registers and memory along the way.
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, m₂.mem, u₁.mem]
  have m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, m₄]
  have ecx₂ : s₁.gpr .ecx = s.gpr .ecx := u₁.other _ (by decide)
  have eax₂ := m₂.eax
  have edx₂ := m₂.edx
  rw [u₁.gpr, ecx₂] at eax₂ edx₂
  have ebx₂ : s₂.gpr .ebx = s.gpr .ebx := by rw [m₂.other _ (by decide) (by decide), u₁.other _ (by decide)]
  have eax₃ : s₃.gpr .eax = s₂.gpr .eax + s₂.gpr .ebx := u₃.gpr
  have edx₄ : s₄.gpr .edx = s₃.gpr .edx + 0 + (BitVec.ofBool _).setWidth 32 := u₄.gpr
  have eax₄ : s₄.gpr .eax = s₃.gpr .eax := u₄.other _ (by decide)
  have edx₃ : s₃.gpr .edx = s₂.gpr .edx := u₃.other _ (by decide)
  have eax₅ : s₅.gpr .eax = s₄.gpr .eax + s.mem.readW (off base (4 * i + (acc + 4 * j))) 32 := by
    rw [u₅.gpr, m₄]
  have edx₆ : s₆.gpr .edx = s₅.gpr .edx + 0 + (BitVec.ofBool _).setWidth 32 := u₆.gpr
  have eax₆ : s₆.gpr .eax = s₅.gpr .eax := u₆.other _ (by decide)
  have edx₅ : s₅.gpr .edx = s₄.gpr .edx := u₅.other _ (by decide)
  -- The arithmetic.
  have hpost := VG.Proof.Mont.X86.step_regs (s.mem.readW (off base (b + 4 * j)) 32) (s.gpr .ecx) (s.gpr .ebx)
    (s.mem.readW (off base (4 * i + (acc + 4 * j))) 32) _ _ rfl rfl
  have ex₆ : s₆.gpr .eax = BitVec.ofNat 32 ((s.mem.readW (off base (b + 4 * j)) 32).toNat * (s.gpr .ecx).toNat) +
      s.gpr .ebx + s.mem.readW (off base (4 * i + (acc + 4 * j))) 32 := by
    rw [eax₆, eax₅, eax₄, eax₃, eax₂, ebx₂]
  have dx₆ := edx₆
  rw [edx₅, edx₄, edx₃, edx₂, eax₄, eax₃, eax₂, ebx₂, m₄] at dx₆
  have hx : s₆.gpr .eax = BitVec.ofNat 32 ((s.gpr .ecx).toNat * w32 s.mem base (b + 4 * j) +
      (s.gpr .ebx).toNat + w32 s.mem base (4 * i + (acc + 4 * j))) := by
    apply BitVec.eq_of_toNat_eq
    rw [ex₆, hpost.1, BitVec.toNat_ofNat]
  refine ⟨by rw [u₈.mem, m₇.mem, m₆, hx], by rw [u₈.gpr, m₇.gpr, dx₆, hpost.2], fun r hr => ?_,
    by rw [u₈.rd, m₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, m₂.rd, u₁.rd],
    by rw [u₈.wr, m₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, m₂.wr, u₁.wr]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h1, h2, h3⟩ := hr
  rw [u₈.other _ h2, m₇.gpr, u₆.other _ h3, u₅.other _ h1, u₄.other _ h3, u₃.other _ h1, m₂.other _ h1 h3,
    u₁.other _ h1]

end VG.Proof.Mont.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Mont.X86.Chain`. -/
section

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
  (List.range k).flatMap fun j => VG.Proof.Mont.X86.triple (if j = 0 then op else op') acc a b j

theorem chain_eq (M : Mod) (op op' : AluOp) (acc a b : Nat) :
    chain M op op' acc a b = VG.Proof.Mont.X86.chainK op op' acc a b (words M) := rfl

theorem diffs_eq (M : Mod) (src : Nat) : diffs M src = VG.Proof.Mont.X86.chainK .sub .sbb M.tmp src M.mo (words M) := rfl

theorem chainK_succ (op op' : AluOp) (acc a b k : Nat) :
    VG.Proof.Mont.X86.chainK op op' acc a b (k + 1) = VG.Proof.Mont.X86.chainK op op' acc a b k ++ VG.Proof.Mont.X86.triple (if k = 0 then op else op') acc a b k := by
  simp only [VG.Proof.Mont.X86.chainK, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem chainK_one (op op' : AluOp) (acc a b : Nat) : VG.Proof.Mont.X86.chainK op op' acc a b 1 = VG.Proof.Mont.X86.triple op acc a b 0 := by
  rw [VG.Proof.Mont.X86.chainK_succ]; rfl

theorem sub_toNat (a b : BitVec 32) : (a - b).toNat = (a.toNat + 2 ^ 32 * 2 - b.toNat) % 2 ^ 32 := by
  have ha := a.isLt
  have hb := b.isLt
  rw [BitVec.toNat_sub]
  omega

/-- A word of an addition, with the carry in `cin` (none for `add`). -/
theorem tripleAdd_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {op : AluOp} {cin : Bool}
    (hop : (op = .add ∧ cin = false) ∨ (op = .adc ∧ s.cf = some cin)) {acc a b j : Nat}
    (ha : a + 4 * j + 4 ≤ size) (hb : b + 4 * j + 4 ≤ size) (hacc : acc + 4 * j + 4 ≤ size) :
    WP isa (.block (VG.Proof.Mont.X86.triple op acc a b j)) s fun u =>
      Outside base (acc + 4 * j) 4 s.mem u.mem ∧
      (∃ c, u.cf = some c ∧ w32 u.mem base (acc + 4 * j) + 2 ^ 32 * c.toNat =
        w32 s.mem base (a + 4 * j) + w32 s.mem base (b + 4 * j) + cin.toNat) ∧
      Keeps [.eax] s u := by
  have hn := hs.nowrap
  simp only [VG.Proof.Mont.X86.triple]
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
    WP isa (.block (VG.Proof.Mont.X86.triple op acc a b j)) s fun u =>
      Outside base (acc + 4 * j) 4 s.mem u.mem ∧
      (∃ c, u.cf = some c ∧ w32 u.mem base (acc + 4 * j) + w32 s.mem base (b + 4 * j) + cin.toNat =
        w32 s.mem base (a + 4 * j) + 2 ^ 32 * c.toNat) ∧
      Keeps [.eax] s u := by
  have hn := hs.nowrap
  simp only [VG.Proof.Mont.X86.triple]
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
    · rw [m₃.mem, w32_write_self, u₂.gpr, VG.Proof.Mont.X86.sub_toNat, u₁.gpr, u₁.mem]
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
    WP isa (.block (VG.Proof.Mont.X86.chainK .add .adc acc a b (k + 1))) s fun u =>
      Outside base acc (4 * (k + 1)) s.mem u.mem ∧
      (∃ c, u.cf = some c ∧ val32 u.mem base acc (k + 1) + 2 ^ (32 * (k + 1)) * c.toNat =
        val32 s.mem base a (k + 1) + val32 s.mem base b (k + 1)) ∧
      Keeps [.eax] s u
  | 0, hacc, ha, hb, _, _ => by
    rw [VG.Proof.Mont.X86.chainK_one]
    refine WP.mono (VG.Proof.Mont.X86.tripleAdd_ok hs (.inl ⟨rfl, rfl⟩) (j := 0) (by omega) (by omega) (by omega))
      fun u ⟨O, ⟨c, hc, V⟩, K⟩ => ⟨O, ⟨c, hc, ?_⟩, K⟩
    simp only [val32, Nat.mul_zero, Nat.add_zero, Bool.toNat_false] at V ⊢
    exact V
  | k + 1, hacc, ha, hb, hsa, hsb => by
    have hn := hs.nowrap
    rw [VG.Proof.Mont.X86.chainK_succ, ite_eq_right_of_eq_false _ _ (eq_false (Nat.add_one_ne_zero k))]
    refine WP.block_append (WP.mono (VG.Proof.Mont.X86.chainAdd_ok hs k (by omega) (by omega) (by omega) (by omega) (by omega))
      fun s₁ ⟨O₁, ⟨c₁, hc₁, V₁⟩, K₁⟩ => ?_)
    have hs₁ := hs.of_keeps K₁ (by decide)
    refine WP.mono (VG.Proof.Mont.X86.tripleAdd_ok hs₁ (.inr ⟨rfl, hc₁⟩) (j := k + 1) (by omega) (by omega) (by omega))
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
    WP isa (.block (VG.Proof.Mont.X86.chainK .sub .sbb acc a b (k + 1))) s fun u =>
      Outside base acc (4 * (k + 1)) s.mem u.mem ∧
      (∃ c, u.cf = some c ∧ val32 u.mem base acc (k + 1) + val32 s.mem base b (k + 1) =
        val32 s.mem base a (k + 1) + 2 ^ (32 * (k + 1)) * c.toNat) ∧
      Keeps [.eax] s u
  | 0, hacc, ha, hb, _, _ => by
    rw [VG.Proof.Mont.X86.chainK_one]
    refine WP.mono (VG.Proof.Mont.X86.tripleSub_ok hs (.inl ⟨rfl, rfl⟩) (j := 0) (by omega) (by omega) (by omega))
      fun u ⟨O, ⟨c, hc, V⟩, K⟩ => ⟨O, ⟨c, hc, ?_⟩, K⟩
    simp only [val32, Nat.mul_zero, Nat.add_zero, Bool.toNat_false] at V ⊢
    exact V
  | k + 1, hacc, ha, hb, hsa, hsb => by
    have hn := hs.nowrap
    rw [VG.Proof.Mont.X86.chainK_succ, ite_eq_right_of_eq_false _ _ (eq_false (Nat.add_one_ne_zero k))]
    refine WP.block_append (WP.mono (VG.Proof.Mont.X86.chainSub_ok hs k (by omega) (by omega) (by omega) (by omega) (by omega))
      fun s₁ ⟨O₁, ⟨c₁, hc₁, V₁⟩, K₁⟩ => ?_)
    have hs₁ := hs.of_keeps K₁ (by decide)
    refine WP.mono (VG.Proof.Mont.X86.tripleSub_ok hs₁ (.inr ⟨rfl, hc₁⟩) (j := k + 1) (by omega) (by omega) (by omega))
      fun u ⟨O, ⟨c, hc, V⟩, K⟩ => ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (O.mono (by omega) (by omega)),
        ⟨c, hc, ?_⟩, K₁.trans K⟩
    rw [O₁.w32 (d := a + 4 * (k + 1)) (by omega) (by omega), O₁.w32 (d := b + 4 * (k + 1)) (by omega) (by omega)] at V
    rw [val32_succ u.mem base acc (k + 1), val32_succ s.mem base a (k + 1), val32_succ s.mem base b (k + 1),
      O.val32 (by omega) (by omega), pow32_succ (k + 1)]
    generalize 2 ^ (32 * (k + 1)) = P at *
    grind

end VG.Proof.Mont.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Mont.X86.Csub`. -/
section

/-!
# Montgomery arithmetic on x86 (32-bit): the conditional subtraction

`csub M src o` reduces the number `T < 2m` at `[src]` (`N` words and a top
word) below `m` into `[o]` (`csub_ok`): `[tmp] = [src] - [mo]` with its
borrow (`diffs`, a chain), then the top word minus the borrow, whose own
borrow makes the mask `eax` (all ones if `T ≥ m`, `mask_ok`), which
selects `[tmp]` or `[src]` word by word (`selects_ok`).
-/

namespace VG.Proof.Mont.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont

/-- The first `k` words of `selects`. -/
def selK (src o tmp k : Nat) : List Instr :=
  (List.range k).flatMap fun j =>
    [.mov .ebx (.mem (sc (src + 4 * j))), .mov .edx (.mem (sc (tmp + 4 * j))), .alu .xor .edx (.reg .ebx),
      .alu .and .edx (.reg .eax), .alu .xor .ebx (.reg .edx), .store (sc (o + 4 * j)) .ebx]

theorem selects_eq (M : Mod) (src o : Nat) : selects M src o = VG.Proof.Mont.X86.selK src o M.tmp (words M) := rfl

theorem selK_succ (src o tmp k : Nat) : VG.Proof.Mont.X86.selK src o tmp (k + 1) = VG.Proof.Mont.X86.selK src o tmp k ++
    ([.mov .ebx (.mem (sc (src + 4 * k))), .mov .edx (.mem (sc (tmp + 4 * k))), .alu .xor .edx (.reg .ebx),
      .alu .and .edx (.reg .eax), .alu .xor .ebx (.reg .edx), .store (sc (o + 4 * k)) .ebx] : List Instr) := by
  simp only [VG.Proof.Mont.X86.selK, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The selection of a word by a mask. -/
theorem select_val (b d : BitVec 32) (k : Bool) :
    b ^^^ ((d ^^^ b) &&& (if k then BitVec.allOnes 32 else 0)) = if k then d else b := by
  cases k
  · simp only [Bool.false_eq_true, ite_false]
    rw [show (0 : BitVec 32) = 0#32 from rfl, BitVec.and_zero, BitVec.xor_zero]
  · simp only [ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm d b, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- `[o] = [tmp]` if `k`, else `[src]`, under the mask `eax` (`k + 1` words). -/
theorem selects_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {src o tmp : Nat} (k : Bool)
    (hm : s.gpr .eax = if k then BitVec.allOnes 32 else 0) :
    ∀ n, src + 4 * n ≤ size → tmp + 4 * n ≤ size → o + 4 * n ≤ size →
    (o + 4 * n ≤ src ∨ src + 4 * n ≤ o) → (o + 4 * n ≤ tmp ∨ tmp + 4 * n ≤ o) →
    WP isa (.block (VG.Proof.Mont.X86.selK src o tmp n)) s fun u =>
      Outside base o (4 * n) s.mem u.mem ∧
      val32 u.mem base o n = val32 s.mem base (if k then tmp else src) n ∧
      Keeps [.ebx, .edx] s u
  | 0, _, _, _, _, _ => WP.block_nil ⟨VG.Proof.Mont.Outside.refl _ _ _ _, rfl, Keeps.refl _ _⟩
  | n + 1, hsrc, htmp, ho, hso, hto => by
    have hn := hs.nowrap
    rw [VG.Proof.Mont.X86.selK_succ]
    refine WP.block_append (WP.mono (VG.Proof.Mont.X86.selects_ok hs k hm n (by omega) (by omega) (by omega) (by omega) (by omega))
      fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
    have hs₁ := hs.of_keeps K₁ (by decide)
    refine wp_movS (readSrc_sc hs₁ (d := src + 4 * n) (by omega)) fun s₂ u₂ _ => ?_
    have hs₂ := hs₁.of_keeps u₂.keeps (by decide)
    refine wp_movS (readSrc_sc hs₂ (d := tmp + 4 * n) (by omega)) fun s₃ u₃ _ => ?_
    have hs₃ := hs₂.of_keeps u₃.keeps (by decide)
    refine wp_logicS (.inr rfl) rfl fun s₄ u₄ => ?_
    refine wp_logicS (.inl rfl) rfl fun s₅ u₅ => ?_
    refine wp_logicS (.inr rfl) rfl fun s₆ u₆ => ?_
    have k₆ : Keeps [.ebx, .edx] s s₆ := (((K₁.widen u₂.keeps).widen u₃.keeps).widen u₄.keeps |>.widen
      u₅.keeps).widen u₆.keeps
    have hs₆ := hs.of_keeps k₆ (by decide)
    refine wp_storeS (hs₆.ea (d := o + 4 * n) (by omega)) (hs₆.write (d := o + 4 * n) (n := 4) (by omega))
      fun s₇ m₇ => WP.block_nil ?_
    have mem₆ : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    have W : Outside base (o + 4 * n) 4 s₁.mem s₇.mem := by
      rw [m₇.mem, mem₆]; exact writeW32_outside _ _ _ (by omega)
    refine ⟨(O₁.mono (o' := o) (n' := 4 * (n + 1)) (Nat.le_refl _) (by omega)).trans
      (W.mono (o' := o) (n' := 4 * (n + 1)) (by omega) (by omega)), ?_,
      k₆.trans (m₇.keeps _)⟩
    have eax₄ : s₄.gpr .eax = s.gpr .eax := by
      rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), K₁.1 _ (by decide)]
    have ebx₆ : s₆.gpr .ebx = s₁.mem.readW (off base (src + 4 * n)) 32 ^^^
        ((s₁.mem.readW (off base (tmp + 4 * n)) 32 ^^^ s₁.mem.readW (off base (src + 4 * n)) 32) &&&
          (if k then BitVec.allOnes 32 else 0)) := by
      rw [u₆.gpr, u₅.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₄.gpr, eax₄, hm,
        u₃.other _ (by decide), u₃.gpr, u₂.gpr, u₂.mem]
      rfl
    rw [VG.Proof.Mont.X86.select_val] at ebx₆
    rw [val32_succ, val32_succ, ← V₁, m₇.mem, mem₆,
      (writeW32_outside s₁.mem base (d := o + 4 * n) (s₆.gpr .ebx) (by omega)).val32 (by omega) (by omega),
      w32_write_self, ebx₆]
    congr 1
    cases k
    · exact congrArg (2 ^ (32 * n) * ·) (O₁.w32 (by omega) (by omega))
    · exact congrArg (2 ^ (32 * n) * ·) (O₁.w32 (by omega) (by omega))

/-- The mask from a borrow: `sbb eax, eax`, then `xor eax, -1`. -/
theorem mask_val (x : BitVec 32) (b : Bool) :
    (x - x - (BitVec.ofBool b).setWidth 32) ^^^ (-1) = if !b then BitVec.allOnes 32 else 0 := by
  rw [BitVec.sub_self]
  cases b <;> decide

/-- `[o] = T mod m` for the number `T < 2m` at `[src]` (`N` words and the
top word), through `[tmp]`. -/
theorem csub_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {N src o m : Nat}
    (hNw : words M = N) (hN : 0 < N) (hsrc : src + 4 * (N + 1) ≤ size) (ho : o + 4 * N ≤ size)
    (htmp : M.tmp + 4 * N ≤ size) (hmo : M.mo + 4 * N ≤ size)
    (hts : M.tmp + 4 * N ≤ src ∨ src + 4 * (N + 1) ≤ M.tmp) (htm : M.tmp + 4 * N ≤ M.mo ∨ M.mo + 4 * N ≤ M.tmp)
    (hos : o + 4 * N ≤ src ∨ src + 4 * N ≤ o) (hot : o + 4 * N ≤ M.tmp ∨ M.tmp + 4 * N ≤ o)
    (hm : val32 s.mem base M.mo N = m) (hV : val32 s.mem base src (N + 1) < 2 * m) :
    WP isa (.block (csub M src o)) s fun u =>
      Outs base [(M.tmp, 4 * N), (o, 4 * N)] s.mem u.mem ∧
      val32 u.mem base o N = val32 s.mem base src (N + 1) % m ∧
      Keeps [.eax, .ebx, .edx] s u := by
  have hn := hs.nowrap
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  simp only [csub, VG.Proof.Mont.X86.diffs_eq, VG.Proof.Mont.X86.selects_eq, hNw, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.block_append (WP.mono (VG.Proof.Mont.X86.chainSub_ok hs k (by omega) (by omega) (by omega) (by omega) (by omega))
    fun s₁ ⟨O₁, ⟨c, hc, V₁⟩, K₁⟩ => ?_)
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine wp_movS (readSrc_sc hs₁ (d := src + 4 * (k + 1)) (by omega)) fun s₂ u₂ cf₂ => ?_
  refine wp_sbbS rfl (by rw [cf₂]; exact hc) fun s₃ u₃ c₃ => ?_
  refine wp_sbbS rfl c₃ fun s₄ u₄ _ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₅ u₅ => ?_
  have k₅ : Keeps [.eax, .ebx, .edx] s s₅ :=
    (((K₁.mono (by decide)).widen u₂.keeps).widen u₃.keeps |>.widen u₄.keeps).widen u₅.keeps
  have hs₅ := hs.of_keeps k₅ (by decide)
  have mask := u₅.gpr
  simp only [reduceCtorEq, ite_false] at mask
  rw [u₄.gpr, VG.Proof.Mont.X86.mask_val] at mask
  have mem₅ : s₅.mem = s₁.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have z : (0 : BitVec 32).toNat = 0 := rfl
  have top : (s₂.gpr .eax).toNat = w32 s.mem base (src + 4 * (k + 1)) := by
    rw [u₂.gpr, ← O₁.w32 (by omega) (by omega)]
  rw [top, z, Nat.zero_add] at mask
  have hsrcN : val32 s₁.mem base src (k + 1) = val32 s.mem base src (k + 1) := O₁.val32 (by omega) (by omega)
  refine WP.mono (VG.Proof.Mont.X86.selects_ok hs₅ _ mask (k + 1) (by omega) (by omega) (by omega) (by omega) (by omega))
    fun u ⟨O, V, K⟩ => ⟨(Outs.of_outside O₁ (by simp)).trans (Outs.of_outside (mem₅ ▸ O) (by simp)), ?_,
      k₅.trans (K.mono (by decide))⟩
  rw [V, mem₅]
  have hmX : m < 2 ^ (32 * (k + 1)) := hm ▸ val32_lt _ _ _ _
  have := csub_arith (T := val32 s.mem base src (k + 1)) (D := val32 s₁.mem base M.tmp (k + 1))
    (top := w32 s.mem base (src + 4 * (k + 1))) (b := c) hmX (val32_lt _ _ _ _)
    (by rw [← val32_succ]; exact hV) (by rw [← hm]; exact V₁)
  rw [val32_succ s.mem base src (k + 1), ← this]
  by_cases h : w32 s.mem base (src + 4 * (k + 1)) < c.toNat
  · simp only [h, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, ite_true, hsrcN]
  · simp only [h, decide_false, Bool.not_false, ite_true, ite_false]

end VG.Proof.Mont.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Mont.X86.Row`. -/
section

/-!
# Montgomery arithmetic on x86 (32-bit): a row

`mulRow acc b N` adds `ecx · [b]` (`N` words) to the window of the
accumulator at `[ebp + acc]`, `w` bytes into the working space (`ebp` is
`edi + 4i`, `w = 4i + acc`): the steps (`steps_ok`) add it to the window's
low `N` words, leaving the carry word in `ebx`, which `carryUp` adds to
words `N` and `N + 1` (`carryUp_ok`); the sum must fit the `N + 2` words
(`mulRow_ok`). Only the window's bytes change.
-/

namespace VG.Proof.Mont.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont

/-- The first `k` steps of a row. -/
def steps (acc b k : Nat) : List Instr := (List.range k).flatMap (mulStep acc b)

theorem steps_succ (acc b k : Nat) : VG.Proof.Mont.X86.steps acc b (k + 1) = VG.Proof.Mont.X86.steps acc b k ++ mulStep acc b k := by
  simp only [VG.Proof.Mont.X86.steps, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

/-- The window's low `k` words `+= ecx · [b] + ebx`, the carry word to `ebx`. -/
theorem steps_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {acc b i w : Nat}
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i)) (hw : 4 * i + acc = w) :
    ∀ {k : Nat}, b + 4 * k ≤ size → w + 4 * k ≤ size → (b + 4 * k ≤ w ∨ w + 4 * k ≤ b) →
    WP isa (.block (VG.Proof.Mont.X86.steps acc b k)) s fun u =>
      Outside base w (4 * k) s.mem u.mem ∧
      val32 u.mem base w k + 2 ^ (32 * k) * (u.gpr .ebx).toNat =
        val32 s.mem base w k + (s.gpr .ecx).toNat * val32 s.mem base b k + (s.gpr .ebx).toNat ∧
      Keeps [.eax, .ebx, .edx] s u
  | 0, _, _, _ => WP.block_nil ⟨VG.Proof.Mont.Outside.refl _ _ _ _, by simp only [val32, Nat.mul_zero, Nat.pow_zero,
      Nat.one_mul, Nat.zero_add], Keeps.refl ..⟩
  | k + 1, hb, hwk, hsep => by
    have hn := hs.nowrap
    rw [VG.Proof.Mont.X86.steps_succ]
    refine WP.block_append (WP.mono (VG.Proof.Mont.X86.steps_ok hs hp hw (k := k) (by omega) (by omega) (by omega))
      fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
    have hs₁ := hs.of_keeps K₁ (by decide)
    have hp₁ : s₁.gpr .ebp = s₁.gpr .edi + BitVec.ofNat 32 (4 * i) := by
      rw [K₁.1 _ (by decide), K₁.1 _ (by decide)]; exact hp
    refine WP.mono (VG.Proof.Mont.X86.mulStep_ok hs₁ hp₁ (j := k) (by omega) (by omega)) fun u ⟨m₂, b₂, K₂⟩ => ?_
    have e : 4 * i + (acc + 4 * k) = w + 4 * k := by omega
    rw [e] at m₂ b₂
    have ecx₁ : s₁.gpr .ecx = s.gpr .ecx := K₁.1 _ (by decide)
    have bk : w32 s₁.mem base (b + 4 * k) = w32 s.mem base (b + 4 * k) := O₁.w32 (by omega) (by omega)
    have tk : w32 s₁.mem base (w + 4 * k) = w32 s.mem base (w + 4 * k) := O₁.w32 (by omega) (by omega)
    rw [ecx₁, bk, tk] at m₂ b₂
    have W := writeW32_outside s₁.mem base (d := w + 4 * k)
      (BitVec.ofNat 32 ((s.gpr .ecx).toNat * w32 s.mem base (b + 4 * k) + (s₁.gpr .ebx).toNat +
        w32 s.mem base (w + 4 * k))) (by omega)
    rw [← m₂] at W
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (W.mono (by omega) (by omega)), ?_, K₁.trans K₂⟩
    have hlow : val32 u.mem base w k = val32 s₁.mem base w k := W.val32 (by omega) (by omega)
    have htop : w32 u.mem base (w + 4 * k) = ((s.gpr .ecx).toNat * w32 s.mem base (b + 4 * k) +
        (s₁.gpr .ebx).toNat + w32 s.mem base (w + 4 * k)) % 2 ^ 32 := by
      rw [m₂, w32_write_self, BitVec.toNat_ofNat]
    rw [val32_succ, val32_succ, val32_succ, hlow, htop, b₂, pow32_succ]
    generalize hxd : (s.gpr .ecx).toNat * w32 s.mem base (b + 4 * k) + (s₁.gpr .ebx).toNat +
      w32 s.mem base (w + 4 * k) = x at *
    have hx := Nat.div_add_mod x (2 ^ 32)
    generalize 2 ^ (32 * k) = P at *
    grind

/-- The carry word `ebx` added to the window's words `N` and `N + 1`, when
the sum fits them. -/
theorem carryUp_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {acc i w N : Nat}
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i)) (hw : 4 * i + acc = w)
    (hN : w + 4 * N + 8 ≤ size)
    (hlt : val32 s.mem base (w + 4 * N) 2 + (s.gpr .ebx).toNat < 2 ^ 64) :
    WP isa (.block (carryUp acc N)) s fun u =>
      Outside base (w + 4 * N) 8 s.mem u.mem ∧
      val32 u.mem base (w + 4 * N) 2 = val32 s.mem base (w + 4 * N) 2 + (s.gpr .ebx).toNat ∧
      Keeps [.eax] s u := by
  have hn := hs.nowrap
  have e₀ : 4 * i + (acc + 4 * N) = w + 4 * N := by omega
  have e₁ : 4 * i + (acc + 4 * N + 4) = w + 4 * N + 4 := by omega
  simp only [carryUp]
  refine wp_movS (readSrc_at hs hp (d := acc + 4 * N) (by omega)) fun s₁ u₁ cf₁ => ?_
  refine wp_addS rfl fun s₂ u₂ c₂ => ?_
  have k₂ : Keeps [.eax] s s₂ := ⟨fun r hr => by
      rw [u₂.other _ (by simpa using hr), u₁.other _ (by simpa using hr)],
    by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
  have hs₂ := hs.of_keeps k₂ (by decide)
  have hp₂ : s₂.gpr .ebp = s₂.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [k₂.1 _ (by decide), k₂.1 _ (by decide)]; exact hp
  refine wp_storeS (hs₂.ea_at hp₂ (d := acc + 4 * N) (by omega)) (hs₂.write (n := 4) (by omega))
    fun s₃ m₃ => ?_
  have k₃ : Keeps [.eax] s s₃ := ⟨fun r hr => by rw [m₃.gpr]; exact k₂.1 r hr, by rw [m₃.rd, k₂.2.1],
    by rw [m₃.wr, k₂.2.2]⟩
  have hs₃ := hs.of_keeps k₃ (by decide)
  have hp₃ : s₃.gpr .ebp = s₃.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [k₃.1 _ (by decide), k₃.1 _ (by decide)]; exact hp
  refine wp_movS (readSrc_at hs₃ hp₃ (d := acc + 4 * N + 4) (by omega)) fun s₄ u₄ cf₄ => ?_
  refine wp_adcS rfl (by rw [cf₄, m₃.cf]; exact c₂) fun s₅ u₅ _ => ?_
  have k₅ : Keeps [.eax] s s₅ := ⟨fun r hr => by
      rw [u₅.other _ (by simpa using hr), u₄.other _ (by simpa using hr)]; exact k₃.1 r hr,
    by rw [u₅.rd, u₄.rd, k₃.2.1], by rw [u₅.wr, u₄.wr, k₃.2.2]⟩
  have hs₅ := hs.of_keeps k₅ (by decide)
  have hp₅ : s₅.gpr .ebp = s₅.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [k₅.1 _ (by decide), k₅.1 _ (by decide)]; exact hp
  refine wp_storeS (hs₅.ea_at hp₅ (d := acc + 4 * N + 4) (by omega)) (hs₅.write (n := 4) (by omega))
    fun s₆ m₆ => WP.block_nil ?_
  rw [e₀] at m₃
  rw [e₁] at m₆
  have hm₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have hm₅ : s₅.mem = s₃.mem := by rw [u₅.mem, u₄.mem]
  rw [hm₂] at m₃
  rw [hm₅, m₃.mem] at m₆
  have W₀ := writeW32_outside s.mem base (d := w + 4 * N) (s₂.gpr .eax) (by omega)
  have W₁ := writeW32_outside (s.mem.writeW (off base (w + 4 * N)) (s₂.gpr .eax)) base
    (d := w + 4 * N + 4) (s₅.gpr .eax) (by omega)
  rw [← m₆.mem] at W₁
  refine ⟨(W₀.mono (Nat.le_refl _) (by omega)).trans (W₁.mono (by omega) (by omega)), ?_,
    ⟨fun r hr => by rw [m₆.gpr]; exact k₅.1 r hr, by rw [m₆.rd, k₅.2.1], by rw [m₆.wr, k₅.2.2]⟩⟩
  -- The words.
  have a₂ : s₂.gpr .eax = s.mem.readW (off base (w + 4 * N)) 32 + s.gpr .ebx := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), e₀]
  have h0 : ∀ x : BitVec 32, x + 0 = x := BitVec.add_zero
  have a₅ : s₅.gpr .eax = s₃.mem.readW (off base (w + 4 * N + 4)) 32 +
      (BitVec.ofBool (decide (2 ^ 32 ≤ (s₁.gpr .eax).toNat + (s₁.gpr .ebx).toNat))).setWidth 32 := by
    rw [u₅.gpr, u₄.gpr, e₁, h0]
  have t₁ : w32 s₃.mem base (w + 4 * N + 4) = w32 s.mem base (w + 4 * N + 4) := by
    rw [m₃.mem]; exact w32_write_ne hn (by omega) (by omega) (by omega) _
  rw [u₁.gpr, u₁.other _ (by decide), e₀, m₃.mem] at a₅
  simp only [val32, Nat.mul_zero, Nat.add_zero]
  rw [m₆.mem, w32_write_ne hn (by omega) (by omega) (by omega), w32_write_self, w32_write_self,
    a₂, a₅, BitVec.toNat_add, BitVec.toNat_add, VG.Proof.Mont.X86.ofBool_toNat]
  simp only [val32, Nat.mul_zero, Nat.add_zero] at hlt
  rw [m₃.mem] at t₁
  simp only [w32] at t₁ hlt ⊢
  rw [t₁]
  have := (s.mem.readW (off base (w + 4 * N)) 32).isLt
  have := (s.gpr .ebx).isLt
  by_cases hc : 2 ^ 32 ≤ (s.mem.readW (off base (w + 4 * N)) 32).toNat + (s.gpr .ebx).toNat <;>
    simp only [hc, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

theorem pow32_add (a b : Nat) : 2 ^ (32 * (a + b)) = 2 ^ (32 * a) * 2 ^ (32 * b) := by
  rw [Nat.mul_add, Nat.pow_add]

/-- The window `+= ecx · [b]` (`N` words), when the sum fits its `N + 2`
words. -/
theorem mulRow_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {acc b i w N : Nat}
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i)) (hw : 4 * i + acc = w)
    (hb : b + 4 * N ≤ size) (hwN : w + 4 * N + 8 ≤ size) (hsep : b + 4 * N ≤ w ∨ w + 4 * N + 8 ≤ b)
    (hlt : val32 s.mem base w (N + 2) + (s.gpr .ecx).toNat * val32 s.mem base b N < 2 ^ (32 * (N + 2))) :
    WP isa (.block (mulRow acc b N)) s fun u =>
      Outside base w (4 * N + 8) s.mem u.mem ∧
      val32 u.mem base w (N + 2) = val32 s.mem base w (N + 2) + (s.gpr .ecx).toNat * val32 s.mem base b N ∧
      Keeps [.eax, .ebx, .edx] s u := by
  have hn := hs.nowrap
  simp only [mulRow, List.cons_append]
  refine wp_movS rfl fun s₀ u₀ _ => ?_
  have k₀ : Keeps [.eax, .ebx, .edx] s s₀ := ⟨fun r hr => u₀.other r (by simp_all), u₀.rd, u₀.wr⟩
  have hs₀ := hs.of_keeps k₀ (by decide)
  have hp₀ : s₀.gpr .ebp = s₀.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [k₀.1 _ (by decide), k₀.1 _ (by decide)]; exact hp
  refine WP.block_append (WP.mono (VG.Proof.Mont.X86.steps_ok hs₀ hp₀ hw (k := N) hb (by omega) (by omega))
    fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
  have k₁ := k₀.trans K₁
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hp₁ : s₁.gpr .ebp = s₁.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [k₁.1 _ (by decide), k₁.1 _ (by decide)]; exact hp
  have z : (0 : BitVec 32).toNat = 0 := rfl
  rw [u₀.gpr, u₀.mem, u₀.other _ (by decide), z, Nat.add_zero] at V₁
  rw [u₀.mem] at O₁
  have hhi : val32 s₁.mem base (w + 4 * N) 2 = val32 s.mem base (w + 4 * N) 2 := O₁.val32 (by omega) (by omega)
  have hsplit : val32 s.mem base w (N + 2) = val32 s.mem base w N + 2 ^ (32 * N) * val32 s.mem base (w + 4 * N) 2 :=
    val32_append _ _ _ _ _
  rw [VG.Proof.Mont.X86.pow32_add, show 32 * 2 = 64 by rfl] at hlt
  have hP : 0 < 2 ^ (32 * N) := Nat.two_pow_pos _
  have hlt₁ : val32 s₁.mem base (w + 4 * N) 2 + (s₁.gpr .ebx).toNat < 2 ^ 64 := by
    rw [hhi]
    rw [hsplit] at hlt
    refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ (32 * N)) ?_
    rw [Nat.mul_add]
    omega
  refine WP.mono (VG.Proof.Mont.X86.carryUp_ok hs₁ hp₁ hw hwN hlt₁) fun u ⟨O₂, V₂, K₂⟩ => ⟨?_, ?_, k₁.trans (K₂.mono (by simp))⟩
  · exact (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))
  · rw [val32_append, V₂, (O₂.val32 (d := w) (k := N) (by omega) (by omega)), hhi, hsplit, Nat.mul_add]
    omega

end VG.Proof.Mont.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Mont.X86.Loop`. -/
section

/-!
# Montgomery arithmetic on x86 (32-bit): the loop of the multiplication

An iteration of `mul`'s loop (`row`), at `ebp = edi + 4i`, adds `a_i [b]`
and then `q m` to the window at `acc + 4i`, which holds `T`, the number
below `2m` in the accumulator's words from `i` up (`row_ok`): `q` makes the
sum's low word zero, so the accumulator's words from `i + 1` up hold
`(T + a_i B + q m) / 2³²`, below `2m` again; `ZF` is whether `i + 1 = N`.
-/

namespace VG.Proof.Mont.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont

/-- The registers the arithmetic changes. -/
def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp]

/-- `t₀ + (t₀ m' mod 2³²) m ≡ 0 (mod 2³²)` when `m m' ≡ -1`. -/
theorem mont_low32 (t0 minv m : Nat) (h : (m * minv + 1) % 2 ^ 32 = 0) :
    (t0 + t0 * minv % 2 ^ 32 * m) % 2 ^ 32 = 0 := by
  rw [Nat.add_mod, Nat.mul_mod (t0 * minv % 2 ^ 32), Nat.mod_mod, ← Nat.mul_mod,
    ← Nat.add_mod, show t0 + t0 * minv * m = t0 * (m * minv + 1) by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm minv m]; omega,
    Nat.mul_mod, h, Nat.mul_zero, Nat.zero_mod]

/-- `-m⁻¹ mod 2⁶⁴` gives `-m⁻¹ mod 2³²`. -/
theorem minv32_inv {M : Mod} {m : Nat} (h : (m * M.minv.toNat + 1) % 2 ^ 64 = 0) :
    (m * (minv32 M).toNat + 1) % 2 ^ 32 = 0 := by
  rw [minv32, BitVec.toNat_setWidth, Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod,
    ← Nat.mod_mod_of_dvd (m * M.minv.toNat + 1) (show 2 ^ 32 ∣ 2 ^ 64 from ⟨2 ^ 32, by decide⟩), h]

/-- A row's sum stays below `2m` once divided. -/
theorem row_lt {T a B q m : Nat} (hT : T < 2 * m) (ha : a < 2 ^ 32) (hB : B < m) (hq : q < 2 ^ 32) :
    T + a * B + q * m < 2 ^ 32 * (2 * m) := by
  have h1 : a * B ≤ (2 ^ 32 - 1) * B := Nat.mul_le_mul_right _ (by omega)
  have h2 : q * m ≤ (2 ^ 32 - 1) * m := Nat.mul_le_mul_right _ (by omega)
  omega

/-- The offsets of a multiplication: `[a]`, `[b]` and the modulus (`N`
words) in the working space and apart from the accumulator (`2N + 1` words
at `acc`). -/
structure MulLay (N size acc a b mo : Nat) : Prop where
  acc_le : acc + 4 * (2 * N + 1) ≤ size
  a_le : a + 4 * N ≤ size
  b_le : b + 4 * N ≤ size
  mo_le : mo + 4 * N ≤ size
  sa : a + 4 * N ≤ acc ∨ acc + 4 * (2 * N + 1) ≤ a
  sb : b + 4 * N ≤ acc ∨ acc + 4 * (2 * N + 1) ≤ b
  smo : mo + 4 * N ≤ acc ∨ acc + 4 * (2 * N + 1) ≤ mo

/-- `ZF` after the loop's comparison: whether `ebp` reached `edi + 4N`. -/
theorem row_zf (e : BitVec 32) {i N : Nat} (hi : i < N) (hN : 4 * N < 2 ^ 32) :
    (e + BitVec.ofNat 32 (4 * i) + 4 - (e + BitVec.ofNat 32 (4 * N)) == 0) = decide (i + 1 = N) := by
  by_cases h : i + 1 = N
  · subst h; simp only [decide_true, beq_iff_eq]; bv_omega
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]; bv_omega

theorem row_ebp (e : BitVec 32) (i : Nat) :
    e + BitVec.ofNat 32 (4 * i) + 4 = e + BitVec.ofNat 32 (4 * (i + 1)) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have : (4 : BitVec 32).toNat = 4 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, this]
  omega

/-- An iteration of the loop. -/
theorem row_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {N acc a b i m : Nat}
    (hNw : words M = N) (hL : VG.Proof.Mont.X86.MulLay N size acc a b M.mo) (hi : i < N)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (hm : val32 s.mem base M.mo N = m) (hinv : (m * (minv32 M).toNat + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem base b N < m)
    (hT : val32 s.mem base (acc + 4 * i) (2 * N + 1 - i) < 2 * m) :
    WP isa (.block (row M acc a b)) s fun u =>
      u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 (4 * (i + 1)) ∧
      u.zf = some (decide (i + 1 = N)) ∧
      Outside base acc (4 * (2 * N + 1)) s.mem u.mem ∧
      (∃ q, 2 ^ 32 * val32 u.mem base (acc + 4 * (i + 1)) (2 * N + 1 - (i + 1)) =
        val32 s.mem base (acc + 4 * i) (2 * N + 1 - i) + w32 s.mem base (a + 4 * i) * val32 s.mem base b N +
          q * m) ∧
      val32 u.mem base (acc + 4 * (i + 1)) (2 * N + 1 - (i + 1)) < 2 * m ∧
      Keeps VG.Proof.Mont.X86.clob s u := by
  have hn := hs.nowrap
  have := hL.acc_le
  have := hL.a_le
  have := hL.b_le
  have := hL.mo_le
  have := hL.sa
  have := hL.sb
  have := hL.smo
  have hmP : m < 2 ^ (32 * N) := hm ▸ val32_lt _ _ _ _
  have hP : 0 < 2 ^ (32 * N) := Nat.two_pow_pos _
  have hpow : 2 ^ (32 * (N + 2)) = 2 ^ (32 * N) * 2 ^ 64 := by rw [VG.Proof.Mont.X86.pow32_add]
  have hpow1 : 2 ^ (32 * (N + 1)) = 2 ^ (32 * N) * 2 ^ 32 := by rw [VG.Proof.Mont.X86.pow32_add]
  -- The window: the accumulator's words from `i`, of which only the low
  -- `N + 2` may be nonzero.
  obtain ⟨w, hw⟩ : ∃ w, 4 * i + acc = w := ⟨_, rfl⟩
  have ew : acc + 4 * i = w := by omega
  rw [ew] at hT
  have hsplit : ∀ mem : Mem, val32 mem base w (2 * N + 1 - i) =
      val32 mem base w (N + 2) + 2 ^ (32 * (N + 2)) * val32 mem base (w + 4 * (N + 2)) (N - 1 - i) := by
    intro mem
    rw [show 2 * N + 1 - i = (N + 2) + (N - 1 - i) by omega, val32_append]
  have habove : val32 s.mem base (w + 4 * (N + 2)) (N - 1 - i) = 0 := by
    rw [hsplit] at hT
    rcases Nat.eq_zero_or_pos (val32 s.mem base (w + 4 * (N + 2)) (N - 1 - i)) with h | h
    · exact h
    · have : 2 ^ (32 * (N + 2)) * 1 ≤ 2 ^ (32 * (N + 2)) * val32 s.mem base (w + 4 * (N + 2)) (N - 1 - i) :=
        Nat.mul_le_mul_left _ h
      have : 2 * 2 ^ (32 * N) ≤ 2 ^ (32 * (N + 2)) := by rw [hpow]; omega
      omega
  have hTw : val32 s.mem base w (N + 2) = val32 s.mem base w (2 * N + 1 - i) := by
    rw [hsplit s.mem, habove]; omega
  simp only [row]
  rw [hNw]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- `ecx = a_i`.
  refine wp_movS (readSrc_at hs hp (d := a) (by omega)) fun s₁ u₁ _ => ?_
  have k₁ : Keeps VG.Proof.Mont.X86.clob s s₁ := u₁.keeps.mono (by decide)
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hp₁ : s₁.gpr .ebp = s₁.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [u₁.other _ (by decide), u₁.other _ (by decide)]; exact hp
  have ecx₁ : (s₁.gpr .ecx).toNat = w32 s.mem base (a + 4 * i) := by rw [u₁.gpr, Nat.add_comm a]
  have mem₁ : s₁.mem = s.mem := u₁.mem
  -- The window `+= a_i B`.
  have hlt₁ : val32 s₁.mem base w (N + 2) + (s₁.gpr .ecx).toNat * val32 s₁.mem base b N < 2 ^ (32 * (N + 2)) := by
    rw [mem₁, hTw, ecx₁, hpow]
    have := (s.mem.readW (off base (a + 4 * i)) 32).isLt
    have : w32 s.mem base (a + 4 * i) * val32 s.mem base b N ≤ (2 ^ 32 - 1) * val32 s.mem base b N :=
      Nat.mul_le_mul_right _ (by omega)
    have : 2 ^ (32 * N) * 2 ^ 32 ≤ 2 ^ (32 * N) * 2 ^ 64 := Nat.mul_le_mul_left _ (by decide)
    have : m * 2 ^ 32 < 2 ^ (32 * N) * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hmP (by decide)
    omega
  refine WP.block_append (WP.mono (VG.Proof.Mont.X86.mulRow_ok hs₁ hp₁ hw hL.b_le (by omega) (by omega) hlt₁)
    fun s₂ ⟨O₂, V₂, K₂⟩ => ?_)
  have k₂ : Keeps VG.Proof.Mont.X86.clob s s₂ := k₁.widen K₂
  have hs₂ := hs.of_keeps k₂ (by decide)
  have hp₂ : s₂.gpr .ebp = s₂.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [K₂.1 _ (by decide), K₂.1 _ (by decide)]; exact hp₁
  rw [mem₁, hTw, ecx₁] at V₂
  rw [mem₁] at O₂
  -- `ecx = q`, from the window's low word.
  refine wp_movS (readSrc_at hs₂ hp₂ (d := acc) (by omega)) fun s₃ u₃ _ => ?_
  refine wp_movS rfl fun s₄ u₄ _ => ?_
  refine wp_mul fun s₅ m₅ => ?_
  refine wp_movS rfl fun s₆ u₆ _ => ?_
  have k₆ : Keeps VG.Proof.Mont.X86.clob s s₆ :=
    ((k₂.widen u₃.keeps).widen u₄.keeps |>.widen m₅.keeps).widen u₆.keeps
  have hs₆ := hs.of_keeps k₆ (by decide)
  have hp₆ : s₆.gpr .ebp = s₆.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [u₆.other _ (by decide), m₅.other _ (by decide) (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₆.other _ (by decide), m₅.other _ (by decide) (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide)]; exact hp₂
  have mem₆ : s₆.mem = s₂.mem := by rw [u₆.mem, m₅.mem, u₄.mem, u₃.mem]
  have t0 : (s₂.mem.readW (off base (4 * i + acc)) 32).toNat = val32 s₂.mem base w (N + 2) % 2 ^ 32 := by
    rw [hw, val32]
    have := (s₂.mem.readW (off base w) 32).isLt
    simp only [w32]
    omega
  have ecx₆ : (s₆.gpr .ecx).toNat = val32 s₂.mem base w (N + 2) % 2 ^ 32 * (minv32 M).toNat % 2 ^ 32 := by
    rw [u₆.gpr, m₅.eax, u₄.other .eax (by decide), u₃.gpr, u₄.gpr, BitVec.toNat_ofNat, t0]
  -- The window `+= q m`.
  have hmo₂ : val32 s₂.mem base M.mo N = m := by rw [O₂.val32 (by omega) (by omega), hm]
  have hq : (s₆.gpr .ecx).toNat < 2 ^ 32 := (s₆.gpr .ecx).isLt
  have hW1 := VG.Proof.Mont.X86.row_lt (q := 0) (a := w32 s.mem base (a + 4 * i)) hT (s.mem.readW (off base (a + 4 * i)) 32).isLt hB (by decide)
  have hlt₆ : val32 s₆.mem base w (N + 2) + (s₆.gpr .ecx).toNat * val32 s₆.mem base M.mo N < 2 ^ (32 * (N + 2)) := by
    rw [mem₆, V₂, hmo₂, hpow]
    have : (s₆.gpr .ecx).toNat * m ≤ (2 ^ 32 - 1) * m := Nat.mul_le_mul_right _ (by omega)
    have : m * 2 ^ 32 < 2 ^ (32 * N) * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hmP (by decide)
    have : 2 ^ (32 * N) * 2 ^ 32 ≤ 2 ^ (32 * N) * 2 ^ 64 := Nat.mul_le_mul_left _ (by decide)
    omega
  refine WP.block_append (WP.mono (VG.Proof.Mont.X86.mulRow_ok hs₆ hp₆ hw hL.mo_le (by omega) (by omega) hlt₆)
    fun s₇ ⟨O₇, V₇, K₇⟩ => ?_)
  have k₇ : Keeps VG.Proof.Mont.X86.clob s s₇ := k₆.widen K₇
  have hp₇ : s₇.gpr .ebp = s₇.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [K₇.1 _ (by decide), K₇.1 _ (by decide)]; exact hp₆
  rw [mem₆, V₂, hmo₂] at V₇
  rw [mem₆] at O₇
  -- `ebp += 4`, and the comparison.
  refine wp_addS rfl fun s₈ u₈ _ => ?_
  refine wp_movS rfl fun s₉ u₉ _ => ?_
  refine wp_addS rfl fun s₁₀ u₁₀ _ => ?_
  refine wp_cmpS rfl fun s₁₁ f₁₁ z₁₁ => WP.block_nil ?_
  have k₁₁ : Keeps VG.Proof.Mont.X86.clob s s₁₁ :=
    (((k₇.widen u₈.keeps).widen u₉.keeps).widen u₁₀.keeps).widen (f₁₁.keeps VG.Proof.Mont.X86.clob)
  have mem₁₁ : s₁₁.mem = s₇.mem := by rw [f₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem]
  have edi₁₁ : s₁₁.gpr .edi = s₇.gpr .edi := by
    rw [f₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide)]
  have ebp₁₁ : s₁₁.gpr .ebp = s₇.gpr .ebp + 4 := by
    rw [f₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr]
  have edx₁₀ : s₁₀.gpr .edx = s₇.gpr .edi + BitVec.ofNat 32 (4 * N) := by
    rw [u₁₀.gpr, u₉.gpr, u₈.other _ (by decide)]
  have hN32 : 4 * N < 2 ^ 32 := by omega
  -- The new window.
  have hO : Outside base w (4 * N + 8) s.mem s₁₁.mem := by
    rw [mem₁₁]; exact O₂.trans O₇
  have habove' : val32 s₁₁.mem base (w + 4 * (N + 2)) (N - 1 - i) = 0 := by
    rw [hO.val32 (by omega) (by omega), habove]
  have hW2 : val32 s₁₁.mem base w (N + 2) = val32 s.mem base w (2 * N + 1 - i) +
      w32 s.mem base (a + 4 * i) * val32 s.mem base b N + (s₆.gpr .ecx).toNat * m := by
    rw [mem₁₁, V₇]
  have hlow : val32 s₁₁.mem base w (N + 2) % 2 ^ 32 = 0 := by
    rw [hW2, ← V₂, ecx₆, ← Nat.mod_add_mod]; exact VG.Proof.Mont.X86.mont_low32 _ _ _ hinv
  have hT' : val32 s₁₁.mem base (acc + 4 * (i + 1)) (2 * N + 1 - (i + 1)) =
      val32 s₁₁.mem base (w + 4) (N + 1) := by
    rw [show acc + 4 * (i + 1) = w + 4 by omega, show 2 * N + 1 - (i + 1) = (N + 1) + (N - 1 - i) by omega,
      val32_append, show w + 4 + 4 * (N + 1) = w + 4 * (N + 2) by omega, habove', Nat.mul_zero, Nat.add_zero]
  have hsh : val32 s₁₁.mem base w (N + 2) = w32 s₁₁.mem base w + 2 ^ 32 * val32 s₁₁.mem base (w + 4) (N + 1) :=
    rfl
  have h32 : w32 s₁₁.mem base w < 2 ^ 32 := (s₁₁.mem.readW (off base w) 32).isLt
  have hW : 2 ^ 32 * val32 s₁₁.mem base (w + 4) (N + 1) = val32 s₁₁.mem base w (N + 2) := by omega
  have hlt := VG.Proof.Mont.X86.row_lt (a := w32 s.mem base (a + 4 * i)) hT (s.mem.readW (off base (a + 4 * i)) 32).isLt hB hq
  refine ⟨?_, ?_, hO.mono (by omega) (by omega), ⟨(s₆.gpr .ecx).toNat, ?_⟩, ?_, k₁₁⟩
  · rw [ebp₁₁, edi₁₁, hp₇, VG.Proof.Mont.X86.row_ebp]
  · have ebp₁₀ : s₁₀.gpr .ebp = s₇.gpr .ebp + 4 := by
      rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr]
    rw [z₁₁, ebp₁₀, edx₁₀, hp₇, VG.Proof.Mont.X86.row_zf _ hi hN32]
  · rw [hT', hW, hW2, ew]
  · rw [hT']
    rw [← hW2, ← hW] at hlt
    omega

/-- The invariant of the loop, before iteration `i`: the accumulator's
words from `i` up hold `T < 2m` with `2^(32 i) T ≡ A_i B`, for the low `i`
words `A_i` of `[a]`. -/
structure LoopInv (base : Addr) (N acc a b m i : Nat) (s t : State) : Prop where
  ebp : t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * i)
  out : Outside base acc (4 * (2 * N + 1)) s.mem t.mem
  keeps : Keeps VG.Proof.Mont.X86.clob s t
  lt : val32 t.mem base (acc + 4 * i) (2 * N + 1 - i) < 2 * m
  cong : ∃ U, 2 ^ (32 * i) * val32 t.mem base (acc + 4 * i) (2 * N + 1 - i) =
    val32 s.mem base a i * val32 s.mem base b N + U * m

/-- The loop of `mul`: from the invariant at 0 to the invariant at `N`. -/
theorem loop_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {N acc a b m : Nat}
    (hNw : words M = N) (hL : VG.Proof.Mont.X86.MulLay N size acc a b M.mo) (hN : 0 < N)
    (hm : val32 s.mem base M.mo N = m) (hinv : (m * (minv32 M).toNat + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem base b N < m) {t : State} (h0 : VG.Proof.Mont.X86.LoopInv base N acc a b m 0 s t) :
    WP isa (.loop (.block (row M acc a b)) .ne) t fun u => VG.Proof.Mont.X86.LoopInv base N acc a b m N s u := by
  have := hL.acc_le
  have := hL.a_le
  have := hL.b_le
  have := hL.mo_le
  have := hL.sa
  have := hL.sb
  have := hL.smo
  have hn := hs.nowrap
  refine WP.loop (M := isa)
    (fun n t' => ∃ i, n = N - i ∧ i < N ∧ VG.Proof.Mont.X86.LoopInv base N acc a b m i s t') ?_ N t ⟨0, rfl, hN, h0⟩
  rintro n t' ⟨i, rfl, hi, I⟩
  have ht := hs.of_keeps I.keeps (by decide)
  have hm' : val32 t'.mem base M.mo N = m := by rw [I.out.val32 (by omega) (by omega), hm]
  have hb' : val32 t'.mem base b N = val32 s.mem base b N := I.out.val32 (by omega) (by omega)
  have ha' : w32 t'.mem base (a + 4 * i) = w32 s.mem base (a + 4 * i) := I.out.w32 (by omega) (by omega)
  refine WP.mono (VG.Proof.Mont.X86.row_ok ht hNw hL hi I.ebp hm' hinv (hb' ▸ hB) I.lt)
    fun u ⟨hp, hz, O, ⟨q, hq⟩, hT, K⟩ => ?_
  rw [hb', ha'] at hq
  have I' : VG.Proof.Mont.X86.LoopInv base N acc a b m (i + 1) s u := by
    refine ⟨hp, I.out.trans (O.mono (Nat.le_refl _) (Nat.le_refl _)), I.keeps.trans K, hT, ?_⟩
    obtain ⟨U, hU⟩ := I.cong
    refine ⟨U + 2 ^ (32 * i) * q, ?_⟩
    rw [pow32_succ, val32_succ, Nat.mul_assoc, Nat.mul_left_comm, hq]
    generalize 2 ^ (32 * i) = P at *
    grind
  by_cases hNi : i + 1 = N
  · refine .inl ⟨by simp only [eval, hz, hNi, decide_true, Option.map_some, Bool.not_true], hNi ▸ I'⟩
  · exact .inr ⟨by simp only [eval, hz, decide_eq_false hNi, Option.map_some, Bool.not_false],
      N - (i + 1), by omega, i + 1, rfl, by omega, I'⟩

end VG.Proof.Mont.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Mont.X86.Ops`. -/
section

/-!
# Montgomery arithmetic on x86 (32-bit): the operations

For a modulus `m` in the working space (`ModOk`) and an accumulator of
`accLen M` bytes at `acc` apart from the numbers (`OpLay`): `mul acc o a b`
writes `[a] [b] R⁻¹ mod m` to `[o]` (`mul_ok`), `add` writes
`[a] + [b] mod m` (`add_ok`) and `sub` writes `[a] - [b] mod m` (`sub_ok`),
for `[a]`, `[b]` below `m`, in the shape of the other targets' operations
(`n` 64-bit words). Each changes only the registers `clob`, the result, the
temporary area and the accumulator (`OpKeep`).
-/

namespace VG.Proof.Mont.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont

/-- The bytes of the accumulator: `2N + 1` words. -/
def accLen (M : Mod) : Nat := 4 * (2 * words M + 1)

/-- Where the operations' numbers are: in the working space, and the
accumulator apart from them, from the modulus and from the temporary area,
which `[o]` is apart from too. -/
structure OpLay (M : Mod) (size acc o a b : Nat) : Prop where
  acc_le : acc + VG.Proof.Mont.X86.accLen M ≤ size
  o_le : o + 8 * M.n ≤ size
  a_le : a + 8 * M.n ≤ size
  b_le : b + 8 * M.n ≤ size
  acc_o : acc + VG.Proof.Mont.X86.accLen M ≤ o ∨ o + 8 * M.n ≤ acc
  acc_a : acc + VG.Proof.Mont.X86.accLen M ≤ a ∨ a + 8 * M.n ≤ acc
  acc_b : acc + VG.Proof.Mont.X86.accLen M ≤ b ∨ b + 8 * M.n ≤ acc
  acc_mo : acc + VG.Proof.Mont.X86.accLen M ≤ M.mo ∨ M.mo + 8 * M.n ≤ acc
  acc_tmp : acc + VG.Proof.Mont.X86.accLen M ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ acc
  o_tmp : o + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ o

/-- What an operation writing `[o]` keeps: the registers but `clob`, the
regions, and the memory but `[o]`, the temporary area and the accumulator. -/
structure OpKeep (M : Mod) (base : Addr) (acc o : Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ VG.Proof.Mont.X86.clob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Outs base [(o, 8 * M.n), (M.tmp, 8 * M.n), (acc, VG.Proof.Mont.X86.accLen M)] s.mem s'.mem

theorem OpKeep.of {M : Mod} {base : Addr} {acc o : Nat} {s s' : State} {rs : List Reg} (h : Keeps rs s s')
    (hr : ∀ r ∈ rs, r ∈ VG.Proof.Mont.X86.clob := by decide)
    (hm : Outs base [(o, 8 * M.n), (M.tmp, 8 * M.n), (acc, VG.Proof.Mont.X86.accLen M)] s.mem s'.mem) : VG.Proof.Mont.X86.OpKeep M base acc o s s' :=
  ⟨fun r h' => h.1 r fun h'' => h' (hr r h''), h.2.1, h.2.2, hm⟩

/-- `k` stores of `eax = 0` from `[acc]`. -/
theorem stores0_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (heax : s.gpr .eax = 0)
    {acc : Nat} : ∀ k, acc + 4 * k ≤ size →
    WP isa (.block ((List.range k).map fun j => .store (sc (acc + 4 * j)) .eax)) s fun u =>
      Outside base acc (4 * k) s.mem u.mem ∧ val32 u.mem base acc k = 0 ∧ Keeps [] s u
  | 0, _ => WP.block_nil ⟨VG.Proof.Mont.Outside.refl _ _ _ _, rfl, Keeps.refl _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    refine WP.block_append (WP.mono (VG.Proof.Mont.X86.stores0_ok hs heax k (by omega)) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
    have hs₁ := hs.of_keeps K₁ (by decide)
    refine wp_storeS (hs₁.ea (d := acc + 4 * k) (by omega)) (hs₁.write (d := acc + 4 * k) (n := 4) (by omega))
      fun u m => WP.block_nil ⟨?_, ?_, K₁.trans (m.keeps _)⟩
    · rw [m.mem]
      exact (O₁.mono (Nat.le_refl _) (by omega)).trans
        ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))
    · rw [val32_succ, m.mem, (writeW32_outside _ _ _ (by omega)).val32 (by omega) (by omega), V₁,
        w32_write_self, K₁.1 _ (by decide), heax]
      rfl

theorem zeros_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {acc k : Nat}
    (hk : acc + 4 * k ≤ size) :
    WP isa (.block (zeros acc k)) s fun u =>
      Outside base acc (4 * k) s.mem u.mem ∧ val32 u.mem base acc k = 0 ∧ Keeps [.eax] s u := by
  simp only [zeros]
  refine wp_movS rfl fun s₁ u₁ _ => ?_
  refine WP.mono (VG.Proof.Mont.X86.stores0_ok (hs.of_keeps u₁.keeps (by decide)) u₁.gpr k hk) fun u ⟨O, V, K⟩ =>
    ⟨u₁.mem ▸ O, V, u₁.keeps.trans (K.mono (by decide))⟩

theorem m_pos_of_inv {m : Nat} {minv : Nat} (h : (m * minv + 1) % 2 ^ 64 = 0) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with rfl | h'
  · simp at h
  · exact h'

/-- `[o] = [a] [b] R⁻¹ mod m`. -/
theorem mul_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOk M size m s.mem base) {acc o a b : Nat} (hL : VG.Proof.Mont.X86.OpLay M size acc o a b)
    (hB : wordsVal s.mem base b M.n < m) :
    WP isa (mul M acc o a b) s fun s' => VG.Proof.Mont.X86.OpKeep M base acc o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  have hn := hs.nowrap
  obtain ⟨N, hNw⟩ : ∃ N, words M = N := ⟨_, rfl⟩
  have hN2 : N = 2 * M.n := hNw ▸ rfl
  have hacc : VG.Proof.Mont.X86.accLen M = 4 * (2 * N + 1) := by rw [VG.Proof.Mont.X86.accLen, hNw]
  have := hL.acc_le; have := hL.o_le; have := hL.a_le; have := hL.b_le; have := hL.acc_o; have := hL.acc_a
  have := hL.acc_b; have := hL.acc_mo; have := hL.acc_tmp; have := hL.o_tmp
  have := hM.mo; have := hM.tmp; have := hM.sep; have := hM.n0
  have hm0 := VG.Proof.Mont.X86.m_pos_of_inv hM.inv
  have hmv : val32 s.mem base M.mo N = m := by rw [hN2, ← wordsVal_eq_val32]; exact hM.val
  have hBv : val32 s.mem base b N < m := by rw [hN2, ← wordsVal_eq_val32]; exact hB
  have hML : VG.Proof.Mont.X86.MulLay N size acc a b M.mo := ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  simp only [mul, hNw]
  refine WP.seq (WP.block_append (WP.mono (VG.Proof.Mont.X86.zeros_ok hs (k := 2 * N + 1) (by omega)) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_))
  refine wp_movS rfl fun s₂ u₂ _ => WP.block_nil ?_
  have k₂ : Keeps VG.Proof.Mont.X86.clob s s₂ := (K₁.mono (by decide)).widen u₂.keeps
  have hs₂ := hs.of_keeps k₂ (by decide)
  have mem₂ : s₂.mem = s₁.mem := u₂.mem
  have O₂ : Outside base acc (4 * (2 * N + 1)) s.mem s₂.mem := mem₂ ▸ O₁
  have hm₂ : val32 s₂.mem base M.mo N = m := by rw [O₂.val32 (by omega) (by omega), hmv]
  have hB₂ : val32 s₂.mem base b N < m := by rw [O₂.val32 (by omega) (by omega)]; exact hBv
  have I₀ : VG.Proof.Mont.X86.LoopInv base N acc a b m 0 s₂ s₂ := by
    refine ⟨?_, VG.Proof.Mont.Outside.refl _ _ _ _, Keeps.refl _ _, ?_, ⟨0, ?_⟩⟩
    · rw [u₂.gpr, u₂.other _ (by decide), K₁.1 _ (by decide), Nat.mul_zero]; exact (BitVec.add_zero _).symm
    · rw [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, mem₂, V₁]; omega
    · rw [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, mem₂, V₁]; simp [val32]
  refine WP.seq (WP.mono (VG.Proof.Mont.X86.loop_ok hs₂ hNw hML (by omega) hm₂ (VG.Proof.Mont.X86.minv32_inv hM.inv) hB₂ I₀) fun t I => ?_)
  have ht := hs₂.of_keeps I.keeps (by decide)
  have hmt : val32 t.mem base M.mo N = m := by rw [I.out.val32 (by omega) (by omega), hm₂]
  have hlt := I.lt
  rw [show 2 * N + 1 - N = N + 1 by omega] at hlt
  refine WP.mono (VG.Proof.Mont.X86.csub_ok ht hNw (src := acc + 4 * N) (o := o) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) hmt hlt) fun u ⟨O, V, K⟩ => ⟨?_, ?_, ?_⟩
  · refine OpKeep.of ((k₂.trans I.keeps).trans (K.mono (by decide))) (by decide) ?_
    have O₂' : Outside base acc (VG.Proof.Mont.X86.accLen M) s.mem s₂.mem := by rw [hacc]; exact O₂
    have O₃ : Outside base acc (VG.Proof.Mont.X86.accLen M) s₂.mem t.mem := by rw [hacc]; exact I.out
    refine ((Outs.of_outside O₂' (by simp)).trans (Outs.of_outside O₃ (by simp))).trans ?_
    rw [show 4 * N = 8 * M.n by omega] at O
    exact O.mono (by simp)
  · rw [wordsVal_eq_val32, ← hN2, V]; exact Nat.mod_lt _ hm0
  · obtain ⟨U, hU⟩ := I.cong
    rw [show 2 * N + 1 - N = N + 1 by omega] at hU
    rw [wordsVal_eq_val32, wordsVal_eq_val32, wordsVal_eq_val32, ← hN2, V,
      show 64 * M.n = 32 * N by omega, ← O₂.val32 (d := a) (by omega) (by omega),
      ← O₂.val32 (d := b) (by omega) (by omega), Nat.mod_mul_mod, Nat.mul_comm, hU, Nat.add_mul_mod_self_right]

/-- `[o] = [a] + [b] mod m`. -/
theorem add_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOk M size m s.mem base) {acc o a b : Nat} (hL : VG.Proof.Mont.X86.OpLay M size acc o a b)
    (hAB : wordsVal s.mem base a M.n + wordsVal s.mem base b M.n < 2 * m) :
    WP isa (.block (add M acc o a b)) s fun s' => VG.Proof.Mont.X86.OpKeep M base acc o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + wordsVal s.mem base b M.n) % m := by
  have hn := hs.nowrap
  obtain ⟨N, hNw⟩ : ∃ N, words M = N := ⟨_, rfl⟩
  have hN2 : N = 2 * M.n := hNw ▸ rfl
  have hacc : VG.Proof.Mont.X86.accLen M = 4 * (2 * N + 1) := by rw [VG.Proof.Mont.X86.accLen, hNw]
  have := hL.acc_le; have := hL.o_le; have := hL.a_le; have := hL.b_le; have := hL.acc_o; have := hL.acc_a
  have := hL.acc_b; have := hL.acc_mo; have := hL.acc_tmp; have := hL.o_tmp
  have := hM.mo; have := hM.tmp; have := hM.sep; have := hM.n0
  obtain ⟨k, hk⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  simp only [add, VG.Proof.Mont.X86.chain_eq, hNw, hk, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.block_append (WP.mono (VG.Proof.Mont.X86.chainAdd_ok hs (acc := acc) (a := a) (b := b) k (by omega) (by omega)
    (by omega) (by omega) (by omega)) fun s₁ ⟨O₁, ⟨c, hc, V₁⟩, K₁⟩ => ?_)
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine wp_movS rfl fun s₂ u₂ cf₂ => ?_
  refine wp_adcS rfl (by rw [cf₂]; exact hc) fun s₃ u₃ _ => ?_
  have k₃ : Keeps [.eax] s s₃ := (K₁.widen u₂.keeps).widen u₃.keeps
  have hs₃ := hs.of_keeps k₃ (by decide)
  refine wp_storeS (hs₃.ea (d := acc + 4 * (k + 1)) (by omega))
    (hs₃.write (d := acc + 4 * (k + 1)) (n := 4) (by omega)) fun s₄ m₄ => ?_
  have hs₄ := hs₃.of_keeps (m₄.keeps []) (by decide)
  have O₄ : Outside base acc (4 * (k + 1) + 4) s.mem s₄.mem := by
    rw [m₄.mem, u₃.mem, u₂.mem]
    exact (O₁.mono (Nat.le_refl _) (by omega)).trans
      ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))
  have hsum : val32 s₄.mem base acc (k + 1 + 1) =
      wordsVal s.mem base a M.n + wordsVal s.mem base b M.n := by
    rw [val32_succ, m₄.mem, u₃.mem, u₂.mem, (writeW32_outside _ _ _ (by omega)).val32 (by omega) (by omega),
      w32_write_self, u₃.gpr, u₂.gpr, wordsVal_eq_val32, wordsVal_eq_val32, ← hN2, hk, ← V₁]
    have : ((0 : BitVec 32) + 0 + (BitVec.ofBool c).setWidth 32).toNat = c.toNat := by cases c <;> rfl
    rw [this]
  have hm₄ : val32 s₄.mem base M.mo (k + 1) = m := by
    rw [O₄.val32 (by omega) (by omega), ← hk, hN2, ← wordsVal_eq_val32]; exact hM.val
  refine WP.mono (VG.Proof.Mont.X86.csub_ok hs₄ (hNw.trans hk) (src := acc) (o := o) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) hm₄ (by rw [hsum]; exact hAB))
    fun u ⟨O, V, K⟩ => ⟨?_, ?_⟩
  · refine OpKeep.of (((k₃.mono (rs' := VG.Proof.Mont.X86.clob) (by decide)).widen (m₄.keeps [])).widen K) (by decide) ?_
    have O₄' : Outside base acc (VG.Proof.Mont.X86.accLen M) s.mem s₄.mem := O₄.mono (Nat.le_refl _) (by omega)
    refine (Outs.of_outside O₄' (by simp)).trans ?_
    rw [show 4 * (k + 1) = 8 * M.n by omega] at O
    exact O.mono (by simp)
  · rw [wordsVal_eq_val32, ← hN2, hk, V, hsum]

/-- The first `k` words of `masked`. -/
def maskK (mo tmp k : Nat) : List Instr :=
  (List.range k).flatMap fun j =>
    [.mov .edx (.mem (sc (mo + 4 * j))), .alu .and .edx (.reg .eax), .store (sc (tmp + 4 * j)) .edx]

theorem masked_eq (M : Mod) : masked M = VG.Proof.Mont.X86.maskK M.mo M.tmp (words M) := rfl

theorem maskK_succ (mo tmp k : Nat) : VG.Proof.Mont.X86.maskK mo tmp (k + 1) = VG.Proof.Mont.X86.maskK mo tmp k ++
    ([.mov .edx (.mem (sc (mo + 4 * k))), .alu .and .edx (.reg .eax), .store (sc (tmp + 4 * k)) .edx] :
      List Instr) := by
  simp only [VG.Proof.Mont.X86.maskK, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- `[tmp] = [mo]` if `c`, else zero, under the mask `eax`. -/
theorem masked_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {mo tmp : Nat} (c : Bool)
    (hm : s.gpr .eax = if c then BitVec.allOnes 32 else 0) :
    ∀ k, mo + 4 * k ≤ size → tmp + 4 * k ≤ size → (tmp + 4 * k ≤ mo ∨ mo + 4 * k ≤ tmp) →
    WP isa (.block (VG.Proof.Mont.X86.maskK mo tmp k)) s fun u =>
      Outside base tmp (4 * k) s.mem u.mem ∧
      val32 u.mem base tmp k = (if c then val32 s.mem base mo k else 0) ∧ Keeps [.edx] s u
  | 0, _, _, _ => WP.block_nil ⟨VG.Proof.Mont.Outside.refl _ _ _ _, by cases c <;> rfl, Keeps.refl _ _⟩
  | k + 1, hmo, htmp, hsep => by
    have hn := hs.nowrap
    rw [VG.Proof.Mont.X86.maskK_succ]
    refine WP.block_append (WP.mono (VG.Proof.Mont.X86.masked_ok hs c hm k (by omega) (by omega) (by omega))
      fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
    have hs₁ := hs.of_keeps K₁ (by decide)
    refine wp_movS (readSrc_sc hs₁ (d := mo + 4 * k) (by omega)) fun s₂ u₂ _ => ?_
    refine wp_logicS (.inl rfl) rfl fun s₃ u₃ => ?_
    have k₃ : Keeps [.edx] s s₃ := (K₁.widen u₂.keeps).widen u₃.keeps
    have hs₃ := hs.of_keeps k₃ (by decide)
    refine wp_storeS (hs₃.ea (d := tmp + 4 * k) (by omega)) (hs₃.write (d := tmp + 4 * k) (n := 4) (by omega))
      fun s₄ m₄ => WP.block_nil ⟨?_, ?_, k₃.trans (m₄.keeps _)⟩
    · rw [m₄.mem, u₃.mem, u₂.mem]
      exact (O₁.mono (Nat.le_refl _) (by omega)).trans
        ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))
    · have heax : s₂.gpr .eax = s.gpr .eax := by rw [u₂.other _ (by decide), K₁.1 _ (by decide)]
      have hw : w32 s₁.mem base (mo + 4 * k) = w32 s.mem base (mo + 4 * k) := O₁.w32 (by omega) (by omega)
      rw [val32_succ, m₄.mem, u₃.mem, u₂.mem, (writeW32_outside _ _ _ (by omega)).val32 (by omega) (by omega),
        w32_write_self, V₁, u₃.gpr, u₂.gpr, heax, hm]
      cases c
      · simp only [Bool.false_eq_true, ite_false]
        rw [show (0 : BitVec 32) = 0#32 from rfl, BitVec.and_zero]; rfl
      · simp only [ite_true, BitVec.and_allOnes, val32_succ]
        rw [← hw]

/-- `sbb eax, eax`: the mask of the borrow. -/
theorem borrow_mask (x : BitVec 32) (c : Bool) :
    x - x - (BitVec.ofBool c).setWidth 32 = if c then BitVec.allOnes 32 else 0 := by
  rw [BitVec.sub_self]
  cases c <;> decide

theorem sub_arith {A B m X acc o : Nat} {c c' : Bool} (hA : A < m) (hB : B < m)
    (hacc : acc < X) (ho : o < X) (h1 : acc + B = A + X * c.toNat)
    (h2 : o + X * c'.toNat = acc + (if c then m else 0)) : o = (A + m - B) % m := by
  rcases Nat.lt_or_ge A B with h | h
  · rw [Nat.mod_eq_of_lt (by omega)]
    cases c <;> cases c' <;> simp only [Bool.toNat_false, Bool.toNat_true, ite_true, Bool.false_eq_true,
      ite_false, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at h1 h2 <;> omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    cases c <;> cases c' <;> simp only [Bool.toNat_false, Bool.toNat_true, ite_true, Bool.false_eq_true,
      ite_false, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at h1 h2 <;> omega

/-- `[o] = [a] - [b] mod m`. -/
theorem sub_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOk M size m s.mem base) {acc o a b : Nat} (hL : VG.Proof.Mont.X86.OpLay M size acc o a b)
    (hA : wordsVal s.mem base a M.n < m) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (sub M acc o a b)) s fun s' => VG.Proof.Mont.X86.OpKeep M base acc o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + m - wordsVal s.mem base b M.n) % m := by
  have hn := hs.nowrap
  obtain ⟨N, hNw⟩ : ∃ N, words M = N := ⟨_, rfl⟩
  have hN2 : N = 2 * M.n := hNw ▸ rfl
  have hacc : VG.Proof.Mont.X86.accLen M = 4 * (2 * N + 1) := by rw [VG.Proof.Mont.X86.accLen, hNw]
  have := hL.acc_le; have := hL.o_le; have := hL.a_le; have := hL.b_le; have := hL.acc_o; have := hL.acc_a
  have := hL.acc_b; have := hL.acc_mo; have := hL.acc_tmp; have := hL.o_tmp
  have := hM.mo; have := hM.tmp; have := hM.sep; have := hM.n0
  obtain ⟨k, hk⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  simp only [sub, VG.Proof.Mont.X86.chain_eq, VG.Proof.Mont.X86.masked_eq, hNw, hk, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.block_append (WP.mono (VG.Proof.Mont.X86.chainSub_ok hs (acc := acc) (a := a) (b := b) k (by omega) (by omega)
    (by omega) (by omega) (by omega)) fun s₁ ⟨O₁, ⟨c, hc, V₁⟩, K₁⟩ => ?_)
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine wp_sbbS rfl hc fun s₂ u₂ _ => ?_
  have k₂ : Keeps [.eax, .edx] s s₂ := (K₁.mono (by decide)).widen u₂.keeps
  have hs₂ := hs.of_keeps k₂ (by decide)
  have mask : s₂.gpr .eax = if c then BitVec.allOnes 32 else 0 := by rw [u₂.gpr, VG.Proof.Mont.X86.borrow_mask]
  refine WP.block_append (WP.mono (VG.Proof.Mont.X86.masked_ok hs₂ c mask (k + 1) (mo := M.mo) (tmp := M.tmp) (by omega)
    (by omega) (by omega)) fun s₃ ⟨O₃, V₃, K₃⟩ => ?_)
  have k₃ : Keeps [.eax, .edx] s s₃ := k₂.widen K₃
  have hs₃ := hs.of_keeps k₃ (by decide)
  refine WP.mono (VG.Proof.Mont.X86.chainAdd_ok hs₃ (acc := o) (a := acc) (b := M.tmp) k (by omega) (by omega)
    (by omega) (by omega) (by omega)) fun u ⟨O, ⟨c', _, V⟩, K⟩ => ⟨?_, ?_⟩
  · refine OpKeep.of (k₃.widen K) (by decide) ?_
    have O₁' : Outside base acc (VG.Proof.Mont.X86.accLen M) s.mem s₁.mem := O₁.mono (Nat.le_refl _) (by omega)
    rw [u₂.mem] at O₃
    rw [show 4 * (k + 1) = 8 * M.n by omega] at O₃ O
    exact ((Outs.of_outside O₁' (by simp)).trans (Outs.of_outside O₃ (by simp))).trans
      (Outs.of_outside O (by simp))
  · have hacc₃ : val32 s₃.mem base acc (k + 1) = val32 s₁.mem base acc (k + 1) := by
      rw [O₃.val32 (by omega) (by omega), u₂.mem]
    have hmo : val32 s₁.mem base M.mo (k + 1) = m := by
      rw [O₁.val32 (by omega) (by omega), ← hk, hN2, ← wordsVal_eq_val32]; exact hM.val
    rw [hacc₃, V₃, u₂.mem, hmo] at V
    have e : 2 * M.n = k + 1 := by omega
    have hA' : val32 s.mem base a (k + 1) < m := by rw [← e, ← wordsVal_eq_val32]; exact hA
    have hB' : val32 s.mem base b (k + 1) < m := by rw [← e, ← wordsVal_eq_val32]; exact hB
    rw [wordsVal_eq_val32, wordsVal_eq_val32, wordsVal_eq_val32, e]
    exact VG.Proof.Mont.X86.sub_arith hA' hB' (val32_lt _ _ _ _) (val32_lt _ _ _ _) V₁ V

end VG.Proof.Mont.X86

end
