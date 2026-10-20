module

public import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Rows
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Step
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# X25519 on x86-64, inversion by divsteps: the rows of `f` and `g`

`fRow m₁ m₂ dst` leaves at `dst` the four words `fRowV` of the words at `m₁`,
`m₂` and the numbers `f`, `g` (`fRow_ok`): the two products from `c`, the sum
of the corrections (`cols_ok`), less `2²⁵⁶` times the corrections of the
tops (`sub12_val`, `topCorr_val`), and the five words shifted right by 59
into four (`shStores_ok`).
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64

/-- Word `j` of the five words shifted right by 59. -/
abbrev shW (lo hi : BitVec 64) : BitVec 64 := lo >>> 59 + hi <<< 5

/-- The shifts and stores of a row of `f` and `g`. -/
abbrev shStores (dst : Nat) : List Instr :=
  [(Reg.r8, Reg.r9, 0), (.r9, .r10, 8), (.r10, .r11, 16), (.r11, .r12, 24)].flatMap fun (lo, hi, d) =>
    [.mov .rax (.reg lo), .shift .shr .rax 59, .mov .rdx (.reg hi), .shift .shl .rdx 5,
      .alu .add .rax (.reg .rdx), .store (sc (dst + d)) .rax]

theorem shStores_ok {s : State} {base : Addr} (hs : Scr s base) {dst : Nat} (hd : dst + 32 ≤ 4096) :
    WP isa (.block (shStores dst)) s fun t =>
      t.mem = st4 s.mem base dst (shW (s.gpr .r8) (s.gpr .r9)) (shW (s.gpr .r9) (s.gpr .r10))
        (shW (s.gpr .r10) (s.gpr .r11)) (shW (s.gpr .r11) (s.gpr .r12)) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have w : ∀ d, d + 8 ≤ 4096 → InRegions s.wr (off base d) 8 :=
    fun d hd => ⟨_, hs.wr, contains_sc hd⟩
  drun [shStores, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil, Nat.add_zero,
    ea_sc, hs.rdi, State.store64, w dst (by omega), w (dst + 8) (by omega), w (dst + 16) (by omega),
    w (dst + 24) (by omega), RegUpd.gpr_setReg_self, RegUpd.wr_setFlags, RegUpd.gpr_setFlags,
    RegUpd.mem_setFlags, RegUpd.rd_setFlags]
  refine ⟨rfl, fun r h1 h2 => ?_⟩
  simp only [h1, h2, ↓reduceIte]

/-- The four words `shW` are the five shifted right by 59. -/
theorem shW_val (p0 p1 p2 p3 p4 : BitVec 64) :
    val4 (shW p0 p1) (shW p1 p2) (shW p2 p3) (shW p3 p4) =
      (val4 p0 p1 p2 p3 + 2 ^ 256 * p4.toNat) / 2 ^ 59 % 2 ^ 256 := by
  have e : ∀ lo hi : BitVec 64, (shW lo hi).toNat = lo.toNat / 2 ^ 59 + hi.toNat % 2 ^ 59 * 32 := by
    intro lo hi
    have := lo.isLt; have := hi.isLt
    simp only [shW, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
      Nat.shiftLeft_eq]
    omega
  simp only [val4, e]
  have := p0.isLt; have := p1.isLt; have := p2.isLt; have := p3.isLt; have := p4.isLt
  omega

theorem absN_le (w : BitVec 64) : absN w ≤ 2 ^ 63 := by
  unfold absN
  have := w.toInt_lt; have := w.le_toInt
  simp only [Nat.reducePow] at *
  omega

theorem topN_le (w : BitVec 64) (X : Nat) : topN w X ≤ 2 ^ 63 := by
  unfold topN; split
  · exact absN_le w
  · omega

/-- Bits 59 to 315 of a number modulo `2³²⁰` are its own. -/
theorem mod320_div (x : Nat) : x % (2 ^ 256 * 2 ^ 64) / 2 ^ 59 % 2 ^ 256 = x / 2 ^ 59 % 2 ^ 256 := by
  have e : (2 : Nat) ^ 256 * 2 ^ 64 = 2 ^ 59 * (2 ^ 197 * 2 ^ 64) := by
    rw [← Nat.mul_assoc, ← Nat.pow_add]
  have d : 2 ^ 256 ∣ (2 : Nat) ^ 197 * 2 ^ 64 := ⟨2 ^ 5, by rw [← Nat.pow_add]⟩
  rw [e, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ d]

/-- `r12 -= v` modulo `2⁶⁴` is `r8–r12 -= 2²⁵⁶ v` modulo `2³²⁰`. -/
theorem sub12_val {s t : State} {v : BitVec 64} (h : t.gpr .r12 = s.gpr .r12 - v)
    (k : ∀ r, r ∈ [Reg.r8, .r9, .r10, .r11] → t.gpr r = s.gpr r) :
    val5 t = (val5 s + (2 ^ 256 * 2 ^ 64 - 2 ^ 256 * v.toNat)) % (2 ^ 256 * 2 ^ 64) := by
  simp only [val5, val4, h, k .r8 (by simp), k .r9 (by simp), k .r10 (by simp), k .r11 (by simp), BitVec.toNat_sub]
  have := (s.gpr .r8).isLt; have := (s.gpr .r9).isLt; have := (s.gpr .r10).isLt
  have := (s.gpr .r11).isLt; have := (s.gpr .r12).isLt; have := v.isLt
  omega_arith

/-- The correction of a top is `topN`. -/
theorem topCorr_val (mem : Mem) (base : Addr) (x : Nat) (w a : BitVec 64) (ha : a.toNat = absN w) :
    (if (word mem base (x + 24) ^^^ maskW w).msb = true then a else 0).toNat = topN w (fe mem base x) := by
  unfold topN
  by_cases h : 2 ^ 255 ≤ flipN w (fe mem base x)
  · simp only [(top_iff _ _ _ _).2 h, h, ↓reduceIte, ha]
  · have h' : ¬ (word mem base (x + 24) ^^^ maskW w).msb = true := fun h' => h ((top_iff _ _ _ _).1 h')
    simp only [h', h, ↓reduceIte]; rfl

/-- The arithmetic of a row of `f` and `g`. -/
theorem fsum_arith (V T₁ T₂ : Nat) (h₁ : T₁ ≤ 2 ^ 63) (h₂ : T₂ ≤ 2 ^ 63) :
    ((V + (2 ^ 256 * 2 ^ 64 - 2 ^ 256 * T₁)) % (2 ^ 256 * 2 ^ 64) + (2 ^ 256 * 2 ^ 64 - 2 ^ 256 * T₂)) %
        (2 ^ 256 * 2 ^ 64) / 2 ^ 59 % 2 ^ 256 =
      (V + (2 ^ 256 * 2 ^ 65 - 2 ^ 256 * (T₁ + T₂))) / 2 ^ 59 % 2 ^ 256 := by
  have h : ((V + (2 ^ 256 * 2 ^ 64 - 2 ^ 256 * T₁)) % (2 ^ 256 * 2 ^ 64) + (2 ^ 256 * 2 ^ 64 - 2 ^ 256 * T₂)) %
      (2 ^ 256 * 2 ^ 64) = (V + (2 ^ 256 * 2 ^ 65 - 2 ^ 256 * (T₁ + T₂))) % (2 ^ 256 * 2 ^ 64) := by omega
  rw [h, mod320_div]

/-- The registers the inversion writes. -/
abbrev dsClob : List Reg := [.rax, .rbx, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- The registers a row writes: those of the inversion but `rbp`. -/
abbrev rowClob : List Reg := [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

theorem fRow_eq (m₁ m₂ dst : Nat) :
    fRow m₁ m₂ dst = absMk m₁ .rcx .r14 ++ (absMk m₂ .r13 .r15 ++ (cSum .r8 ++ (cols dsF dsG ++
      (topCorr dsF .rcx .r14 ++ (topCorr dsG .r13 .r15 ++ shStores dst))))) := by
  simp only [fRow, rowP, ↓reduceIte, List.append_nil, List.append_assoc]

/-- `|m|` and the masks of a row's two words. -/
theorem absMk2_ok {s : State} {base : Addr} (hs : Scr s base) {m₁ m₂ : Nat} (h₁ : m₁ + 8 ≤ 4096)
    (h₂ : m₂ + 8 ≤ 4096) :
    WP isa (.block (absMk m₁ .rcx .r14 ++ absMk m₂ .r13 .r15)) s fun t =>
      (t.gpr .rcx).toNat = absN (word s.mem base m₁) ∧ t.gpr .r14 = maskW (word s.mem base m₁) ∧
      (t.gpr .r13).toNat = absN (word s.mem base m₂) ∧ t.gpr .r15 = maskW (word s.mem base m₂) ∧
      Keeps [.rax, .rcx, .r13, .r14, .r15] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (absMk_ok hs h₁ (by decide) (by decide) (by decide)) fun s₁ ⟨k1, a1, K1⟩ => ?_
  refine WP.mono (absMk_ok (hs.of_keeps K1 (by decide)) h₂ (by decide) (by decide) (by decide))
    fun t ⟨k2, a2, K2⟩ => ⟨?_, ?_, ?_, ?_, (K1.mono (by decide)).trans (K2.mono (by decide))⟩
  · rw [K2.1 _ (by decide)]; exact a1
  · rw [K2.1 _ (by decide)]; exact k1
  · rw [a2, K1.2.1]
  · rw [k2, K1.2.1]

/-- A row of `f` and `g`: `[dst] = fRowV [m₁] [m₂] f g`. -/
theorem fRow_ok {s : State} {base : Addr} (hs : Scr s base) {m₁ m₂ dst : Nat} (h₁ : m₁ + 8 ≤ 4096)
    (h₂ : m₂ + 8 ≤ 4096) (hd : dst + 32 ≤ 4096) :
    WP isa (.block (fRow m₁ m₂ dst)) s fun t =>
      fe t.mem base dst = fRowV (word s.mem base m₁) (word s.mem base m₂) (fe s.mem base dsF)
        (fe s.mem base dsG) ∧
      Outside base dst 32 s.mem t.mem ∧ (∀ r, r ∉ rowClob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [fRow_eq, ← List.append_assoc, WP.block_append_iff]
  refine WP.mono (absMk2_ok hs h₁ h₂) fun s₂ ⟨a1, k1, a2, k2, K2⟩ => ?_
  have hs₂ := hs.of_keeps K2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (cSum_ok s₂ (cd := .r8) (by decide)) fun s₃ ⟨c3, K3⟩ => ?_
  have hs₃ := hs₂.of_keeps K3 (by decide)
  have R3 : ∀ r, r ∈ [Reg.rcx, .r13, .r14, .r15] → s₃.gpr r = s₂.gpr r := fun r hr =>
    K3.1 r (fun h => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr h
                        rcases hr with rfl | rfl | rfl | rfl <;> simp at h)
  rw [WP.block_append_iff]
  refine WP.mono (cols_ok hs₃ (by decide) (by decide) (by rw [R3 _ (by simp), a1]; exact absN_le _)
    (by rw [R3 _ (by simp), a2]; exact absN_le _)) fun s₄ ⟨v4, K4⟩ => ?_
  have hs₄ := hs₃.of_keeps K4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (topCorr_ok hs₄ (x := dsF) (by decide) (a := .rcx) (k := .r14) (by decide) (by decide))
    fun s₅ ⟨e5, K5⟩ => ?_
  have hs₅ := hs₄.of_keeps K5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (topCorr_ok hs₅ (x := dsG) (by decide) (a := .r13) (k := .r15) (by decide) (by decide))
    fun s₆ ⟨e6, K6⟩ => ?_
  have hs₆ := hs₅.of_keeps K6 (by decide)
  refine WP.mono (shStores_ok hs₆ hd) fun t ⟨mt, gt, rt, wt⟩ => ⟨?_, ?_, ?_, ?_, ?_⟩
  · have M2 : s₂.mem = s.mem := K2.2.1
    have M4 : s₄.mem = s.mem := K4.2.1.trans (K3.2.1.trans M2)
    have M6 : s₆.mem = s.mem := K6.2.1.trans (K5.2.1.trans M4)
    have g4 : ∀ r, r ∈ [Reg.rcx, .r13, .r14, .r15] → s₄.gpr r = s₂.gpr r := fun r hr =>
      (K4.1 r (fun h => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr h
                           rcases hr with rfl | rfl | rfl | rfl <;> simp at h)).trans (R3 r hr)
    have g5 : ∀ r, r ∈ [Reg.r13, .r15] → s₅.gpr r = s₄.gpr r := fun r hr =>
      K5.1 r (fun h => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr h
                          rcases hr with rfl | rfl <;> simp at h)
    have q : ∀ {u v : State} (K : Keeps [.rax, .rdx, .r12] u v), ∀ r, r ∈ [Reg.r8, .r9, .r10, .r11] →
        v.gpr r = u.gpr r := fun K r hr =>
      K.1 r (fun h => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr h
                         rcases hr with rfl | rfl | rfl | rfl <;> simp at h)
    rw [g4 .r14 (by simp), g4 .rcx (by simp), k1, M4] at e5
    rw [g5 .r15 (by simp), g5 .r13 (by simp), g4 .r15 (by simp), g4 .r13 (by simp), k2, K5.2.1, M4] at e6
    have v5 := sub12_val e5 (q K5)
    have v6 := sub12_val e6 (q K6)
    rw [topCorr_val _ _ _ _ _ a1] at v5
    rw [topCorr_val _ _ _ _ _ a2] at v6
    rw [c3, R3 .rcx (by simp), R3 .r13 (by simp), R3 .r14 (by simp), R3 .r15 (by simp), k1, k2,
      cSum_val _ _ _ _ a1 a2, a1, a2, K3.2.1, M2, feX_mask, feX_mask] at v4
    rw [mt, M6, fe_st4 _ _ (by omega), shW_val]
    change val5 s₆ / 2 ^ 59 % 2 ^ 256 = _
    rw [v6, v5, v4]
    unfold fRowV
    rw [fsum_arith _ _ _ (topN_le _ _) (topN_le _ _)]
    congr 2
    omega
  · rw [mt, K6.2.1, K5.2.1, K4.2.1, K3.2.1, K2.2.1]
    exact st4_outside _ _ (by omega) _ _ _ _
  · intro r hr
    have sub : ∀ L : List Reg, (∀ x ∈ L, x ∈ rowClob) → r ∉ L := fun L hL h => hr (hL r h)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gt r hr.1 hr.2.2.2.1, K6.1 r (sub _ (by decide)), K5.1 r (sub _ (by decide)), K4.1 r (sub _ (by decide)),
      K3.1 r (sub _ (by decide)), K2.1 r (sub _ (by decide))]
  · rw [rt, K6.2.2.1, K5.2.2.1, K4.2.2.1, K3.2.2.1, K2.2.2.1]
  · rw [wt, K6.2.2.2, K5.2.2.2, K4.2.2.2, K3.2.2.2, K2.2.2.2]

end VG.Proof.X25519.X86_64
