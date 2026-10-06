import VerifiedGarbage.Proof.X25519.X86_64.Divstep.FRow

/-!
# X25519 on x86-64, inversion by divsteps: the rows of `a` and `b`

`aRow m₁ m₂ dst` leaves at `dst` the four words `aRowV` of the words at
`m₁`, `m₂` and the numbers `a`, `b` (`aRow_ok`): the two products
(`prod_ok`), then `foldP`, which brings the five words `Q` less `37 c` below
`2²⁵⁶` (`foldP_ok`): `w = 38 Q₄ - 37 c` in two words (`foldA_ok`), added to
the low four with its sign (`foldB_ok`), and the carry of that folded in as
`±38`.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64

/-- `w = 38 r12 - 37 rbx` in `r13`, `r14` (modulo `2¹²⁸`), and the mask of its sign in `rax`. -/
abbrev foldA : List Instr :=
  [.mov32 .rax (.imm 38), .mul .r12, .mov .r13 (.reg .rax), .mov .r14 (.reg .rdx),
    .mov32 .rax (.imm 37), .mul .rbx, .alu .sub .r13 (.reg .rax), .alu .sbb .r14 (.reg .rdx),
    .mov .r15 (.reg .r14), .shift .shr .r15 63, .mov32 .rax (.imm 0), .alu .sub .rax (.reg .r15)]

/-- `r8–r11 += w` (sign-extended), then the carry of that, as `±38`. -/
abbrev foldB : List Instr :=
  [.alu .add .r8 (.reg .r13), .alu .adc .r9 (.reg .r14), .alu .adc .r10 (.reg .rax), .alu .adc .r11 (.reg .rax),
    .alu .sbb .rdx (.reg .rdx), .alu .and .rdx (.imm 38), .alu .and .rax (.imm 38), .alu .sub .rdx (.reg .rax),
    .mov .r15 (.reg .rdx), .shift .shr .r15 63, .mov32 .rax (.imm 0), .alu .sub .rax (.reg .r15),
    .alu .add .r8 (.reg .rdx), .alu .adc .r9 (.reg .rax), .alu .adc .r10 (.reg .rax), .alu .adc .r11 (.reg .rax)]

theorem foldP_eq : foldP = foldA ++ foldB := rfl

theorem z38 : (38 : BitVec 32).setWidth 64 = 38 := by decide
theorem z37 : (37 : BitVec 32).setWidth 64 = 37 := by decide

/-- The halves of a product of words below `2¹²⁸`. -/
theorem mul_halves (d v : Nat) (hd : d < 2 ^ 64) (hv : v < 2 ^ 64) :
    (BitVec.ofNat 64 (d * v)).toNat = d * v % 2 ^ 64 ∧ (BitVec.ofNat 64 (d * v / 2 ^ 64)).toNat = d * v / 2 ^ 64 := by
  have : d * v < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hd hv
  refine ⟨BitVec.toNat_ofNat _ _, ?_⟩
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem foldA_ok (s : State) :
    WP isa (.block foldA) s fun t =>
      (t.gpr .r13).toNat + 2 ^ 64 * (t.gpr .r14).toNat =
        (38 * (s.gpr .r12).toNat + 2 ^ 128 - 37 * (s.gpr .rbx).toNat) % 2 ^ 128 ∧
      t.gpr .rax = maskW (t.gpr .r14) ∧ Keeps [.rax, .rdx, .r13, .r14, .r15] s t := by
  drun [foldA, z38, z37, zs0, RegUpd.gpr_setReg_self]
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have h12 := (s.gpr .r12).isLt; have hb := (s.gpr .rbx).isLt
    have e38 : (38 : BitVec 64).toNat = 38 := rfl
    have e37 : (37 : BitVec 64).toNat = 37 := rfl
    rw [e38, e37]
    obtain ⟨l1, h1⟩ := mul_halves 38 (s.gpr .r12).toNat (by decide) h12
    obtain ⟨l2, h2⟩ := mul_halves 37 (s.gpr .rbx).toNat (by decide) hb
    generalize BitVec.ofNat 64 (38 * (s.gpr .r12).toNat) = L1 at l1 ⊢
    generalize BitVec.ofNat 64 (37 * (s.gpr .rbx).toNat) = L2 at l2 ⊢
    generalize BitVec.ofNat 64 (38 * (s.gpr .r12).toNat / 2 ^ 64) = H1 at h1 ⊢
    generalize BitVec.ofNat 64 (37 * (s.gpr .rbx).toNat / 2 ^ 64) = H2 at h2 ⊢
    have sb := sub_borrow L1 L2
    have sbb := sbb_borrow H1 H2 (decide (L1.toNat < L2.toNat))
    generalize decide (L1.toNat < L2.toNat) = b at sb sbb ⊢
    generalize decide (H1.toNat < H2.toNat + b.toNat) = b' at sbb
    have := Bool.toNat_le b; have := Bool.toNat_le b'
    have := (L1 - L2).isLt; have := (H1 - H2 - (BitVec.ofBool b).setWidth 64).isLt
    omega
  · exact maskW_eq _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5⟩ := hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, h1, h2, h3, h4, h5, ↓reduceIte]

theorem maskW_toNat (x : BitVec 64) : (maskW x).toNat = if 2 ^ 63 ≤ x.toNat then 2 ^ 64 - 1 else 0 := by
  unfold maskW
  by_cases h : 2 ^ 63 ≤ x.toNat
  · simp only [(msb_iff x).2 h, ↓reduceIte, h, BitVec.toNat_allOnes]
  · have h' : ¬ x.msb = true := fun h' => h ((msb_iff x).1 h')
    simp only [h', h, Bool.false_eq_true, ↓reduceIte]; rfl

theorem and38 (x : BitVec 64) : (maskW x &&& BitVec.signExtend 64 (38 : BitVec 32)).toNat =
    if 2 ^ 63 ≤ x.toNat then 38 else 0 := by
  unfold maskW
  by_cases h : 2 ^ 63 ≤ x.toNat
  · simp only [(msb_iff x).2 h, ↓reduceIte, h, BitVec.allOnes_and]; decide
  · have h' : ¬ x.msb = true := fun h' => h ((msb_iff x).1 h')
    simp only [h', h, Bool.false_eq_true, ↓reduceIte]; rfl

/-- The arithmetic of `foldB`. -/
theorem foldB_arith (lo Q4 c r13 r14 S c3 F c3' fix : Nat) (hlo : lo < 2 ^ 256) (hQ4 : Q4 < 2 ^ 64)
    (hc : c < 2 ^ 64) (h13 : r13 < 2 ^ 64) (h14 : r14 < 2 ^ 64)
    (hW : r13 + 2 ^ 64 * r14 = (38 * Q4 + 2 ^ 128 - 37 * c) % 2 ^ 128)
    (hS : S < 2 ^ 256) (hc3 : c3 ≤ 1)
    (e1 : S + 2 ^ 256 * c3 = lo + (r13 + 2 ^ 64 * r14 + (if 2 ^ 63 ≤ r14 then 2 ^ 256 - 2 ^ 128 else 0)))
    (hfix : fix = (38 * c3 + 2 ^ 64 - (if 2 ^ 63 ≤ r14 then 38 else 0)) % 2 ^ 64)
    (hF : F < 2 ^ 256) (hc3' : c3' ≤ 1)
    (e2 : F + 2 ^ 256 * c3' = S + (fix + (if 2 ^ 63 ≤ fix then 2 ^ 256 - 2 ^ 64 else 0))) :
    F = foldV (lo + 2 ^ 256 * Q4) c := by
  unfold foldV
  dsimp only
  have q1 : (lo + 2 ^ 256 * Q4) % 2 ^ 256 = lo := by omega
  have q2 : (lo + 2 ^ 256 * Q4) / 2 ^ 256 = Q4 := by omega
  rw [q1, q2]
  by_cases hn : 2 ^ 63 ≤ r14 <;> simp only [hn, ↓reduceIte] at e1 hfix <;>
    rcases (by omega : c3 = 0 ∨ c3 = 1) with rfl | rfl <;> simp only [Nat.mul_zero, Nat.mul_one] at hfix <;>
    (by_cases hf : 2 ^ 63 ≤ fix <;> simp only [hf, ↓reduceIte] at e2) <;>
    (split <;> (try split)) <;> omega

/-- Four `add`/`adc` of registers into `r8–r11`, the carry out in `CF`. -/
theorem add4_ok (s : State) (b0 b1 b2 b3 : Reg) (h1 : b1 ≠ .r8)
    (h2 : b2 ≠ .r8 ∧ b2 ≠ .r9) (h3 : b3 ≠ .r8 ∧ b3 ≠ .r9 ∧ b3 ≠ .r10) :
    WP isa (.block [.alu .add .r8 (.reg b0), .alu .adc .r9 (.reg b1), .alu .adc .r10 (.reg b2),
      .alu .adc .r11 (.reg b3)]) s fun t => ∃ c : Bool, t.cf = some c ∧
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) + 2 ^ 256 * c.toNat =
        val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
          val4 (s.gpr b0) (s.gpr b1) (s.gpr b2) (s.gpr b3) ∧
      Keeps [.r8, .r9, .r10, .r11] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true, ite_false, reduceCtorEq, Option.some.injEq,
    exists_eq_left', h1, h2.1, h2.2, h3.1, h3.2.1, h3.2.2]
  refine ⟨chain_add _ _ _ _ _ _ _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨g1, g2, g3, g4⟩ := hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, g1, g2, g3, g4, ↓reduceIte]

/-- The fix: `rdx = 38 CF - (rax & 38)`, and `rax` = the mask of its sign. -/
theorem fixC_ok (s : State) {c : Bool} (hc : s.cf = some c) :
    WP isa (.block [.alu .sbb .rdx (.reg .rdx), .alu .and .rdx (.imm 38), .alu .and .rax (.imm 38),
      .alu .sub .rdx (.reg .rax), .mov .r15 (.reg .rdx), .shift .shr .r15 63, .mov32 .rax (.imm 0),
      .alu .sub .rax (.reg .r15)]) s fun t =>
      (t.gpr .rdx).toNat = (38 * c.toNat + 2 ^ 64 -
        (s.gpr .rax &&& BitVec.signExtend 64 (38 : BitVec 32)).toNat) % 2 ^ 64 ∧
      t.gpr .rax = maskW (t.gpr .rdx) ∧ Keeps [.rax, .rdx, .r15] s t := by
  drun [hc, zs0, RegUpd.gpr_setReg_self]
  refine ⟨?_, maskW_eq _, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [BitVec.toNat_sub, mask38]
    have := (s.gpr .rax &&& BitVec.signExtend 64 (38 : BitVec 32)).isLt
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨g1, g2, g3⟩ := hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, g1, g2, g3, ↓reduceIte]

theorem foldB_eq : foldB = ([.alu .add .r8 (.reg .r13), .alu .adc .r9 (.reg .r14),
      .alu .adc .r10 (.reg .rax), .alu .adc .r11 (.reg .rax)] : List Instr) ++
      (([.alu .sbb .rdx (.reg .rdx), .alu .and .rdx (.imm 38), .alu .and .rax (.imm 38),
        .alu .sub .rdx (.reg .rax), .mov .r15 (.reg .rdx), .shift .shr .r15 63, .mov32 .rax (.imm 0),
        .alu .sub .rax (.reg .r15)] : List Instr) ++
      ([.alu .add .r8 (.reg .rdx), .alu .adc .r9 (.reg .rax), .alu .adc .r10 (.reg .rax),
        .alu .adc .r11 (.reg .rax)] : List Instr)) := rfl

theorem val4_ext (a b : BitVec 64) :
    val4 a b (maskW b) (maskW b) = a.toNat + 2 ^ 64 * b.toNat + (if 2 ^ 63 ≤ b.toNat then 2 ^ 256 - 2 ^ 128 else 0) := by
  simp only [val4, maskW_toNat]
  split <;> omega

theorem val4_ext3 (a : BitVec 64) :
    val4 a (maskW a) (maskW a) (maskW a) = a.toNat + (if 2 ^ 63 ≤ a.toNat then 2 ^ 256 - 2 ^ 64 else 0) := by
  simp only [val4, maskW_toNat]
  split <;> omega

/-- `r8–r11 = foldV (r8–r12) rbx`. -/
theorem foldP_ok (s : State) :
    WP isa (.block foldP) s fun t =>
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) = foldV (val5 s) (s.gpr .rbx).toNat ∧
      Keeps [.r8, .r9, .r10, .r11, .r13, .r14, .r15, .rax, .rdx] s t := by
  rw [foldP_eq, WP.block_append_iff]
  refine WP.mono (foldA_ok s) fun s₁ ⟨hW, hx, k1⟩ => ?_
  rw [foldB_eq, WP.block_append_iff]
  refine WP.mono (add4_ok s₁ .r13 .r14 .rax .rax (by decide) (by decide) (by decide))
    fun s₂ ⟨c, hc, e1, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (fixC_ok s₂ hc) fun s₃ ⟨hf, hx3, k3⟩ => ?_
  refine WP.mono (add4_ok s₃ .rdx .rax .rax .rax (by decide) (by decide) (by decide))
    fun t ⟨c', _, e2, k4⟩ => ⟨?_, ?_⟩
  · have a2 : s₂.gpr .rax = s₁.gpr .rax := k2.1 _ (by decide)
    have r13 : s₂.gpr .r13 = s₁.gpr .r13 := k2.1 _ (by decide)
    have r14 : s₂.gpr .r14 = s₁.gpr .r14 := k2.1 _ (by decide)
    rw [hx, val4_ext] at e1
    rw [a2, hx, and38] at hf
    have g8 : s₃.gpr .r8 = s₂.gpr .r8 := k3.1 _ (by decide)
    have g9 : s₃.gpr .r9 = s₂.gpr .r9 := k3.1 _ (by decide)
    have g10 : s₃.gpr .r10 = s₂.gpr .r10 := k3.1 _ (by decide)
    have g11 : s₃.gpr .r11 = s₂.gpr .r11 := k3.1 _ (by decide)
    rw [hx3, val4_ext3, g8, g9, g10, g11] at e2
    have f8 : s₁.gpr .r8 = s.gpr .r8 := k1.1 _ (by decide)
    have f9 : s₁.gpr .r9 = s.gpr .r9 := k1.1 _ (by decide)
    have f10 : s₁.gpr .r10 = s.gpr .r10 := k1.1 _ (by decide)
    have f11 : s₁.gpr .r11 = s.gpr .r11 := k1.1 _ (by decide)
    rw [f8, f9, f10, f11] at e1
    have q : val5 s = val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) + 2 ^ 256 * (s.gpr .r12).toNat := rfl
    rw [q]
    refine foldB_arith _ _ _ _ _ _ c.toNat _ c'.toNat (s₃.gpr .rdx).toNat ?_ (s.gpr .r12).isLt (s.gpr .rbx).isLt
      (s₁.gpr .r13).isLt (s₁.gpr .r14).isLt hW ?_ (Bool.toNat_le c) e1 hf ?_ (Bool.toNat_le c') e2
    · simp only [val4]; have := (s.gpr .r8).isLt; have := (s.gpr .r9).isLt; have := (s.gpr .r10).isLt
      have := (s.gpr .r11).isLt; omega
    · simp only [val4]; have := (s₂.gpr .r8).isLt; have := (s₂.gpr .r9).isLt; have := (s₂.gpr .r10).isLt
      have := (s₂.gpr .r11).isLt; omega
    · simp only [val4]; have := (t.gpr .r8).isLt; have := (t.gpr .r9).isLt; have := (t.gpr .r10).isLt
      have := (t.gpr .r11).isLt; omega
  · exact ((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide)) |>.trans
      (k4.mono (by decide))

theorem fe_lt (m : Mem) (base : Addr) (x : Nat) : fe m base x < 2 ^ 256 := by
  simp only [fe, val4]
  have := (word m base x).isLt; have := (word m base (x + 8)).isLt
  have := (word m base (x + 16)).isLt; have := (word m base (x + 24)).isLt
  omega

theorem prodN_le (w : BitVec 64) {X : Nat} (hX : X < 2 ^ 256) :
    absN w * flipN w X ≤ 2 ^ 63 * (2 ^ 256 - 1) := by
  have h1 := absN_le w
  have h2 : flipN w X ≤ 2 ^ 256 - 1 := by unfold flipN; split <;> omega
  exact Nat.mul_le_mul h1 h2

theorem aRow_eq (m₁ m₂ dst : Nat) :
    aRow m₁ m₂ dst = zeroP ++ (prod m₁ dsA false ++ (prod m₂ dsB false ++ (foldP ++ store4 dst))) := by
  simp only [aRow, List.append_assoc]

/-- A row of `a` and `b`: `[dst] = aRowV [m₁] [m₂] a b`. -/
theorem aRow_ok {s : State} {base : Addr} (hs : Scr s base) {m₁ m₂ dst : Nat} (h₁ : m₁ + 8 ≤ 4096)
    (h₂ : m₂ + 8 ≤ 4096) (hd : dst + 32 ≤ 4096) :
    WP isa (.block (aRow m₁ m₂ dst)) s fun t =>
      fe t.mem base dst = aRowV (word s.mem base m₁) (word s.mem base m₂) (fe s.mem base dsA)
        (fe s.mem base dsB) ∧
      Outside base dst 32 s.mem t.mem ∧ (∀ r, r ∉ rowClob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hA : dsA + 32 ≤ 4096 := by decide
  have hB : dsB + 32 ≤ 4096 := by decide
  rw [aRow_eq, WP.block_append_iff]
  refine WP.mono (zeroP_ok s) fun s₁ ⟨v1, b1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (prod_ok hs₁ h₁ hA false) fun s₂ ⟨v2, b2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (prod_ok hs₂ h₂ hB false) fun s₃ ⟨v3, b3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (foldP_ok s₃) fun s₄ ⟨v4, k4⟩ => ?_
  have hs₄ := hs₃.of_keeps k4 (by decide)
  refine WP.mono (store4_ok hs₄ (by unfold Slot; omega)) fun t ⟨mt, gt, rt, wt⟩ => ⟨?_, ?_, ?_, ?_, ?_⟩
  · have M1 : s₁.mem = s.mem := k1.2.1
    have M2 : s₂.mem = s.mem := k2.2.1.trans M1
    rw [M1] at v2 b2
    rw [M2] at v3 b3
    rw [mt, fe_st4 _ _ (by omega), v4, v3, v2, v1, b3, b2, b1]
    unfold aRowV cN
    have z : (0 : BitVec 64).toNat = 0 := rfl
    have p1 := prodN_le (word s.mem base m₁) (fe_lt s.mem base dsA)
    have p2 := prodN_le (word s.mem base m₂) (fe_lt s.mem base dsB)
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.mul_zero, Nat.sub_zero, z, Nat.zero_add]
    refine congr (congrArg foldV ?_) ?_
    · omega
    · omega
  · rw [mt, k4.2.1, k3.2.1, k2.2.1, k1.2.1]
    exact st4_outside _ _ (by omega) _ _ _ _
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gt r, k4.1 r (by simp_all), k3.1 r (by simp_all), k2.1 r (by simp_all), k1.1 r (by simp_all)]
  · rw [rt, k4.2.2.1, k3.2.2.1, k2.2.2.1, k1.2.2.1]
  · rw [wt, k4.2.2.2, k3.2.2.2, k2.2.2.2, k1.2.2.2]

end VG.Proof.X25519.X86_64
