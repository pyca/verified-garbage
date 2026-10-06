import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Rows

/-!
# X25519 on x86-64, inversion by divsteps: the rows of `f` and `g`

`fRow m₁ m₂ dst` leaves at `dst` the four words `fRowV` of the words at `m₁`,
`m₂` and the numbers `f`, `g` (`fRow_ok`): the two products (`prod_ok`), the
sum `c` of the corrections (`addC_ok`), and the five words shifted right by
59 into four (`shStores_ok`).
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64

/-- `r8–r12 = 0`, `rbx = 0`. -/
theorem zeroP_ok (s : State) :
    WP isa (.block zeroP) s fun t => val5 t = 0 ∧ t.gpr .rbx = 0 ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .rbx] s t := by
  drun [zeroP, zs0, RegUpd.gpr_setReg_self]
  refine ⟨by simp only [val5, val4, RegUpd.gpr_setReg]; rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
  simp only [RegUpd.gpr_setReg, h1, h2, h3, h4, h5, h6, ↓reduceIte]

theorem se0' : (0 : BitVec 32).signExtend 64 = 0 := by decide

/-- `r8–r12 += rbx`, modulo `2³²⁰`. -/
theorem addC_ok (s : State) :
    WP isa (.block [.alu .add .r8 (.reg .rbx), .alu .adc .r9 (.imm 0), .alu .adc .r10 (.imm 0),
      .alu .adc .r11 (.imm 0), .alu .adc .r12 (.imm 0)]) s fun t =>
      val5 t = (val5 s + (s.gpr .rbx).toNat) % (2 ^ 256 * 2 ^ 64) ∧
      Keeps [.r8, .r9, .r10, .r11, .r12] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true, ite_false, reduceCtorEq, Option.some.injEq,
    exists_eq_left', se0', val5, val4]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := chain_add (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .rbx) 0 0 0
    simp only at e
    generalize hc : decide (2 ^ 64 ≤ (s.gpr Reg.r11).toNat + BitVec.toNat 0 +
      (decide (2 ^ 64 ≤ (s.gpr Reg.r10).toNat + BitVec.toNat 0 +
        (decide (2 ^ 64 ≤ (s.gpr Reg.r9).toNat + BitVec.toNat 0 +
          (decide (2 ^ 64 ≤ (s.gpr Reg.r8).toNat + (s.gpr Reg.rbx).toNat)).toNat)).toNat)).toNat) = c at e ⊢
    simp only [val4] at e
    rw [BitVec.toNat_add (s.gpr .r12 + 0), BitVec.toNat_add (s.gpr .r12), toNat_ofBool]
    have z : (0 : BitVec 64).toNat = 0 := rfl
    rw [z] at e ⊢
    have := (s.gpr .r12).isLt; have := Bool.toNat_le c
    have := (s.gpr .r8 + s.gpr .rbx).isLt
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5⟩ := hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h1, h2, h3, h4, h5, ↓reduceIte]

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

/-- The arithmetic of a row of `f` and `g`. -/
theorem fsum_arith (A₁ A₂ T₁ T₂ n₁ n₂ : Nat) (h₁ : T₁ ≤ 2 ^ 63) (h₂ : T₂ ≤ 2 ^ 63) :
    (((0 + A₁ + (2 ^ 256 * 2 ^ 64 - 2 ^ 256 * T₁)) % (2 ^ 256 * 2 ^ 64) + A₂ + (2 ^ 256 * 2 ^ 64 - 2 ^ 256 * T₂)) % (2 ^ 256 * 2 ^ 64) +
        ((0 + n₁) % 2 ^ 64 + n₂) % 2 ^ 64) % (2 ^ 256 * 2 ^ 64) / 2 ^ 59 % 2 ^ 256 =
      (A₁ + A₂ + (n₁ + n₂) % 2 ^ 64 + (2 ^ 256 * 2 ^ 65 - 2 ^ 256 * (T₁ + T₂))) / 2 ^ 59 % 2 ^ 256 := by
  have h : (((0 + A₁ + (2 ^ 256 * 2 ^ 64 - 2 ^ 256 * T₁)) % (2 ^ 256 * 2 ^ 64) + A₂ + (2 ^ 256 * 2 ^ 64 - 2 ^ 256 * T₂)) % (2 ^ 256 * 2 ^ 64) +
      ((0 + n₁) % 2 ^ 64 + n₂) % 2 ^ 64) % (2 ^ 256 * 2 ^ 64) =
      (A₁ + A₂ + (n₁ + n₂) % 2 ^ 64 + (2 ^ 256 * 2 ^ 65 - 2 ^ 256 * (T₁ + T₂))) % (2 ^ 256 * 2 ^ 64) := by omega
  rw [h, mod320_div]

/-- The registers the inversion writes. -/
abbrev dsClob : List Reg := [.rax, .rbx, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- The registers a row writes: those of the inversion but `rbp`. -/
abbrev rowClob : List Reg := [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

theorem fRow_eq (m₁ m₂ dst : Nat) :
    fRow m₁ m₂ dst = zeroP ++ (prod m₁ dsF true ++ (prod m₂ dsG true ++
      (([.alu .add .r8 (.reg .rbx), .alu .adc .r9 (.imm 0), .alu .adc .r10 (.imm 0),
        .alu .adc .r11 (.imm 0), .alu .adc .r12 (.imm 0)] : List Instr) ++ shStores dst))) := by
  simp only [fRow, List.append_assoc]

/-- A row of `f` and `g`: `[dst] = fRowV [m₁] [m₂] f g`. -/
theorem fRow_ok {s : State} {base : Addr} (hs : Scr s base) {m₁ m₂ dst : Nat} (h₁ : m₁ + 8 ≤ 4096)
    (h₂ : m₂ + 8 ≤ 4096) (hd : dst + 32 ≤ 4096) :
    WP isa (.block (fRow m₁ m₂ dst)) s fun t =>
      fe t.mem base dst = fRowV (word s.mem base m₁) (word s.mem base m₂) (fe s.mem base dsF)
        (fe s.mem base dsG) ∧
      Outside base dst 32 s.mem t.mem ∧ (∀ r, r ∉ rowClob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hF : dsF + 32 ≤ 4096 := by decide
  have hG : dsG + 32 ≤ 4096 := by decide
  rw [fRow_eq, WP.block_append_iff]
  refine WP.mono (zeroP_ok s) fun s₁ ⟨v1, b1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (prod_ok hs₁ h₁ hF true) fun s₂ ⟨v2, b2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (prod_ok hs₂ h₂ hG true) fun s₃ ⟨v3, b3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (addC_ok s₃) fun s₄ ⟨v4, k4⟩ => ?_
  have hs₄ := hs₃.of_keeps k4 (by decide)
  refine WP.mono (shStores_ok hs₄ hd) fun t ⟨mt, gt, rt, wt⟩ => ⟨?_, ?_, ?_, ?_, ?_⟩
  · have M1 : s₁.mem = s.mem := k1.2.1
    have M2 : s₂.mem = s.mem := k2.2.1.trans M1
    have M4 : s₄.mem = s.mem := k4.2.1.trans (k3.2.1.trans M2)
    rw [M1] at v2 b2
    rw [M2] at v3 b3
    rw [mt, M4, fe_st4 _ _ (by omega), shW_val]
    change val5 s₄ / 2 ^ 59 % 2 ^ 256 = _
    rw [v4, v3, v2, v1, b3, b2, b1]
    unfold fRowV cN
    have z : (0 : BitVec 64).toNat = 0 := rfl
    simp only [↓reduceIte, z]
    exact fsum_arith _ _ _ _ _ _ (topN_le _ _) (topN_le _ _)
  · rw [mt, k4.2.1, k3.2.1, k2.2.1, k1.2.1]
    exact st4_outside _ _ (by omega) _ _ _ _
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gt r hr.1 hr.2.2.2.1, k4.1 r (by simp_all), k3.1 r (by simp_all), k2.1 r (by simp_all),
      k1.1 r (by simp_all)]
  · rw [rt, k4.2.2.1, k3.2.2.1, k2.2.2.1, k1.2.2.1]
  · rw [wt, k4.2.2.2, k3.2.2.2, k2.2.2.2, k1.2.2.2]

end VG.Proof.X25519.X86_64
