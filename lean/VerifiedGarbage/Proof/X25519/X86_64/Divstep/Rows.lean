import VerifiedGarbage.Proof.X25519.X86_64.Ops
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Spec
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Step

/-!
# X25519 on x86-64, inversion by divsteps: the products

A product row (`dsRow`): the five words `r8–r12` plus `r14` times the four
words at `x`, each xored with `r15`, modulo `2³²⁰` (`dsRow_ok`), from
multiply-accumulate steps (`mulStepX_ok`); `|m|` and the mask of `m`'s sign
(`absM_ok`); and a product of a signed word by four words (`prod_ok`).
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64

/-- The five words `r8–r12`. -/
abbrev val5 (s : State) : Nat :=
  val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) + 2 ^ 256 * (s.gpr .r12).toNat

/-- The four words at `x`, each xored with `k`. -/
abbrev feX (m : Mem) (base : Addr) (x : Nat) (k : BitVec 64) : Nat :=
  val4 (word m base x ^^^ k) (word m base (x + 8) ^^^ k) (word m base (x + 16) ^^^ k) (word m base (x + 24) ^^^ k)

/-- A multiply-accumulate step on a word xored with `k`: `t:c = t + c + ai · (src ^ k)`. -/
theorem mulStepX_ok (s : State) {t c ai k : Reg} {src : Src} {v : BitVec 64}
    (hsrc : readSrc s src = some v) (ht : t ≠ .rax) (ht' : t ≠ .rdx) (hc : c ≠ .rax)
    (hc' : c ≠ .rdx) (ha : ai ≠ .rax) (htc : t ≠ c) (hk : k ≠ .rax) :
    WP isa (.block (mulStepX t c ai k src)) s fun s' =>
      (s'.gpr t).toNat + 2 ^ 64 * (s'.gpr c).toNat =
        (s.gpr t).toNat + (s.gpr c).toNat + (s.gpr ai).toNat * (v ^^^ s.gpr k).toNat ∧
      Keeps [t, c, .rax, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [mulStepX, mulStep, List.tail_cons, List.cons_append, List.nil_append, runBlock_cons, exec, hsrc,
    Option.map_some, runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execMul,
    execAlu, Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true, ha, hc, ht, htc, hc', ht', hk,
    Ne.symm htc, Ne.symm ht', ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left', se0]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := step_arith (s.gpr ai) (v ^^^ s.gpr k) (s.gpr c) (s.gpr t)
    simp only at e
    rw [Nat.mul_comm (s.gpr ai).toNat] at e ⊢
    exact e
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2, ite_false]

theorem zext0' : (0 : BitVec 32).setWidth 64 = 0 := by decide

/-- `r = 0` (by `mov32`). -/
theorem movZero_ok (s : State) (r : Reg) :
    WP isa (.block [.mov32 r (.imm 0)]) s fun t => t.gpr r = 0 ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some, State.setReg32,
    RegUpd.gpr_setReg_self, zext0', Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r' hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  rw [RegUpd.gpr_setReg_of_ne _ _ hr]

/-- `d += src` (64-bit, no flags needed). -/
theorem addReg_ok (s : State) (d src : Reg) :
    WP isa (.block [.alu .add d (.reg src)]) s fun t =>
      t.gpr d = s.gpr d + s.gpr src ∧ Keeps [d] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r' hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-- A product row: `r8–r12 += r14 · ([x] ^ r15)` modulo `2³²⁰`. -/
theorem dsRow_ok {s : State} {base : Addr} (hs : Scr s base) {x : Nat} (hx : x + 32 ≤ 4096) :
    WP isa (.block (dsRow x)) s fun t =>
      val5 t = (val5 s + (s.gpr .r14).toNat * feX s.mem base x (s.gpr .r15)) % (2 ^ 256 * 2 ^ 64) ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .r13, .rax, .rdx] s t := by
  simp only [dsRow, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (movZero_ok s .r13) fun s₀ ⟨z0, k0⟩ => ?_
  have hs₀ := hs.of_keeps k0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulStepX_ok s₀ (readSrc_sc hs₀ (by omega)) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₁ ⟨e1, k1⟩ => ?_
  have hs₁ := hs₀.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulStepX_ok s₁ (readSrc_sc hs₁ (by omega)) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulStepX_ok s₂ (readSrc_sc hs₂ (by omega)) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulStepX_ok s₃ (readSrc_sc hs₃ (by omega)) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₄ ⟨e4, k4⟩ => ?_
  refine WP.mono (addReg_ok s₄ .r12 .r13) fun t ⟨e5, k5⟩ => ⟨?_, ?_⟩
  · -- The memory, `r14`, `r15` along the way.
    have M1 : s₁.mem = s.mem := k1.2.1.trans k0.2.1
    have M2 : s₂.mem = s.mem := k2.2.1.trans M1
    have M3 : s₃.mem = s.mem := k3.2.1.trans M2
    have A1 : s₁.gpr .r14 = s.gpr .r14 := (k1.1 _ (by decide)).trans (k0.1 _ (by decide))
    have A2 : s₂.gpr .r14 = s.gpr .r14 := (k2.1 _ (by decide)).trans A1
    have A3 : s₃.gpr .r14 = s.gpr .r14 := (k3.1 _ (by decide)).trans A2
    have A0 : s₀.gpr .r14 = s.gpr .r14 := k0.1 _ (by decide)
    have K0 : s₀.gpr .r15 = s.gpr .r15 := k0.1 _ (by decide)
    have K1 : s₁.gpr .r15 = s.gpr .r15 := (k1.1 _ (by decide)).trans K0
    have K2 : s₂.gpr .r15 = s.gpr .r15 := (k2.1 _ (by decide)).trans K1
    have K3 : s₃.gpr .r15 = s.gpr .r15 := (k3.1 _ (by decide)).trans K2
    rw [A0, K0, k0.2.1] at e1
    rw [A1, K1, M1] at e2
    rw [A2, K2, M2] at e3
    rw [A3, K3, M3] at e4
    -- The registers each step leaves.
    have r8₂ : s₂.gpr .r8 = s₁.gpr .r8 := k2.1 _ (by decide)
    have r8₃ : s₃.gpr .r8 = s₁.gpr .r8 := (k3.1 _ (by decide)).trans r8₂
    have r8₄ : s₄.gpr .r8 = s₁.gpr .r8 := (k4.1 _ (by decide)).trans r8₃
    have r9₃ : s₃.gpr .r9 = s₂.gpr .r9 := k3.1 _ (by decide)
    have r9₄ : s₄.gpr .r9 = s₂.gpr .r9 := (k4.1 _ (by decide)).trans r9₃
    have r10₄ : s₄.gpr .r10 = s₃.gpr .r10 := k4.1 _ (by decide)
    have r9₁ : s₁.gpr .r9 = s.gpr .r9 := (k1.1 _ (by decide)).trans (k0.1 _ (by decide))
    have r10₂ : s₂.gpr .r10 = s.gpr .r10 :=
      (k2.1 _ (by decide)).trans ((k1.1 _ (by decide)).trans (k0.1 _ (by decide)))
    have r11₃ : s₃.gpr .r11 = s.gpr .r11 :=
      (k3.1 _ (by decide)).trans ((k2.1 _ (by decide)).trans ((k1.1 _ (by decide)).trans (k0.1 _ (by decide))))
    have r12₄ : s₄.gpr .r12 = s.gpr .r12 := (k4.1 _ (by decide)).trans ((k3.1 _ (by decide)).trans
      ((k2.1 _ (by decide)).trans ((k1.1 _ (by decide)).trans (k0.1 _ (by decide)))))
    have r8₀ : s₀.gpr .r8 = s.gpr .r8 := k0.1 _ (by decide)
    rw [r8₀, z0] at e1
    rw [r9₁] at e2
    rw [r10₂] at e3
    rw [r11₃] at e4
    have t8 : t.gpr .r8 = s₄.gpr .r8 := k5.1 _ (by decide)
    have t9 : t.gpr .r9 = s₄.gpr .r9 := k5.1 _ (by decide)
    have t10 : t.gpr .r10 = s₄.gpr .r10 := k5.1 _ (by decide)
    have t11 : t.gpr .r11 = s₄.gpr .r11 := k5.1 _ (by decide)
    simp only [val5, val4, feX, t8, t9, t10, t11, e5, r8₄, r9₄, r10₄, r12₄, BitVec.toNat_add]
    have h12 := (s.gpr .r12).isLt
    have h13 := (s₄.gpr .r13).isLt
    have z : (0 : BitVec 64).toNat = 0 := rfl
    rw [z] at e1
    simp only [Nat.mul_add, Nat.mul_left_comm (s.gpr .r14).toNat]
    omega
  · exact ((((k0.mono (by decide)).trans (k1.mono (by decide))).trans (k2.mono (by decide))).trans
      (k3.mono (by decide))).trans (k4.mono (by decide)) |>.trans (k5.mono (by decide))

/-! ## `|m|` and the mask of its sign -/

/-- The mask of a word's sign. -/
def maskW (w : BitVec 64) : BitVec 64 := if w.msb then BitVec.allOnes 64 else 0

theorem xor0' (w : BitVec 64) : w ^^^ 0 = w := by simp
theorem sub0' (w : BitVec 64) : w - 0 = w := by simp
theorem and0' (w : BitVec 64) : w &&& 0 = 0 := by simp

theorem msb_iff (w : BitVec 64) : w.msb = true ↔ 2 ^ 63 ≤ w.toNat := by
  rw [BitVec.msb_eq_decide]; simp

theorem maskW_eq (w : BitVec 64) : (0 : BitVec 64) - (w >>> 63) = maskW w := by
  apply BitVec.eq_of_toNat_eq
  have h := w.isLt
  unfold maskW
  by_cases hm : w.msb = true
  · have := (msb_iff w).1 hm
    simp only [hm, ↓reduceIte]
    rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_allOnes]
    simp; omega
  · have : ¬ 2 ^ 63 ≤ w.toNat := fun h' => hm ((msb_iff w).2 h')
    simp only [Bool.not_eq_true] at hm
    simp only [hm, Bool.false_eq_true, ↓reduceIte]
    rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    simp; omega

theorem absN_eq (w : BitVec 64) : ((w ^^^ maskW w) - maskW w).toNat = absN w := by
  have h := w.isLt
  unfold maskW absN
  rw [BitVec.toInt_eq_msb_cond]
  by_cases hm : w.msb = true
  · have h63 := (msb_iff w).1 hm
    simp only [hm, ↓reduceIte, BitVec.xor_allOnes, BitVec.toNat_sub, BitVec.toNat_not, BitVec.toNat_allOnes]
    omega
  · simp only [Bool.not_eq_true] at hm
    simp only [hm, Bool.false_eq_true, ↓reduceIte, xor0', sub0']
    omega

theorem xor_word_mask (w : BitVec 64) (m : BitVec 64) :
    (w ^^^ maskW m).toNat = if m.msb then 2 ^ 64 - 1 - w.toNat else w.toNat := by
  unfold maskW
  by_cases hm : m.msb = true
  · simp only [hm, ↓reduceIte, BitVec.xor_allOnes, BitVec.toNat_not]
  · simp only [Bool.not_eq_true] at hm
    simp only [hm, Bool.false_eq_true, ↓reduceIte, xor0']

theorem feX_mask (mem : Mem) (base : Addr) (x : Nat) (m : BitVec 64) :
    feX mem base x (maskW m) = flipN m (fe mem base x) := by
  simp only [feX, fe, flipN, val4, xor_word_mask]
  have := (word mem base x).isLt; have := (word mem base (x + 8)).isLt
  have := (word mem base (x + 16)).isLt; have := (word mem base (x + 24)).isLt
  split <;> omega

theorem and_mask (r m : BitVec 64) : (r &&& maskW m).toNat = if m.msb then r.toNat else 0 := by
  unfold maskW
  by_cases hm : m.msb = true
  · simp only [hm, ↓reduceIte, BitVec.and_allOnes]
  · simp only [Bool.not_eq_true] at hm
    simp only [hm, Bool.false_eq_true, ↓reduceIte, and0']; rfl

theorem zs0 : (0 : BitVec 32).setWidth 64 = 0 := by decide

/-- `r15` = the mask of `[m]`'s sign, `r14 = |[m]|`. -/
theorem absM_ok {s : State} {base : Addr} (hs : Scr s base) {m : Nat} (hm : m + 8 ≤ 4096) :
    WP isa (.block (absM m)) s fun t =>
      t.gpr .r15 = maskW (word s.mem base m) ∧ (t.gpr .r14).toNat = absN (word s.mem base m) ∧
      Keeps [.rax, .rcx, .r14, .r15] s t := by
  drun [absM, load_sc hs hm, zs0, RegUpd.gpr_setReg_self]
  refine ⟨maskW_eq _, by rw [maskW_eq]; exact absN_eq _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h1, h2, h3, h4⟩ := hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, h1, h2, h3, h4, ↓reduceIte]

/-- `r12 -= r14` if `[x + 24] ^ r15` is negative. -/
theorem topCorr_ok {s : State} {base : Addr} (hs : Scr s base) {x : Nat} (hx : x + 32 ≤ 4096) :
    WP isa (.block (topCorr x)) s fun t =>
      t.gpr .r12 = s.gpr .r12 -
        (if (word s.mem base (x + 24) ^^^ s.gpr .r15).msb then s.gpr .r14 else 0) ∧
      Keeps [.rax, .rdx, .r12] s t := by
  drun [topCorr, load_sc hs (show x + 24 + 8 ≤ 4096 by omega), zs0, RegUpd.gpr_setReg_self]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · congr 1
    rw [maskW_eq]
    unfold maskW
    split
    · rw [BitVec.allOnes_and]
    · simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3⟩ := hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, h1, h2, h3, ↓reduceIte]

/-- `rbx += r14 & r15`. -/
theorem cAcc_ok (s : State) :
    WP isa (.block cAcc) s fun t =>
      t.gpr .rbx = s.gpr .rbx + (s.gpr .r14 &&& s.gpr .r15) ∧ Keeps [.rax, .rbx] s t := by
  drun [cAcc, RegUpd.gpr_setReg_self]
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h1, h2⟩ := hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h1, h2, ↓reduceIte]

theorem top_iff (mem : Mem) (base : Addr) (x : Nat) (m : BitVec 64) :
    (word mem base (x + 24) ^^^ maskW m).msb = true ↔ 2 ^ 255 ≤ flipN m (fe mem base x) := by
  rw [msb_iff, xor_word_mask, ← feX_mask]
  simp only [feX, val4, xor_word_mask]
  have := (word mem base x).isLt; have := (word mem base (x + 8)).isLt
  have := (word mem base (x + 16)).isLt; have := (word mem base (x + 24)).isLt
  split <;> omega

/-- A product: `r8–r12 += |m| ([x] ^ s)` (less `2²⁵⁶ |m|` if signed and negative),
`rbx += |m|` if `m < 0`. -/
theorem prod_ok {s : State} {base : Addr} (hs : Scr s base) {m x : Nat} (hm : m + 8 ≤ 4096)
    (hx : x + 32 ≤ 4096) (signed : Bool) :
    WP isa (.block (prod m x signed)) s fun t =>
      val5 t = (val5 s + absN (word s.mem base m) * flipN (word s.mem base m) (fe s.mem base x) +
        (2 ^ 256 * 2 ^ 64 - 2 ^ 256 * (if signed then topN (word s.mem base m) (fe s.mem base x) else 0))) % (2 ^ 256 * 2 ^ 64) ∧
      (t.gpr .rbx).toNat = ((s.gpr .rbx).toNat + negN (word s.mem base m)) % 2 ^ 64 ∧
      Keeps [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  rw [prod, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (absM_ok hs hm) fun s₁ ⟨m1, a1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  refine WP.mono (dsRow_ok hs₁ hx) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  have M1 : s₁.mem = s.mem := k1.2.1
  have M2 : s₂.mem = s.mem := k2.2.1.trans M1
  rw [M1, m1, a1, feX_mask] at e2
  have R14 : s₂.gpr .r14 = s₁.gpr .r14 := k2.1 _ (by decide)
  have R15 : s₂.gpr .r15 = s₁.gpr .r15 := k2.1 _ (by decide)
  -- The top correction, as a change of `r12` only.
  have hT : WP isa (.block (if signed then topCorr x else [])) s₂ fun s₃ =>
      val5 s₃ = (val5 s₂ + (2 ^ 256 * 2 ^ 64 - 2 ^ 256 * (if signed then topN (word s.mem base m) (fe s.mem base x) else 0))) % (2 ^ 256 * 2 ^ 64) ∧
      Keeps [.rax, .rdx, .r12] s₂ s₃ := by
    cases signed
    · refine WP.block_nil ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.mul_zero, Nat.sub_zero]
      have : val5 s₂ < 2 ^ 256 * 2 ^ 64 := by
        simp only [val5, val4]
        have := (s₂.gpr .r8).isLt; have := (s₂.gpr .r9).isLt; have := (s₂.gpr .r10).isLt
        have := (s₂.gpr .r11).isLt; have := (s₂.gpr .r12).isLt
        omega
      omega
    · refine WP.mono (topCorr_ok hs₂ hx) fun s₃ ⟨e3, k3⟩ => ⟨?_, k3⟩
      have o8 : s₃.gpr .r8 = s₂.gpr .r8 := k3.1 _ (by decide)
      have o9 : s₃.gpr .r9 = s₂.gpr .r9 := k3.1 _ (by decide)
      have o10 : s₃.gpr .r10 = s₂.gpr .r10 := k3.1 _ (by decide)
      have o11 : s₃.gpr .r11 = s₂.gpr .r11 := k3.1 _ (by decide)
      rw [M2, R15, m1, R14] at e3
      have ht : (if (word s.mem base (x + 24) ^^^ maskW (word s.mem base m)).msb = true then s₁.gpr .r14 else 0).toNat =
          topN (word s.mem base m) (fe s.mem base x) := by
        unfold topN
        by_cases h : 2 ^ 255 ≤ flipN (word s.mem base m) (fe s.mem base x)
        · simp only [(top_iff _ _ _ _).2 h, h, ↓reduceIte, a1]
        · have h' : ¬ (word s.mem base (x + 24) ^^^ maskW (word s.mem base m)).msb = true :=
            fun h' => h ((top_iff _ _ _ _).1 h')
          simp only [h', h, ↓reduceIte]; rfl
      simp only [val5, val4, o8, o9, o10, o11, e3, BitVec.toNat_sub, ht, ↓reduceIte]
      have := (s₂.gpr .r8).isLt; have := (s₂.gpr .r9).isLt; have := (s₂.gpr .r10).isLt
      have := (s₂.gpr .r11).isLt; have := (s₂.gpr .r12).isLt
      have : topN (word s.mem base m) (fe s.mem base x) < 2 ^ 64 := by
        unfold topN absN; split
        · have := (word s.mem base m).toInt_le; have := (word s.mem base m).le_toInt; omega
        · omega
      omega
  refine WP.mono hT fun s₃ ⟨e3, k3⟩ => ?_
  refine WP.mono (cAcc_ok s₃) fun t ⟨e4, k4⟩ => ⟨?_, ?_, ?_⟩
  · have o8 : t.gpr .r8 = s₃.gpr .r8 := k4.1 _ (by decide)
    have o9 : t.gpr .r9 = s₃.gpr .r9 := k4.1 _ (by decide)
    have o10 : t.gpr .r10 = s₃.gpr .r10 := k4.1 _ (by decide)
    have o11 : t.gpr .r11 = s₃.gpr .r11 := k4.1 _ (by decide)
    have o12 : t.gpr .r12 = s₃.gpr .r12 := k4.1 _ (by decide)
    have ev : val5 t = val5 s₃ := by simp only [val5, val4, o8, o9, o10, o11, o12]
    have s8 : s₁.gpr .r8 = s.gpr .r8 := k1.1 _ (by decide)
    have s9 : s₁.gpr .r9 = s.gpr .r9 := k1.1 _ (by decide)
    have s10 : s₁.gpr .r10 = s.gpr .r10 := k1.1 _ (by decide)
    have s11 : s₁.gpr .r11 = s.gpr .r11 := k1.1 _ (by decide)
    have s12 : s₁.gpr .r12 = s.gpr .r12 := k1.1 _ (by decide)
    have ev1 : val5 s₁ = val5 s := by simp only [val5, val4, s8, s9, s10, s11, s12]
    rw [ev, e3, e2, ev1]
    omega
  · have r14 : s₃.gpr .r14 = s₁.gpr .r14 := (k3.1 _ (by decide)).trans R14
    have r15 : s₃.gpr .r15 = s₁.gpr .r15 := (k3.1 _ (by decide)).trans R15
    have rb : s₃.gpr .rbx = s.gpr .rbx :=
      (k3.1 _ (by decide)).trans ((k2.1 _ (by decide)).trans (k1.1 _ (by decide)))
    rw [e4, BitVec.toNat_add, rb, r14, r15, m1, and_mask]
    unfold negN
    split
    · rw [a1]
    · rfl
  · exact ((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide)) |>.trans
      (k4.mono (by decide))

end VG.Proof.X25519.X86_64
