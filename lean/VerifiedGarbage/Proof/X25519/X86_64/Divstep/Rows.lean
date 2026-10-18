module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.X25519.X86_64.Ops
public import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Spec
public import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Step

/-!
# X25519 on x86-64, inversion by divsteps: the products

`|m|` and the mask of `m`'s sign (`absMk_ok`); the two products of a row,
summed column by column into the five words `r8–r12` (`cols_ok`), each
column from two multiply-accumulate steps (`term_ok`, `col_ok`), which never
overflow as `|m| ≤ 2⁶³`; the sum of the corrections `cN` (`cSum_ok`,
`cSum_val`); and the correction of a signed top (`topCorr_ok`).
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64

/-- The five words `r8–r12`. -/
abbrev val5 (s : State) : Nat :=
  val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) + 2 ^ 256 * (s.gpr .r12).toNat

/-- The four words at `x`, each xored with `k`. -/
abbrev feX (m : Mem) (base : Addr) (x : Nat) (k : BitVec 64) : Nat :=
  val4 (word m base x ^^^ k) (word m base (x + 8) ^^^ k) (word m base (x + 16) ^^^ k) (word m base (x + 24) ^^^ k)

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
    simp; omega_arith
  · have : ¬ 2 ^ 63 ≤ w.toNat := fun h' => hm ((msb_iff w).2 h')
    simp only [Bool.not_eq_true] at hm
    simp only [hm, Bool.false_eq_true, ↓reduceIte]
    rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    simp; omega_arith

theorem absN_eq (w : BitVec 64) : ((w ^^^ maskW w) - maskW w).toNat = absN w := by
  have h := w.isLt
  unfold maskW absN
  rw [BitVec.toInt_eq_msb_cond]
  by_cases hm : w.msb = true
  · have h63 := (msb_iff w).1 hm
    simp only [hm, ↓reduceIte, BitVec.xor_allOnes, BitVec.toNat_sub, BitVec.toNat_not, BitVec.toNat_allOnes]
    omega_arith
  · simp only [Bool.not_eq_true] at hm
    simp only [hm, Bool.false_eq_true, ↓reduceIte, xor0', sub0']
    omega_arith

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
  split <;> omega_arith

theorem and_mask (r m : BitVec 64) : (r &&& maskW m).toNat = if m.msb then r.toNat else 0 := by
  unfold maskW
  by_cases hm : m.msb = true
  · simp only [hm, ↓reduceIte, BitVec.and_allOnes]
  · simp only [Bool.not_eq_true] at hm
    simp only [hm, Bool.false_eq_true, ↓reduceIte, and0']; rfl

theorem zs0 : (0 : BitVec 32).setWidth 64 = 0 := by decide

theorem top_iff (mem : Mem) (base : Addr) (x : Nat) (m : BitVec 64) :
    (word mem base (x + 24) ^^^ maskW m).msb = true ↔ 2 ^ 255 ≤ flipN m (fe mem base x) := by
  rw [msb_iff, xor_word_mask, ← feX_mask]
  simp only [feX, val4, xor_word_mask]
  have := (word mem base x).isLt; have := (word mem base (x + 8)).isLt
  have := (word mem base (x + 16)).isLt; have := (word mem base (x + 24)).isLt
  split <;> omega_arith

/-- `a = |[m]|`, `k` = the mask of its sign. -/
theorem absMk_ok {s : State} {base : Addr} (hs : Scr s base) {m : Nat} (hm : m + 8 ≤ 4096) {a k : Reg}
    (ha : a ≠ .rax) (hk : k ≠ .rax) (hak : a ≠ k) :
    WP isa (.block (absMk m a k)) s fun t =>
      t.gpr k = maskW (word s.mem base m) ∧ (t.gpr a).toNat = absN (word s.mem base m) ∧
      Keeps [.rax, a, k] s t := by
  drun [absMk, load_sc hs hm, zs0, RegUpd.gpr_setReg_self, ha, hk, hak, Ne.symm ha, Ne.symm hk, Ne.symm hak]
  refine ⟨maskW_eq _, by rw [maskW_eq]; exact absN_eq _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h1, h2, h3⟩ := hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, h1, h2, h3, ↓reduceIte]

/-- `hi:lo += a · ([x] ^ k)`, modulo `2¹²⁸`. -/
theorem term_ok {s : State} {base : Addr} (hs : Scr s base) {x : Nat} (hx : x + 8 ≤ 4096) {a k lo hi : Reg}
    (ha : a ≠ .rax) (hk : k ≠ .rax) (hl : lo ≠ .rax) (hl' : lo ≠ .rdx) (hh : hi ≠ .rax) (hh' : hi ≠ .rdx)
    (hlh : lo ≠ hi) :
    WP isa (.block (term x a k lo hi)) s fun t =>
      (t.gpr lo).toNat + 2 ^ 64 * (t.gpr hi).toNat =
        ((s.gpr lo).toNat + 2 ^ 64 * (s.gpr hi).toNat +
          (s.gpr a).toNat * (word s.mem base x ^^^ s.gpr k).toNat) % 2 ^ 128 ∧
      Keeps [lo, hi, .rax, .rdx] s t := by
  drun [term, load_sc hs hx, ha, hk, hl, hl', hh, hh', hlh, Ne.symm ha, Ne.symm hk, Ne.symm hl, Ne.symm hl',
    Ne.symm hh, Ne.symm hh', Ne.symm hlh, RegUpd.gpr_setReg_self]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := mulx_arith (word s.mem base x ^^^ s.gpr k) (s.gpr a)
    generalize BitVec.ofNat 64 ((word s.mem base x ^^^ s.gpr k).toNat * (s.gpr a).toNat) = L at e ⊢
    generalize BitVec.ofNat 64 ((word s.mem base x ^^^ s.gpr k).toNat * (s.gpr a).toNat / 2 ^ 64) = H at e ⊢
    have e0 := add_carry (s.gpr lo) L
    have e1 := adc_carry (s.gpr hi) H (decide (2 ^ 64 ≤ (s.gpr lo).toNat + L.toNat))
    have := (s.gpr hi + H + (BitVec.ofBool (decide (2 ^ 64 ≤ (s.gpr lo).toNat + L.toNat))).setWidth 64).isLt
    have := (s.gpr lo + L).isLt
    rw [Nat.mul_comm (s.gpr a).toNat]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4⟩ := hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, h1, h2, h3, h4, ↓reduceIte]

theorem col_eq (X Y c : Nat) (lo hi : Reg) :
    col X Y c lo hi = ([.mov32 hi (.imm 0)] : List Instr) ++
      (term (X + 8 * c) .rcx .r14 lo hi ++ term (Y + 8 * c) .r13 .r15 lo hi) := rfl

/-- The registers a column writes: not those it reads, nor `rdi`. -/
abbrev colRegs : List Reg := [.rax, .rdx, .rcx, .r13, .r14, .r15, .rdi]

theorem rdi_not_mem {lo hi : Reg} (hL : lo ∉ colRegs) (hH : hi ∉ colRegs) : Reg.rdi ∉ [lo, hi, .rax, .rdx] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hL hH ⊢
  exact ⟨fun h => hL.2.2.2.2.2.2 h.symm, fun h => hH.2.2.2.2.2.2 h.symm, by decide, by decide⟩

/-- A product of a word below `2⁶³` by a word. -/
theorem prod63 (a w : BitVec 64) (h : a.toNat ≤ 2 ^ 63) : a.toNat * w.toNat ≤ 2 ^ 63 * (2 ^ 64 - 1) :=
  Nat.mul_le_mul h (by have := w.isLt; omega)

/-- Column `c`: `hi:lo = lo + |m₁| ([X + 8c] ^ s₁) + |m₂| ([Y + 8c] ^ s₂)`. -/
theorem col_ok {s : State} {base : Addr} (hs : Scr s base) {X Y c : Nat} (hX : X + 8 * c + 8 ≤ 4096)
    (hY : Y + 8 * c + 8 ≤ 4096) {lo hi : Reg} (hL : lo ∉ colRegs) (hH : hi ∉ colRegs) (hlh : lo ≠ hi)
    (h1 : (s.gpr .rcx).toNat ≤ 2 ^ 63) (h2 : (s.gpr .r13).toNat ≤ 2 ^ 63) :
    WP isa (.block (col X Y c lo hi)) s fun t =>
      (t.gpr lo).toNat + 2 ^ 64 * (t.gpr hi).toNat = (s.gpr lo).toNat +
        (s.gpr .rcx).toNat * (word s.mem base (X + 8 * c) ^^^ s.gpr .r14).toNat +
        (s.gpr .r13).toNat * (word s.mem base (Y + 8 * c) ^^^ s.gpr .r15).toNat ∧
      Keeps [lo, hi, .rax, .rdx] s t := by
  have nr := rdi_not_mem hL hH
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hL hH
  rw [col_eq, WP.block_append_iff]
  refine WP.mono (movZero_ok s hi) fun s₀ ⟨z0, k0⟩ => ?_
  have k0' : Keeps [lo, hi, .rax, .rdx] s s₀ := k0.mono (by simp)
  have hs₀ := hs.of_keeps k0' nr
  rw [WP.block_append_iff]
  refine WP.mono (term_ok hs₀ hX (by decide) (by decide) hL.1 hL.2.1 hH.1 hH.2.1 hlh) fun s₁ ⟨e1, k1⟩ => ?_
  have hs₁ := hs₀.of_keeps k1 nr
  refine WP.mono (term_ok hs₁ hY (by decide) (by decide) hL.1 hL.2.1 hH.1 hH.2.1 hlh) fun t ⟨e2, k2⟩ =>
    ⟨?_, k0'.trans (k1.trans k2)⟩
  have nk : ∀ r : Reg, r = .rcx ∨ r = .r13 ∨ r = .r14 ∨ r = .r15 → r ∉ [lo, hi, .rax, .rdx] := by
    rintro r (rfl | rfl | rfl | rfl) <;> simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] <;>
      exact ⟨fun h => by simp_all, fun h => by simp_all, by decide, by decide⟩
  have M1 : s₁.mem = s.mem := k1.2.1.trans k0.2.1
  have c0 : s₀.gpr .rcx = s.gpr .rcx := k0'.1 _ (nk _ (by simp))
  have q0 : s₀.gpr .r14 = s.gpr .r14 := k0'.1 _ (nk _ (by simp))
  have c1 : s₁.gpr .r13 = s.gpr .r13 := (k1.1 _ (nk _ (by simp))).trans (k0'.1 _ (nk _ (by simp)))
  have q1 : s₁.gpr .r15 = s.gpr .r15 := (k1.1 _ (nk _ (by simp))).trans (k0'.1 _ (nk _ (by simp)))
  have l0 : s₀.gpr lo = s.gpr lo := k0.1 _ (by simpa using hlh)
  rw [c0, q0, k0.2.1, l0, z0] at e1
  rw [c1, q1, M1] at e2
  have p1 := prod63 (s.gpr .rcx) (word s.mem base (X + 8 * c) ^^^ s.gpr .r14) h1
  have p2 := prod63 (s.gpr .r13) (word s.mem base (Y + 8 * c) ^^^ s.gpr .r15) h2
  have := (s.gpr lo).isLt
  have z : (0 : BitVec 64).toNat = 0 := rfl
  rw [z] at e1
  omega

/-- The columns: `r8–r12 = r8 + |m₁| ([X] ^ s₁) + |m₂| ([Y] ^ s₂)`. -/
theorem cols_ok {s : State} {base : Addr} (hs : Scr s base) {X Y : Nat} (hX : X + 32 ≤ 4096)
    (hY : Y + 32 ≤ 4096) (h1 : (s.gpr .rcx).toNat ≤ 2 ^ 63) (h2 : (s.gpr .r13).toNat ≤ 2 ^ 63) :
    WP isa (.block (cols X Y)) s fun t =>
      val5 t = (s.gpr .r8).toNat + (s.gpr .rcx).toNat * feX s.mem base X (s.gpr .r14) +
        (s.gpr .r13).toNat * feX s.mem base Y (s.gpr .r15) ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .rax, .rdx] s t := by
  simp only [cols, List.append_assoc]
  have K : ∀ {lo hi : Reg} {s s' : State}, lo ∈ [.r8, .r9, .r10, .r11, .r12] →
      hi ∈ [.r8, .r9, .r10, .r11, .r12] →
      Keeps [lo, hi, .rax, .rdx] s s' → Keeps [.r8, .r9, .r10, .r11, .r12, .rax, .rdx] s s' := by
    intro lo hi s s' hl hh k
    refine k.mono fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl hh hr ⊢
    rcases hr with rfl | rfl | rfl | rfl
    · rcases hl with rfl | rfl | rfl | rfl | rfl <;> simp
    · rcases hh with rfl | rfl | rfl | rfl | rfl <;> simp
    · simp
    · simp
  have R : ∀ {s s' : State}, Keeps [.r8, .r9, .r10, .r11, .r12, .rax, .rdx] s s' →
      s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .r13 = s.gpr .r13 ∧ s'.gpr .r14 = s.gpr .r14 ∧
        s'.gpr .r15 = s.gpr .r15 ∧ s'.mem = s.mem := fun k =>
    ⟨k.1 _ (by decide), k.1 _ (by decide), k.1 _ (by decide), k.1 _ (by decide), k.2.1⟩
  rw [WP.block_append_iff]
  refine WP.mono (col_ok (c := 0) hs (by omega) (by omega) (lo := .r8) (hi := .r9) (by decide) (by decide)
    (by decide) h1 h2) fun s₁ ⟨e1, k1⟩ => ?_
  have k1' := K (by simp) (by simp) k1
  obtain ⟨a1, b1, c1, d1, m1⟩ := R k1'
  rw [WP.block_append_iff]
  refine WP.mono (col_ok (c := 1) (hs.of_keeps k1' (by decide)) (by omega) (by omega) (lo := .r9) (hi := .r10)
    (by decide) (by decide) (by decide) (a1 ▸ h1) (b1 ▸ h2)) fun s₂ ⟨e2, k2⟩ => ?_
  have k2' := K (by simp) (by simp) k2
  obtain ⟨a2, b2, c2, d2, m2⟩ := R k2'
  rw [WP.block_append_iff]
  refine WP.mono (col_ok (c := 2) (hs.of_keeps (k1'.trans k2') (by decide)) (by omega) (by omega)
    (lo := .r10) (hi := .r11) (by decide) (by decide) (by decide) (a2 ▸ a1 ▸ h1) (b2 ▸ b1 ▸ h2))
    fun s₃ ⟨e3, k3⟩ => ?_
  have k3' := K (by simp) (by simp) k3
  obtain ⟨a3, b3, c3, d3, m3⟩ := R k3'
  refine WP.mono (col_ok (c := 3) (hs.of_keeps ((k1'.trans k2').trans k3') (by decide)) (by omega) (by omega)
    (lo := .r11) (hi := .r12) (by decide) (by decide) (by decide) (a3 ▸ a2 ▸ a1 ▸ h1) (b3 ▸ b2 ▸ b1 ▸ h2))
    fun t ⟨e4, k4⟩ => ⟨?_, ((k1'.trans k2').trans k3').trans (K (by simp) (by simp) k4)⟩
  rw [a1, c1, b1, d1, m1] at e2
  rw [a2, a1, c2, c1, b2, b1, d2, d1, m2, m1] at e3
  rw [a3, a2, a1, c3, c2, c1, b3, b2, b1, d3, d2, d1, m3, m2, m1] at e4
  have t8 : t.gpr .r8 = s₁.gpr .r8 := (k4.1 _ (by decide)).trans ((k3.1 _ (by decide)).trans (k2.1 _ (by decide)))
  have t9 : t.gpr .r9 = s₂.gpr .r9 := (k4.1 _ (by decide)).trans (k3.1 _ (by decide))
  have t10 : t.gpr .r10 = s₃.gpr .r10 := k4.1 _ (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul] at e1 e2 e3 e4
  simp only [val5, val4, feX, t8, t9, t10, Nat.mul_add, Nat.mul_left_comm (s.gpr .rcx).toNat,
    Nat.mul_left_comm (s.gpr .r13).toNat]
  omega_arith

/-- `cd = (rcx & r14) + (r13 & r15)`. -/
theorem cSum_ok (s : State) {cd : Reg} (hcd : cd ∉ [.rax, .rcx, .r13, .r14, .r15]) :
    WP isa (.block (cSum cd)) s fun t =>
      t.gpr cd = (s.gpr .rcx &&& s.gpr .r14) + (s.gpr .r13 &&& s.gpr .r15) ∧ Keeps [cd, .rax] s t := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hcd
  obtain ⟨h1, h2, h3, h4, h5⟩ := hcd
  drun [cSum, h1, h2, h3, h4, h5, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5,
    RegUpd.gpr_setReg_self]
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨g1, g2⟩ := hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, g1, g2, ↓reduceIte]

/-- `cSum` of `|m|` and the masks is `cN`. -/
theorem cSum_val (m₁ m₂ a b : BitVec 64) (ha : a.toNat = absN m₁) (hb : b.toNat = absN m₂) :
    ((a &&& maskW m₁) + (b &&& maskW m₂)).toNat = cN m₁ m₂ := by
  rw [BitVec.toNat_add, and_mask, and_mask]
  unfold cN negN
  split <;> split <;> simp only [ha, hb]

/-- `r12 -= a` if `[x + 24] ^ k` is negative. -/
theorem topCorr_ok {s : State} {base : Addr} (hs : Scr s base) {x : Nat} (hx : x + 32 ≤ 4096) {a k : Reg}
    (ha : a ∉ [.rax, .rdx]) (hk : k ≠ .rax) :
    WP isa (.block (topCorr x a k)) s fun t =>
      t.gpr .r12 = s.gpr .r12 - (if (word s.mem base (x + 24) ^^^ s.gpr k).msb then s.gpr a else 0) ∧
      Keeps [.rax, .rdx, .r12] s t := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
  drun [topCorr, load_sc hs (show x + 24 + 8 ≤ 4096 by omega_arith), zs0, RegUpd.gpr_setReg_self, ha.1, ha.2,
    hk, Ne.symm ha.1, Ne.symm ha.2, Ne.symm hk]
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

end VG.Proof.X25519.X86_64
