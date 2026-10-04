import VerifiedGarbage.Proof.Bignum.X86_64.IfmaVec

/-!
# RSA with AVX512_IFMA on x86-64: moving numbers between the layouts

`to52` (`to52_ok`) reads sixteen 64-bit words and writes the twenty 52-bit
limbs of their value in the vector layout; `to64` (`to64_ok`) the reverse,
into seventeen words. A left shift is a rotation and a mask (`shl_eq'`).
-/

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum.X86_64 (off word ofs Outside off_off Scr ofs_off writeW_outside wv)
open VG.Impl.Rsa.X86_64.CrtIfma (D mask52)

theorem testBit_hiMask {t i : Nat} (ht : t ≤ 64) (hi : i < 64) : (2 ^ 64 - 2 ^ t).testBit i = decide (t ≤ i) := by
  rw [show 2 ^ 64 - 2 ^ t = (2 ^ (64 - t) - 1) * 2 ^ t by
    rw [Nat.sub_mul, Nat.one_mul, ← Nat.pow_add, Nat.sub_add_cancel ht]]
  rw [Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases h : t ≤ i
  · simp only [h, decide_true, Bool.true_and]; exact decide_eq_true (by omega)
  · simp only [h, decide_false, Bool.false_and]

/-- `shl r t`: rotated right by `64 - t`, its low `t` bits cleared. -/
theorem shl_eq' (x : BitVec 64) {t : Nat} (h1 : 1 ≤ t) (h2 : t ≤ 63) :
    x.rotateRight (64 - t) &&& BitVec.ofNat 64 (2 ^ 64 - 2 ^ t) = x <<< t := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and,
    testBit_hiMask (show t ≤ 64 by omega) hi]
  by_cases h : i < t
  · simp [h, show ¬ t ≤ i by omega]
  · rw [BitVec.getLsbD_rotateRight_of_lt (by omega)]
    simp only [show t ≤ i by omega, decide_true, Bool.and_true, h, decide_false, Bool.not_false, Bool.true_and]
    rw [show 64 - (64 - t) = t by omega]
    simp [h, hi]


theorem drop_hi (a k y : Nat) (hk : 52 ≤ k) : (a + 2 ^ k * y) % 2 ^ 52 = a % 2 ^ 52 := by
  rw [show 2 ^ k = 2 ^ 52 * 2 ^ (k - 52) by rw [← Nat.pow_add, Nat.add_sub_cancel' hk], Nat.mul_assoc,
    Nat.add_mul_mod_self_left]

theorem div_split (a c s : Nat) (hs : s ≤ 64) : (a + 2 ^ 64 * c) / 2 ^ s = a / 2 ^ s + 2 ^ (64 - s) * c := by
  rw [show 2 ^ 64 * c = 2 ^ s * (2 ^ (64 - s) * c) by rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_cancel' hs],
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]

/-- A limb across two words, as the code assembles it. -/
theorem or_shr_shl (x y : BitVec 64) {s : Nat} (h1 : 1 ≤ s) (h2 : s ≤ 63) :
    (x >>> s ||| y <<< (64 - s)).toNat = x.toNat / 2 ^ s + y.toNat * 2 ^ (64 - s) % 2 ^ 64 := by
  rw [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]
  have hx : x.toNat / 2 ^ s < 2 ^ (64 - s) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.sub_add_cancel (by omega)]; exact x.isLt
  have e : y.toNat * 2 ^ (64 - s) % 2 ^ 64 = (y.toNat % 2 ^ s) * 2 ^ (64 - s) := by
    rw [show 2 ^ 64 = 2 ^ s * 2 ^ (64 - s) by rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)],
      Nat.mul_mod_mul_right]
  rw [e, ← Nat.shiftLeft_eq, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.add_comm]


theorem and_mask' (x : BitVec 64) : x &&& mask52 = BitVec.ofNat 64 (x.toNat % 2 ^ 52) := by
  rw [← and_mask x.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem mod52_of_mod64 (X Y : Nat) : (X + Y % 2 ^ 64) % 2 ^ 52 = (X + Y) % 2 ^ 52 := by
  rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (show 2 ^ 52 ∣ 2 ^ 64 from Nat.pow_dvd_pow 2 (by decide)), ← Nat.add_mod]

/-- The words from word `w` on, a number. -/
theorem wv_div {m : Mem} {A : Addr} {w : Nat} (hw : w < 16) :
    wv m A 0 16 / 2 ^ (64 * w) = (word m A (8 * w)).toNat + 2 ^ 64 * wv m A (8 * w + 8) (15 - w) := by
  have e := VG.Proof.Bignum.X86_64.wv_add m A 0 w (16 - w)
  rw [show w + (16 - w) = 16 by omega] at e
  have e1 := VG.Proof.Bignum.X86_64.wv_add m A (0 + 8 * w) 1 (15 - w)
  rw [show 1 + (15 - w) = 16 - w by omega] at e1
  rw [e, e1, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (VG.Proof.Bignum.X86_64.wv_lt m A 0 w), Nat.zero_add]
  simp only [VG.Proof.Bignum.X86_64.wv, Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.mul_one,
    Nat.add_zero]

theorem wv_one {m : Mem} {A : Addr} {d k : Nat} (hk : 1 ≤ k) :
    wv m A d k = (word m A d).toNat + 2 ^ 64 * wv m A (d + 8) (k - 1) := by
  have e := VG.Proof.Bignum.X86_64.wv_add m A d 1 (k - 1)
  rw [show 1 + (k - 1) = k by omega] at e
  rw [e]
  simp only [VG.Proof.Bignum.X86_64.wv, Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.mul_one,
    Nat.add_zero]


/-- Limb `j` of `N`. -/
def limbN (N j : Nat) : Nat := N / 2 ^ (52 * j) % 2 ^ 52

/-- Limb `j` of `to52`. -/
def l52 (j : Nat) : List Instr :=
  let b := 52 * j
  let w := b / 64
  let s := b % 64
  ([.mov .rax (.mem (VG.Impl.Rsa.X86_64.CrtIfma.at_ .rsi (8 * w)))] : List Instr) ++
  (if s = 0 then [] else [.shift .shr .rax s]) ++
  (if 12 < s ∧ w + 1 < 16 then
    ([.mov .rcx (.mem (VG.Impl.Rsa.X86_64.CrtIfma.at_ .rsi (8 * (w + 1))))] : List Instr) ++
      VG.Impl.Rsa.X86_64.CrtIfma.shl .rcx (64 - s) ++ ([.alu .or .rax (.reg .rcx)] : List Instr)
  else []) ++
  ([.alu .and .rax (.reg .r12), .store (VG.Impl.Rsa.X86_64.CrtIfma.at_ .r11 (VG.Impl.Rsa.X86_64.CrtIfma.off j)) .rax] :
    List Instr)

theorem to52_eq : VG.Impl.Rsa.X86_64.CrtIfma.to52 = (List.range 20).flatMap l52 := rfl

/-- The value of a limb within one word (`s ≤ 12`) or in the last (`w = 15`). -/
theorem limbN_one {m : Mem} {A : Addr} {j : Nat} (hj : j < 20) (h : 52 * j % 64 ≤ 12 ∨ 52 * j / 64 = 15) :
    limbN (wv m A 0 16) j = (word m A (8 * (52 * j / 64))).toNat / 2 ^ (52 * j % 64) % 2 ^ 52 := by
  have hw : 52 * j / 64 < 16 := by omega
  unfold limbN
  rw [show 52 * j = 64 * (52 * j / 64) + 52 * j % 64 by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul,
    show (64 * (52 * j / 64) + 52 * j % 64) / 64 = 52 * j / 64 by omega,
    show (64 * (52 * j / 64) + 52 * j % 64) % 64 = 52 * j % 64 by omega, wv_div hw, div_split _ _ _ (by omega)]
  rcases h with h | h
  · exact drop_hi _ _ _ (by omega)
  · rw [h, show 15 - 15 = 0 from rfl]; simp [VG.Proof.Bignum.X86_64.wv]

/-- The value of a limb across two words. -/
theorem limbN_two {m : Mem} {A : Addr} {j : Nat} (h : 12 < 52 * j % 64) (h' : 52 * j / 64 + 1 < 16) :
    limbN (wv m A 0 16) j = ((word m A (8 * (52 * j / 64))).toNat / 2 ^ (52 * j % 64) +
      (word m A (8 * (52 * j / 64 + 1))).toNat * 2 ^ (64 - 52 * j % 64) % 2 ^ 64) % 2 ^ 52 := by
  have hw : 52 * j / 64 < 16 := by omega
  unfold limbN
  rw [show 52 * j = 64 * (52 * j / 64) + 52 * j % 64 by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul,
    show (64 * (52 * j / 64) + 52 * j % 64) / 64 = 52 * j / 64 by omega,
    show (64 * (52 * j / 64) + 52 * j % 64) % 64 = 52 * j % 64 by omega, wv_div hw, div_split _ _ _ (by omega),
    wv_one (by omega), mod52_of_mod64, Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add, ← Nat.add_assoc,
    show 8 * (52 * j / 64) + 8 = 8 * (52 * j / 64 + 1) by omega, Nat.mul_comm (2 ^ (64 - _))]
  exact drop_hi _ _ _ (by omega)


theorem l52_writes : ∀ j < 20, VG.Proof.MlKem.X86_64.writesOnly [.rax, .rcx, .rbp] (.block (l52 j)) = true := by
  decide

/-- Limb `j` of the sixteen words at `rsi = A` into `r11 + off j`. -/
theorem l52_ok {s : State} {A C : Addr} {j : Nat} (hj : j < 20) (hA : s.gpr .rsi = A) (hC : s.gpr .r11 = C)
    (h12 : s.gpr .r12 = mask52) (hrd : ∀ i < 16, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (8 * i)) 8)
    (hwr : InRegions s.wr (C + BitVec.ofNat 64 (VG.Impl.Rsa.X86_64.CrtIfma.off j)) 8) :
    WP isa (.block (l52 j)) s fun s' =>
      s'.mem = s.mem.writeW (off C (VG.Impl.Rsa.X86_64.CrtIfma.off j)) (BitVec.ofNat 64 (limbN (wv s.mem A 0 16) j)) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rbp] s s' ∧ s'.mxcsr = s.mxcsr := by
  have hw : 52 * j / 64 < 16 := by omega
  have r0 := hrd _ hw
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax, .rcx, .rbp] (Q := fun s' =>
    s'.mem = s.mem.writeW (off C (VG.Impl.Rsa.X86_64.CrtIfma.off j)) (BitVec.ofNat 64 (limbN (wv s.mem A 0 16) j)) ∧
      s'.mxcsr = s.mxcsr) ?_ (l52_writes j hj)) fun s' ⟨⟨a, b⟩, k⟩ => ⟨a, k, b⟩
  by_cases h0 : 52 * j % 64 = 0
  · have hC' : (12 < 0 ∧ 52 * j / 64 + 1 < 16) = False := eq_false (by omega)
    simp only [l52, h0, ite_true, hC', ite_false, List.append_nil, List.cons_append, List.nil_append]
    xrun [ea_at', hA, hC, h12, r0, hwr]
    refine ⟨congrArg (Mem.writeW _ _) ?_, rfl⟩
    rw [and_mask', limbN_one hj (.inl (by omega)), h0, Nat.pow_zero, Nat.div_one]
  · have hsc : (1 ≤ 52 * j % 64 ∧ 52 * j % 64 ≤ 63) = True := eq_true ⟨by omega, by omega⟩
    by_cases hC2 : 12 < 52 * j % 64 ∧ 52 * j / 64 + 1 < 16
    · have r1 := hrd _ hC2.2
      have hmc : (1 ≤ 64 - (64 - 52 * j % 64) ∧ 64 - (64 - 52 * j % 64) ≤ 63) = True :=
        eq_true ⟨by omega, by omega⟩
      simp only [l52, h0, ite_false, hC2, and_self, ite_true, VG.Impl.Rsa.X86_64.CrtIfma.shl,
        List.cons_append, List.nil_append]
      xrun [ea_at', hA, hC, h12, r0, r1, hwr, hsc, hmc]
      refine ⟨congrArg (Mem.writeW _ _) ?_, rfl⟩
      rw [shl_eq' _ (by omega) (by omega), and_mask', or_shr_shl _ _ (by omega) (by omega), limbN_two hC2.1 hC2.2]
    · simp only [l52, h0, ite_false, hC2, List.append_nil, List.cons_append, List.nil_append]
      xrun [ea_at', hA, hC, h12, r0, hwr, hsc]
      refine ⟨congrArg (Mem.writeW _ _) ?_, rfl⟩
      rw [and_mask', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, limbN_one hj (by omega)]


/-- The sixteen words at `rsi = A` into twenty limbs at `r11 = C`. -/
theorem to52_ok {s : State} {A C : Addr} (hA : s.gpr .rsi = A) (hC : s.gpr .r11 = C)
    (h12 : s.gpr .r12 = mask52) (hrd : ∀ i < 16, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (8 * i)) 8)
    (hwr : ∀ j < 20, InRegions s.wr (C + BitVec.ofNat 64 (VG.Impl.Rsa.X86_64.CrtIfma.off j)) 8)
    (hsep : ∀ m m' : Mem, Outside C 0 160 m m' → ∀ i < 16, word m' A (8 * i) = word m A (8 * i)) :
    WP isa (.block VG.Impl.Rsa.X86_64.CrtIfma.to52) s fun s' =>
      (∀ j < 20, word s'.mem C (VG.Impl.Rsa.X86_64.CrtIfma.off j) = BitVec.ofNat 64 (limbN (wv s.mem A 0 16) j)) ∧
      Outside C 0 160 s.mem s'.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rbp] s s' ∧ s'.mxcsr = s.mxcsr := by
  rw [to52_eq]
  suffices h : ∀ n ≤ 20, WP isa (.block ((List.range n).flatMap l52)) s fun s' =>
      (∀ j < n, word s'.mem C (VG.Impl.Rsa.X86_64.CrtIfma.off j) = BitVec.ofNat 64 (limbN (wv s.mem A 0 16) j)) ∧
      Outside C 0 160 s.mem s'.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rbp] s s' ∧ s'.mxcsr = s.mxcsr from
    h 20 (Nat.le_refl _)
  intro n
  induction n with
  | zero => intro _; exact WP.block_nil ⟨fun _ h => absurd h (by omega), Outside.refl _ _ _ _,
      VG.Proof.MlKem.X86_64.Keep.refl _ _, rfl⟩
  | succ n ih =>
    intro hn
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨v, o, k, x⟩ => ?_
    have hwv : wv t.mem A 0 16 = wv s.mem A 0 16 := VG.Proof.Bignum.X86_64.wv_congr fun i hi => by
      rw [Nat.zero_add]; exact hsep _ _ o i hi
    refine WP.mono (l52_ok (j := n) (A := A) (C := C) (by omega) ((k.gpr (by decide)).trans hA)
      ((k.gpr (by decide)).trans hC) ((k.gpr (by decide)).trans h12)
      (fun i hi => by rw [k.2.1, k.2.2]; exact hrd i hi) (by rw [k.2.2]; exact hwr n (by omega)))
      fun t' ⟨m', k', x'⟩ => ⟨fun j hj => ?_, ?_, (k.trans k').mono (by simp), x'.trans x⟩
    · have := off_lt n (by omega)
      rw [m', hwv]
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
      · have := off_lt j (by omega)
        have hs := off_sep (j := n) (l := j) (by omega) (by omega) (by omega)
        rw [(writeW_outside _ C _ (by omega)).word (by omega) (by omega)]
        exact v j hj
      · exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _
    · rw [m']
      exact o.trans ((writeW_outside _ C _ (by have := off_lt n (by omega); omega)).mono (by omega)
        (by have := off_lt n (by omega); omega))


/-! ## Back to words -/

/-- Limb `j`'s part of the word at bit `lo`. -/
def cj (lo j : Nat) (L : BitVec 64) : BitVec 64 :=
  if lo ≤ 52 * j then (if 52 * j = lo then L else L <<< (52 * j - lo)) else L >>> (lo - 52 * j)

/-- The code OR'ing limb `j` into the word at bit `lo`. -/
def orj (lo j : Nat) : List Instr :=
  ([.mov .rcx (.mem (VG.Impl.Rsa.X86_64.CrtIfma.at_ .r11 (VG.Impl.Rsa.X86_64.CrtIfma.off j)))] : List Instr) ++
  (if lo ≤ 52 * j then (if 52 * j = lo then [] else VG.Impl.Rsa.X86_64.CrtIfma.shl .rcx (52 * j - lo))
    else [.shift .shr .rcx (lo - 52 * j)]) ++
  ([.alu .or .rax (.reg .rcx)] : List Instr)

theorem orj_writes (lo j : Nat) : VG.Proof.MlKem.X86_64.writesOnly [.rax, .rcx, .rbp] (.block (orj lo j)) = true := by
  unfold orj
  split
  · split <;> rfl
  · rfl

/-- `rax |= cj lo j L`, for limb `j` of the word at bit `lo`. -/
theorem orj_ok {s : State} {C : Addr} {lo j : Nat} (h1 : 52 * j < lo + 64) (h2 : lo < 52 * j + 52)
    (hC : s.gpr .r11 = C) (hrd : InRegions (s.rd ++ s.wr) (C + BitVec.ofNat 64 (VG.Impl.Rsa.X86_64.CrtIfma.off j)) 8) :
    WP isa (.block (orj lo j)) s fun s' =>
      s'.gpr .rax = s.gpr .rax ||| cj lo j (word s.mem C (VG.Impl.Rsa.X86_64.CrtIfma.off j)) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rbp] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax, .rcx, .rbp] (Q := fun s' =>
    s'.gpr .rax = s.gpr .rax ||| cj lo j (word s.mem C (VG.Impl.Rsa.X86_64.CrtIfma.off j)) ∧ s'.mem = s.mem ∧
      s'.mxcsr = s.mxcsr) ?_ (orj_writes lo j)) fun s' ⟨⟨a, b, c⟩, k⟩ => ⟨a, k, b, c⟩
  unfold orj cj
  by_cases hl : lo ≤ 52 * j
  · by_cases he : 52 * j = lo
    · simp only [he, Nat.le_refl, ite_true, List.cons_append, List.nil_append]
      xrun [ea_at', hC, hrd]
      rfl
    · have hmc : (1 ≤ 64 - (52 * j - lo) ∧ 64 - (52 * j - lo) ≤ 63) = True := eq_true ⟨by omega, by omega⟩
      simp only [hl, he, ite_true, ite_false, VG.Impl.Rsa.X86_64.CrtIfma.shl, List.cons_append, List.nil_append]
      xrun [ea_at', hC, hrd, hmc]
      refine ⟨?_, rfl⟩
      rw [shl_eq' _ (by omega) (by omega)]
  · have hsc : (1 ≤ lo - 52 * j ∧ lo - 52 * j ≤ 63) = True := eq_true ⟨by omega, by omega⟩
    simp only [hl, ite_false, List.cons_append, List.nil_append]
    xrun [ea_at', hC, hrd, hsc]
    rfl


theorem testBit_hi {x k j : Nat} (hx : x < 2 ^ k) (hj : k ≤ j) : x.testBit j = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hj))

/-- Bit `i` of limb `j`'s part of the word at bit `lo`. -/
theorem cj_bit {lo j : Nat} {L : BitVec 64} (h1 : 52 * j < lo + 64) (h2 : lo < 52 * j + 52)
    {i : Nat} (hi : i < 64) :
    (cj lo j L).getLsbD i = (decide (52 * j ≤ lo + i) && L.toNat.testBit (lo + i - 52 * j)) := by
  unfold cj
  by_cases hl : lo ≤ 52 * j
  · by_cases he : 52 * j = lo
    · subst he
      simp [BitVec.testBit_toNat]
    · simp only [hl, he, ite_true, ite_false, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and,
        BitVec.testBit_toNat]
      by_cases hk : i < 52 * j - lo
      · simp [hk, show ¬ 52 * j ≤ lo + i by omega]
      · simp only [hk, decide_false, Bool.not_false, Bool.true_and, show 52 * j ≤ lo + i by omega, decide_true]
        congr 1; omega
  · simp only [hl, ite_false, BitVec.getLsbD_ushiftRight, show 52 * j ≤ lo + i by omega, decide_true,
      Bool.true_and, BitVec.testBit_toNat]
    congr 1; omega

/-- The bits of a number of limbs below `2⁵²`. -/
theorem testBit_lval {L : Nat → Nat} (hL : ∀ j, L j < 2 ^ 52) :
    ∀ n b, (lval L n).testBit b = (decide (b < 52 * n) && (L (b / 52)).testBit (b % 52))
  | 0, b => by rw [lval_zero]; simp
  | n + 1, b => by
    rw [lval_succ, Nat.add_comm, Nat.mul_comm, Nat.testBit_two_pow_mul_add _ (lval_lt (fun j _ => hL j)),
      testBit_lval hL n b]
    by_cases hb : b < 52 * n
    · simp [hb, show b < 52 * (n + 1) by omega]
    · simp only [hb, ite_false]
      by_cases hb' : b < 52 * (n + 1)
      · simp only [hb', decide_true, Bool.true_and]
        rw [show b / 52 = n by omega, show b - 52 * n = b % 52 by omega]
      · simp only [hb', decide_false, Bool.false_and]
        exact testBit_hi (hL n) (by omega)


/-- The limbs with bits in the word at bit `lo`. -/
def js (lo : Nat) : List Nat := (List.range 20).filter fun j => 52 * j < lo + 64 ∧ lo < 52 * j + 52

theorem getLsbD_foldl_or (f : Nat → BitVec 64) (i : Nat) :
    ∀ (l : List Nat) (a : BitVec 64), (l.foldl (fun a j => a ||| f j) a).getLsbD i =
      (a.getLsbD i || l.any fun j => (f j).getLsbD i)
  | [], a => by simp
  | j :: l, a => by
    rw [List.foldl_cons, getLsbD_foldl_or f i l, BitVec.getLsbD_or, List.any_cons, Bool.or_assoc]

/-- The word at bit `lo` of a number of twenty limbs below `2⁵²`. -/
theorem foldl_cj {Ls : Nat → BitVec 64} (hL : ∀ j, (Ls j).toNat < 2 ^ 52) (lo : Nat) :
    (js lo).foldl (fun a j => a ||| cj lo j (Ls j)) 0 =
      BitVec.ofNat 64 (lval (fun j => (Ls j).toNat) 20 / 2 ^ lo % 2 ^ 64) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_foldl_or, BitVec.getLsbD_ofNat, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    testBit_lval hL]
  have z : (0 : BitVec 64).getLsbD i = false := by simp
  rw [z, Bool.false_or]
  simp only [hi, decide_true, Bool.true_and]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, js, List.mem_filter, List.mem_range, decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · rintro ⟨j, ⟨hj, h1, h2⟩, hb⟩
    rw [cj_bit h1 h2 hi] at hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨hle, hb⟩ := hb
    have hlt : lo + i - 52 * j < 52 := by
      by_contra h
      rw [testBit_hi (hL j) (by omega)] at hb
      exact Bool.false_ne_true hb
    refine ⟨by omega, ?_⟩
    rw [show (i + lo) / 52 = j by omega, show (i + lo) % 52 = lo + i - 52 * j by omega]
    exact hb
  · rintro ⟨hlt, hb⟩
    refine ⟨(i + lo) / 52, ⟨by omega, by omega, by omega⟩, ?_⟩
    rw [cj_bit (by omega) (by omega) hi]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by omega, by rw [show lo + i - 52 * ((i + lo) / 52) = (i + lo) % 52 by omega]; exact hb⟩


/-- The limbs of `l` OR'ed into `rax`. -/
theorem orList_ok {C : Addr} {lo : Nat} :
    ∀ (l : List Nat) (s : State), (∀ j ∈ l, 52 * j < lo + 64 ∧ lo < 52 * j + 52 ∧ j < 20) → s.gpr .r11 = C →
      (∀ j < 20, InRegions (s.rd ++ s.wr) (C + BitVec.ofNat 64 (VG.Impl.Rsa.X86_64.CrtIfma.off j)) 8) →
      WP isa (.block (l.flatMap (orj lo))) s fun s' =>
        s'.gpr .rax = l.foldl (fun a j => a ||| cj lo j (word s.mem C (VG.Impl.Rsa.X86_64.CrtIfma.off j))) (s.gpr .rax) ∧
        VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rbp] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr
  | [], s, _, _, _ => WP.block_nil ⟨rfl, VG.Proof.MlKem.X86_64.Keep.refl _ _, rfl, rfl⟩
  | j :: l, s, hl, hC, hrd => by
    obtain ⟨h1, h2, hj⟩ := hl j (List.mem_cons_self ..)
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (orj_ok h1 h2 hC (hrd j hj)) fun t ⟨a, k, m, x⟩ => ?_
    refine WP.mono (orList_ok l t (fun j hj => hl j (List.mem_cons_of_mem _ hj)) ((k.gpr (by decide)).trans hC)
      (fun j hj => by rw [k.2.1, k.2.2]; exact hrd j hj)) fun t' ⟨a', k', m', x'⟩ =>
        ⟨?_, (k.trans k').mono (by simp), m'.trans m, x'.trans x⟩
    rw [a', a, m, List.foldl_cons]

theorem wv_digits {m : Mem} {D' : Addr} {V : Nat} :
    ∀ n, (∀ w < n, word m D' (8 * w) = BitVec.ofNat 64 (V / 2 ^ (64 * w) % 2 ^ 64)) → wv m D' 0 n = V % 2 ^ (64 * n)
  | 0, _ => by simp [VG.Proof.Bignum.X86_64.wv, Nat.mod_one]
  | n + 1, h => by
    rw [VG.Proof.Bignum.X86_64.wv, wv_digits n fun w hw => h w (by omega), Nat.zero_add, h n (by omega),
      BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide), Nat.mul_succ, Nat.pow_add, Nat.mod_mul]


theorem foldl_congr' {f g : BitVec 64 → Nat → BitVec 64} :
    ∀ (l : List Nat) {a : BitVec 64}, (∀ a j, j ∈ l → f a j = g a j) → l.foldl f a = l.foldl g a
  | [], _, _ => rfl
  | j :: l, a, h => by
    rw [List.foldl_cons, List.foldl_cons, h a j (List.mem_cons_self ..)]
    exact foldl_congr' l fun a j hj => h a j (List.mem_cons_of_mem _ hj)

/-- Word `w` of `to64`. -/
def w64 (w : Nat) : List Instr :=
  (Instr.mov32 .rax (.imm 0) :: (js (64 * w)).flatMap (orj (64 * w))) ++
    [.store (VG.Impl.Rsa.X86_64.CrtIfma.at_ .r8 (8 * w)) .rax]

theorem to64_eq : VG.Impl.Rsa.X86_64.CrtIfma.to64 = (List.range 17).flatMap w64 := rfl

/-- The limbs at `C` as numbers, zero above 20. -/
def limbsAt (m : Mem) (C : Addr) (j : Nat) : BitVec 64 :=
  if j < 20 then word m C (VG.Impl.Rsa.X86_64.CrtIfma.off j) else 0

/-- Word `w` of the twenty limbs below `2⁵²` at `r11 = C`, into `r8 + 8 w`. -/
theorem w64_ok {s : State} {C D' : Addr} {w : Nat} (hC : s.gpr .r11 = C) (h8 : s.gpr .r8 = D')
    (hrd : ∀ j < 20, InRegions (s.rd ++ s.wr) (C + BitVec.ofNat 64 (VG.Impl.Rsa.X86_64.CrtIfma.off j)) 8)
    (hwr : InRegions s.wr (D' + BitVec.ofNat 64 (8 * w)) 8)
    (hL : ∀ j < 20, (word s.mem C (VG.Impl.Rsa.X86_64.CrtIfma.off j)).toNat < 2 ^ 52) :
    WP isa (.block (w64 w)) s fun s' =>
      s'.mem = s.mem.writeW (off D' (8 * w))
        (BitVec.ofNat 64 (lval (fun j => (limbsAt s.mem C j).toNat) 20 / 2 ^ (64 * w) % 2 ^ 64)) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rbp] s s' ∧ s'.mxcsr = s.mxcsr := by
  rw [w64, List.cons_append, WP.block_cons_iff]
  refine ⟨s.setReg32 .rax 0, rfl, ?_⟩
  have g₀ : ∀ r, r ≠ .rax → (s.setReg32 .rax 0).gpr r = s.gpr r := fun r hr => by
    rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ hr]
  rw [WP.block_append_iff]
  refine WP.mono (orList_ok (C := C) (lo := 64 * w) (js (64 * w)) _ (fun j hj => by
      simp only [js, List.mem_filter, List.mem_range, decide_eq_true_eq] at hj; exact ⟨hj.2.1, hj.2.2, hj.1⟩)
    ((g₀ _ (by decide)).trans hC) hrd) fun t ⟨a, k, m, x⟩ => ?_
  have hlm : (js (64 * w)).foldl (fun a j => a ||| cj (64 * w) j
      (word (s.setReg32 .rax 0).mem C (VG.Impl.Rsa.X86_64.CrtIfma.off j))) ((s.setReg32 .rax 0).gpr .rax) =
      BitVec.ofNat 64 (lval (fun j => (limbsAt s.mem C j).toNat) 20 / 2 ^ (64 * w) % 2 ^ 64) := by
    rw [← foldl_cj (Ls := limbsAt s.mem C) (fun j => by
      unfold limbsAt; split
      · exact hL j (by assumption)
      · simp) (64 * w)]
    have e0 : (s.setReg32 .rax 0).gpr .rax = 0 := by rw [State.setReg32, RegUpd.gpr_setReg_self]; rfl
    rw [e0]
    refine foldl_congr' _ fun a j hj => ?_
    simp only [js, List.mem_filter, List.mem_range] at hj
    simp only [limbsAt, hj.1, ite_true]; rfl
  have hst : InRegions t.wr (D' + BitVec.ofNat 64 (8 * w)) 8 := by rw [k.2.2]; exact hwr
  have h8t : t.gpr .r8 = D' := by rw [k.gpr (by decide), g₀ _ (by decide)]; exact h8
  rw [WP.block_cons_iff]
  refine ⟨{ t with mem := t.mem.writeW (D' + BitVec.ofNat 64 (8 * w)) (t.gpr .rax) }, by
    simp only [exec, ea_at', h8t, State.store64, hst, ite_true], WP.block_nil ⟨?_, ?_, x⟩⟩
  · show t.mem.writeW _ (t.gpr .rax) = _
    rw [a, hlm, m]; rfl
  · exact ⟨fun r hr => by
      show t.gpr r = s.gpr r
      rw [k.gpr hr, g₀ _ (fun h => hr (by simp [h]))], k.2.1, k.2.2⟩

end VG.Proof.Bignum.X86_64.AmmSym
