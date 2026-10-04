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

end VG.Proof.Bignum.X86_64.AmmSym
