module

public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtSave
public import VerifiedGarbage.Proof.Bignum.RISCV64.PubMont
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCore
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Bignum.RISCV64.MontCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The RSA private-key operation on RISC-V: the checks

Masks are all ones or 0 (`if … then BitVec.allOnes 64 else 0`).

* `checkN_ok`: `s9 :=` the mask of whether `n` (from the header) is a valid
  modulus (`Precompute.check`).
* `cmpLt_ok`, `checkLt_ok`: the mask of whether array `a` is below array `m`
  (`subMod64` into array 3), into `s4`, or and-ed into `s9`.
* `checkPQ_ok`: `p q` (arrays 4, 5) into array 6 by a Montgomery
  multiplication modulo `M = 2^(64 w) - 1` (array 0, `-M⁻¹ = 1`), exact
  since `R ≡ 1` and `p q < M`; `s9 &=` the mask of `p q = n` (array 1).
* `maskWords_ok`: `w` words `&= s9`. `orThree_ok`: an array kept under the
  mask, else 3.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Crt

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot Arrays)

/-! ## `n` valid -/

/-- Whether a word is zero, as a bit. -/
theorem isZero_bits (v : BitVec 64) :
    (((v >>> 1) ||| (v &&& 1#64)) - 1#64) >>> 63 = BitVec.ofNat 64 (if v = 0 then 1 else 0) := by
  by_cases h : v.toNat ≤ 1
  · rcases (show v = 0 ∨ v = 1 by
      rcases (show v.toNat = 0 ∨ v.toNat = 1 by omega_arith) with h | h
      · exact Or.inl (BitVec.eq_of_toNat_eq h)
      · exact Or.inr (BitVec.eq_of_toNat_eq h)) with rfl | rfl <;> decide
  · have hu1 : 1 ≤ ((v >>> 1) ||| (v &&& 1#64)).toNat := by
      have := Nat.left_le_or (n := (v >>> 1).toNat) (m := (v &&& 1#64).toNat)
      rw [BitVec.toNat_or]
      have : (v >>> 1).toNat = v.toNat / 2 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      omega_arith
    have hu2 : ((v >>> 1) ||| (v &&& 1#64)).toNat < 2 ^ 63 := by
      rw [BitVec.toNat_or]
      apply Nat.or_lt_two_pow
      · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := v.isLt; omega_arith
      · rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    have hv : v ≠ 0 := fun e => by subst e; simp at h
    simp only [hv, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    omega_arith

theorem zero_sub_bit (b : Bool) :
    BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0) = if b then BitVec.allOnes 64 else 0 := by
  cases b <;> decide

/-- `checkN`: `s9 :=` all ones if the `k` bytes of `n` (at `N`, from the
header) are a valid modulus, else 0. -/
theorem checkN_ok {s : State} {S N : Addr} {Z k : Nat} {nb : List Byte} (hs : Scr s S Z) (hZ : 256 ≤ Z)
    (h6 : s.gpr .s6 = Mont.off S 0) (hN : Mont.word s.mem S oN = Mont.off N 0)
    (hNL : Mont.word s.mem S oNLen = BitVec.ofNat 64 k)
    (hk : 64 ≤ k) (hk' : k ≤ 1024) (hlen : nb.length = k)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (Mont.off N i) 1)
    (hb : ∀ i (h : i < k), s.mem (Mont.off N i) = nb[i]'(by omega_arith)) :
    WP isa checkN s fun t =>
      (t.gpr .s9 = (if Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k then BitVec.allOnes 64 else 0) ∧
        t.mem = s.mem) ∧
      Keep [.s0, .s7, .s8, .s9, .t2, .t3, .t4, .t5] s t := by
  have hnw := hs.nowrap
  unfold checkN
  refine WP.seq (WP.mono (WP.keep [.s7, .s8] (Q := fun t => t.gpr .s7 = Mont.off N 0 ∧
    t.gpr .s8 = BitVec.ofNat 64 k ∧ t.mem = s.mem) ?_ (by rfl) (by rfl)) fun s₁ ⟨⟨a7, a8, m1⟩, k1⟩ => ?_)
  · brun [h6, Nat.zero_add, oN, oNLen, hs.ld (show 8 + 8 ≤ Z by omega_arith),
      hs.al8 (show 8 + 8 ≤ Z by omega_arith) (by decide), hs.ld (show 16 + 8 ≤ Z by omega_arith),
      hs.al8 (show 16 + 8 ≤ Z by omega_arith) (by decide),
      show Mont.word s.mem S 8 = Mont.off N 0 from hN, show Mont.word s.mem S 16 = BitVec.ofNat 64 k from hNL]
  refine WP.seq (WP.mono (check_ok (nb := nb) a7 a8 hk hk' hlen (by rw [k1.2.1, k1.2.2]; exact hrd)
    fun i hi => by rw [m1]; exact hb i hi) fun s₂ ⟨hv, m2, k2⟩ => ?_)
  refine WP.mono (WP.keep [.t2, .t3, .s9] (Q := fun t => t.gpr .s9 = BitVec.ofNat 64 0 -
    ((((s₂.gpr .s0 >>> 1) ||| (s₂.gpr .s0 &&& 1#64)) - 1#64) >>> 63) ∧ t.mem = s₂.mem) ?_ (by rfl) (by rfl))
    fun t ⟨⟨t9, tm⟩, k3⟩ => ⟨⟨?_, tm.trans (m2.trans m1)⟩, ((k1.trans k2).trans k3).mono (by decide)⟩
  · brun [exec_li]
  · rw [t9, isZero_bits, ← zero_sub_bit]
    by_cases h0 : s₂.gpr .s0 = 0
    · simp only [h0, hv.mp h0, ↓reduceIte]
    · have h1 : ¬ Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true := fun h => h0 (hv.mpr h)
      simp only [h0, h1, Bool.false_eq_true, ↓reduceIte]

/-! ## One array below another -/

/-- The registers `cmpLt` writes. -/
def cmpRegs : List Reg := [.a5, .a6, .a7, .a0, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4]

/-- `cmpLt a m`, with array `a`'s word `w` zero: `s4 :=` all ones if array
`a` is below array `m`, else 0, through array 3; `a7` back to array 0. -/
theorem cmpLt_ok {s : State} {B : Addr} {Z w a m : Nat} (hs : Scr s B Z) (ha : a < 8) (hm : m < 8)
    (ha3 : a ≠ 3) (hm3 : m ≠ 3) (hw1 : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (h7 : s.gpr .a7 = Mont.off B (slot w 0)) (hra : s.gpr .ra = Mont.off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (h0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (htop : Mont.word s.mem B (slot w a + 8 * w) = 0) :
    WP isa (cmpLt a m) s fun t =>
      (t.gpr .s4 = (if wordsVal s.mem B (slot w a) w < wordsVal s.mem B (slot w m) w
          then BitVec.allOnes 64 else 0) ∧
        Mont.Outside B (slot w 3) (8 * w) s.mem t.mem ∧ t.gpr .a7 = Mont.off B (slot w 0)) ∧
      Keep cmpRegs s t := by
  have hnw := hs.nowrap
  have sa := Nat.le_trans (VG.Proof.Bignum.slot_le (w := w) ha) hZ
  have sm := Nat.le_trans (VG.Proof.Bignum.slot_le (w := w) hm) hZ
  have s3 := Nat.le_trans (VG.Proof.Bignum.slot_le (w := w) (j := 3) (by decide)) hZ
  have d3a := VG.Proof.Bignum.slot_sep (w := w) (Ne.symm ha3)
  have d3m := VG.Proof.Bignum.slot_sep (w := w) (Ne.symm hm3)
  unfold cmpLt
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) h7 h5 a) fun s₁ ⟨⟨a5, m1⟩, k1⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) ((k1.gpr (by decide)).trans h7)
    ((k1.gpr (by decide)).trans h5) 3) fun s₂ ⟨⟨a6, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.mono (Pub.base_ok (rd := .a7) (by decide) ((k12.gpr (by decide)).trans h7)
    ((k12.gpr (by decide)).trans h5) m) fun s₃ ⟨⟨a7, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  refine WP.seq (WP.mono (subMod64_ok (w := w) (dA := slot w a) (dT := slot w 3) (dM := slot w m)
    (hs.congr k13.2.2) ((k3.gpr (by decide)).trans ((k2.gpr (by decide)).trans a5))
    ((k3.gpr (by decide)).trans a6) a7 ((k13.gpr (by decide)).trans h0) hw1 hw' (slot_al w a) (slot_al w 3)
    (slot_al w m) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₄ ⟨⟨c, hc, hD, h4⟩, out, k4⟩ => ?_)
  have k14 := k13.trans k4
  refine WP.mono (WP.keep [.a7] (Q := fun t => t.gpr .a7 = Mont.off B (slot w 0) ∧ t.mem = s₄.mem)
    (by brun [(k14.gpr (r := .ra) (by decide)).trans hra, BitVec.add_zero]) (by rfl) (by rfl))
    fun t ⟨⟨t7, tm⟩, k5⟩ =>
    ⟨⟨?_, by rw [m3, m2, m1] at out; rw [tm]; exact out, t7⟩, (k14.trans k5).mono (by decide)⟩
  rw [k5.gpr (r := .s4) (by decide), h4, m3, m2, m1, htop]
  rw [m3, m2, m1] at hD
  have hDl := wordsVal_lt s₄.mem B (slot w 3) w
  have hAl := wordsVal_lt s.mem B (slot w a) w
  have hMl := wordsVal_lt s.mem B (slot w m) w
  rcases (show c = 0 ∨ c = 1 by omega_arith) with rfl | rfl
  · have h : ¬ wordsVal s.mem B (slot w a) w < wordsVal s.mem B (slot w m) w := by omega_arith
    simp [h]
  · have h : wordsVal s.mem B (slot w a) w < wordsVal s.mem B (slot w m) w := by omega_arith
    simp [h]

/-- `checkLt a m`: `s9 &=` `cmpLt a m`'s mask. -/
theorem checkLt_ok {s : State} {B : Addr} {Z w a m : Nat} (hs : Scr s B Z) (ha : a < 8) (hm : m < 8)
    (ha3 : a ≠ 3) (hm3 : m ≠ 3) (hw1 : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (h7 : s.gpr .a7 = Mont.off B (slot w 0)) (hra : s.gpr .ra = Mont.off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (h0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (htop : Mont.word s.mem B (slot w a + 8 * w) = 0) :
    WP isa (checkLt a m) s fun t =>
      (t.gpr .s9 = s.gpr .s9 &&& (if wordsVal s.mem B (slot w a) w < wordsVal s.mem B (slot w m) w
          then BitVec.allOnes 64 else 0) ∧
        Mont.Outside B (slot w 3) (8 * w) s.mem t.mem ∧ t.gpr .a7 = Mont.off B (slot w 0)) ∧
      Keep (.s9 :: cmpRegs) s t := by
  unfold checkLt
  refine WP.seq (WP.mono (cmpLt_ok hs ha hm ha3 hm3 hw1 hw' hZ h7 hra h5 h0 htop)
    fun s₁ ⟨⟨a4, o1, a7⟩, k1⟩ => ?_)
  refine WP.mono (WP.keep [.s9] (Q := fun t => t.gpr .s9 = s₁.gpr .s9 &&& s₁.gpr .s4 ∧ t.mem = s₁.mem)
    (by brun) (by rfl) (by rfl)) fun t ⟨⟨t9, tm⟩, k2⟩ =>
    ⟨⟨by rw [t9, a4, k1.gpr (r := .s9) (by decide)], by rw [tm]; exact o1,
      by rw [k2.gpr (r := .a7) (by decide)]; exact a7⟩, (k1.trans k2).mono (by decide)⟩

/-! ## `p q = n` -/

theorem mont_exact {o x R N : Nat} (hN : N + 1 = R) (ho : o < N) (hx : x < N) (h : o * R % N = x % N) :
    o = x := by
  have hR : R % N = 1 % N := by rw [← hN, Nat.add_mod_left]
  rw [Nat.mul_mod, hR, ← Nat.mul_mod, Nat.mul_one, Nat.mod_eq_of_lt ho, Nat.mod_eq_of_lt hx] at h
  exact h

/-- Neither below the other: equal. -/
theorem eq_masks (x y : Nat) :
    ((if x < y then BitVec.allOnes 64 else 0) ||| (if y < x then BitVec.allOnes 64 else 0)) ^^^
        BitVec.allOnes 64 = if x = y then BitVec.allOnes 64 else 0 := by
  rcases Nat.lt_trichotomy x y with h | h | h
  · simp only [h, ↓reduceIte, Nat.lt_asymm h, Nat.ne_of_lt h]; decide
  · subst h; simp only [Nat.lt_irrefl, ↓reduceIte]; decide
  · simp only [h, ↓reduceIte, Nat.lt_asymm h, Nat.ne_of_gt h]; decide

/-- The registers `checkPQ` writes. -/
def pqRegs : List Reg := [.t1, .t2, .s7, .s9] ++ Pub.montRegs ++ cmpRegs

/-- `checkPQ`, with `M = 2^(64 w) - 1` in array 0, `n` in array 1 (its word
`w` zero), `p` in array 4 and `q` in array 5, `q < M` and `p q < M`:
`s9 &=` all ones if `p q = n`, else 0, changing only arrays 2, 3 and 6. -/
theorem checkPQ_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (h7 : s.gpr .a7 = Mont.off B (slot w 0)) (hra : s.gpr .ra = Mont.off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (h0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hM : wordsVal s.mem B (slot w 0) w = 2 ^ (64 * w) - 1)
    (hM0 : Mont.word s.mem B (slot w 0) = BitVec.allOnes 64)
    (hq : wordsVal s.mem B (slot w 5) w < 2 ^ (64 * w) - 1)
    (hpq : wordsVal s.mem B (slot w 4) w * wordsVal s.mem B (slot w 5) w < 2 ^ (64 * w) - 1)
    (h1top : Mont.word s.mem B (slot w 1 + 8 * w) = 0) :
    WP isa checkPQ s fun t =>
      (t.gpr .s9 = s.gpr .s9 &&& (if wordsVal s.mem B (slot w 4) w * wordsVal s.mem B (slot w 5) w =
            wordsVal s.mem B (slot w 1) w then BitVec.allOnes 64 else 0) ∧
        Arrays B w [2, 3, 6] s.mem t.mem ∧ t.gpr .a7 = Mont.off B (slot w 0)) ∧ Keep pqRegs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e6 := e 6; have e7 := e 7
  have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hR1 : 1 ≤ 2 ^ (64 * w) := Nat.one_le_two_pow
  have hn8 : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_arith
  unfold checkPQ
  -- `t1 := 1`.
  refine WP.seq (WP.mono (WP.keep [.t1] (Q := fun t => t.gpr .t1 = BitVec.ofNat 64 1 ∧ t.mem = s.mem)
    (by brun [exec_li]) (by rfl) (by rfl)) fun s₁ ⟨⟨a1, m1⟩, k1⟩ => ?_)
  -- `p q` into array 6, exactly.
  refine WP.seq (WP.mono (Pub.montOp_ok (o := 6) (a := 4) (b := 5) (hs.congr k1.2.2) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' hZ ((k1.gpr (by decide)).trans h7)
    ((k1.gpr (by decide)).trans h5) ((k1.gpr (by decide)).trans h0)
    (by rw [m1, a1, show VG.Proof.Bignum.word s.mem B (slot w 0) = BitVec.allOnes 64 from hM0]; decide)
    (by rw [m1, hM]; exact hq)) fun s₂ ⟨⟨h6l, e6v, o2⟩, k2⟩ => ?_)
  rw [m1, hM] at h6l e6v
  have k12 := k1.trans k2
  have hP : wordsVal s₂.mem B (slot w 6) w = wordsVal s.mem B (slot w 4) w * wordsVal s.mem B (slot w 5) w :=
    mont_exact (by omega_arith) h6l hpq e6v
  rw [m1] at o2
  have v21 : wordsVal s₂.mem B (slot w 1) w = wordsVal s.mem B (slot w 1) w := by
    rw [Pre.wordsVal_eq_wv, Pre.wordsVal_eq_wv]; exact o2.wv_of_not_mem (by decide) (by decide) hn8
  have w21 : Mont.word s₂.mem B (slot w 1 + 8 * w) = Mont.word s.mem B (slot w 1 + 8 * w) :=
    o2.word_eq (fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl <;> omega_arith) (by omega_arith)
  -- Array 6's word `w` := 0.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) ((k12.gpr (by decide)).trans h7)
    ((k12.gpr (by decide)).trans h5) 6) fun s₃ ⟨⟨a3, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  have e16 : Mont.off B (slot w 6 + 8 * (w + 2)) - BitVec.ofNat 64 16 = Mont.off B (slot w 6 + 8 * w) := by
    rw [off_sub B (show 16 ≤ slot w 6 + 8 * (w + 2) by omega_arith),
      show slot w 6 + 8 * (w + 2) - 16 = slot w 6 + 8 * w by omega_arith]
  refine WP.mono (WP.keep [.t3, .s0] (Q := fun t =>
    t.mem = s₃.mem.writeW (Mont.off B (slot w 6 + 8 * w)) (0 : BitVec 64)) ?_ (by rfl) (by rfl))
    fun s₄ ⟨m4, k4⟩ => ?_
  · brun [a3, (k13.gpr (r := .s5) (by decide)).trans h5, off_add, e16, exec_li, add_ofNat_zero,
      (hs.congr k13.2.2).st (show slot w 6 + 8 * w + 8 ≤ Z by omega_arith),
      (hs.congr k13.2.2).al8 (show slot w 6 + 8 * w + 8 ≤ Z by omega_arith) (by omega_arith)]
    rfl
  have k14 := k13.trans k4
  rw [m3] at m4
  have ow := Mont.writeW_outside s₂.mem B (d := slot w 6 + 8 * w) (0 : BitVec 64) (by omega_arith)
  have v46 : wordsVal s₄.mem B (slot w 6) w = wordsVal s.mem B (slot w 4) w * wordsVal s.mem B (slot w 5) w := by
    rw [m4, Mont.Outside.wordsVal ow (by omega_arith) (by omega_arith), hP]
  have v41 : wordsVal s₄.mem B (slot w 1) w = wordsVal s.mem B (slot w 1) w := by
    rw [m4, Mont.Outside.wordsVal ow (by omega_arith) (by omega_arith), v21]
  have t46 : Mont.word s₄.mem B (slot w 6 + 8 * w) = 0 := by rw [m4]; exact Mont.word_writeW_self _ _ _ _
  have t41 : Mont.word s₄.mem B (slot w 1 + 8 * w) = 0 := by
    rw [m4, ow.word (by omega_arith) (by omega_arith), w21]; exact h1top
  -- `p q < n`?
  refine WP.seq (WP.mono (cmpLt_ok (a := 6) (m := 1) (hs.congr k14.2.2) (by decide) (by decide) (by decide)
    (by decide) (by omega_arith) hw' hZ ((k14.gpr (by decide)).trans h7) ((k14.gpr (by decide)).trans hra)
    ((k14.gpr (by decide)).trans h5) ((k14.gpr (by decide)).trans h0) t46)
    fun s₅ ⟨⟨a4, o5, a7⟩, k5⟩ => ?_)
  rw [v46, v41] at a4
  refine WP.seq (WP.mono (WP.keep [.s7] (Q := fun t => t.gpr .s7 = s₅.gpr .s4 ∧ t.mem = s₅.mem)
    (by brun [BitVec.add_zero]) (by rfl) (by rfl)) fun s₆ ⟨⟨a7', m6⟩, k6⟩ => ?_)
  have k16 := (k14.trans k5).trans k6
  -- `n < p q`?
  refine WP.seq (WP.mono (cmpLt_ok (a := 1) (m := 6) (hs.congr k16.2.2) (by decide) (by decide) (by decide)
    (by decide) (by omega_arith) hw' hZ (by rw [k6.gpr (r := .a7) (by decide)]; exact a7)
    ((k16.gpr (by decide)).trans hra) ((k16.gpr (by decide)).trans h5) ((k16.gpr (by decide)).trans h0)
    (by rw [m6, o5.word (by omega_arith) (by omega_arith)]; exact t41))
    fun s₇ ⟨⟨b4, o7, b7⟩, k7⟩ => ?_)
  rw [m6, Mont.Outside.wordsVal o5 (by omega_arith) (by omega_arith),
    Mont.Outside.wordsVal o5 (by omega_arith) (by omega_arith), v46, v41] at b4
  refine WP.mono (WP.keep [.t2, .s9] (Q := fun t => t.gpr .s9 = s₇.gpr .s9 &&&
    ((s₇.gpr .s7 ||| s₇.gpr .s4) ^^^ BitVec.allOnes 64) ∧ t.mem = s₇.mem)
    (by brun; rw [BitVec.neg_one_eq_allOnes]) (by rfl) (by rfl))
    fun t ⟨⟨t9, tm⟩, k8⟩ => ⟨⟨?_, ?_, by rw [k8.gpr (r := .a7) (by decide)]; exact b7⟩, ?_⟩
  · rw [t9, b4, k7.gpr (r := .s7) (by decide), a7', a4, eq_masks, k7.gpr (r := .s9) (by decide),
      k6.gpr (r := .s9) (by decide), k5.gpr (r := .s9) (by decide), k14.gpr (r := .s9) (by decide)]
  · intro x hx
    rw [tm]
    have hx3 : ofs B x < slot w 3 ∨ slot w 3 + 8 * w ≤ ofs B x := by
      have := hx 3 (by simp); omega_arith
    have hx6 : ofs B x < slot w 6 + 8 * w ∨ slot w 6 + 8 * w + 8 ≤ ofs B x := by
      have := hx 6 (by simp); omega_arith
    rw [o7 x hx3, m6, o5 x hx3, m4, ow x hx6]
    exact o2 x hx
  · exact (k16.trans (k7.trans k8)).mono (by decide)

/-! ## Masking the key -/

/-- `maskWords`, at `d` of `B` (`t3`) with `w` in `t0`: the `w` words
`&= s9`. -/
theorem maskWords_ok {s : State} {B : Addr} {Z d w : Nat} (hs : Scr s B Z)
    (h3 : s.gpr .t3 = Mont.off B d) (h0 : s.gpr .t0 = BitVec.ofNat 64 w) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hd8 : d % 8 = 0) (hZ : d + 8 * w ≤ Z) :
    WP isa maskWords s fun t =>
      ((∀ i < w, Mont.word t.mem B (d + 8 * i) = Mont.word s.mem B (d + 8 * i) &&& s.gpr .s9) ∧
        Mont.Outside B d (8 * w) s.mem t.mem) ∧ Keep [.s0, .t3, .t5] s t := by
  have hnw := hs.nowrap
  unfold maskWords
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .t5 .t0 0]) s fun s₁ =>
      (s₁.gpr .t5 = BitVec.ofNat 64 w ∧ s₁.gpr .t3 = Mont.off B d ∧ s₁.mem = s.mem) ∧ Keep [.t5] s s₁ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h0, h3, BitVec.add_zero]
  refine WP.mono hpre fun s₁ ⟨⟨i5, i3, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = Mont.off B (d + 8 * i) ∧ Mont.Outside B d (8 * i) s.mem t.mem ∧
      (∀ k < i, Mont.word t.mem B (d + 8 * k) = Mont.word s.mem B (d + 8 * k) &&& s.gpr .s9) ∧
      Keep [.s0, .t3, .t5] s t
  refine WP.mono (wp_countdown (body := .block ([.load .d .s0 .t3 0, .logic .and .s0 .s0 .s9,
      .store .d .s0 .t3 0, .addi .t3 .t3 8] ++ ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5) (N := w)
    (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j3, jout, jz, jk⟩ hc => ?_)
    ⟨by rw [i3]; rfl, by rw [← im]; exact Mont.Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith),
      k₁.mono (by decide)⟩ i5) fun t ⟨_, tout, tz, tk⟩ => ⟨⟨tz, tout⟩, tk⟩
  have h9 : t.gpr .s9 = s.gpr .s9 := jk.gpr (by decide)
  have hwd : Mont.word t.mem B (d + 8 * i) = Mont.word s.mem B (d + 8 * i) :=
    jout.word (Or.inr (Nat.le_refl _)) (by omega_arith)
  refine WP.mono (WP.keep [.s0, .t3, .t5] (Q := fun t' =>
    t'.mem = t.mem.writeW (Mont.off B (d + 8 * i)) (Mont.word t.mem B (d + 8 * i) &&& s.gpr .s9) ∧
      t'.gpr .t3 = Mont.off B (d + 8 * (i + 1)) ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1) ?_ (by rfl) (by rfl))
    fun t' ⟨⟨a, b, c⟩, k⟩ => ⟨⟨b, ?_, ?_, Keep.trans' jk k⟩, c⟩
  · brun [add_ofNat_zero, j3, h9, (hs.congr jk.2.2).ld (show d + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.2.2).st (show d + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.2.2).al8 (show d + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
    rw [show d + 8 * i + 8 = d + 8 * (i + 1) by omega_arith]
  · have hw := Mont.writeW_outside t.mem B (d := d + 8 * i) (Mont.word t.mem B (d + 8 * i) &&& s.gpr .s9)
      (by omega_arith)
    rw [a]; exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans (hw.mono (by omega_arith) (by omega_arith))
  · intro k hk
    have hw := Mont.writeW_outside t.mem B (d := d + 8 * i) (Mont.word t.mem B (d + 8 * i) &&& s.gpr .s9)
      (by omega_arith)
    rw [a]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [hw.word (by omega_arith) (by omega_arith)]; exact jz k hk
    · rw [Mont.word_writeW_self, hwd]

theorem and_mask (x : BitVec 64) (b : Bool) :
    x &&& (if b then BitVec.allOnes 64 else 0) = if b then x else 0 := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact BitVec.and_zero
  · simp only [↓reduceIte]; exact BitVec.and_allOnes

theorem three_mask (x : BitVec 64) (b : Bool) :
    x ||| ((if b = true then BitVec.allOnes 64 else 0) ^^^ -1#64) &&& 3#64 = x ||| (if b = true then 0 else 3) := by
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> congr 1

/-- `orThree j`, the mask of `b` in `s9`: array `j` (`w` words) kept if `b`,
else 3. -/
theorem orThree_ok {s : State} {B : Addr} {Z w j : Nat} {b : Bool} (hs : Scr s B Z) (hj : j < 8)
    (h7 : s.gpr .a7 = Mont.off B (slot w 0)) (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)))
    (h0 : s.gpr .t0 = BitVec.ofNat 64 w) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z)
    (h9 : s.gpr .s9 = if b then BitVec.allOnes 64 else 0) :
    WP isa (orThree j) s fun t =>
      (wordsVal t.mem B (slot w j) w = (if b then wordsVal s.mem B (slot w j) w else 3) ∧
        Mont.Outside B (slot w j) (8 * w) s.mem t.mem) ∧ Keep [.s0, .t2, .t3, .t5] s t := by
  have hnw := hs.nowrap
  have sj : slot w j + 8 * (w + 2) ≤ Z := Nat.le_trans (VG.Proof.Bignum.slot_le hj) hZ
  have alj := slot_al w j
  unfold orThree
  refine WP.seq (WP.mono (Pub.base_ok (rd := .t3) (by decide) h7 h5 j) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (maskWords_ok (hs.congr k1.2.2) a3 ((k1.gpr (by decide)).trans h0) hw hw' alj
    (by omega_arith)) fun s₂ ⟨⟨hm, out₂⟩, k₂⟩ => ?_)
  have k12 := k1.trans k₂
  rw [m1, k1.gpr (r := .s9) (by decide), h9] at hm
  rw [m1] at out₂
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) ((k12.gpr (by decide)).trans h7)
    ((k12.gpr (by decide)).trans h5) j) fun s₃ ⟨⟨b3, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  refine WP.mono (WP.keep [.s0, .t2] (Q := fun t => t.mem = s₃.mem.writeW (Mont.off B (slot w j))
    (Mont.word s₃.mem B (slot w j) ||| (if b then 0 else 3))) ?_ (by rfl) (by rfl)) fun t ⟨tm, k4⟩ =>
    ⟨⟨?_, ?_⟩, (k13.trans k4).mono (by decide)⟩
  · brun [b3, add_ofNat_zero, (k13.gpr (r := .s9) (by decide)).trans h9,
      (hs.congr k13.2.2).ld (show slot w j + 8 ≤ Z by omega_arith),
      (hs.congr k13.2.2).st (show slot w j + 8 ≤ Z by omega_arith),
      (hs.congr k13.2.2).al8 (show slot w j + 8 ≤ Z by omega_arith) alj]
    rw [three_mask]
  · rw [m3] at tm
    have ow := Mont.writeW_outside s₂.mem B (d := slot w j) (Mont.word s₂.mem B (slot w j) ||| (if b then 0 else 3))
      (by omega_arith)
    have hm0 := hm 0 (by omega_arith)
    rw [Nat.mul_zero, Nat.add_zero] at hm0
    rw [Pre.wordsVal_eq_wv, Pre.wordsVal_eq_wv]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [VG.Proof.Bignum.wv_single (i := 0) _ _ _ w (by omega_arith) fun q hq hne => ?_]
      · rw [tm, Nat.mul_zero, Nat.add_zero]
        show (Mont.word (s₂.mem.writeW _ _) B (slot w j)).toNat * _ = 3
        rw [Mont.word_writeW_self, hm0, and_mask]
        simp
      · show Mont.word t.mem B _ = 0
        rw [tm, ow.word (by omega_arith) (by omega_arith), hm q hq, and_mask]; rfl
    · simp only [↓reduceIte]
      refine VG.Proof.Bignum.wv_congr fun q hq => ?_
      show Mont.word t.mem B _ = Mont.word s.mem B _
      rcases Nat.eq_zero_or_pos q with rfl | hq0
      · rw [tm, Nat.mul_zero, Nat.add_zero, Mont.word_writeW_self, hm0, and_mask]
        simp
      · rw [tm, ow.word (by omega_arith) (by omega_arith), hm q hq, and_mask]; rfl
  · rw [m3] at tm
    rw [tm]
    exact out₂.trans ((Mont.writeW_outside s₂.mem B (d := slot w j) _ (by omega_arith)).mono (Nat.le_refl _)
      (by omega_arith))

end VG.Proof.Bignum.RISCV64.Crt
