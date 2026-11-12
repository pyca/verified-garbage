module

public import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.ModArith
import VerifiedGarbage.Proof.Bignum.WordStep
import VerifiedGarbage.Proof.Bignum.WordStepNorm
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The precomputed values of an RSA modulus on RISC-V: the quotients' estimates

The pieces of a step of `Precompute.step` that estimate its quotient, for
`R² mod n` (`PreR2Lazy.lean`) and the key operations' division
(`Proof/Rsa/RISCV64/KeyWordDiv.lean`), for any odd `n` of `w ≥ 4` words whose
top word is not zero:

* `normTail_ok`: `P = 2^z`, `d' = ⌊n P / 2^(64 (w - 1))⌋ ≥ 2^63` and the
  word below it, `(d', d'ₗ) = ⌊n P / 2^(64 (w - 2))⌋`, in the temporary;
* `recip_ok`: `v = ⌊(2^128 - 1) / d'⌋ - 2^64` there, by restoring division
  (`WordStep.divBit_inv`, `WordStep.recip_eq`);
* `quot_ok`: the estimate `min(⌊u / d'⌋, 2^64 - 1)` from the top two words
  `u` of `x P`, for `x = ⌊V / 2^64⌋` (`WordStep.qhat_norm`), by Möller and
  Granlund's division (`WordStep.mg_quot`);
* `quot3_ok`: corrected by the top three words `U` of `x P` and `D = (d',
  d'ₗ)` to `q̂ = min(⌊U / D⌋, 2^64 - 1)` (`q3_val`, `WordStep.quot3_val`),
  so that `q ≤ q̂ ≤ q + 1` for `q = ⌊V / n⌋` (`WordStep.qhat3_div`);
* `mul_arith`: a word of `q̂ n`.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
open VG.Impl.Bignum.RISCV64.Precompute
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.WordStep (shl_add_lt top_shift top3_shift)

/-- `8 w + d - c`: a word near the top of `w` words at `d`. -/
theorem ea_top (B : Addr) {d w c : Nat} (hc : c ≤ 8 * w) (hn : B.toNat + d + 8 * w < 2 ^ 64) :
    BitVec.ofNat 64 w <<< 3 + off B d - BitVec.ofNat 64 c = off B (d + 8 * w - c) := by
  have hB := B.isLt
  have h1 : (BitVec.ofNat 64 w <<< 3).toNat = 8 * w := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_using [hn, hB]), Nat.mod_eq_of_lt (by omega_using [hn, hB])]; omega_using []
  have h2 : (off B d).toNat = B.toNat + d := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := d) (by omega_using [hn, hB]), Nat.mod_eq_of_lt (by omega_using [hn])]
  have h3 : (off B (d + 8 * w - c)).toNat = B.toNat + (d + 8 * w - c) := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := d + 8 * w - c) (by omega_using [hn, hB]), Nat.mod_eq_of_lt (by omega_using [hn])]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_add, h1, h2, h3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega_using [hc, hn])]
  omega_using [hc, hn]

/-- `8 w + d`: the word after `w` words at `d`. -/
theorem ea_end (B : Addr) {d w : Nat} (hn : B.toNat + d + 8 * w < 2 ^ 64) :
    BitVec.ofNat 64 w <<< 3 + off B d = off B (d + 8 * w) := by
  have h := ea_top B (c := 0) (Nat.zero_le _) hn
  rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.sub_zero, Nat.sub_zero] at h

/-- The value of `n`'s top two words `T` and `L` and the rest. -/
theorem top_two (m : Mem) (B : Addr) (d : Nat) {w : Nat} (hw : 2 ≤ w) :
    wordsVal m B d w = (Mont.word m B (d + 8 * (w - 1))).toNat * 2 ^ (64 * (w - 2) + 64) +
      (Mont.word m B (d + 8 * (w - 2))).toNat * 2 ^ (64 * (w - 2)) + wordsVal m B d (w - 2) := by
  have e1 := wordsVal_succ_top m B d (w - 1)
  have e2 := wordsVal_succ_top m B d (w - 2)
  rw [show w - 1 + 1 = w by omega] at e1
  rw [show w - 2 + 1 = w - 1 by omega] at e2
  rw [e1, e2, show 64 * (w - 1) = 64 * (w - 2) + 64 by omega, Nat.mul_comm (2 ^ (64 * (w - 2) + 64)),
    Nat.mul_comm (2 ^ (64 * (w - 2)))]
  omega

/-- The registers `normTail` writes. -/
def normRegs : List Reg := [.s0, .s1, .s2, .s3, .s4, .t3]

/-- `n`'s top three words `T`, `L` and `L'` and the rest. -/
theorem top_three (m : Mem) (B : Addr) (d : Nat) {w : Nat} (hw : 3 ≤ w) :
    wordsVal m B d w = (Mont.word m B (d + 8 * (w - 1))).toNat * 2 ^ (64 * (w - 3) + 64 + 64) +
      (Mont.word m B (d + 8 * (w - 2))).toNat * 2 ^ (64 * (w - 3) + 64) +
      (Mont.word m B (d + 8 * (w - 3))).toNat * 2 ^ (64 * (w - 3)) + wordsVal m B d (w - 3) := by
  have e1 := top_two m B d (w := w) (by omega)
  have e2 := wordsVal_succ_top m B d (w - 3)
  rw [show w - 3 + 1 = w - 2 by omega] at e2
  rw [e1, e2, show 64 * (w - 2) = 64 * (w - 3) + 64 by omega, Nat.mul_comm (2 ^ (64 * (w - 3)))]
  omega

/-- `normTail`, after `lz` (`a1 = z`, `2^63 ≤ T 2^z < 2^64` for `n`'s top
word `T`): `P = 2^z`, `d' = ⌊n P / 2^(64 (w - 1))⌋ ≥ 2^63` and `d'ₗ`, with
`(d', d'ₗ) = ⌊n P / 2^(64 (w - 2))⌋`, in the temporary's words 0, 1 and 3,
`d'` also in `s2`. -/
theorem normTail_ok {s : State} {B : Addr} {Z dN dT w z : Nat} (hs : Scr s B Z)
    (h6 : s.gpr .a6 = off B dT) (h7 : s.gpr .a7 = off B dN) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (h1 : s.gpr .a1 = BitVec.ofNat 64 z) (hw : 3 ≤ w) (hw' : w < 2 ^ 31) (hN8 : dN % 8 = 0) (hT8 : dT % 8 = 0)
    (hNZ : dN + 8 * (w + 1) ≤ Z) (hTZ : dT + 32 ≤ Z)
    (hb1 : 2 ^ 63 ≤ (Mont.word s.mem B (dN + 8 * (w - 1))).toNat * 2 ^ z)
    (hb2 : (Mont.word s.mem B (dN + 8 * (w - 1))).toNat * 2 ^ z < 2 ^ 64) :
    WP isa (.block normTail) s fun t =>
      ((Mont.word t.mem B dT).toNat = 2 ^ z ∧ z ≤ 63 ∧
        (Mont.word t.mem B (dT + 8)).toNat = wordsVal s.mem B (dN) w * 2 ^ z / 2 ^ (64 * (w - 1)) ∧
        2 ^ 63 ≤ wordsVal s.mem B (dN) w * 2 ^ z / 2 ^ (64 * (w - 1)) ∧
        (Mont.word t.mem B (dT + 8)).toNat * 2 ^ 64 + (Mont.word t.mem B (dT + 24)).toNat =
          wordsVal s.mem B (dN) w * 2 ^ z / 2 ^ (64 * (w - 2)) ∧
        t.gpr .s2 = Mont.word t.mem B (dT + 8) ∧ Outside B (dT) 32 s.mem t.mem) ∧ Keep normRegs s t := by
  have hnw := hs.nowrap
  have a0 := hN8; have a3 := hT8
  generalize hTw : Mont.word s.mem B (dN + 8 * (w - 1)) = T at hb1 hb2
  generalize hLw : Mont.word s.mem B (dN + 8 * (w - 2)) = L
  generalize hL'w : Mont.word s.mem B (dN + 8 * (w - 3)) = L'
  have hT0 : 0 < T.toNat := by
    rcases Nat.eq_zero_or_pos T.toNat with h | h
    · rw [h, Nat.zero_mul] at hb1; exact absurd hb1 (by decide)
    · exact h
  have hz : z ≤ 63 := by
    refine Nat.le_of_lt_succ (Nat.lt_of_not_le fun h => ?_)
    have := Nat.mul_le_mul hT0 (Nat.pow_le_pow_right (show 0 < 2 by decide) h)
    omega
  have ea := ea_top B (d := dN) (w := w) (c := 24) (by omega_arith) (by omega_arith)
  rw [show dN + 8 * w - 24 = dN + 8 * (w - 3) by omega] at ea
  have hz64 : (BitVec.ofNat 64 z).toNat % 64 = z := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hP : ((1 : BitVec 64) <<< z).toNat = 2 ^ z := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show BitVec.toNat (1 : BitVec 64) = 1 from rfl, Nat.one_mul]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))
  have hTP : (T <<< z).toNat = T.toNat * 2 ^ z := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; exact Nat.mod_eq_of_lt hb2
  have hLP : L.toNat * 2 ^ z / 2 ^ 64 < 2 ^ z := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64), Nat.mul_comm (2 ^ z)]
    exact Nat.mul_lt_mul_of_pos_right L.isLt (Nat.two_pow_pos z)
  have hL'P : L'.toNat * 2 ^ z / 2 ^ 64 < 2 ^ z := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64), Nat.mul_comm (2 ^ z)]
    exact Nat.mul_lt_mul_of_pos_right L'.isLt (Nat.two_pow_pos z)
  have rT : s.mem.readW (off B (dN + 8 * (w - 3) + 16)) 64 = T := by
    rw [← hTw, show dN + 8 * (w - 3) + 16 = dN + 8 * (w - 1) by omega_arith]
  have rL : s.mem.readW (off B (dN + 8 * (w - 3) + 8)) 64 = L := by
    rw [← hLw, show dN + 8 * (w - 3) + 8 = dN + 8 * (w - 2) by omega_arith]
  have rL' : s.mem.readW (off B (dN + 8 * (w - 3))) 64 = L' := hL'w
  generalize hD : T <<< z + BitVec.ofNat 64 (L.toNat * ((1 : BitVec 64) <<< z).toNat / 2 ^ 64) = D
  generalize hDl : L * (1 : BitVec 64) <<< z + BitVec.ofNat 64 (L'.toNat * ((1 : BitVec 64) <<< z).toNat / 2 ^ 64) = Dl
  refine WP.mono (WP.keep normRegs (Q := fun t => t.gpr .s2 = D ∧
      t.mem = ((s.mem.writeW (off B dT) ((1 : BitVec 64) <<< z)).writeW (off B (dT + 8)) D).writeW
        (off B (dT + 24)) Dl) (by
    unfold normTail
    brun [r2_exec_li_one, exec_sllReg, h1, h6, h7, ht0, hz64, ea, rT, rL, rL', hD, hDl, BitVec.add_zero,
      hs.ld (show dN + 8 * (w - 3) + 16 + 8 ≤ Z by omega),
      hs.al8 (show dN + 8 * (w - 3) + 16 + 8 ≤ Z by omega) (by omega),
      hs.ld (show dN + 8 * (w - 3) + 8 + 8 ≤ Z by omega),
      hs.al8 (show dN + 8 * (w - 3) + 8 + 8 ≤ Z by omega) (by omega),
      hs.ld (show dN + 8 * (w - 3) + 8 ≤ Z by omega),
      hs.al8 (show dN + 8 * (w - 3) + 8 ≤ Z by omega) (by omega),
      hs.st (show dT + 8 ≤ Z by omega), hs.al8 (show dT + 8 ≤ Z by omega) a3,
      hs.st (show dT + 8 + 8 ≤ Z by omega), hs.al8 (show dT + 8 + 8 ≤ Z by omega) (by omega),
      hs.st (show dT + 24 + 8 ≤ Z by omega), hs.al8 (show dT + 24 + 8 ≤ Z by omega) (by omega)])
    (by rfl) (by rfl))
    fun t ⟨⟨t2, tm⟩, k⟩ => ⟨?_, k⟩
  have wD : Mont.word t.mem B (dT + 8) = D := by
    rw [tm]
    exact (Outside.word (writeW_outside _ B (d := dT + 24) _ (by omega))
      (Or.inl (by omega)) (by omega)).trans (Mont.word_writeW_self _ _ _ _)
  have wDl : Mont.word t.mem B (dT + 24) = Dl := by rw [tm, Mont.word_writeW_self]
  have hN := top_three s.mem B (dN) hw
  rw [hTw, hLw, hL'w] at hN
  have hlow := wordsVal_lt s.mem B (dN) (w - 3)
  have hNv : wordsVal s.mem B (dN) w * 2 ^ z / 2 ^ (64 * (w - 1)) =
      T.toNat * 2 ^ z + L.toNat * 2 ^ z / 2 ^ 64 := by
    rw [top_two s.mem B (dN) (by omega), hTw, hLw, show 64 * (w - 1) = 64 * (w - 2) + 64 by omega_arith]
    exact top_shift (by omega_arith) (wordsVal_lt _ _ _ _)
  have hNv2 : wordsVal s.mem B (dN) w * 2 ^ z / 2 ^ (64 * (w - 2)) =
      T.toNat * 2 ^ z * 2 ^ 64 + (L.toNat * 2 ^ z + L'.toNat * 2 ^ z / 2 ^ 64) := by
    rw [hN, show 64 * (w - 2) = 64 * (w - 3) + 64 by omega_arith]
    exact top3_shift (by omega_arith) hlow
  have hpz : 2 ^ z ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) hz
  have hDv : D.toNat = T.toNat * 2 ^ z + L.toNat * 2 ^ z / 2 ^ 64 := by
    rw [← hD, BitVec.toNat_add, hTP, BitVec.toNat_ofNat, hP,
      Nat.mod_eq_of_lt (show L.toNat * 2 ^ z / 2 ^ 64 < 2 ^ 64 by omega_using [hLP, hpz]),
      Nat.mod_eq_of_lt (shl_add_lt (by omega_arith) hb2 hLP)]
  -- `d'ₗ = L P mod 2^64 + ⌊L' P / 2^64⌋`, which does not wrap.
  have e64 : (2 : Nat) ^ 64 = 2 ^ (64 - z) * 2 ^ z := by rw [← Nat.pow_add]; congr 1; omega
  have hLm : L.toNat * 2 ^ z % 2 ^ 64 = L.toNat % 2 ^ (64 - z) * 2 ^ z := by
    rw [e64, Nat.mul_mod_mul_right]
  have hLm' : L.toNat % 2 ^ (64 - z) * 2 ^ z < 2 ^ 64 := by
    rw [e64]; exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.two_pow_pos z)
  have hDlv : Dl.toNat = L.toNat * 2 ^ z % 2 ^ 64 + L'.toNat * 2 ^ z / 2 ^ 64 := by
    rw [← hDl, BitVec.toNat_add, BitVec.toNat_mul, hP, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show L'.toNat * 2 ^ z / 2 ^ 64 < 2 ^ 64 by omega_using [hL'P, hpz]), hLm]
    exact Nat.mod_eq_of_lt (shl_add_lt (by omega_arith) hLm' hL'P)
  have hLd := Nat.div_add_mod (L.toNat * 2 ^ z) (2 ^ 64)
  refine ⟨?_, hz, by rw [wD, hDv, hNv], by rw [hNv]; omega_using [hb1], ?_, by rw [t2, wD], ?_⟩
  · rw [tm, ← hP]
    exact congrArg BitVec.toNat ((Outside.word (writeW_outside _ B (d := dT + 24) _ (by omega))
      (Or.inl (by omega)) (by omega)).trans ((Outside.word (writeW_outside _ B (d := dT + 8) _ (by omega))
      (Or.inl (Nat.le_refl _)) (by omega)).trans (Mont.word_writeW_self _ _ _ _)))
  · rw [wD, wDl, hDv, hDlv, hNv2, Nat.add_mul, Nat.mul_comm (L.toNat * 2 ^ z / 2 ^ 64)]
    omega_using [hLd]
  · rw [tm]
    exact (((writeW_outside s.mem B (d := dT) _ (by omega)).mono (Nat.le_refl _) (by omega)).trans
      ((writeW_outside _ B (d := dT + 8) _ (by omega)).mono (by omega) (by omega))).trans
      ((writeW_outside _ B (d := dT + 24) _ (by omega)).mono (by omega) (by omega))


/-! ## The reciprocal -/

/-- `2 x + b` modulo `2^64`, as a shift and an or. -/
theorem shl1_or_bit (x : BitVec 64) (b : Bool) :
    (x <<< 1 ||| BitVec.ofNat 64 b.toNat).toNat = (2 * x.toNat + b.toNat) % 2 ^ 64 := by
  have h : x <<< 1 &&& BitVec.ofNat 64 b.toNat = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    cases b
    · simp
    · rw [BitVec.toNat_and, BitVec.toNat_shiftLeft, show (BitVec.ofNat 64 (true : Bool).toNat).toNat = 1 from rfl,
        Nat.and_one_is_mod, Nat.shiftLeft_eq, Nat.pow_one, show (0#64).toNat = 0 from rfl]
      omega
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ h, BitVec.toNat_add, BitVec.toNat_shiftLeft]
  simp only [Nat.shiftLeft_eq, Nat.pow_one, BitVec.toNat_ofNat]
  have := Bool.toNat_le b
  omega

/-- `2 r + 1` modulo `2^64`, as `divBit` computes it. -/
def dS (r : BitVec 64) : BitVec 64 := r <<< 1 ||| 1#64

/-- The bit of the quotient: `2 r + 1 ≥ d`, or the carry out of `2 r + 1`. -/
def dB (r d : BitVec 64) : BitVec 64 := (if dS r < d then (1 : BitVec 64) else 0) ^^^ 1#64 ||| r >>> 63

/-- The remainder. -/
def dR (r d : BitVec 64) : BitVec 64 := dS r - ((0 - dB r d) &&& d)

theorem shr63_toNat (r : BitVec 64) : (r >>> 63) = BitVec.ofNat 64 (decide (2 ^ 63 ≤ r.toNat)).toNat := by
  have := r.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  by_cases h : 2 ^ 63 ≤ r.toNat <;> simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;>
    omega

theorem lt_xor_one (a b : BitVec 64) :
    (if a < b then (1 : BitVec 64) else 0) ^^^ 1#64 = BitVec.ofNat 64 (decide (b.toNat ≤ a.toNat)).toNat := by
  by_cases h : a < b
  · rw [ite_eq_left h, decide_eq_false (by rw [BitVec.lt_def] at h; omega)]; rfl
  · rw [ite_eq_right h, decide_eq_true (by rw [BitVec.lt_def] at h; omega)]; rfl

theorem or_bits (a b : Bool) :
    BitVec.ofNat 64 a.toNat ||| BitVec.ofNat 64 b.toNat = BitVec.ofNat 64 (a || b).toNat := by
  cases a <;> cases b <;> rfl

theorem dB_val {r d : Nat} (hr : r < d) (hd : d < 2 ^ 64) :
    dB (BitVec.ofNat 64 r) (BitVec.ofNat 64 d) = BitVec.ofNat 64 (decide (d ≤ 2 * r + 1)).toNat := by
  have hR : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hD : (BitVec.ofNat 64 d).toNat = d := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]
  have hS : (dS (BitVec.ofNat 64 r)).toNat = (2 * r + 1) % 2 ^ 64 := by
    rw [dS, show (1#64 : BitVec 64) = BitVec.ofNat 64 (true : Bool).toNat from rfl, shl1_or_bit, hR]; rfl
  rw [dB, lt_xor_one, shr63_toNat, hS, hR, hD, or_bits]
  congr 2
  by_cases h : 2 ^ 63 ≤ r
  · simp only [h, decide_true, Bool.or_true]
    symm; apply decide_eq_true; omega
  · simp only [h, decide_false, Bool.or_false]
    apply decide_eq_decide.mpr
    rw [Nat.mod_eq_of_lt (by omega)]

theorem dR_val {r d : Nat} (hr : r < d) (hd : d < 2 ^ 64) :
    dR (BitVec.ofNat 64 r) (BitVec.ofNat 64 d) =
      BitVec.ofNat 64 (if d ≤ 2 * r + 1 then 2 * r + 1 - d else 2 * r + 1) := by
  have hR : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hD : (BitVec.ofNat 64 d).toNat = d := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]
  have hS : (dS (BitVec.ofNat 64 r)).toNat = (2 * r + 1) % 2 ^ 64 := by
    rw [dS, show (1#64 : BitVec 64) = BitVec.ofNat 64 (true : Bool).toNat from rfl, shl1_or_bit, hR]; rfl
  rw [dR, dB_val hr hd]
  apply BitVec.eq_of_toNat_eq
  by_cases h : d ≤ 2 * r + 1
  · rw [decide_eq_true h, ite_eq_left h, show (0 : BitVec 64) - BitVec.ofNat 64 (true : Bool).toNat =
      BitVec.allOnes 64 from rfl, BitVec.allOnes_and, BitVec.toNat_sub, hS, hD, BitVec.toNat_ofNat]
    omega
  · rw [decide_eq_false h, ite_eq_right h, show (0 : BitVec 64) - BitVec.ofNat 64 (false : Bool).toNat = 0#64 from rfl,
      BitVec.zero_and, BitVec.sub_zero, hS, BitVec.toNat_ofNat]

/-- After `k` bits of `recip`'s loop from `s₀`: `s3 = r`, `s4 = q` for
`r₀ 2^k + 2^k - 1 = q d + r`, `r < d`. -/
structure RecInv (s₀ : State) (d r0 : Nat) (k : Nat) (t : State) : Prop where
  keep : Keep [.s0, .s1, .s3, .s4, .t5] s₀ t
  mem : t.mem = s₀.mem
  val : ∃ q r, t.gpr .s3 = BitVec.ofNat 64 r ∧ t.gpr .s4 = BitVec.ofNat 64 q ∧
    r0 * 2 ^ k + (2 ^ k - 1) = q * d + r ∧ r < d

theorem divBit_ok (t : State) (h4 : t.gpr .a4 = 0) :
    WP isa (.block (divBit ++ ([.addi .t5 .t5 (-1)] : List Instr))) t fun t' =>
      (t'.gpr .s3 = dR (t.gpr .s3) (t.gpr .s2) ∧
        t'.gpr .s4 = t.gpr .s4 <<< 1 ||| dB (t.gpr .s3) (t.gpr .s2) ∧ t'.mem = t.mem ∧
        t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1) ∧ Keep [.s0, .s1, .s3, .s4, .t5] t t' := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold divBit
  brun [h4]
  exact ⟨rfl, rfl⟩

theorem divStep_ok {s₀ : State} {d r0 : Nat} (hd : d < 2 ^ 64) (hr0 : r0 < d) (h4 : s₀.gpr .a4 = 0)
    (h2 : s₀.gpr .s2 = BitVec.ofNat 64 d) {k : Nat} (hk : k < 64) {t : State} (hI : RecInv s₀ d r0 k t) :
    WP isa (.block (divBit ++ ([.addi .t5 .t5 (-1)] : List Instr))) t fun t' =>
      RecInv s₀ d r0 (k + 1) t' ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 := by
  obtain ⟨q, r, h3, h4q, hP, hr⟩ := hI.val
  have t4 := (hI.keep.gpr (r := .a4) (by decide)).trans h4
  have t2 := (hI.keep.gpr (r := .s2) (by decide)).trans h2
  refine WP.mono (divBit_ok t t4) fun t' ⟨⟨u3, u4, um, u5⟩, k'⟩ => ⟨?_, u5⟩
  -- `q < 2^k`, as `q d ≤ r₀ 2^k + 2^k - 1 < d 2^k`.
  have hpk : 0 < 2 ^ k := Nat.two_pow_pos k
  have hq : q < 2 ^ k := by
    have h1 : q * d < 2 ^ k * d := by
      have := Nat.mul_le_mul_left (2 ^ k) (show r0 + 1 ≤ d by omega)
      rw [Nat.mul_add, Nat.mul_one] at this
      rw [Nat.mul_comm r0] at hP
      omega
    exact Nat.lt_of_mul_lt_mul_right h1
  have hk' : 2 ^ k ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨hP', hr'⟩ := WordStep.divBit_inv (P := r0 * 2 ^ k + (2 ^ k - 1)) (q := q) (r := r)
    (d := d) hP hr (b := 1) (by decide)
  refine ⟨Keep.trans' hI.keep k', by rw [um, hI.mem], ?_⟩
  refine ⟨2 * q + (if d ≤ 2 * r + 1 then 1 else 0), if d ≤ 2 * r + 1 then 2 * r + 1 - d else 2 * r + 1,
    by rw [u3, h3, t2, dR_val hr hd], ?_, ?_, hr'⟩
  · rw [u4, h3, t2, h4q, dB_val hr hd]
    apply BitVec.eq_of_toNat_eq
    rw [shl1_or_bit, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show q < 2 ^ 64 by omega)]
    by_cases h : d ≤ 2 * r + 1 <;> simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false,
      ↓reduceIte] <;> omega
  · rw [Nat.pow_succ]
    have e : r0 * (2 ^ k * 2) + (2 ^ k * 2 - 1) = 2 * (r0 * 2 ^ k + (2 ^ k - 1)) + 1 := by
      have := Nat.two_pow_pos k; rw [← Nat.mul_assoc, Nat.mul_add, Nat.mul_comm 2 (r0 * 2 ^ k)]; omega
    rw [e, hP']

theorem exec_li_m1 {s : State} {d : Reg} : exec (.li d (-1)) s = some (s.write d (BitVec.allOnes 64)) := by
  rw [exec_li (by decide)]; rfl

theorem exec_li_64 {s : State} {d : Reg} : exec (.li d 64) s = some (s.write d (BitVec.ofNat 64 64)) := by
  rw [exec_li (by decide)]; rfl

theorem exec_li_zero {s : State} {d : Reg} : exec (.li d 0) s = some (s.write d 0) := by
  rw [exec_li (by decide)]; rfl

/-- The registers `recip` writes. -/
def recipRegs : List Reg := [.a4, .s0, .s1, .s3, .s4, .t5]

/-- `recip`, for `d' ≥ 2^63` in `s2`: `v = ⌊(2^128 - 1) / d'⌋ - 2^64` into the
temporary's word 2 (`a6` at array 3), and `a4 := 0`. -/
theorem recip_ok {s : State} {B : Addr} {Z dT : Nat} (hs : Scr s B Z) (h6 : s.gpr .a6 = off B dT)
    (hT8 : dT % 8 = 0) (hZ : dT + 24 ≤ Z) (hd : 2 ^ 63 ≤ (s.gpr .s2).toNat) :
    WP isa recip s fun t =>
      ((Mont.word t.mem B (dT + 16)).toNat = (2 ^ 128 - 1) / (s.gpr .s2).toNat - 2 ^ 64 ∧
        t.gpr .a4 = 0 ∧ Outside B (dT + 16) 8 s.mem t.mem) ∧ Keep recipRegs s t := by
  have hn := hs.nowrap
  generalize hD : s.gpr .s2 = D at hd
  have hD' := D.isLt
  have hsub : BitVec.allOnes 64 - D = BitVec.ofNat 64 (2 ^ 64 - 1 - D.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_allOnes, BitVec.toNat_ofNat]
    omega_using [hD']
  unfold recip
  refine WP.seq (WP.mono (WP.keep [.a4, .s3, .s4, .t5] (Q := fun t =>
    t.gpr .a4 = 0 ∧ t.gpr .s3 = BitVec.ofNat 64 (2 ^ 64 - 1 - D.toNat) ∧
    t.gpr .s4 = BitVec.ofNat 64 0 ∧ t.gpr .t5 = BitVec.ofNat 64 64 ∧ t.mem = s.mem)
    (by unfold recipHead; brun [exec_li_zero, exec_li_m1, exec_li_64, hD, hsub]; rfl) (by rfl) (by rfl))
    fun s₁ ⟨⟨a4, a3, a4q, a5, hm₁⟩, k₁⟩ => ?_)
  have hr0 : 2 ^ 64 - 1 - D.toNat < D.toNat := by omega
  have h2₁ : s₁.gpr .s2 = BitVec.ofNat 64 D.toNat := by rw [k₁.gpr (by decide), hD, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h0 : RecInv s₁ D.toNat (2 ^ 64 - 1 - D.toNat) 0 s₁ :=
    ⟨Keep.refl _ _, rfl, 0, 2 ^ 64 - 1 - D.toNat, a3, a4q, by simp, hr0⟩
  refine WP.seq (WP.mono (wp_countdown (N := 64) (by decide) (by decide) (RecInv s₁ D.toNat (2 ^ 64 - 1 - D.toNat))
    (fun k hk t hI _ => divStep_ok hD' hr0 a4 h2₁ hk hI) h0 a5) fun t hI => ?_)
  obtain ⟨q, r, _, h4t, hP, hr⟩ := hI.val
  have t6 : t.gpr .a6 = off B (dT) := (hI.keep.gpr (by decide)).trans ((k₁.gpr (by decide)).trans h6)
  have hs' := hs.congr (k₁.trans hI.keep).2.2
  refine WP.mono (WP.keep [] (Q := fun t' => t'.mem = t.mem.writeW (off B (dT + 16)) (t.gpr .s4))
    (by brun [t6, hs'.st (show dT + 16 + 8 ≤ Z by omega),
      hs'.al8 (show dT + 16 + 8 ≤ Z by omega) (by omega)]) (by rfl) (by rfl))
    fun t' ⟨hm', k'⟩ => ?_
  have hq : q = (2 ^ 128 - 1) / D.toNat - 2 ^ 64 := by
    rw [← WordStep.recip_eq hD' (by omega), hP, Nat.mul_comm q, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr,
      Nat.add_zero]
  have hqB : q < 2 ^ 64 := by
    rw [hq]
    have : (2 ^ 128 - 1) / D.toNat < 2 ^ 65 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      have := Nat.mul_le_mul_left (2 ^ 65) hd
      omega
    omega
  refine ⟨⟨by rw [hm', Mont.word_writeW_self, h4t, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqB, hq],
    by rw [k'.gpr (by decide), hI.keep.gpr (by decide), a4], ?_⟩, ((k₁.trans hI.keep).trans k').mono (by decide)⟩
  rw [hm', hI.mem, hm₁]
  exact writeW_outside _ _ _ (by omega)


/-! ## The estimate of the quotient -/

/-- What `quotMG` computes from `v` (`s3`), `u` (`t4`), `a` (`t5`) and `d`
(`s2`), instruction by instruction. -/
def mgq (v u a d : BitVec 64) : BitVec 64 :=
  let q0 := v * u + a
  let Q := BitVec.ofNat 64 (v.toNat * u.toNat / 2 ^ 64) + u + (if q0 < a then (1 : BitVec 64) else 0) + 1#64
  let r := a - Q * d
  let c : BitVec 64 := if q0 < r then 1 else 0
  let r1 := r + ((0 - c) &&& d)
  Q - c + ((if r1 < d then (1 : BitVec 64) else 0) ^^^ 1#64)

/-- The carry of `x + y`, by `sltu`. -/
theorem carry_val (x y : BitVec 64) :
    (if x + y < y then (1 : BitVec 64) else 0).toNat = (decide (2 ^ 64 ≤ x.toNat + y.toNat)).toNat := by
  have hx := x.isLt; have hy := y.isLt
  by_cases h : x + y < y
  · rw [ite_eq_left h]
    rw [BitVec.lt_def, BitVec.toNat_add] at h
    rw [decide_eq_true (by omega)]; rfl
  · rw [ite_eq_right h]
    rw [BitVec.lt_def, BitVec.toNat_add] at h
    rw [decide_eq_false (by omega)]; rfl

theorem mgq_val {v u a d : Nat} (hd : d < 2 ^ 64) (hn : 2 ^ 63 ≤ d) (hu : u < d) (ha : a < 2 ^ 64)
    (hv : v = (2 ^ 128 - 1) / d - 2 ^ 64) :
    (mgq (BitVec.ofNat 64 v) (BitVec.ofNat 64 u) (BitVec.ofNat 64 a) (BitVec.ofNat 64 d)).toNat =
      (u * 2 ^ 64 + a) / d := by
  have hd0 : 0 < d := by omega
  have hVd : (2 ^ 128 - 1) / d * d ≤ 2 ^ 128 - 1 := Nat.div_mul_le_self _ _
  have hVB : 2 ^ 64 ≤ (2 ^ 128 - 1) / d := by
    rw [Nat.le_div_iff_mul_le hd0]
    have := Nat.mul_le_mul_left (2 ^ 64) (show d ≤ 2 ^ 64 - 1 by omega)
    omega
  generalize hV : (2 ^ 128 - 1) / d = V at hVd hVB hv
  have hVu : V * u + V ≤ V * d := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hu
  have hPe : v * u + a + 2 ^ 64 * u = V * u + a := by
    rw [hv, Nat.sub_mul]; have := Nat.mul_le_mul_right u hVB; omega
  have hVd' : V * d = d * V := Nat.mul_comm _ _
  have hPB : V * u + a < 2 ^ 128 := by omega
  have hvl : v < 2 ^ 64 := by
    rw [hv]
    have : V < 2 ^ 65 := by
      rw [← hV, Nat.div_lt_iff_lt_mul hd0]
      have := Nat.mul_le_mul_left (2 ^ 65) hn
      omega
    omega
  have hul : u < 2 ^ 64 := by omega
  have hU : (BitVec.ofNat 64 u).toNat = u := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hul]
  have hA : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  have hD : (BitVec.ofNat 64 d).toNat = d := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]
  have hVv : (BitVec.ofNat 64 v).toNat = v := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvl]
  unfold mgq
  simp only []
  -- `(q₁, q₀) = V u + a`.
  have hl : v * u ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hvu : v * u / 2 ^ 64 ≤ 2 ^ 64 - 2 := Nat.le_trans (Nat.div_le_div_right (c := 2 ^ 64) hl) (by decide)
  have hdm := Nat.div_add_mod (v * u) (2 ^ 64)
  have hmm := Nat.mod_lt (v * u) (show 0 < 2 ^ 64 by decide)
  generalize hq0 : BitVec.ofNat 64 v * BitVec.ofNat 64 u + BitVec.ofNat 64 a = q0
  have hq0v : q0.toNat = (V * u + a) % 2 ^ 64 := by
    rw [← hq0, BitVec.toNat_add, BitVec.toNat_mul, hVv, hU, hA, ← hPe]
    omega
  have hc := carry_val (BitVec.ofNat 64 v * BitVec.ofNat 64 u) (BitVec.ofNat 64 a)
  rw [hq0] at hc
  rw [BitVec.toNat_mul, hVv, hU, hA] at hc
  generalize hQ : BitVec.ofNat 64 ((BitVec.ofNat 64 v).toNat * (BitVec.ofNat 64 u).toNat / 2 ^ 64) +
    BitVec.ofNat 64 u + (if q0 < BitVec.ofNat 64 a then (1 : BitVec 64) else 0) + 1#64 = Q
  have hQv : Q.toNat = ((V * u + a) / 2 ^ 64 + 1) % 2 ^ 64 := by
    rw [← hQ, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, hc, hVv, hU, BitVec.toNat_ofNat,
      show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt (show v * u / 2 ^ 64 < 2 ^ 64 by omega), ← hPe]
    have : (v * u + a + 2 ^ 64 * u) / 2 ^ 64 = v * u / 2 ^ 64 + u + (decide (2 ^ 64 ≤ v * u % 2 ^ 64 + a)).toNat := by
      by_cases h : 2 ^ 64 ≤ v * u % 2 ^ 64 + a <;> simp only [h, decide_true, decide_false, Bool.toNat_true,
        Bool.toNat_false] <;> omega
    rw [this]
    have := Bool.toNat_le (decide (2 ^ 64 ≤ v * u % 2 ^ 64 + a))
    omega
  generalize hr : BitVec.ofNat 64 a - Q * BitVec.ofNat 64 d = r
  have hrv : r.toNat = (a + (2 ^ 64 - Q.toNat * d % 2 ^ 64)) % 2 ^ 64 := by
    rw [← hr, BitVec.toNat_sub, BitVec.toNat_mul, hA, hD]
    have : Q.toNat * d % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
    rw [Nat.add_comm]
  generalize hcv : decide ((V * u + a) % 2 ^ 64 < r.toNat) = c
  have hcb : (if q0 < r then (1 : BitVec 64) else 0) = BitVec.ofNat 64 c.toNat := by
    rw [← hcv]
    by_cases h : q0 < r
    · rw [ite_eq_left h, decide_eq_true (by rw [BitVec.lt_def, hq0v] at h; exact h)]; rfl
    · rw [ite_eq_right h, decide_eq_false (by rw [BitVec.lt_def, hq0v] at h; exact h)]; rfl
  rw [hcb]
  have hQ1 : (Q - BitVec.ofNat 64 c.toNat).toNat = (Q.toNat + if c then 2 ^ 64 - 1 else 0) % 2 ^ 64 := by
    have := Q.isLt
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.mod_eq_of_lt this, Bool.toNat_false]
      rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.sub_zero]
    · simp only [↓reduceIte, BitVec.toNat_sub, BitVec.toNat_ofNat, Bool.toNat_true]
      omega
  have hr1 : (r + ((0 - BitVec.ofNat 64 c.toNat) &&& BitVec.ofNat 64 d)).toNat = (r.toNat + if c then d else 0) % 2 ^ 64 := by
    have := r.isLt
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.mod_eq_of_lt this, Bool.toNat_false]
      rw [show (0 : BitVec 64) - BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.zero_and, BitVec.add_zero]
    · simp only [↓reduceIte, Bool.toNat_true]
      rw [show (0 : BitVec 64) - BitVec.ofNat 64 1 = BitVec.allOnes 64 from rfl, BitVec.allOnes_and,
        BitVec.toNat_add, hD]
  generalize hQ1v : Q - BitVec.ofNat 64 c.toNat = Q1 at hQ1
  generalize hr1v : r + ((0 - BitVec.ofNat 64 c.toNat) &&& BitVec.ofNat 64 d) = r1 at hr1
  have hfin := WordStep.mg_quot hd hn hu ha hV.symm rfl hQv hrv (Q1 := Q1.toNat) (r1 := r1.toNat)
    (by rw [hQ1, ← hcv]; simp only [decide_eq_true_eq]) (by rw [hr1, ← hcv]; simp only [decide_eq_true_eq])
  rw [← hfin, lt_xor_one, BitVec.toNat_add, BitVec.toNat_ofNat, hD]
  have := Q1.isLt
  by_cases h : d ≤ r1.toNat
  · simp only [h, decide_true, Bool.toNat_true, show d - 1 < r1.toNat by omega, ↓reduceIte]
  · simp only [h, decide_false, Bool.toNat_false, show ¬ d - 1 < r1.toNat by omega, ↓reduceIte]

/-- The estimate as `quotFix` makes it, all ones when the top word `u₂` of
the dividend is the divisor `d`. -/
theorem fix_val (q u2 d : BitVec 64) :
    (q ||| ((if 0 < d - u2 then (1 : BitVec 64) else 0) - 1#64)) = if u2 = d then BitVec.allOnes 64 else q := by
  by_cases h : u2 = d
  · subst h
    rw [BitVec.sub_self, ite_eq_right (by decide), ite_eq_left rfl]
    exact BitVec.or_allOnes
  · have hne : 0 < d - u2 := by
      rw [BitVec.lt_def]
      refine Nat.pos_of_ne_zero fun e => h ?_
      have := BitVec.eq_of_toNat_eq (x := d - u2) (y := 0) e
      rw [BitVec.sub_eq_iff_eq_add] at this
      exact (this.trans (BitVec.zero_add u2)).symm
    rw [ite_eq_left hne, ite_eq_right h, show (1 : BitVec 64) - 1#64 = 0#64 from rfl, BitVec.or_zero]

/-- The registers `quot` writes. -/
def quotRegs : List Reg := [.a3, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4]

/-- `quot`, `x` (`w ≥ 3` words) at `dX`, a word above `a2` (`V`'s words 1 to
`w`), and the temporary at `a6`, holding
`P = 2^z`, `d' ≥ 2^63` and `v = ⌊(2^128 - 1) / d'⌋ - 2^64`, with
`⌊x P / 2^(64 (w - 1))⌋ ≤ d'`: `q̂ = min(⌊u / d'⌋, 2^64 - 1)` in `s1` for the
top two words `u = ⌊x P / 2^(64 (w - 2))⌋` of `x P`, `u` in `t4` and `t5`,
`d'` in `s2` and the address of `x`'s word `w - 3` in `t3`. -/
theorem quot_ok {s : State} {B : Addr} {Z dX dT w z : Nat} (hs : Scr s B Z)
    (h2 : s.gpr .a2 = off B (dX - 8)) (h6 : s.gpr .a6 = off B dT)
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (h4 : s.gpr .a4 = 0) (hw : 3 ≤ w) (hw' : w < 2 ^ 31)
    (hX8 : dX % 8 = 0) (hX8' : 8 ≤ dX) (hT8 : dT % 8 = 0) (hXZ : dX + 8 * w ≤ Z) (hTZ : dT + 32 ≤ Z)
    (hP : (Mont.word s.mem B dT).toNat = 2 ^ z) (hz : z ≤ 63)
    (hd : 2 ^ 63 ≤ (Mont.word s.mem B (dT + 8)).toNat)
    (hv : (Mont.word s.mem B (dT + 16)).toNat =
      (2 ^ 128 - 1) / (Mont.word s.mem B (dT + 8)).toNat - 2 ^ 64)
    (hXd : wordsVal s.mem B dX w * 2 ^ z / 2 ^ (64 * (w - 1)) ≤ (Mont.word s.mem B (dT + 8)).toNat) :
    WP isa (.block quot) s fun t => ((t.gpr .s1).toNat =
      min (wordsVal s.mem B dX w * 2 ^ z / 2 ^ (64 * (w - 2)) / (Mont.word s.mem B (dT + 8)).toNat)
        (2 ^ 64 - 1) ∧ t.mem = s.mem ∧ t.gpr .t3 = off B (dX + 8 * (w - 3)) ∧
      (t.gpr .t4).toNat * 2 ^ 64 + (t.gpr .t5).toNat = wordsVal s.mem B dX w * 2 ^ z / 2 ^ (64 * (w - 2)) ∧
      t.gpr .s2 = Mont.word s.mem B (dT + 8)) ∧ Keep quotRegs s t := by
  have hnw := hs.nowrap
  have a1 := hX8; have a3 := hT8
  generalize hDw : Mont.word s.mem B (dT + 8) = D at hd hv hXd ⊢
  generalize hPw : Mont.word s.mem B (dT) = P at hP
  generalize hVw : Mont.word s.mem B (dT + 16) = V at hv
  generalize hx2 : Mont.word s.mem B (dX + 8 * (w - 1)) = x2
  generalize hx1 : Mont.word s.mem B (dX + 8 * (w - 2)) = x1
  generalize hx0 : Mont.word s.mem B (dX + 8 * (w - 3)) = x0
  generalize hK : 64 * (w - 3) = K
  have hk1 : 64 * (w - 1) = K + 64 + 64 := by omega
  have hk2 : 64 * (w - 2) = K + 64 := by omega
  rw [hk1] at hXd
  rw [hk2]
  generalize hX : wordsVal s.mem B dX w = X at hXd ⊢
  have hlow := wordsVal_lt s.mem B dX (w - 3)
  rw [hK] at hlow
  have hXe : X = x2.toNat * 2 ^ (K + 64 + 64) + x1.toNat * 2 ^ (K + 64) + x0.toNat * 2 ^ K +
      wordsVal s.mem B dX (w - 3) := by
    have f1 := wordsVal_succ_top s.mem B dX (w - 1)
    have f2 := wordsVal_succ_top s.mem B dX (w - 2)
    have f3 := wordsVal_succ_top s.mem B dX (w - 3)
    rw [show w - 1 + 1 = w by omega, hx2, hX, hk1] at f1
    rw [show w - 2 + 1 = w - 1 by omega, hx1, hk2] at f2
    rw [show w - 3 + 1 = w - 2 by omega, hx0, hK] at f3
    rw [f1, f2, f3, Nat.mul_comm x2.toNat, Nat.mul_comm x1.toNat, Nat.mul_comm x0.toNat]
    generalize 2 ^ (K + 64 + 64) * x2.toNat = a
    generalize 2 ^ (K + 64) * x1.toNat = b
    generalize 2 ^ K * x0.toNat = c
    omega_using []
  -- The top words of `x P`.
  have hu2 : X * 2 ^ z / 2 ^ (K + 64 + 64) = x2.toNat * 2 ^ z + x1.toNat * 2 ^ z / 2 ^ 64 := by
    rw [hXe, Nat.add_assoc _ (x0.toNat * 2 ^ K)]
    refine top_shift (by omega) ?_
    have := Nat.mul_le_mul_right (2 ^ K) (show x0.toNat + 1 ≤ 2 ^ 64 from x0.isLt)
    rw [Nat.add_mul, Nat.one_mul, ← Nat.pow_add, Nat.add_comm 64 K] at this
    omega_using [this, hlow]
  have hU : X * 2 ^ z / 2 ^ (K + 64) = x2.toNat * 2 ^ z * 2 ^ 64 + (x1.toNat * 2 ^ z + x0.toNat * 2 ^ z / 2 ^ 64) := by
    have : X = (x2.toNat * 2 ^ 64 + x1.toNat) * 2 ^ (K + 64) + x0.toNat * 2 ^ K +
        wordsVal s.mem B dX (w - 3) := by
      rw [hXe, Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm 64 (K + 64)]
    rw [this, top_shift (by omega) hlow, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (2 ^ 64), ← Nat.mul_assoc,
      Nat.add_assoc]
  generalize hUd : X * 2 ^ z / 2 ^ (K + 64) = U at hU ⊢
  have hUu : U / 2 ^ 64 = X * 2 ^ z / 2 ^ (K + 64 + 64) := by
    rw [← hUd, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have hf0 : x0.toNat * 2 ^ z / 2 ^ 64 < 2 ^ z := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64), Nat.mul_comm (2 ^ z)]
    exact Nat.mul_lt_mul_of_pos_right x0.isLt (Nat.two_pow_pos z)
  have hpz : 2 ^ z ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) hz
  have hf1 : x1.toNat * 2 ^ z / 2 ^ 64 < 2 ^ 64 := by
    have : x1.toNat * 2 ^ z / 2 ^ 64 < 2 ^ z := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64), Nat.mul_comm (2 ^ z)]
      exact Nat.mul_lt_mul_of_pos_right x1.isLt (Nat.two_pow_pos z)
    omega_using [this, hpz]
  have hDlt := D.isLt
  -- `u₂` and `u₁` as `quotHead` computes them.
  generalize hU2 : x2 * P + BitVec.ofNat 64 (x1.toNat * P.toNat / 2 ^ 64) = U2
  generalize hU1 : x1 * P + BitVec.ofNat 64 (x0.toNat * P.toNat / 2 ^ 64) = U1
  have hU2v : U2.toNat = U / 2 ^ 64 := by
    rw [← hU2, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, hP, Nat.mod_eq_of_lt hf1, Nat.mod_add_mod,
      hUu, hu2]
    exact Nat.mod_eq_of_lt (by omega_using [hu2, hXd, hDlt])
  have hU1v : U1.toNat = U % 2 ^ 64 := by
    rw [← hU1, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, hP,
      Nat.mod_eq_of_lt (by omega_using [hf0, hpz] : x0.toNat * 2 ^ z / 2 ^ 64 < 2 ^ 64), Nat.mod_add_mod, hU,
      Nat.add_comm (x2.toNat * 2 ^ z * 2 ^ 64), Nat.add_mul_mod_self_right]
  have ea := ea_top B (d := dX - 8) (w := w) (c := 16) (by omega) (by omega)
  rw [show dX - 8 + 8 * w - 16 = dX + 8 * (w - 3) by omega] at ea
  have r2 : s.mem.readW (off B (dX + 8 * (w - 3) + 16)) 64 = x2 := by
    rw [← hx2, show dX + 8 * (w - 3) + 16 = dX + 8 * (w - 1) by omega]
  have r1 : s.mem.readW (off B (dX + 8 * (w - 3) + 8)) 64 = x1 := by
    rw [← hx1, show dX + 8 * (w - 3) + 8 = dX + 8 * (w - 2) by omega]
  have r0 : s.mem.readW (off B (dX + 8 * (w - 3))) 64 = x0 := hx0
  have rP : s.mem.readW (off B dT) 64 = P := hPw
  have rD : s.mem.readW (off B (dT + 8)) 64 = D := hDw
  have rV : s.mem.readW (off B (dT + 16)) 64 = V := hVw
  refine WP.mono (WP.keep quotRegs (Q := fun t =>
      t.gpr .s1 = (mgq V U2 U1 D ||| ((if 0 < D - U2 then (1 : BitVec 64) else 0) - 1#64)) ∧ t.mem = s.mem ∧
        t.gpr .t3 = off B (dX + 8 * (w - 3)) ∧ t.gpr .t4 = U2 ∧ t.gpr .t5 = U1 ∧ t.gpr .s2 = D) (by
    unfold quot quotHead quotMG quotFix
    brun [h2, h6, ht0, h4, ea, r2, r1, r0, rP, rD, rV, hU2, hU1, BitVec.add_zero,
      hs.ld (show dX + 8 * (w - 3) + 16 + 8 ≤ Z by omega),
      hs.al8 (show dX + 8 * (w - 3) + 16 + 8 ≤ Z by omega) (by omega),
      hs.ld (show dX + 8 * (w - 3) + 8 + 8 ≤ Z by omega),
      hs.al8 (show dX + 8 * (w - 3) + 8 + 8 ≤ Z by omega) (by omega),
      hs.ld (show dX + 8 * (w - 3) + 8 ≤ Z by omega),
      hs.al8 (show dX + 8 * (w - 3) + 8 ≤ Z by omega) (by omega),
      hs.ld (show dT + 8 ≤ Z by omega), hs.al8 (show dT + 8 ≤ Z by omega) a3,
      hs.ld (show dT + 8 + 8 ≤ Z by omega), hs.al8 (show dT + 8 + 8 ≤ Z by omega) (by omega),
      hs.ld (show dT + 16 + 8 ≤ Z by omega), hs.al8 (show dT + 16 + 8 ≤ Z by omega) (by omega)]
    rfl) (by rfl) (by rfl)) fun t ⟨⟨t1, tm, t3, t4, t5, ts2⟩, k⟩ =>
      ⟨⟨?_, tm, t3, by rw [t4, t5, hU2v, hU1v, Nat.div_add_mod'], ts2⟩, k⟩
  have hu2D : U / 2 ^ 64 ≤ D.toNat := by rw [hUu]; exact hXd
  have hd0 : 0 < D.toNat := by omega_using [hd]
  have hfix := WordStep.qhat_fix hd0 hu2D (Nat.mod_lt U (show 0 < 2 ^ 64 by decide))
  rw [Nat.div_add_mod'] at hfix
  rw [← hfix, t1, fix_val]
  by_cases hc : U2 = D
  · rw [ite_eq_left hc, ite_eq_left (by rw [← hU2v, hc]), BitVec.toNat_allOnes]
  · have hne : U / 2 ^ 64 ≠ D.toNat := fun h => hc (BitVec.eq_of_toNat_eq (by rw [hU2v, h]))
    rw [ite_eq_right hc, ite_eq_right hne]
    have hlt : U2.toNat < D.toNat := by rw [hU2v]; exact Nat.lt_of_le_of_ne hu2D hne
    have hq := mgq_val (v := V.toNat) (u := U2.toNat) (a := U1.toNat) hDlt hd hlt U1.isLt hv
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hq
    rw [hq, hU2v, hU1v, Nat.div_add_mod']


/-! ## `t = x 2^64 - q̂ n` -/

/-- A word of `q̂ n`: the low word of `n q + c`, and the high word of `n q`
plus the carry, the next carry. -/
theorem mul_arith (n q c : BitVec 64) :
    (n * q + c).toNat + 2 ^ 64 * (BitVec.ofNat 64 (n.toNat * q.toNat / 2 ^ 64) +
      (if n * q + c < c then 1 else 0)).toNat = n.toNat * q.toNat + c.toNat := by
  have hn := n.isLt; have hq := q.isLt; have hc := c.isLt
  have hhi : n.toNat * q.toNat / 2 ^ 64 ≤ 2 ^ 64 - 2 := by
    have := Nat.mul_le_mul (show n.toNat ≤ 2 ^ 64 - 1 by omega) (show q.toNat ≤ 2 ^ 64 - 1 by omega)
    exact Nat.le_trans (Nat.div_le_div_right (c := 2 ^ 64) this) (by decide)
  have hd := Nat.div_add_mod (n.toNat * q.toNat) (2 ^ 64)
  have hlo := Nat.mod_lt (n.toNat * q.toNat) (show 0 < 2 ^ 64 by decide)
  have e := carry_val (n * q) c
  rw [BitVec.toNat_add (BitVec.ofNat 64 _), e, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show n.toNat * q.toNat / 2 ^ 64 < 2 ^ 64 by omega)]
  rw [BitVec.toNat_mul] at e
  generalize n.toNat * q.toNat / 2 ^ 64 = hi at hhi hd ⊢
  generalize n.toNat * q.toNat % 2 ^ 64 = lo at hd hlo ⊢
  generalize n.toNat * q.toNat = P at hd ⊢
  by_cases h : 2 ^ 64 ≤ lo + c.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

/-! ## The 3-by-2 estimate -/

/-- Three words, top first. -/
def val3 (t : BitVec 64 × BitVec 64 × BitVec 64) : Nat := t.1.toNat * 2 ^ 128 + t.2.1.toNat * 2 ^ 64 + t.2.2.toNat

/-- What `quot3Head` computes from `q̂` (`s1`), `U = (u₂, u₁, u₀)` (`t4`,
`t5`, `t6`) and `D = (d₁, d₀)` (`s2`, `a0`), instruction by instruction: `q̂ D`
(`h`, `m`, `l`), and `t = U - q̂ D` (`t4`, `t5`, `t6`). -/
def sub3 (q u2 u1 u0 d1 d0 : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 :=
  let lh := BitVec.ofNat 64 (q.toNat * d0.toNat / 2 ^ 64)
  let l := q * d0
  let m := q * d1 + lh
  let h := BitVec.ofNat 64 (q.toNat * d1.toNat / 2 ^ 64) + (if m < lh then (1 : BitVec 64) else 0)
  let b0 : BitVec 64 := if u0 < l then 1 else 0
  let b1 := (if u1 < m then (1 : BitVec 64) else 0) ||| (if u1 - m < b0 then 1 else 0)
  (u2 - h - b1, u1 - m - b0, u0 - l)

/-- What `quot3Fix` adds to `t` (`t4`, `t5`, `t6`): `y = (y₁, y₀)`, with its
carries. -/
def add3 (t2 t1 t0 y1 y0 : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 :=
  let c0 : BitVec 64 := if t0 + y0 < y0 then 1 else 0
  let c1 := (if t1 + y1 < y1 then (1 : BitVec 64) else 0) ||| (if t1 + y1 + c0 < c0 then 1 else 0)
  (t2 + c1, t1 + y1 + c0, t0 + y0)

/-- What `quot3` computes: `t = U - q̂ D`, `D` added to it if negative, and
`q̂` less the two signs. -/
def q3 (q u2 u1 u0 d1 d0 : BitVec 64) : BitVec 64 :=
  let t := sub3 q u2 u1 u0 d1 d0
  let sg := t.1 >>> 63
  q - sg - (add3 t.1 t.2.1 t.2.2 (d1 &&& (0 - sg)) (d0 &&& (0 - sg))).1 >>> 63

/-- The borrow of `x - y`, by `sltu`. -/
theorem borrow_val (x y : BitVec 64) :
    (x - y).toNat + y.toNat = x.toNat + 2 ^ 64 * (if x < y then (1 : BitVec 64) else 0).toNat := by
  have hx := x.isLt; have hy := y.isLt
  by_cases h : x < y
  · rw [ite_eq_left h]; rw [BitVec.lt_def] at h
    rw [BitVec.toNat_sub, show (1 : BitVec 64).toNat = 1 from rfl]; omega
  · rw [ite_eq_right h]; rw [BitVec.lt_def] at h
    rw [BitVec.toNat_sub, show (0 : BitVec 64).toNat = 0 from rfl]; omega

theorem ite_one_le (p : Prop) [Decidable p] : (if p then (1 : BitVec 64) else 0).toNat ≤ 1 := by
  split <;> decide

/-- `x + y` with its carry `c`. -/
theorem add_carry (x y : BitVec 64) :
    (x + y).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ x.toNat + y.toNat)).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add]
  have := x.isLt; have := y.isLt
  by_cases hc : 2 ^ 64 ≤ x.toNat + y.toNat <;>
    simp only [hc, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

/-- `sub3`: `t + q̂ D = U + 2^192 b` for its borrow `b`. -/
theorem sub3_val (q u2 u1 u0 d1 d0 : BitVec 64) :
    ∃ b < 2, val3 (sub3 q u2 u1 u0 d1 d0) + q.toNat * (d1.toNat * 2 ^ 64 + d0.toNat) =
      u2.toNat * 2 ^ 128 + u1.toNat * 2 ^ 64 + u0.toNat + 2 ^ 192 * b := by
  have hqB := q.isLt; have hd0B := d0.isLt
  unfold sub3 val3
  simp only []
  -- `q̂ D = h 2^128 + m 2^64 + l`.
  have pl : (q * d0).toNat + 2 ^ 64 * (BitVec.ofNat 64 (q.toNat * d0.toNat / 2 ^ 64)).toNat =
      q.toNat * d0.toNat := by
    have hlt : q.toNat * d0.toNat < 2 ^ 128 := by
      have := Nat.mul_lt_mul_of_lt_of_le hqB (Nat.le_of_lt hd0B) (by omega)
      exact Nat.lt_of_lt_of_le this (by decide)
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := q.toNat * d0.toNat / 2 ^ 64) (by omega)]
    exact Nat.mod_add_div _ _
  generalize BitVec.ofNat 64 (q.toNat * d0.toNat / 2 ^ 64) = lh at pl ⊢
  have pm := mul_arith q d1 lh
  generalize q * d0 = l at pl ⊢
  generalize q * d1 + lh = m at pm ⊢
  generalize BitVec.ofNat 64 (q.toNat * d1.toNat / 2 ^ 64) + (if m < lh then (1 : BitVec 64) else 0) = h at pm ⊢
  have s0 := borrow_val u0 l
  generalize (if u0 < l then (1 : BitVec 64) else 0) = b0 at s0 ⊢
  have s1 := sub64_arith u1 m b0 (by have := s0; have := l.isLt; have := (u0 - l).isLt; omega)
  generalize (if u1 < m then (1 : BitVec 64) else 0) ||| (if u1 - m < b0 then 1 else 0) = b1 at s1 ⊢
  have s2 := sub64_arith u2 h b1 s1.2
  refine ⟨_, Nat.lt_succ_of_le s2.2, ?_⟩
  have hqD : q.toNat * (d1.toNat * 2 ^ 64 + d0.toNat) = q.toNat * d1.toNat * 2 ^ 64 + q.toNat * d0.toNat := by
    rw [Nat.mul_add, Nat.mul_assoc]
  rw [hqD]
  have s1' := s1.1; have s2' := s2.1
  generalize q.toNat * d1.toNat = A at pm ⊢
  generalize q.toNat * d0.toNat = A0 at pl ⊢
  omega

/-- `add3`: `t + y` modulo `2^192`, with its carry `c`. -/
theorem add3_val (t2 t1 t0 y1 y0 : BitVec 64) :
    ∃ c < 2, val3 (add3 t2 t1 t0 y1 y0) + 2 ^ 192 * c = val3 (t2, t1, t0) + (y1.toNat * 2 ^ 64 + y0.toNat) := by
  unfold add3 val3
  simp only []
  have a0 := add_carry t0 y0
  rw [← carry_val] at a0
  generalize (if t0 + y0 < y0 then (1 : BitVec 64) else 0) = c0 at a0 ⊢
  have hc0 : c0.toNat ≤ 1 := by have := (t0 + y0).isLt; have := t0.isLt; have := y0.isLt; omega
  have a1 := ModArith.add_arith t1 y1 c0 hc0
  rw [BitVec.or_comm] at a1
  generalize (if t1 + y1 < y1 then (1 : BitVec 64) else 0) ||| (if t1 + y1 + c0 < c0 then 1 else 0) = c1 at a1 ⊢
  have a2 := add_carry t2 c1
  refine ⟨(decide (2 ^ 64 ≤ t2.toNat + c1.toNat)).toNat, Nat.lt_succ_of_le (Bool.toNat_le _), ?_⟩
  have := a1.1
  omega

/-- The top half of three words: their top word's top bit. -/
theorem val3_top (t : BitVec 64 × BitVec 64 × BitVec 64) : 2 ^ 192 / 2 ≤ val3 t ↔ 2 ^ 63 ≤ t.1.toNat := by
  unfold val3
  have := t.2.1.isLt; have := t.2.2.isLt
  omega

theorem val3_lt (t : BitVec 64 × BitVec 64 × BitVec 64) : val3 t < 2 ^ 192 := by
  unfold val3
  have := t.1.isLt; have := t.2.1.isLt; have := t.2.2.isLt
  omega

/-- `x >>> 63`, the sign. -/
theorem shr63_val (x : BitVec 64) : (x >>> 63).toNat = if 2 ^ 63 ≤ x.toNat then 1 else 0 := by
  rw [shr63_toNat, BitVec.toNat_ofNat]
  by_cases h : 2 ^ 63 ≤ x.toNat <;> simp [h]

/-- `q3`: `min(⌊U / D⌋, 2^64 - 1)` from an estimate `q̂` at most 2 above it,
for `U < (2^64 + 1) D` (`WordStep.quot3_val`). -/
theorem q3_val {q u2 u1 u0 d1 d0 : BitVec 64} (hD : 0 < d1.toNat * 2 ^ 64 + d0.toNat)
    (hUD : u2.toNat * 2 ^ 128 + u1.toNat * 2 ^ 64 + u0.toNat < (2 ^ 64 + 1) * (d1.toNat * 2 ^ 64 + d0.toNat))
    (hge : min ((u2.toNat * 2 ^ 128 + u1.toNat * 2 ^ 64 + u0.toNat) / (d1.toNat * 2 ^ 64 + d0.toNat))
      (2 ^ 64 - 1) ≤ q.toNat)
    (hle : q.toNat ≤ min ((u2.toNat * 2 ^ 128 + u1.toNat * 2 ^ 64 + u0.toNat) / (d1.toNat * 2 ^ 64 + d0.toNat))
      (2 ^ 64 - 1) + 2) :
    (q3 q u2 u1 u0 d1 d0).toNat =
      min ((u2.toNat * 2 ^ 128 + u1.toNat * 2 ^ 64 + u0.toNat) / (d1.toNat * 2 ^ 64 + d0.toNat)) (2 ^ 64 - 1) := by
  obtain ⟨b, hb, h1⟩ := sub3_val q u2 u1 u0 d1 d0
  unfold q3
  simp only []
  generalize sub3 q u2 u1 u0 d1 d0 = t at h1 ⊢
  obtain ⟨t2, t1, t0⟩ := t
  simp only [] at h1 ⊢
  have hmask : (0 : BitVec 64) - t2 >>> 63 = if decide (2 ^ 63 ≤ t2.toNat) then BitVec.allOnes 64 else 0 := by
    rw [shr63_toNat]; cases decide (2 ^ 63 ≤ t2.toNat) <;> rfl
  rw [hmask, ModArith.and_mask, ModArith.and_mask]
  obtain ⟨c, hc, h2⟩ := add3_val t2 t1 t0 (if decide (2 ^ 63 ≤ t2.toNat) then d1 else 0)
    (if decide (2 ^ 63 ≤ t2.toNat) then d0 else 0)
  generalize add3 t2 t1 t0 (if decide (2 ^ 63 ≤ t2.toNat) then d1 else 0)
    (if decide (2 ^ 63 ≤ t2.toNat) then d0 else 0) = a at h2 ⊢
  have hy : ((if decide (2 ^ 63 ≤ t2.toNat) then d1 else 0).toNat * 2 ^ 64 +
      (if decide (2 ^ 63 ≤ t2.toNat) then d0 else 0).toNat) =
      if 2 ^ 192 / 2 ≤ val3 (t2, t1, t0) then d1.toNat * 2 ^ 64 + d0.toNat else 0 := by
    by_cases h : 2 ^ 63 ≤ t2.toNat
    · have h' := (val3_top (t2, t1, t0)).mpr h
      simp only [h, h', decide_true, ite_true]
    · have h' := mt (val3_top (t2, t1, t0)).mp h
      simp only [h, h', decide_false, ite_false, Bool.false_eq_true]
      rfl
  rw [hy] at h2
  have hv := WordStep.quot3_val (W := 2 ^ 192) hD (by have := d1.isLt; have := d0.isLt; omega) hUD hge hle q.isLt
    (val3_lt _) hb h1 (val3_lt _) hc h2
  simp only [val3_top] at hv
  rw [BitVec.toNat_sub, BitVec.toNat_sub, shr63_val, shr63_val]
  generalize min ((u2.toNat * 2 ^ 128 + u1.toNat * 2 ^ 64 + u0.toNat) / (d1.toNat * 2 ^ 64 + d0.toNat))
    (2 ^ 64 - 1) = Q at hv ⊢
  have := q.isLt
  by_cases e1 : 2 ^ 63 ≤ t2.toNat <;> by_cases e2 : 2 ^ 63 ≤ a.1.toNat <;>
    simp only [e1, e2, ite_true, ite_false] at hv ⊢ <;> omega


/-- The registers `quot3` writes. -/
def quot3Regs : List Reg := [.a0, .a3, .t4, .t5, .t6, .s0, .s1, .s3, .s4]

/-- `quot3`, after `quot` (`x`'s word `x₀ = x_(w-3)` at `t3`, the top two
words `(u₂, u₁)` of `U = ⌊x P / 2^(64 (w - 3))⌋` in `t4`, `t5`, and `d'` in
`s2`), with `D = (d', d'ₗ)` (`d'ₗ` in the temporary's word 3) and an
estimate `q̂` in `s1` at most 2 above `Q = min(⌊U / D⌋, 2^64 - 1)`: `Q` in
`s1`. -/
theorem quot3_ok {s : State} {B : Addr} {Z dX dT w z D : Nat} (hs : Scr s B Z)
    (h3 : s.gpr .t3 = off B (dX + 8 * (w - 3))) (h6 : s.gpr .a6 = off B dT) (h4 : s.gpr .a4 = 0)
    (hw : 4 ≤ w) (hw' : w < 2 ^ 31) (hX8 : dX % 8 = 0) (hT8 : dT % 8 = 0) (hXZ : dX + 8 * (w + 1) ≤ Z) (hTZ : dT + 32 ≤ Z)
    (hP : (Mont.word s.mem B dT).toNat = 2 ^ z) (hz : z ≤ 63)
    (hU : (s.gpr .t4).toNat * 2 ^ 64 + (s.gpr .t5).toNat =
      wordsVal s.mem B dX w * 2 ^ z / 2 ^ (64 * (w - 2)))
    (hD : (s.gpr .s2).toNat * 2 ^ 64 + (Mont.word s.mem B (dT + 24)).toNat = D) (hD0 : 0 < D)
    (hUD : wordsVal s.mem B dX w * 2 ^ z / 2 ^ (64 * (w - 3)) < (2 ^ 64 + 1) * D)
    (hge : min (wordsVal s.mem B dX w * 2 ^ z / 2 ^ (64 * (w - 3)) / D) (2 ^ 64 - 1) ≤ (s.gpr .s1).toNat)
    (hle : (s.gpr .s1).toNat ≤ min (wordsVal s.mem B dX w * 2 ^ z / 2 ^ (64 * (w - 3)) / D) (2 ^ 64 - 1) + 2) :
    WP isa (.block quot3) s fun t => ((t.gpr .s1).toNat =
      min (wordsVal s.mem B dX w * 2 ^ z / 2 ^ (64 * (w - 3)) / D) (2 ^ 64 - 1) ∧ t.mem = s.mem) ∧
      Keep quot3Regs s t := by
  have hnw := hs.nowrap
  have a1 := hX8; have a3 := hT8
  generalize hPw : Mont.word s.mem B (dT) = P at hP
  generalize hdw : Mont.word s.mem B (dT + 24) = d0 at hD
  generalize hx0 : Mont.word s.mem B (dX + 8 * (w - 3)) = x0
  generalize hxm : Mont.word s.mem B (dX + 8 * (w - 4)) = xm
  have ea : off B (dX + 8 * (w - 3)) - BitVec.ofNat 64 8 = off B (dX + 8 * (w - 4)) := by
    rw [off_sub _ (by omega)]; congr 1; omega
  have rP : s.mem.readW (off B dT) 64 = P := hPw
  have rd : s.mem.readW (off B (dT + 24)) 64 = d0 := hdw
  have r0 : s.mem.readW (off B (dX + 8 * (w - 3))) 64 = x0 := hx0
  have rm : s.mem.readW (off B (dX + 8 * (w - 4))) 64 = xm := hxm
  refine WP.mono (WP.keep quot3Regs (Q := fun t =>
      t.gpr .s1 = q3 (s.gpr .s1) (s.gpr .t4) (s.gpr .t5)
        (x0 * P + BitVec.ofNat 64 (xm.toNat * P.toNat / 2 ^ 64)) (s.gpr .s2) d0 ∧ t.mem = s.mem) (by
    unfold quot3 quot3Head quot3Fix
    brun [h3, h6, h4, ea, rP, rd, r0, rm, BitVec.add_zero,
      hs.ld (show dT + 8 ≤ Z by omega), hs.al8 (show dT + 8 ≤ Z by omega) a3,
      hs.ld (show dT + 24 + 8 ≤ Z by omega), hs.al8 (show dT + 24 + 8 ≤ Z by omega) (by omega),
      hs.ld (show dX + 8 * (w - 3) + 8 ≤ Z by omega),
      hs.al8 (show dX + 8 * (w - 3) + 8 ≤ Z by omega) (by omega),
      hs.ld (show dX + 8 * (w - 4) + 8 ≤ Z by omega),
      hs.al8 (show dX + 8 * (w - 4) + 8 ≤ Z by omega) (by omega)]
    rfl) (by rfl) (by rfl)) fun t ⟨⟨t1, tm⟩, k⟩ => ⟨⟨?_, tm⟩, k⟩
  -- `U = (u₂, u₁, u₀)`, `u₀ = x₀ P + ⌊x₋₁ P / 2^64⌋ mod 2^64`.
  generalize hK : 64 * (w - 4) = K
  have hk3 : 64 * (w - 3) = K + 64 := by omega
  have hk2 : 64 * (w - 2) = K + 64 + 64 := by omega
  rw [hk3] at hUD hge hle ⊢
  rw [hk2] at hU
  generalize hX : wordsVal s.mem B dX w = X at hU hUD hge hle ⊢
  have hXe : X = (Mont.word s.mem B (dX + 8 * (w - 1))).toNat * 2 ^ 64 * 2 ^ (K + 64 + 64) +
      (Mont.word s.mem B (dX + 8 * (w - 2))).toNat * 2 ^ (K + 64 + 64) +
      x0.toNat * 2 ^ (K + 64) + xm.toNat * 2 ^ K + wordsVal s.mem B dX (w - 4) := by
    have f1 := top_two s.mem B dX (w := w) (by omega)
    have f2 := wordsVal_succ_top s.mem B dX (w - 3)
    have f3 := wordsVal_succ_top s.mem B dX (w - 4)
    rw [hX, show 64 * (w - 2) = K + 64 + 64 by omega] at f1
    rw [show w - 3 + 1 = w - 2 by omega, hx0, hk3] at f2
    rw [show w - 4 + 1 = w - 3 by omega, hxm, hK] at f3
    rw [f1, f2, f3, Nat.mul_comm (2 ^ (K + 64)), Nat.mul_comm (2 ^ K), Nat.mul_assoc _ (2 ^ 64), ← Nat.pow_add,
      show 64 + (K + 64 + 64) = K + 64 + 64 + 64 by omega]
    generalize (Mont.word s.mem B (dX + 8 * (w - 1))).toNat * 2 ^ (K + 64 + 64 + 64) = a
    generalize (Mont.word s.mem B (dX + 8 * (w - 2))).toNat * 2 ^ (K + 64 + 64) = b
    generalize x0.toNat * 2 ^ (K + 64) = c
    generalize xm.toNat * 2 ^ K = d
    omega
  have hlow := wordsVal_lt s.mem B dX (w - 4)
  rw [hK] at hlow
  have hU3 : X * 2 ^ z / 2 ^ (K + 64) = ((Mont.word s.mem B (dX + 8 * (w - 1))).toNat * 2 ^ 64 +
      (Mont.word s.mem B (dX + 8 * (w - 2))).toNat) * 2 ^ z * 2 ^ 64 +
      (x0.toNat * 2 ^ z + xm.toNat * 2 ^ z / 2 ^ 64) := by
    rw [hXe, ← top3_shift (by omega) hlow, Nat.add_mul _ _ (2 ^ (K + 64 + 64))]
  generalize hU3d : X * 2 ^ z / 2 ^ (K + 64) = U at hU3 hUD hge hle ⊢
  have hUu : U / 2 ^ 64 = X * 2 ^ z / 2 ^ (K + 64 + 64) := by
    rw [← hU3d, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have hpz : 2 ^ z ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) hz
  have hfm : xm.toNat * 2 ^ z / 2 ^ 64 < 2 ^ 64 := by
    have : xm.toNat * 2 ^ z / 2 ^ 64 < 2 ^ z := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64), Nat.mul_comm (2 ^ z)]
      exact Nat.mul_lt_mul_of_pos_right xm.isLt (Nat.two_pow_pos z)
    omega
  have hu0 : (x0 * P + BitVec.ofNat 64 (xm.toNat * P.toNat / 2 ^ 64)).toNat = U % 2 ^ 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, hP, Nat.mod_eq_of_lt hfm, Nat.mod_add_mod, hU3,
      Nat.add_comm _ (x0.toNat * 2 ^ z + _), Nat.add_mul_mod_self_right]
  have hUe : U = (s.gpr .t4).toNat * 2 ^ 128 + (s.gpr .t5).toNat * 2 ^ 64 +
      (x0 * P + BitVec.ofNat 64 (xm.toNat * P.toNat / 2 ^ 64)).toNat := by
    rw [hu0]
    have := Nat.div_add_mod U (2 ^ 64)
    rw [hUu, ← hU, Nat.mul_add, Nat.mul_comm (2 ^ 64) (_ * 2 ^ 64), Nat.mul_comm (2 ^ 64) (s.gpr .t5).toNat,
      Nat.mul_assoc, ← Nat.pow_add] at this
    exact this.symm
  rw [hUe, ← hD] at hUD hge hle ⊢
  rw [t1]
  exact q3_val (by rw [hD]; exact hD0) hUD hge hle


end VG.Proof.Bignum.RISCV64
