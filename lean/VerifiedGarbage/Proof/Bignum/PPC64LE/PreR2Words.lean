module

public import VerifiedGarbage.Impl.Bignum.PPC64LE.Precompute
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.Mont.Words32
public meta import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
public meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish64
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.WordStepNorm
import VerifiedGarbage.Proof.Bignum.WordStep
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `R² mod n` by word steps of long division on PPC64LE

`vg_rsa_public_precompute`'s `R² mod n` (`r2Fast`) for any `n` of `w ≥ 4`
words whose top word is not zero, in the working space of `vg_rsa_mont_mul`
(`n` in array 0, `x` in array 1, the accumulator and the temporary in arrays
2 and 3), from its pieces:

* `norm_ok`: `P = 2^z`, `d' = ⌊n P / 2^(64 (w - 1))⌋ ≥ 2^63` and the word
  below it, `(d', d'ₗ) = ⌊n P / 2^(64 (w - 2))⌋`, in the temporary;
* `recip_ok`: `v = ⌊(2^128 - 1) / d'⌋ - 2^64` there, by restoring division
  (`divLoop_ok`, `WordStep.recip_eq`);
* `quot_ok`: the estimate `min(⌊u / d'⌋, 2^64 - 1)` from the top two words
  `u` of `x P`, by Möller and Granlund's division (`mgqP_val`);
* `quot3_ok`: corrected by the top three words `U` of `x P` and `D = (d',
  d'ₗ)` to `q̂ = min(⌊U / D⌋, 2^64 - 1)` (`WordStep.quot3_val`), so that
  `q ≤ q̂ ≤ q + 1` for `q = ⌊x 2^64 / n⌋` (`WordStep.qhat3_norm`);
* `mulSub_ok`, `addBack_ok`: `t = x 2^64 - q̂ n` in place of `x` (`q̂ n`'s
  carry and the difference's borrow in registers), then `n` added once if
  it is negative (`WordStep.wordStepQ1_val`);
* `wordStep_ok`: `x := x 2^64 mod n`, and `wordSteps_ok`, `w + 1` of them.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE
open VG.Impl.Bignum.PPC64LE.Precompute VG.Proof.Bignum.WordStep

/-! ## Normalization -/

/-- The mask of `normStep`: all ones if `x`'s top bit is clear. -/
theorem norm_mask (x : BitVec 64) :
    BitVec.ofNat 64 0 - (x >>> 63 ^^^ BitVec.ofNat 64 1) =
      if x.toNat < 2 ^ 63 then BitVec.allOnes 64 else 0 := by
  have hx := x.isLt
  by_cases h : x.toNat < 2 ^ 63
  · have e : x >>> 63 = BitVec.ofNat 64 0 := BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]; omega_using [h])
    rw [e, ite_eq_left_iff.mpr fun h' => absurd h h']
    decide
  · have e : x >>> 63 = BitVec.ofNat 64 1 := BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]; omega_using [h, hx])
    rw [e, ite_eq_right_iff.mpr fun h' => absurd h' h]
    decide

theorem mask_add (x : BitVec 64) (c : Prop) [Decidable c] :
    x + (x &&& (if c then BitVec.allOnes 64 else 0)) = if c then x + x else x := by
  split
  · rw [BitVec.and_allOnes]
  · rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.and_zero, BitVec.add_zero]

/-- A step of `normStep` on `x = T 2^j`, `p = 2^j`: `j` grows while `x`'s top
bit is clear. -/
theorem norm_inv_step {x p : BitVec 64} {T j i : Nat} (hj : j ≤ i) (hi : i < 63) (hp : p.toNat = 2 ^ j)
    (hx : x.toNat = T * 2 ^ j) (hc : j = i ∨ 2 ^ 63 ≤ T * 2 ^ j) :
    ∃ j' ≤ i + 1, (if x.toNat < 2 ^ 63 then p + p else p).toNat = 2 ^ j' ∧
      (if x.toNat < 2 ^ 63 then x + x else x).toNat = T * 2 ^ j' ∧ (j' = i + 1 ∨ 2 ^ 63 ≤ T * 2 ^ j') := by
  by_cases h : x.toNat < 2 ^ 63
  · simp only [h, ite_true]
    have hji : j = i := by omega_using [hc, h, hx]
    have hpj : 2 ^ j ≤ 2 ^ 62 := Nat.pow_le_pow_right (by decide) (by omega_using [hji, hi])
    refine ⟨j + 1, by omega_using [hj], ?_, ?_, Or.inl (by omega_using [hji])⟩
    · have e2 : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [Nat.pow_succ, Nat.mul_two]
      rw [BitVec.toNat_add, hp, e2]
      generalize 2 ^ j = a at hpj ⊢
      omega_using [hpj]
    · have e2 : T * 2 ^ (j + 1) = T * 2 ^ j + T * 2 ^ j := by rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]
      rw [BitVec.toNat_add, hx, e2]
      rw [hx] at h
      generalize T * 2 ^ j = a at h ⊢
      omega_using [h]
  · simp only [h, ite_false]
    exact ⟨j, by omega_using [hj], hp, hx, Or.inr (by omega_using [h, hx])⟩

/-- `4 (2 w) + d - c`: a word near the top of `w` words at `d`. -/
theorem ea_top (B : Addr) {d w c : Nat} (hc : c ≤ 8 * w) :
    BitVec.ofNat 64 (2 * w) <<< 2 + off B d - BitVec.ofNat 64 c = off B (d + 8 * w - c) := by
  rw [BitVec.sub_eq_iff_eq_add, ofNat_shl2', off, off, BitVec.add_assoc, ← BitVec.ofNat_add,
    Nat.sub_add_cancel (by omega_using [hc]), BitVec.add_comm, BitVec.add_assoc, ← BitVec.ofNat_add,
    show d + 4 * (2 * w) = d + 8 * w by omega_using []]

/-- The registers `norm` writes. -/
def normRegs : List Reg := [.r0, .r3, .r6, .r14, .r15, .r16, .r17, .r20, .r22]

/-- `norm`, `n` (`w ≥ 3` words, its top word not zero) at `r10` and the
temporary at `r9`: `P = 2^z`, `d' = ⌊n P / 2^(64 (w - 1))⌋ ≥ 2^63` and `d'ₗ`,
`(d', d'ₗ) = ⌊n P / 2^(64 (w - 2))⌋`, in the temporary's words 0, 1 and 3. -/
theorem norm_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (h9 : s.gpr .r9 = off B (slot w 3)) (h10 : s.gpr .r10 = off B (slot w 0))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 3 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z)
    (hT : 2 ^ (64 * (w - 1)) ≤ wordsVal s.mem B (slot w 0) w) :
    WP isa norm s fun t => (∃ z ≤ 63, (Mont.word t.mem B (slot w 3)).toNat = 2 ^ z ∧
      (Mont.word t.mem B (slot w 3 + 8)).toNat = wordsVal s.mem B (slot w 0) w * 2 ^ z / 2 ^ (64 * (w - 1)) ∧
      2 ^ 63 ≤ wordsVal s.mem B (slot w 0) w * 2 ^ z / 2 ^ (64 * (w - 1)) ∧
      (Mont.word t.mem B (slot w 3 + 8)).toNat * 2 ^ 64 + (Mont.word t.mem B (slot w 3 + 24)).toNat =
        wordsVal s.mem B (slot w 0) w * 2 ^ z / 2 ^ (64 * (w - 2))) ∧
      Mont.Outside B (slot w 3) 32 s.mem t.mem ∧ Keep normRegs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e3 := e 3; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  -- `n`'s top two words.
  generalize hTw : Mont.word s.mem B (slot w 0 + 8 * (w - 1)) = T
  generalize hLw : Mont.word s.mem B (slot w 0 + 8 * (w - 2)) = L
  generalize hL'w : Mont.word s.mem B (slot w 0 + 8 * (w - 3)) = L'
  have hN : wordsVal s.mem B (slot w 0) w =
      T.toNat * 2 ^ (64 * (w - 2) + 64) + L.toNat * 2 ^ (64 * (w - 2)) + wordsVal s.mem B (slot w 0) (w - 2) := by
    have e1 := wordsVal_succ_top s.mem B (slot w 0) (w - 1)
    have e2 := wordsVal_succ_top s.mem B (slot w 0) (w - 2)
    rw [show w - 1 + 1 = w by omega, hTw] at e1
    rw [show w - 2 + 1 = w - 1 by omega, hLw] at e2
    rw [e1, e2, show 64 * (w - 1) = 64 * (w - 2) + 64 by omega, Nat.mul_comm T.toNat, Nat.mul_comm L.toNat]
    generalize 2 ^ (64 * (w - 2) + 64) * T.toNat = a
    generalize 2 ^ (64 * (w - 2)) * L.toNat = b
    omega_using []
  have hT0 : 0 < T.toNat := by
    rcases Nat.eq_zero_or_pos T.toNat with h | h
    · have hl := wordsVal_lt s.mem B (slot w 0) (w - 2)
      have hL := Nat.mul_le_mul_right (2 ^ (64 * (w - 2))) (show L.toNat + 1 ≤ 2 ^ 64 from L.isLt)
      rw [Nat.add_mul, Nat.one_mul, ← Nat.pow_add, show 64 + 64 * (w - 2) = 64 * (w - 2) + 64 by omega] at hL
      rw [hN, h, Nat.zero_mul, Nat.zero_add, show 64 * (w - 1) = 64 * (w - 2) + 64 by omega] at hT
      generalize L.toNat * 2 ^ (64 * (w - 2)) = a at hT hL
      generalize 2 ^ (64 * (w - 2) + 64) = b at hT hL
      generalize 2 ^ (64 * (w - 2)) = c at hl hL
      omega_using [hT, hL, hl]
    · exact h
  unfold norm
  have ea := ea_top B (d := slot w 0) (w := w) (c := 16) (by omega)
  rw [show slot w 0 + 8 * w - 16 = slot w 0 + 8 * (w - 2) by omega] at ea
  refine WP.seq (WP.mono (WP.keep [.r6, .r14, .r15, .r16, .r17, .r20, .r22] (Q := fun t =>
      t.gpr .r15 = T ∧ t.gpr .r16 = L ∧ t.gpr .r6 = BitVec.ofNat 64 1 ∧ t.gpr .r20 = BitVec.ofNat 64 0 ∧
        t.gpr .r22 = BitVec.ofNat 64 1 ∧ t.gpr .r17 = BitVec.ofNat 64 63 ∧ t.mem = s.mem ∧
        t.gpr .r14 = off B (slot w 0 + 8 * (w - 2))) (by
      unfold normHead
      prun [h10, h11, ea, hs.ld (show slot w 0 + 8 * (w - 2) + 8 + 8 ≤ Z by omega),
        hs.ld (show slot w 0 + 8 * (w - 2) + 8 ≤ Z by omega)]
      exact ⟨by rw [← hTw, show slot w 0 + 8 * (w - 2) + 8 = slot w 0 + 8 * (w - 1) by omega], hLw⟩) (by decide)) fun s₁ ⟨⟨a15, a16, a6, a20, a22, a17, m1, a14⟩, k1⟩ => ?_)
  -- 63 steps of `normStep`.
  let Inv : Nat → State → Prop := fun i t =>
    (∃ j ≤ i, (t.gpr .r6).toNat = 2 ^ j ∧ (t.gpr .r15).toNat = T.toNat * 2 ^ j ∧
      (j = i ∨ 2 ^ 63 ≤ T.toNat * 2 ^ j)) ∧ t.gpr .r16 = L ∧ t.gpr .r20 = BitVec.ofNat 64 0 ∧
      t.gpr .r22 = BitVec.ofNat 64 1 ∧ t.mem = s.mem ∧ Keep normRegs s₁ t ∧
      t.gpr .r14 = off B (slot w 0 + 8 * (w - 2))
  refine WP.seq (WP.mono (wp_countdown (body := .block (normStep ++ ([.subi .r17 .r17 1] : List Instr)))
    (cnt := .r17) (N := 63) (by decide) (by decide) Inv (fun i hi t ⟨⟨j, hj, jp, jx, jc⟩, j16, j20, j22, jm, jk, j14⟩ hc => ?_)
    ⟨⟨0, Nat.le_refl _, by rw [a6]; rfl, by rw [a15, Nat.pow_zero, Nat.mul_one], Or.inl rfl⟩, a16, a20, a22, m1,
      Keep.refl _ _, a14⟩ a17) fun t ⟨⟨j, hj, jp, jx, jc⟩, j16, _, _, jm, jk, j14⟩ => ?_)
  · have hst : WP isa (.block (normStep ++ ([.subi .r17 .r17 1] : List Instr))) t fun t' =>
        (t'.gpr .r6 = (if (t.gpr .r15).toNat < 2 ^ 63 then t.gpr .r6 + t.gpr .r6 else t.gpr .r6) ∧
          t'.gpr .r15 = (if (t.gpr .r15).toNat < 2 ^ 63 then t.gpr .r15 + t.gpr .r15 else t.gpr .r15) ∧
          t'.mem = t.mem ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1) ∧ Keep [.r0, .r3, .r6, .r15, .r17] t t' := by
      refine WP.keep _ ?_ (by decide)
      unfold normStep
      prun [j20, j22, norm_mask, mask_add]
    refine WP.mono hst fun t' ⟨⟨u6, u15, um, u17⟩, uk⟩ => ⟨⟨?_, ?_, ?_, ?_, by rw [um, jm], jk.trans' (uk.mono (by decide)),
      by rw [uk.gpr .r14 (by decide), j14]⟩, u17⟩
    · rw [u6, u15]
      exact norm_inv_step hj (by omega) jp jx jc
    · rw [uk.gpr .r16 (by decide), j16]
    · rw [uk.gpr .r20 (by decide), j20]
    · rw [uk.gpr .r22 (by decide), j22]
  -- `d'` and `P` into the temporary.
  have hTP : 2 ^ 63 ≤ T.toNat * 2 ^ j := by
    rcases jc with rfl | h
    · exact Nat.le_mul_of_pos_left _ hT0
    · exact h
  have hj63 : j ≤ 63 := hj
  have hs₂ := hs.congr (k1.trans jk).wr
  have t9 : t.gpr .r9 = off B (slot w 3) := ((k1.trans jk).gpr .r9 (by decide)).trans h9
  have hLP : L.toNat * 2 ^ j / 2 ^ 64 < 2 ^ j := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64), Nat.mul_comm (2 ^ j)]
    exact Nat.mul_lt_mul_of_pos_right L.isLt (Nat.two_pow_pos j)
  have hpj : 2 ^ j ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) hj63
  have hL'P : L'.toNat * 2 ^ j / 2 ^ 64 < 2 ^ j := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64), Nat.mul_comm (2 ^ j)]
    exact Nat.mul_lt_mul_of_pos_right L'.isLt (Nat.two_pow_pos j)
  have ea8 : off B (slot w 0 + 8 * (w - 2)) - BitVec.ofNat 64 8 = off B (slot w 0 + 8 * (w - 3)) := by
    rw [show slot w 0 + 8 * (w - 2) = slot w 0 + 8 * (w - 3) + 8 by omega]
    simp only [off, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_sub_cancel]
  have rL' : t.mem.readW (off B (slot w 0 + 8 * (w - 3))) 64 = L' := by
    rw [jm]; exact hL'w
  generalize hd' : t.gpr .r15 + BitVec.ofNat 64 (L.toNat * (t.gpr .r6).toNat / 2 ^ 64) = D
  generalize hdl : L * t.gpr .r6 + BitVec.ofNat 64 (L'.toNat * (t.gpr .r6).toNat / 2 ^ 64) = Dl
  refine WP.mono (WP.keep [.r0, .r3, .r15, .r16] (Q := fun u => u.mem = ((t.mem.writeW (off B (slot w 3))
      (t.gpr .r6)).writeW (off B (slot w 3 + 8)) D).writeW (off B (slot w 3 + 24)) Dl) (by
    unfold normTail
    mcrun [j16, j14, t9, hd', hdl, ea8, rL', hs₂.ld (show slot w 0 + 8 * (w - 3) + 8 ≤ Z by omega),
      hs₂.st (show slot w 3 + 8 ≤ Z by omega), hs₂.st (show slot w 3 + 8 + 8 ≤ Z by omega),
      hs₂.st (show slot w 3 + 24 + 8 ≤ Z by omega)])
    (by decide)) fun u ⟨um, uk⟩ => ⟨⟨j, hj63, ?_, ?_⟩, ?_, (k1.trans (jk.trans uk)).mono (by decide)⟩
  · rw [um, Mont.Outside.word (writeW_outside _ B _ (by omega)) (by omega) (by omega),
      Mont.Outside.word (writeW_outside _ B _ (by omega)) (by omega) (by omega), Mont.word_writeW_self, jp]
  · have hNv : wordsVal s.mem B (slot w 0) w * 2 ^ j / 2 ^ (64 * (w - 1)) =
        T.toNat * 2 ^ j + L.toNat * 2 ^ j / 2 ^ 64 := by
      rw [hN, show 64 * (w - 1) = 64 * (w - 2) + 64 by omega]
      exact top_shift (by omega) (wordsVal_lt _ _ _ _)
    have hD : D.toNat = T.toNat * 2 ^ j + L.toNat * 2 ^ j / 2 ^ 64 := by
      have hlt := shl_add_lt (by omega) (show T.toNat * 2 ^ j < 2 ^ 64 by rw [← jx]; exact (t.gpr .r15).isLt) hLP
      rw [← hd', BitVec.toNat_add, BitVec.toNat_ofNat, jx, jp, Nat.mod_eq_of_lt (by omega_using [hLP, hpj] :
        L.toNat * 2 ^ j / 2 ^ 64 < 2 ^ 64), Nat.mod_eq_of_lt hlt]
    -- `d'ₗ = L P mod 2^64 + ⌊L' P / 2^64⌋`, which does not wrap.
    have e64 : (2 : Nat) ^ 64 = 2 ^ (64 - j) * 2 ^ j := by rw [← Nat.pow_add]; congr 1; omega
    have hLm : L.toNat * 2 ^ j % 2 ^ 64 = L.toNat % 2 ^ (64 - j) * 2 ^ j := by
      rw [e64, Nat.mul_mod_mul_right]
    have hLm' : L.toNat % 2 ^ (64 - j) * 2 ^ j < 2 ^ 64 := by
      rw [e64]; exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.two_pow_pos j)
    have hDl : Dl.toNat = L.toNat * 2 ^ j % 2 ^ 64 + L'.toNat * 2 ^ j / 2 ^ 64 := by
      rw [← hdl, BitVec.toNat_add, BitVec.toNat_mul, jp, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show L'.toNat * 2 ^ j / 2 ^ 64 < 2 ^ 64 by omega_using [hL'P, hpj]), hLm]
      exact Nat.mod_eq_of_lt (shl_add_lt (by omega) hLm' hL'P)
    -- `n`'s top three words.
    have hN3 : wordsVal s.mem B (slot w 0) w = T.toNat * 2 ^ (64 * (w - 3) + 64 + 64) +
        L.toNat * 2 ^ (64 * (w - 3) + 64) + L'.toNat * 2 ^ (64 * (w - 3)) + wordsVal s.mem B (slot w 0) (w - 3) := by
      have e2 := wordsVal_succ_top s.mem B (slot w 0) (w - 3)
      rw [show w - 3 + 1 = w - 2 by omega, hL'w] at e2
      rw [hN, e2, show 64 * (w - 2) = 64 * (w - 3) + 64 by omega, Nat.mul_comm (2 ^ (64 * (w - 3)))]
      omega
    have hNv2 : wordsVal s.mem B (slot w 0) w * 2 ^ j / 2 ^ (64 * (w - 2)) =
        T.toNat * 2 ^ j * 2 ^ 64 + (L.toNat * 2 ^ j + L'.toNat * 2 ^ j / 2 ^ 64) := by
      rw [hN3, show 64 * (w - 2) = 64 * (w - 3) + 64 by omega]
      exact top3_shift (by omega) (wordsVal_lt _ _ _ _)
    have hLd := Nat.div_add_mod (L.toNat * 2 ^ j) (2 ^ 64)
    have w8 : Mont.word u.mem B (slot w 3 + 8) = D := by
      rw [um, Mont.Outside.word (writeW_outside _ B _ (by omega)) (by omega) (by omega), Mont.word_writeW_self]
    have w24 : Mont.word u.mem B (slot w 3 + 24) = Dl := by rw [um, Mont.word_writeW_self]
    rw [hNv, w8]
    refine ⟨hD, by omega_using [hTP], ?_⟩
    rw [w24, hD, hDl, hNv2, Nat.add_mul, Nat.mul_comm (L.toNat * 2 ^ j / 2 ^ 64)]
    omega_using [hLd]
  · rw [um, ← jm]
    exact (((writeW_outside _ B _ (by omega)).mono (by omega) (by omega)).trans
      ((writeW_outside _ B _ (by omega)).mono (by omega) (by omega))).trans
      ((writeW_outside _ B _ (by omega)).mono (by omega) (by omega))

/-! ## The estimate of the quotient -/

theorem shr63_val (x : BitVec 64) : (x >>> 63).toNat = x.toNat / 2 ^ 63 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- The quotient bit of `divBit`, from the remainder's top bit `r >>> 63` and
the carry of `r₁ - d` (`r₁ = 2 r + b` modulo `2^64`): whether `d ≤ 2 r + b`. -/
theorem divBit_bit (r c d : BitVec 64) :
    (r >>> 63 ||| BitVec.ofNat 64 ((BitVec.ofNat 64 0).toNat + (decide (18446744073709551615 ≤
      (r + r + c >>> 63).toNat + (18446744073709551616 - 1 - d.toNat))).toNat)) =
      BitVec.ofNat 64 (if d.toNat ≤ 2 * r.toNat + c.toNat / 2 ^ 63 then 1 else 0) := by
  have hR := r.isLt; have hc := c.isLt
  have hcb : c.toNat / 2 ^ 63 < 2 := by omega_using [hc]
  have hr1 : (r + r + c >>> 63).toNat = (2 * r.toNat + c.toNat / 2 ^ 63) % 2 ^ 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, shr63_val]; omega_using [hcb]
  rw [hr1]
  by_cases h1 : r.toNat < 2 ^ 63
  · have e : r >>> 63 = 0#64 := BitVec.eq_of_toNat_eq (by rw [shr63_val]; show _ = 0; omega_using [h1])
    rw [e, BitVec.zero_or, Nat.mod_eq_of_lt (by omega_using [h1, hcb])]
    congr 1
    by_cases h2 : d.toNat ≤ 2 * r.toNat + c.toNat / 2 ^ 63
    · rw [decide_eq_true (by omega_using [h2, d.isLt]), ite_eq_left_iff.mpr fun h => absurd h2 h]; rfl
    · rw [decide_eq_false (by omega_using [h2, d.isLt]), ite_eq_right_iff.mpr fun h => absurd h h2]; rfl
  · have e : r >>> 63 = BitVec.ofNat 64 1 := BitVec.eq_of_toNat_eq (by
      rw [shr63_val, BitVec.toNat_ofNat]; omega_using [h1, hR])
    rw [e, ite_eq_left_iff.mpr fun h => absurd (by omega_using [h1, d.isLt]) h]
    by_cases h3 : 18446744073709551615 ≤ (2 * r.toNat + c.toNat / 2 ^ 63) % 2 ^ 64 + (18446744073709551616 - 1 - d.toNat)
    · rw [decide_eq_true h3]; decide
    · rw [decide_eq_false h3]; decide

/-- `divBit`'s remainder and quotient, for `r < d`: a step of restoring
division (`WordStep.divBit_inv`). -/
theorem divBit_val (r c d q : BitVec 64) (hr : r.toNat < d.toNat) (hq : q.toNat < 2 ^ 63) :
    (r + r + c >>> 63 - (d &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64
      (if d.toNat ≤ 2 * r.toNat + c.toNat / 2 ^ 63 then 1 else 0)))).toNat =
      (if d.toNat ≤ 2 * r.toNat + c.toNat / 2 ^ 63 then 2 * r.toNat + c.toNat / 2 ^ 63 - d.toNat
        else 2 * r.toNat + c.toNat / 2 ^ 63) ∧
    (q + q + BitVec.ofNat 64 (if d.toNat ≤ 2 * r.toNat + c.toNat / 2 ^ 63 then 1 else 0)).toNat =
      2 * q.toNat + (if d.toNat ≤ 2 * r.toNat + c.toNat / 2 ^ 63 then 1 else 0) := by
  have hR := r.isLt; have hc := c.isLt; have hd := d.isLt
  have hcb : c.toNat / 2 ^ 63 < 2 := by omega_using [hc]
  have hr1 : (r + r + c >>> 63).toNat = (2 * r.toNat + c.toNat / 2 ^ 63) % 2 ^ 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, shr63_val]; omega_using [hcb]
  by_cases h2 : d.toNat ≤ 2 * r.toNat + c.toNat / 2 ^ 63
  · simp only [h2, ite_true]
    rw [show BitVec.ofNat 64 0 - BitVec.ofNat 64 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes,
      BitVec.toNat_sub, hr1, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]
    constructor <;> omega_using [hr, hcb, hq, hd, h2]
  · simp only [h2, ite_false]
    rw [show BitVec.ofNat 64 0 - BitVec.ofNat 64 0 = 0#64 by decide, BitVec.and_zero, BitVec.sub_zero, hr1,
      BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]
    constructor <;> omega_using [hr, hcb, hq, hd, h2]

/-- `quotFix`'s mask: `q̂ := q`, or all ones if `e = 0`. -/
theorem quotFix_val (q e : BitVec 64) :
    (q ||| ((BitVec.ofNat 64 0 - e ||| e) >>> 63 - 1#64)) = if e = 0#64 then BitVec.allOnes 64 else q := by
  by_cases he : e = 0#64
  · subst he
    rw [ite_eq_left_iff.mpr fun h => absurd rfl h,
      show (BitVec.ofNat 64 0 - 0#64 ||| 0#64) >>> 63 - 1#64 = BitVec.allOnes 64 by decide, BitVec.or_allOnes]
  · rw [ite_eq_right_iff.mpr fun h => absurd h he]
    have he0 : 0 < e.toNat := by
      rcases Nat.eq_zero_or_pos e.toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [h]; rfl)) he
      · exact h
    have hte : ((BitVec.ofNat 64 0 - e ||| e) >>> 63) = 1#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [shr63_val, BitVec.toNat_or, BitVec.toNat_sub, BitVec.toNat_ofNat]
      have hl := Nat.left_le_or (n := (2 ^ 64 - e.toNat + 0 % 2 ^ 64) % 2 ^ 64) (m := e.toNat)
      have hr := Nat.right_le_or (n := (2 ^ 64 - e.toNat + 0 % 2 ^ 64) % 2 ^ 64) (m := e.toNat)
      have hlt := Nat.or_lt_two_pow (x := (2 ^ 64 - e.toNat + 0 % 2 ^ 64) % 2 ^ 64) (n := 64)
        (Nat.mod_lt _ (by decide)) e.isLt
      have := e.isLt
      show _ = 1
      generalize (2 ^ 64 - e.toNat + 0 % 2 ^ 64) % 2 ^ 64 ||| e.toNat = o at hl hr hlt
      omega_using [hl, hr, hlt, this, he0]
    rw [hte, show (1#64 : BitVec 64) - 1#64 = 0#64 by decide, BitVec.or_zero]

/-- The next bit of the dividend: `⌊2 Q / 2^64⌋ = 2 ⌊Q / 2^64⌋ + ⌊(Q mod 2^64) / 2^63⌋`. -/
theorem div_two_mul (Q : Nat) : 2 * Q / 2 ^ 64 = 2 * (Q / 2 ^ 64) + Q % 2 ^ 64 / 2 ^ 63 := by
  have h := Nat.div_add_mod Q (2 ^ 64)
  have hm := Nat.mod_lt Q (show 0 < 2 ^ 64 by decide)
  generalize Q / 2 ^ 64 = a at h ⊢
  generalize Q % 2 ^ 64 = b at h hm ⊢
  subst h
  omega_using [hm]

theorem bv_sub_eq_zero (x y : BitVec 64) : x - y = 0#64 ↔ x = y := by
  rw [BitVec.sub_eq_iff_eq_add, BitVec.zero_add]

/-- 64 bits of restoring division (`divBit`) of `U < D 2^64`, its top word in
`r15` and its low word in `r16`, by `D` (`r7`): `q = ⌊U / D⌋` in `r18`. -/
theorem divLoop_ok {s : State} {U D : Nat} (hUD : U / 2 ^ 64 < D) (h16 : (s.gpr .r16).toNat = U % 2 ^ 64)
    (h15 : (s.gpr .r15).toNat = U / 2 ^ 64) (h7 : (s.gpr .r7).toNat = D) (h18 : s.gpr .r18 = BitVec.ofNat 64 0)
    (h20 : s.gpr .r20 = BitVec.ofNat 64 0) (h17 : s.gpr .r17 = BitVec.ofNat 64 64) :
    WP isa (Precompute.countLoop .r17 divBit) s fun t => (t.gpr .r18).toNat = U / D ∧ t.mem = s.mem ∧
      Keep [.r0, .r3, .r12, .r15, .r16, .r17, .r18] s t := by
  have hD0 : 0 < D := by omega
  let Inv : Nat → State → Prop := fun i t =>
    (t.gpr .r16).toNat = U * 2 ^ i % 2 ^ 64 ∧ t.gpr .r7 = s.gpr .r7 ∧ t.gpr .r20 = BitVec.ofNat 64 0 ∧
      t.mem = s.mem ∧ Keep [.r0, .r3, .r12, .r15, .r16, .r17, .r18] s t ∧
      (t.gpr .r15).toNat < D ∧ (t.gpr .r18).toNat < 2 ^ i ∧
        U * 2 ^ i / 2 ^ 64 = (t.gpr .r18).toNat * D + (t.gpr .r15).toNat
  refine WP.mono (wp_countdown (body := .block (divBit ++ ([.subi .r17 .r17 1] : List Instr)))
    (cnt := .r17) (N := 64) (by decide) (by decide) Inv (fun i hi t ⟨j16, j7, j20, jm, jk, hr, hq, hv⟩ hc => ?_)
    ⟨by rw [Nat.pow_zero, Nat.mul_one, h16], rfl, h20, rfl, Keep.refl _ _, by rw [h15]; exact hUD,
      by rw [h18]; decide, by
        rw [h18, h15]; show U * 2 ^ 0 / 2 ^ 64 = 0 * D + U / 2 ^ 64
        rw [Nat.pow_zero, Nat.mul_one, Nat.zero_mul, Nat.zero_add]⟩ h17)
    fun t ⟨_, _, _, jm, jk, hr, _, hv⟩ => ⟨?_, jm, jk⟩
  · have hst : WP isa (.block (divBit ++ ([.subi .r17 .r17 1] : List Instr))) t fun t' =>
        (t'.gpr .r16 = t.gpr .r16 + t.gpr .r16 ∧
          t'.gpr .r15 = t.gpr .r15 + t.gpr .r15 + t.gpr .r16 >>> 63 - (t.gpr .r7 &&& (BitVec.ofNat 64 0 -
            BitVec.ofNat 64 (if (t.gpr .r7).toNat ≤ 2 * (t.gpr .r15).toNat + (t.gpr .r16).toNat / 2 ^ 63 then 1
              else 0))) ∧
          t'.gpr .r18 = t.gpr .r18 + t.gpr .r18 + BitVec.ofNat 64
            (if (t.gpr .r7).toNat ≤ 2 * (t.gpr .r15).toNat + (t.gpr .r16).toNat / 2 ^ 63 then 1 else 0) ∧
          t'.mem = t.mem ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1) ∧
          Keep [.r0, .r3, .r12, .r15, .r16, .r17, .r18] t t' := by
      refine WP.keep _ ?_ (by decide)
      unfold divBit
      mcrun [j20, divBit_bit]
    refine WP.mono hst fun t' ⟨⟨u16, u15, u18, um, u17⟩, uk⟩ => ⟨⟨?_, by rw [uk.gpr .r7 (by decide), j7],
      by rw [uk.gpr .r20 (by decide), j20], by rw [um, jm], jk.trans' uk, ?_⟩, u17⟩
    · rw [u16, BitVec.toNat_add, j16, show U * 2 ^ (i + 1) = U * 2 ^ i + U * 2 ^ i by
        rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]]
      exact (Nat.add_mod _ _ _).symm
    · have hpi : 2 ^ i ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
      have hr' : (t.gpr .r15).toNat < (t.gpr .r7).toNat := by rw [j7, h7]; exact hr
      have v := divBit_val (t.gpr .r15) (t.gpr .r16) (t.gpr .r7) (t.gpr .r18) hr' (by omega_using [hq, hpi])
      rw [← u15, ← u18, j7, h7, j16] at v
      have hb : U * 2 ^ i % 2 ^ 64 / 2 ^ 63 < 2 := by
        have := Nat.mod_lt (U * 2 ^ i) (show 0 < 2 ^ 64 by decide); omega_using [this]
      obtain ⟨d1, d2⟩ := divBit_inv hv hr hb
      rw [← v.1] at d1 d2
      rw [← v.2] at d1
      have e2 : U * 2 ^ (i + 1) / 2 ^ 64 = 2 * (U * 2 ^ i / 2 ^ 64) + U * 2 ^ i % 2 ^ 64 / 2 ^ 63 := by
        rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm _ 2, div_two_mul]
      refine ⟨d2, ?_, by rw [e2, d1]⟩
      rw [v.2, Nat.pow_succ]
      split <;> omega_using [hq]
  · rw [Nat.mul_div_cancel _ (Nat.two_pow_pos 64)] at hv
    rw [hv, Nat.add_comm, Nat.add_mul_div_right _ _ hD0, Nat.div_eq_of_lt hr, Nat.zero_add]

/-- What `quotMG` computes from `v` (`r18`), `u` (`r15`), `a` (`r16`) and `d`
(`r7`), with zero in `r20`, instruction by instruction: `Q₀ = q₁` (`q₁ + 1`
below), `r = a - (q₁ + 1) d`, the mask `m` of `r > q₀` (by the carry of
`q₀ - r`), and `q₁ + 1 + m` plus the carry of `r + (m & d) - d`. -/
def mgqP (v u a d : BitVec 64) : BitVec 64 :=
  let Q0 := BitVec.ofNat 64 ((BitVec.ofNat 64 (v.toNat * u.toNat / 2 ^ 64)).toNat + u.toNat +
    (decide (2 ^ 64 ≤ (v * u).toNat + a.toNat)).toNat)
  let r := a - (Q0 + 1#64) * d
  let m := (0#64).toNat + (2 ^ 64 - 1 - (0#64).toNat) +
    (decide (2 ^ 64 - 1 ≤ (BitVec.ofNat 64 ((v * u).toNat + a.toNat)).toNat + (2 ^ 64 - 1 - r.toNat))).toNat
  BitVec.ofNat 64 ((Mont.off Q0 (1 + m)).toNat +
    (decide (2 ^ 64 - 1 ≤ (r + (BitVec.ofNat 64 m &&& d)).toNat + (2 ^ 64 - 1 - d.toNat))).toNat)

/-- `quotMG`'s quotient, `⌊(u 2^64 + a) / d⌋`, for `u < d`, `2^63 ≤ d` and the
reciprocal `v` (`WordStep.mg_quot`). -/
theorem mgqP_val {v u a d : Nat} (hd : d < 2 ^ 64) (hn : 2 ^ 63 ≤ d) (hu : u < d) (ha : a < 2 ^ 64)
    (hv : v = (2 ^ 128 - 1) / d - 2 ^ 64) :
    (mgqP (BitVec.ofNat 64 v) (BitVec.ofNat 64 u) (BitVec.ofNat 64 a) (BitVec.ofNat 64 d)).toNat =
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
  unfold mgqP
  simp only []
  rw [BitVec.toNat_mul, hVv, hU, hA, hD]
  have hl : v * u ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hvu : v * u / 2 ^ 64 ≤ 2 ^ 64 - 2 := Nat.le_trans (Nat.div_le_div_right (c := 2 ^ 64) hl) (by decide)
  have hdm := Nat.div_add_mod (v * u) (2 ^ 64)
  have hmm := Nat.mod_lt (v * u) (show 0 < 2 ^ 64 by decide)
  -- `Q = (q₁, q₀) / 2^64 + 1` for `(q₁, q₀) = V u + a`.
  generalize hQ0 : BitVec.ofNat 64 ((BitVec.ofNat 64 (v * u / 2 ^ 64)).toNat + u +
    (decide (2 ^ 64 ≤ v * u % 2 ^ 64 + a)).toNat) = Q0
  have hQv : (Q0 + 1#64).toNat = ((V * u + a) / 2 ^ 64 + 1) % 2 ^ 64 := by
    rw [← hQ0, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show v * u / 2 ^ 64 < 2 ^ 64 by omega), ← hPe]
    have : (v * u + a + 2 ^ 64 * u) / 2 ^ 64 = v * u / 2 ^ 64 + u + (decide (2 ^ 64 ≤ v * u % 2 ^ 64 + a)).toNat := by
      by_cases h : 2 ^ 64 ≤ v * u % 2 ^ 64 + a <;> simp only [h, decide_true, decide_false, Bool.toNat_true,
        Bool.toNat_false] <;> omega
    rw [this, show (1#64).toNat = 1 from rfl, Nat.mod_add_mod]
  generalize hr : BitVec.ofNat 64 a - (Q0 + 1#64) * BitVec.ofNat 64 d = r
  have hrv : r.toNat = (a + (2 ^ 64 - (Q0 + 1#64).toNat * d % 2 ^ 64)) % 2 ^ 64 := by
    rw [← hr, BitVec.toNat_sub, BitVec.toNat_mul, hA, hD]
    have : (Q0 + 1#64).toNat * d % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
    rw [Nat.add_comm]
  have hq0 : (BitVec.ofNat 64 (v * u % 2 ^ 64 + a)).toNat = (V * u + a) % 2 ^ 64 := by
    rw [BitVec.toNat_ofNat, ← hPe]; omega
  rw [hq0]
  -- The mask: all ones iff `r > q₀`.
  generalize hcv : decide ((V * u + a) % 2 ^ 64 < r.toNat) = c
  have hrl := r.isLt
  have hm : (BitVec.ofNat 64 ((0#64).toNat + (2 ^ 64 - 1 - (0#64).toNat) +
      (decide (2 ^ 64 - 1 ≤ (V * u + a) % 2 ^ 64 + (2 ^ 64 - 1 - r.toNat))).toNat)) =
      if c then BitVec.allOnes 64 else 0#64 := by
    rw [← hcv]
    have hql := Nat.mod_lt (V * u + a) (show 0 < 2 ^ 64 by decide)
    by_cases h : (V * u + a) % 2 ^ 64 < r.toNat
    · rw [decide_eq_false (by omega), decide_eq_true h]; decide
    · rw [decide_eq_true (by omega), decide_eq_false h]; decide
  have hmN : (0#64).toNat + (2 ^ 64 - 1 - (0#64).toNat) +
      (decide (2 ^ 64 - 1 ≤ (V * u + a) % 2 ^ 64 + (2 ^ 64 - 1 - r.toNat))).toNat =
      if c then 2 ^ 64 - 1 else 2 ^ 64 := by
    rw [← hcv]
    have hql := Nat.mod_lt (V * u + a) (show 0 < 2 ^ 64 by decide)
    by_cases h : (V * u + a) % 2 ^ 64 < r.toNat
    · rw [decide_eq_false (by omega), decide_eq_true h]; rfl
    · rw [decide_eq_true (by omega), decide_eq_false h]; rfl
  rw [hm, hmN]
  have hQ1 : (Mont.off Q0 (1 + if c then 2 ^ 64 - 1 else 2 ^ 64)).toNat =
      ((Q0 + 1#64).toNat + if c then 2 ^ 64 - 1 else 0) % 2 ^ 64 := by
    unfold Mont.off
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, show (1#64).toNat = 1 from rfl]
    have := Q0.isLt
    cases c
    · show (Q0.toNat + (1 + 2 ^ 64) % 2 ^ 64) % 2 ^ 64 = ((Q0.toNat + 1) % 2 ^ 64 + 0) % 2 ^ 64
      omega
    · show (Q0.toNat + (1 + (2 ^ 64 - 1)) % 2 ^ 64) % 2 ^ 64 = ((Q0.toNat + 1) % 2 ^ 64 + (2 ^ 64 - 1)) % 2 ^ 64
      omega
  have hr1 : (r + ((if c then BitVec.allOnes 64 else 0#64) &&& BitVec.ofNat 64 d)).toNat =
      (r.toNat + if c then d else 0) % 2 ^ 64 := by
    cases c
    · show (r + (0#64 &&& BitVec.ofNat 64 d)).toNat = (r.toNat + 0) % 2 ^ 64
      rw [BitVec.zero_and, BitVec.add_zero, Nat.add_zero, Nat.mod_eq_of_lt hrl]
    · show (r + (BitVec.allOnes 64 &&& BitVec.ofNat 64 d)).toNat = (r.toNat + d) % 2 ^ 64
      rw [BitVec.allOnes_and, BitVec.toNat_add, hD]
  rw [hQ1]
  generalize hr1v : r + ((if c then BitVec.allOnes 64 else 0#64) &&& BitVec.ofNat 64 d) = r1 at hr1
  have hfin := WordStep.mg_quot hd hn hu ha hV.symm rfl hQv hrv (Q1 := ((Q0 + 1#64).toNat +
      if c then 2 ^ 64 - 1 else 0) % 2 ^ 64) (r1 := r1.toNat)
    (by rw [← hcv]; simp only [decide_eq_true_eq]) (by rw [hr1, ← hcv]; simp only [decide_eq_true_eq])
  rw [← hfin, BitVec.toNat_ofNat]
  have := r1.isLt
  by_cases h : d ≤ r1.toNat
  · have h1 : d - 1 < r1.toNat := by omega
    rw [decide_eq_true (show 2 ^ 64 - 1 ≤ r1.toNat + (2 ^ 64 - 1 - d) by omega)]
    simp only [h1, ↓reduceIte, Bool.toNat_true]
  · have h1 : ¬ d - 1 < r1.toNat := by omega
    rw [decide_eq_false (show ¬ 2 ^ 64 - 1 ≤ r1.toNat + (2 ^ 64 - 1 - d) by omega)]
    simp only [h1, ↓reduceIte, Bool.toNat_false]

/-- The registers `quot` writes. -/
def quotRegs : List Reg := [.r0, .r3, .r6, .r7, .r12, .r14, .r15, .r16, .r17, .r18, .r20, .r22]

/-- `quot`, `x` (`w ≥ 3` words) at `r5` and the temporary at `r9`, holding
`P = 2^z`, `d' ≥ 2^63` and `v = ⌊(2^128 - 1) / d'⌋ - 2^64`, with
`⌊x P / 2^(64 (w - 1))⌋ ≤ d'`: `q̂ = min(⌊u / d'⌋, 2^64 - 1)` in `r18` for the
top two words `u = ⌊x P / 2^(64 (w - 2))⌋` of `x P`, by Möller and
Granlund's division (`mgqP_val`); `u` in `r15` and `r16`, `x`'s word `w - 3`
at `r14`, `P` in `r6`, `d'` in `r7` and zero in `r20`. -/
theorem quot_ok {s : State} {B : Addr} {Z w z : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B (slot w 1)) (h9 : s.gpr .r9 = off B (slot w 3))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 3 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z)
    (hP : (Mont.word s.mem B (slot w 3)).toNat = 2 ^ z) (hz : z ≤ 63)
    (hd63 : 2 ^ 63 ≤ (Mont.word s.mem B (slot w 3 + 8)).toNat)
    (hv : (Mont.word s.mem B (slot w 3 + 16)).toNat =
      (2 ^ 128 - 1) / (Mont.word s.mem B (slot w 3 + 8)).toNat - 2 ^ 64)
    (hXd : wordsVal s.mem B (slot w 1) w * 2 ^ z / 2 ^ (64 * (w - 1)) ≤ (Mont.word s.mem B (slot w 3 + 8)).toNat) :
    WP isa (.block quot) s fun t => ((t.gpr .r18).toNat =
      min (wordsVal s.mem B (slot w 1) w * 2 ^ z / 2 ^ (64 * (w - 2)) / (Mont.word s.mem B (slot w 3 + 8)).toNat)
        (2 ^ 64 - 1) ∧ t.mem = s.mem ∧ t.gpr .r14 = off B (slot w 1 + 8 * (w - 3)) ∧
      (t.gpr .r15).toNat * 2 ^ 64 + (t.gpr .r16).toNat = wordsVal s.mem B (slot w 1) w * 2 ^ z / 2 ^ (64 * (w - 2)) ∧
      t.gpr .r7 = Mont.word s.mem B (slot w 3 + 8) ∧ t.gpr .r6 = Mont.word s.mem B (slot w 3) ∧
      t.gpr .r20 = BitVec.ofNat 64 0) ∧ Keep quotRegs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e1 := e 1; have e3 := e 3; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  generalize hDw : Mont.word s.mem B (slot w 3 + 8) = D at hd63 hv hXd ⊢
  generalize hPw : Mont.word s.mem B (slot w 3) = P at hP ⊢
  generalize hVw : Mont.word s.mem B (slot w 3 + 16) = V at hv
  generalize hx2 : Mont.word s.mem B (slot w 1 + 8 * (w - 1)) = x2
  generalize hx1 : Mont.word s.mem B (slot w 1 + 8 * (w - 2)) = x1
  generalize hx0 : Mont.word s.mem B (slot w 1 + 8 * (w - 3)) = x0
  generalize hK : 64 * (w - 3) = K
  have hk1 : 64 * (w - 1) = K + 64 + 64 := by omega
  have hk2 : 64 * (w - 2) = K + 64 := by omega
  rw [hk1] at hXd
  rw [hk2]
  generalize hX : wordsVal s.mem B (slot w 1) w = X at hXd ⊢
  have hlow := wordsVal_lt s.mem B (slot w 1) (w - 3)
  rw [hK] at hlow
  have hXe : X = x2.toNat * 2 ^ (K + 64 + 64) + x1.toNat * 2 ^ (K + 64) + x0.toNat * 2 ^ K +
      wordsVal s.mem B (slot w 1) (w - 3) := by
    have f1 := wordsVal_succ_top s.mem B (slot w 1) (w - 1)
    have f2 := wordsVal_succ_top s.mem B (slot w 1) (w - 2)
    have f3 := wordsVal_succ_top s.mem B (slot w 1) (w - 3)
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
        wordsVal s.mem B (slot w 1) (w - 3) := by
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
  have hd0 : 0 < D.toNat := by omega
  unfold quot
  rw [List.append_assoc]
  have ea := ea_top B (d := slot w 1) (w := w) (c := 24) (by omega)
  rw [show slot w 1 + 8 * w - 24 = slot w 1 + 8 * (w - 3) by omega] at ea
  refine WP.block_append (WP.mono (WP.keep quotRegs (Q := fun t =>
      (t.gpr .r15).toNat = U / 2 ^ 64 ∧ (t.gpr .r16).toNat = U % 2 ^ 64 ∧ t.gpr .r7 = D ∧
        t.gpr .r22 = D - t.gpr .r15 ∧ t.gpr .r18 = V ∧ t.gpr .r20 = BitVec.ofNat 64 0 ∧
        t.gpr .r6 = P ∧ t.gpr .r14 = off B (slot w 1 + 8 * (w - 3)) ∧ t.mem = s.mem) (by
      unfold quotHead
      mcrun [h5, h9, h11, ea, hs.ld (show slot w 1 + 8 * (w - 3) + 16 + 8 ≤ Z by omega),
        hs.ld (show slot w 1 + 8 * (w - 3) + 8 + 8 ≤ Z by omega), hs.ld (show slot w 1 + 8 * (w - 3) + 8 ≤ Z by omega),
        hs.ld (show slot w 3 + 8 ≤ Z by omega), hs.ld (show slot w 3 + 8 + 8 ≤ Z by omega),
        hs.ld (show slot w 3 + 16 + 8 ≤ Z by omega)]
      have r2 : s.mem.readW (Mont.off B (slot w 1 + 8 * (w - 3) + 16)) 64 = x2 := by
        rw [← hx2, show slot w 1 + 8 * (w - 3) + 16 = slot w 1 + 8 * (w - 1) by omega]
      have r1 : s.mem.readW (Mont.off B (slot w 1 + 8 * (w - 3) + 8)) 64 = x1 := by
        rw [← hx1, show slot w 1 + 8 * (w - 3) + 8 = slot w 1 + 8 * (w - 2) by omega]
      have r0 : s.mem.readW (Mont.off B (slot w 1 + 8 * (w - 3))) 64 = x0 := hx0
      have rP : s.mem.readW (Mont.off B (slot w 3)) 64 = P := hPw
      have rD : s.mem.readW (Mont.off B (slot w 3 + 8)) 64 = D := hDw
      have rV : s.mem.readW (Mont.off B (slot w 3 + 16)) 64 = V := hVw
      rw [r2, r1, r0, rP, rD, rV, show (18446744073709551616 : Nat) = 2 ^ 64 from rfl]
      refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
      · rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, hP, Nat.mod_eq_of_lt hf1, Nat.mod_add_mod,
          hUu, hu2]
        exact Nat.mod_eq_of_lt (by omega_using [hu2, hXd, hDlt])
      · rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, hP,
          Nat.mod_eq_of_lt (by omega_using [hf0, hpz] : x0.toNat * 2 ^ z / 2 ^ 64 < 2 ^ 64), Nat.mod_add_mod, hU,
          Nat.add_comm (x2.toNat * 2 ^ z * 2 ^ 64), Nat.add_mul_mod_self_right]) (by decide))
    fun s₁ ⟨⟨a15, a16, a7, a22, a18, a20, a6, a14, m1⟩, k1⟩ => ?_)
  have hu2D : U / 2 ^ 64 ≤ D.toNat := by rw [hUu]; exact hXd
  -- Möller and Granlund's division.
  refine WP.block_append (WP.mono (WP.keep [.r0, .r3, .r12, .r17, .r18] (Q := fun t =>
      t.gpr .r18 = mgqP V (s₁.gpr .r15) (s₁.gpr .r16) D ∧ t.mem = s₁.mem) (by
      unfold quotMG
      mcrun [exec_adde, a7, a18, a20]
      rfl) (by decide)) fun s₂ ⟨⟨b18, m2⟩, k2⟩ => ?_)
  -- `q̂`, all ones if `u₂ = d'`.
  have hst : WP isa (.block quotFix) s₂ fun t' =>
      (t'.gpr .r18 = (if s₁.gpr .r22 = 0#64 then BitVec.allOnes 64 else s₂.gpr .r18) ∧ t'.mem = s₂.mem) ∧
        Keep [.r12, .r18] s₂ t' := by
    refine WP.keep _ ?_ (by decide)
    unfold quotFix
    mcrun [(k2.gpr .r20 (by decide)).trans a20, (k2.gpr .r22 (by decide)), quotFix_val]
  refine WP.mono hst fun t ⟨⟨u18, um⟩, uk⟩ => ⟨⟨?_, by rw [um, m2, m1], ?_, ?_, ?_, ?_, ?_⟩,
    (k1.trans (k2.trans uk)).mono (by decide)⟩
  rotate_left
  · rw [uk.gpr .r14 (by decide), k2.gpr .r14 (by decide), a14]
  · rw [uk.gpr .r15 (by decide), k2.gpr .r15 (by decide), uk.gpr .r16 (by decide), k2.gpr .r16 (by decide), a15, a16,
      Nat.div_add_mod']
  · rw [uk.gpr .r7 (by decide), k2.gpr .r7 (by decide), a7]
  · rw [uk.gpr .r6 (by decide), k2.gpr .r6 (by decide), a6]
  · rw [uk.gpr .r20 (by decide), k2.gpr .r20 (by decide), a20]
  have hfix := qhat_fix hd0 hu2D (Nat.mod_lt U (show 0 < 2 ^ 64 by decide))
  rw [Nat.div_add_mod'] at hfix
  rw [← hfix, u18]
  by_cases hc : U / 2 ^ 64 = D.toNat
  · have : s₁.gpr .r22 = 0#64 := by
      rw [a22, bv_sub_eq_zero]; exact BitVec.eq_of_toNat_eq (by rw [a15, hc])
    rw [ite_eq_left_iff.mpr fun h => absurd this h, ite_eq_left_iff.mpr fun h => absurd hc h, BitVec.toNat_allOnes]
  · have : ¬ s₁.gpr .r22 = 0#64 := by
      rw [a22, bv_sub_eq_zero]; intro h; exact hc (by rw [← a15, h])
    rw [ite_eq_right_iff.mpr fun h => absurd h this, ite_eq_right_iff.mpr fun h => absurd h hc, b18]
    have hlt : (s₁.gpr .r15).toNat < D.toNat := by rw [a15]; exact Nat.lt_of_le_of_ne hu2D hc
    have hq := mgqP_val (v := V.toNat) (u := (s₁.gpr .r15).toNat) (a := (s₁.gpr .r16).toNat) hDlt hd63 hlt
      (s₁.gpr .r16).isLt hv
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hq
    rw [hq, a15, a16, Nat.div_add_mod']

/-- The registers `recip` writes. -/
def recipRegs : List Reg := [.r0, .r3, .r7, .r12, .r15, .r16, .r17, .r18, .r20]

/-- `recip`, the temporary at `r9` holding `d' ≥ 2^63` in its word 1:
`v = ⌊(2^128 - 1) / d'⌋ - 2^64` into its word 2, by 64 bits of restoring
division of `2^128 - 1 - d' 2^64` (`WordStep.recip_eq`). -/
theorem recip_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (h9 : s.gpr .r9 = off B (slot w 3))
    (hZ : slot w 3 + 24 ≤ Z) (hd : 2 ^ 63 ≤ (Mont.word s.mem B (slot w 3 + 8)).toNat) :
    WP isa recip s fun t =>
      ((Mont.word t.mem B (slot w 3 + 16)).toNat = (2 ^ 128 - 1) / (Mont.word s.mem B (slot w 3 + 8)).toNat - 2 ^ 64 ∧
        Mont.Outside B (slot w 3 + 16) 8 s.mem t.mem) ∧ Keep recipRegs s t := by
  have hn := hs.nowrap
  generalize hDw : Mont.word s.mem B (slot w 3 + 8) = D at hd ⊢
  have hD' := D.isLt
  have rD : s.mem.readW (Mont.off B (slot w 3 + 8)) 64 = D := hDw
  unfold recip
  refine WP.seq (WP.mono (WP.keep [.r7, .r15, .r16, .r17, .r18, .r20] (Q := fun t =>
      t.gpr .r7 = D ∧ (t.gpr .r15).toNat = 2 ^ 64 - 1 - D.toNat ∧ (t.gpr .r16).toNat = 2 ^ 64 - 1 ∧
        t.gpr .r18 = BitVec.ofNat 64 0 ∧ t.gpr .r20 = BitVec.ofNat 64 0 ∧ t.gpr .r17 = BitVec.ofNat 64 64 ∧
        t.mem = s.mem) (by
      unfold recipHead
      mcrun [h9, rD, hs.ld (show slot w 3 + 8 + 8 ≤ Z by omega)]
      all_goals first | decide | (rw [BitVec.toNat_sub]; simp; omega)) (by decide)) fun s₁ ⟨⟨a7, a15, a16, a18, a20, a17, m1⟩, k1⟩ => ?_)
  have hU : ((2 ^ 64 - 1 - D.toNat) * 2 ^ 64 + (2 ^ 64 - 1)) / 2 ^ 64 = 2 ^ 64 - 1 - D.toNat := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 64), Nat.div_eq_of_lt (by decide), Nat.zero_add]
  have hUm : ((2 ^ 64 - 1 - D.toNat) * 2 ^ 64 + (2 ^ 64 - 1)) % 2 ^ 64 = 2 ^ 64 - 1 := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right]
  refine WP.seq (WP.mono (divLoop_ok (U := (2 ^ 64 - 1 - D.toNat) * 2 ^ 64 + (2 ^ 64 - 1)) (D := D.toNat)
    (by rw [hU]; omega) (by rw [hUm, a16]) (by rw [hU, a15]) (by rw [a7]) a18 a20 a17)
    fun t ⟨tq, tm, tk⟩ => ?_)
  have t9 : t.gpr .r9 = off B (slot w 3) := ((k1.trans tk).gpr .r9 (by decide)).trans h9
  have hs' := hs.congr (k1.trans tk).wr
  refine WP.mono (WP.keep [] (Q := fun t' => t'.mem = t.mem.writeW (off B (slot w 3 + 16)) (t.gpr .r18))
    (by mcrun [t9, hs'.st (show slot w 3 + 16 + 8 ≤ Z by omega)]) (by decide)) fun t' ⟨hm', k'⟩ => ?_
  have hqB : (2 ^ 128 - 1) / D.toNat - 2 ^ 64 < 2 ^ 64 := by
    have : (2 ^ 128 - 1) / D.toNat < 2 ^ 65 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      have := Nat.mul_le_mul_left (2 ^ 65) hd
      omega
    omega
  refine ⟨⟨by rw [hm', Mont.word_writeW_self, tq, WordStep.recip_eq hD' (by omega)], ?_⟩,
    ((k1.trans tk).trans k').mono (by decide)⟩
  rw [hm', tm, m1]
  exact writeW_outside _ _ _ (by omega)

/-! ## `t = x 2^64 - q̂ n` -/

theorem toNat_decide (p : Prop) [Decidable p] : (decide p).toNat = if p then 1 else 0 := by
  by_cases h : p <;> simp [h]

/-- A word of `q̂ n`: the low word of `n q̂` plus the carry `c`, and the high
word plus the carry out, the next carry. -/
theorem mul64_arith (n q c : BitVec 64) :
    (BitVec.ofNat 64 ((n * q).toNat + c.toNat)).toNat + 2 ^ 64 * (BitVec.ofNat 64
      ((BitVec.ofNat 64 (n.toNat * q.toNat / 2 ^ 64)).toNat + (decide (2 ^ 64 ≤ (n * q).toNat + c.toNat)).toNat)).toNat =
      n.toNat * q.toNat + c.toNat := by
  have hn := n.isLt; have hq := q.isLt; have hc := c.isLt
  have hhi : n.toNat * q.toNat / 2 ^ 64 ≤ 2 ^ 64 - 2 := by
    have := Nat.mul_le_mul (show n.toNat ≤ 2 ^ 64 - 1 by omega_using [hn]) (show q.toNat ≤ 2 ^ 64 - 1 by omega_using [hq])
    exact Nat.le_trans (Nat.div_le_div_right (c := 2 ^ 64) this) (by decide)
  have hd := Nat.div_add_mod (n.toNat * q.toNat) (2 ^ 64)
  have hlo := Nat.mod_lt (n.toNat * q.toNat) (show 0 < 2 ^ 64 by decide)
  rw [BitVec.toNat_mul]
  generalize n.toNat * q.toNat / 2 ^ 64 = hi at hhi hd ⊢
  generalize n.toNat * q.toNat % 2 ^ 64 = lo at hd hlo ⊢
  generalize n.toNat * q.toNat = P at hd ⊢
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show hi < 2 ^ 64 by omega_using [hhi])]
  by_cases h : 2 ^ 64 ≤ lo + c.toNat
  · simp only [h, decide_true, Bool.toNat_true]
    rw [Nat.mod_eq_of_lt (show hi + 1 < 2 ^ 64 by omega_using [hhi]), Nat.mod_eq_sub_mod h,
      Nat.mod_eq_of_lt (show lo + c.toNat - 2 ^ 64 < 2 ^ 64 by omega_using [hlo, hc])]
    omega_using [hd, h]
  · simp only [h, decide_false, Bool.toNat_false, Nat.add_zero]
    rw [Nat.mod_eq_of_lt (show hi < 2 ^ 64 by omega_using [hhi]),
      Nat.mod_eq_of_lt (show lo + c.toNat < 2 ^ 64 by omega_using [h])]
    omega_using [hd]

/-- `x`'s word before word `i` (`0` before word 0): the word `t`'s word `i`
is subtracted from in `x 2^64`. -/
def xPrev (m : Mem) (B : Addr) (dX i : Nat) : BitVec 64 := if i = 0 then 0 else Mont.word m B (dX + 8 * (i - 1))

theorem xPrev_succ (m : Mem) (B : Addr) (dX i : Nat) : xPrev m B dX (i + 1) = Mont.word m B (dX + 8 * i) := by
  simp [xPrev]

/-- `2^64 x_{<i}` from `2^64 x_{<i-1}` and `x`'s previous word. -/
theorem shift_eq (m : Mem) (B : Addr) (dX : Nat) : ∀ i,
    2 ^ 64 * wordsVal m B dX i = 2 ^ 64 * wordsVal m B dX (i - 1) + 2 ^ (64 * i) * (xPrev m B dX i).toNat
  | 0 => by
    rw [Nat.zero_sub, xPrev, ite_eq_left rfl]
    show _ = _ + _ * 0
    rw [Nat.mul_zero, Nat.add_zero]
  | k + 1 => by
    rw [xPrev_succ, Nat.add_sub_cancel, wordsVal_succ_top, Nat.mul_add, Nat.mul_succ, Nat.pow_add,
      Nat.mul_comm (2 ^ (64 * k)) (2 ^ 64), Nat.mul_assoc]

/-- A word of a difference with its borrow kept as a carry `b ≤ 1` (`CA :=
b` by `b + 2^64 - 1`, then `x - l` less the borrow, and the next carry). -/
theorem sube_arith (x l b : Nat) (hx : x < 2 ^ 64) (hl : l < 2 ^ 64) (hb : b ≤ 1) :
    (BitVec.ofNat 64 (x + (18446744073709551616 - 1 - l) +
        (decide (18446744073709551616 ≤ b + (BitVec.allOnes 64).toNat)).toNat)).toNat + l +
      2 ^ 64 * (decide (18446744073709551616 ≤ x + (18446744073709551616 - 1 - l) +
        (decide (18446744073709551616 ≤ b + (BitVec.allOnes 64).toNat)).toNat)).toNat =
      x + (2 ^ 64 - 1) + b := by
  rw [BitVec.toNat_allOnes, BitVec.toNat_ofNat, toNat_decide, toNat_decide]
  rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> (repeat' split) <;> omega

/-- What `mulSub` keeps after `i` words, from `s` (`q` in `r18`): the
pointers, `x`'s words from `i` on, the carry `c` (`r3`), the borrow as a
carry `b` (`r22`, 1 for no borrow) and `x`'s previous word (`r16`), for
`T + q n_{<i} + 2^(64 i) b = 2^64 x_{<i-1} + 2^(64 i) (1 + c)`. -/
def MSInv (s : State) (B : Addr) (dX dN : Nat) (i : Nat) (t : State) : Prop :=
  t.gpr .r14 = off B (dX + 8 * i) ∧ t.gpr .r15 = off B (dN + 8 * i) ∧ t.gpr .r18 = s.gpr .r18 ∧
    t.gpr .r20 = BitVec.ofNat 64 0 ∧ t.gpr .r6 = BitVec.allOnes 64 ∧ (t.gpr .r22).toNat ≤ 1 ∧
    t.gpr .r16 = xPrev s.mem B dX i ∧ Mont.Outside B dX (8 * i) s.mem t.mem ∧
    wordsVal t.mem B dX i + (s.gpr .r18).toNat * wordsVal s.mem B dN i + 2 ^ (64 * i) * (t.gpr .r22).toNat =
      2 ^ 64 * wordsVal s.mem B dX (i - 1) + 2 ^ (64 * i) * (1 + (t.gpr .r3).toNat) ∧
    Keep [.r0, .r3, .r6, .r7, .r12, .r14, .r15, .r16, .r17, .r22] s t

theorem mulSubWord_ok {s : State} {B : Addr} {Z dX dN w : Nat} (hs : Scr s B Z) (hX : dX + 8 * (w + 1) ≤ Z)
    (hN : dN + 8 * w ≤ Z) (dNX : dN + 8 * w ≤ dX ∨ dX + 8 * (w + 1) ≤ dN) {i : Nat} (hi : i < w) {t : State}
    (hI : MSInv s B dX dN i t) :
    WP isa (.block (mulSubWord ++ ([.subi .r17 .r17 1] : List Instr))) t fun t' =>
      MSInv s B dX dN (i + 1) t' ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 := by
  have hnw := hs.nowrap
  obtain ⟨j14, j15, j18, j20, j6, jb, j16, jout, jv, jk⟩ := hI
  have hs' := hs.congr jk.wr
  have wX : Mont.word t.mem B (dX + 8 * i) = Mont.word s.mem B (dX + 8 * i) := jout.word (by omega) (by omega)
  have wN : Mont.word t.mem B (dN + 8 * i) = Mont.word s.mem B (dN + 8 * i) := jout.word (by omega) (by omega)
  have rN : t.mem.readW (Mont.off B (dN + 8 * i)) 64 = Mont.word s.mem B (dN + 8 * i) := wN
  have rX : t.mem.readW (Mont.off B (dX + 8 * i)) 64 = Mont.word s.mem B (dX + 8 * i) := wX
  generalize hn : Mont.word s.mem B (dN + 8 * i) = n at rN wN
  generalize hl : BitVec.ofNat 64 ((n * t.gpr .r18).toNat + (t.gpr .r3).toNat) = l
  generalize hca : decide (18446744073709551616 ≤ (t.gpr .r22).toNat + (BitVec.allOnes 64).toNat) = ca
  refine WP.mono (WP.keep [.r0, .r3, .r6, .r7, .r12, .r14, .r15, .r16, .r17, .r22] (Q := fun t' =>
      t'.gpr .r14 = off B (dX + 8 * i + 8) ∧ t'.gpr .r15 = off B (dN + 8 * i + 8) ∧
      t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧ t'.gpr .r6 = t.gpr .r6 ∧
      t'.gpr .r3 = BitVec.ofNat 64 ((BitVec.ofNat 64 (n.toNat * (t.gpr .r18).toNat / 2 ^ 64)).toNat +
        (decide (2 ^ 64 ≤ (n * t.gpr .r18).toNat + (t.gpr .r3).toNat)).toNat) ∧
      t'.gpr .r22 = BitVec.ofNat 64 ((0#64).toNat + (decide (18446744073709551616 ≤ (t.gpr .r16).toNat +
        (18446744073709551616 - 1 - l.toNat) + ca.toNat)).toNat) ∧
      t'.gpr .r16 = Mont.word s.mem B (dX + 8 * i) ∧
      t'.mem = t.mem.writeW (off B (dX + 8 * i))
        (BitVec.ofNat 64 ((t.gpr .r16).toNat + (18446744073709551616 - 1 - l.toNat) + ca.toNat))) (by
    unfold mulSubWord
    mcrun [exec_adde, BitVec.add_zero, j14, j15, j20, j6, rN, rX, hl, hca, hs'.ld (show dX + 8 * i + 8 ≤ Z by omega),
      hs'.ld (show dN + 8 * i + 8 ≤ Z by omega), hs'.st (show dX + 8 * i + 8 ≤ Z by omega)]) (by decide))
    fun t' ⟨⟨u14, u15, u17, u6, u3, u22, u16, um⟩, uk⟩ => ⟨⟨?_, ?_, by rw [uk.gpr .r18 (by decide), j18],
      by rw [uk.gpr .r20 (by decide), j20], by rw [u6, j6], ?_, by rw [u16, xPrev_succ], ?_, ?_, jk.trans' uk⟩, u17⟩
  · rw [u14, show dX + 8 * i + 8 = dX + 8 * (i + 1) by omega]
  · rw [u15, show dN + 8 * i + 8 = dN + 8 * (i + 1) by omega]
  · rw [u22, BitVec.toNat_ofNat, show (0#64).toNat = 0 from rfl, Nat.zero_add]
    have := Bool.toNat_le (decide (18446744073709551616 ≤ (t.gpr .r16).toNat +
      (18446744073709551616 - 1 - l.toNat) + ca.toNat))
    omega
  · rw [um]
    exact (jout.mono (Nat.le_refl _) (by omega)).trans
      ((writeW_outside t.mem B (d := dX + 8 * i) _ (by omega)).mono (by omega) (by omega))
  · -- The word's arithmetic.
    have km := mul64_arith n (t.gpr .r18) (t.gpr .r3)
    rw [hl, ← u3] at km
    have ks := sube_arith (t.gpr .r16).toNat l.toNat (t.gpr .r22).toNat (t.gpr .r16).isLt l.isLt jb
    rw [hca] at ks
    have e22 : (t'.gpr .r22).toNat = (decide (18446744073709551616 ≤ (t.gpr .r16).toNat +
        (18446744073709551616 - 1 - l.toNat) + ca.toNat)).toNat := by
      rw [u22, BitVec.toNat_ofNat, show (0#64).toNat = 0 from rfl, Nat.zero_add]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Bool.toNat_le _) (by decide))
    rw [← e22] at ks
    rw [um, fios_wordsVal_write_top _ _ _ _ _ (by omega), wordsVal_succ_top s.mem B dN i, hn,
      Nat.add_sub_cancel, shift_eq s.mem B dX i, show 2 ^ (64 * (i + 1)) = 2 ^ (64 * i) * 2 ^ 64 by
        rw [Nat.mul_succ, Nat.pow_add], ← j16]
    rw [j18] at km
    generalize 2 ^ (64 * i) = P at jv ⊢
    generalize (BitVec.ofNat 64 ((t.gpr .r16).toNat + (18446744073709551616 - 1 - l.toNat) + ca.toNat)).toNat
      = tw at ks ⊢
    generalize (t'.gpr .r22).toNat = b' at ks ⊢
    generalize (t'.gpr .r3).toNat = c' at km ⊢
    generalize l.toNat = ll at km ks
    generalize (t.gpr .r16).toNat = xp at ks ⊢
    generalize (s.gpr .r18).toNat = q at km jv ⊢
    generalize n.toNat = nn at km ⊢
    generalize (t.gpr .r22).toNat = b at ks jv jb
    generalize (t.gpr .r3).toNat = c at km jv
    generalize wordsVal t.mem B dX i = W at jv ⊢
    generalize wordsVal s.mem B dN i = Nw at jv ⊢
    generalize 2 ^ 64 * wordsVal s.mem B dX (i - 1) = Xs at jv ⊢
    have hin : tw + nn * q + 2 ^ 64 * b' + c + 1 = xp + 2 ^ 64 + b + 2 ^ 64 * c' := by
      omega
    have := congrArg (P * ·) hin
    grind

/-- The registers `mulSub` writes. -/
def mulSubRegs : List Reg := [.r0, .r3, .r6, .r7, .r12, .r14, .r15, .r16, .r17, .r22]

/-- `mulSub`, `x` (`w` words, and room for a word more) at `dX` (`r5`), `n`
at `dN` (`r10`), `q` in `r18` and zero in `r20`: `x`'s first `w + 1` words
:= `t` with `t + q n = x 2^64 + 2^(64 (w + 1)) b`, for the borrow `b`. -/
theorem mulSub_ok {s : State} {B : Addr} {Z dX dN w : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B dX) (h10 : s.gpr .r10 = off B dN) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h20 : s.gpr .r20 = BitVec.ofNat 64 0) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hX : dX + 8 * (w + 1) ≤ Z)
    (hN : dN + 8 * w ≤ Z) (dNX : dN + 8 * w ≤ dX ∨ dX + 8 * (w + 1) ≤ dN) :
    WP isa mulSub s fun t =>
      (∃ b < 2, wordsVal t.mem B dX (w + 1) + (s.gpr .r18).toNat * wordsVal s.mem B dN w =
        wordsVal s.mem B dX w * 2 ^ 64 + 2 ^ (64 * (w + 1)) * b) ∧
      Mont.Outside B dX (8 * (w + 1)) s.mem t.mem ∧ Keep mulSubRegs s t := by
  have hnw := hs.nowrap
  unfold mulSub
  refine WP.seq (WP.mono (WP.keep [.r3, .r6, .r14, .r15, .r16, .r17, .r22] (Q := fun t =>
      t.gpr .r14 = off B dX ∧ t.gpr .r15 = off B dN ∧ t.gpr .r17 = BitVec.ofNat 64 w ∧
        t.gpr .r3 = BitVec.ofNat 64 0 ∧ t.gpr .r22 = BitVec.ofNat 64 1 ∧ t.gpr .r16 = BitVec.ofNat 64 0 ∧
        t.gpr .r6 = BitVec.allOnes 64 ∧ t.mem = s.mem) (by
      unfold mulSubHead
      prun [h5, h10, h11, h20, BitVec.add_zero, mont_ofNat_shr1 (show w < 2 ^ 63 by omega)]
      all_goals decide) (by decide))
    fun s₁ ⟨⟨i14, i15, i17, i3, i22, i16, i6, im⟩, k₁⟩ => ?_)
  have I0 : MSInv s₁ B dX dN 0 s₁ := ⟨by rw [i14]; rfl, by rw [i15]; rfl, rfl,
    (k₁.gpr .r20 (by decide)).trans h20, i6, by rw [i22]; decide, by rw [i16]; rfl,
    Mont.Outside.refl _ _ _ _, by simp [wordsVal, i22, i3], Keep.refl _ _⟩
  refine WP.seq (WP.mono (wp_countdown (cnt := .r17) (N := w) (by omega) (by omega) (MSInv s₁ B dX dN)
    (fun i hi t hI _ => mulSubWord_ok (hs.congr k₁.wr) hX hN dNX hi hI) I0 i17)
    fun t ⟨j14, _, j18, j20, j6, jb, j16, jout, jv, jk⟩ => ?_)
  have hs' := hs.congr (k₁.trans jk).wr
  generalize hca : decide (18446744073709551616 ≤ (t.gpr .r22).toNat + (BitVec.allOnes 64).toNat) = ca
  refine WP.mono (WP.keep [.r0, .r12] (Q := fun t' =>
      t'.mem = t.mem.writeW (off B (dX + 8 * w)) (BitVec.ofNat 64 ((t.gpr .r16).toNat +
        (18446744073709551616 - 1 - (t.gpr .r3).toNat) + ca.toNat))) (by
    unfold mulSubTop
    mcrun [exec_adde, j14, j6, hca, hs'.st (show dX + 8 * w + 8 ≤ Z by omega)]) (by decide))
    fun t' ⟨tm, tk⟩ => ⟨?_, ?_, ((k₁.trans jk).trans tk).mono (by decide)⟩
  · have ks := sube_arith (t.gpr .r16).toNat (t.gpr .r3).toNat (t.gpr .r22).toNat (t.gpr .r16).isLt
      (t.gpr .r3).isLt jb
    rw [hca] at ks
    have hq : s₁.gpr .r18 = s.gpr .r18 := k₁.gpr .r18 (by decide)
    rw [im, hq] at jv
    rw [im] at j16
    rw [tm, fios_wordsVal_write_top _ _ _ _ _ (by omega)]
    have hsh := shift_eq s.mem B dX w
    rw [← j16] at hsh
    have e1 : 2 ^ (64 * (w + 1)) = 2 ^ (64 * w) * 2 ^ 64 := by rw [Nat.mul_succ, Nat.pow_add]
    rw [e1]
    have hbl := Bool.toNat_le (decide (18446744073709551616 ≤ (t.gpr .r16).toNat +
      (18446744073709551616 - 1 - (t.gpr .r3).toNat) + ca.toNat))
    generalize 2 ^ (64 * w) = P at jv hsh ⊢
    generalize (BitVec.ofNat 64 ((t.gpr .r16).toNat + (18446744073709551616 - 1 - (t.gpr .r3).toNat) +
      ca.toNat)).toNat = tw at ks ⊢
    generalize (decide (18446744073709551616 ≤ (t.gpr .r16).toNat +
      (18446744073709551616 - 1 - (t.gpr .r3).toNat) + ca.toNat)).toNat = b' at ks hbl
    generalize (t.gpr .r16).toNat = xp at ks hsh
    generalize (t.gpr .r3).toNat = c at ks jv
    generalize (t.gpr .r22).toNat = b at ks jv jb
    rcases (show b' = 0 ∨ b' = 1 by omega) with rfl | rfl
    · refine ⟨1, by decide, ?_⟩
      have hin : tw + c + 1 = xp + 2 ^ 64 + b := by omega
      have := congrArg (P * ·) hin
      rw [Nat.mul_comm (wordsVal s.mem B dX w)]
      grind
    · refine ⟨0, by decide, ?_⟩
      have hin : tw + c + 1 = xp + b := by omega
      have := congrArg (P * ·) hin
      rw [Nat.mul_comm (wordsVal s.mem B dX w)]
      grind
  · rw [tm]
    exact (Mont.Outside.mono (fun x hx => (jout x hx).trans (by rw [im])) (Nat.le_refl _) (by omega)).trans
      ((writeW_outside t.mem B (d := dX + 8 * w) _ (by omega)).mono (by omega) (by omega))

/-- A word of a sum below `2^65` and its carry. -/
theorem add64_arith {v : Nat} (h : v < 2 ^ 65) :
    (BitVec.ofNat 64 v).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ v)).toNat = v := by
  rw [BitVec.toNat_ofNat]
  by_cases hv : 2 ^ 64 ≤ v
  · simp only [hv, decide_true, Bool.toNat_true]
    rw [Nat.mod_eq_sub_mod hv, Nat.mod_eq_of_lt (by omega_using [h])]; omega_using [hv]
  · simp only [hv, decide_false, Bool.toNat_false]
    rw [Nat.mod_eq_of_lt (by omega_using [hv])]; omega_using []

theorem and_mask (n : BitVec 64) (c : Prop) [Decidable c] :
    (n &&& (if c then BitVec.allOnes 64 else 0)).toNat = if c then n.toNat else 0 := by
  split
  · rw [BitVec.and_allOnes]
  · rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.and_zero]; rfl

/-- The mask of the sign of `x`. -/
theorem sign_mask (x : BitVec 64) :
    BitVec.ofNat 64 0 - x >>> 63 = if 2 ^ 63 ≤ x.toNat then BitVec.allOnes 64 else 0 := by
  have hx := x.isLt
  by_cases h : 2 ^ 63 ≤ x.toNat
  · have e : x >>> 63 = BitVec.ofNat 64 1 := BitVec.eq_of_toNat_eq (by
      rw [shr63_val, BitVec.toNat_ofNat]; omega_using [h, hx])
    rw [e, ite_eq_left_iff.mpr fun h' => absurd h h']; decide
  · have e : x >>> 63 = BitVec.ofNat 64 0 := BitVec.eq_of_toNat_eq (by
      rw [shr63_val, BitVec.toNat_ofNat]; omega_using [h])
    rw [e, ite_eq_right_iff.mpr fun h' => absurd h' h]; decide

/-- The top half of `k + 1` words: their top word's top bit. -/
theorem top_half (m : Mem) (B : Addr) (d k : Nat) :
    2 ^ (64 * (k + 1)) / 2 ≤ wordsVal m B d (k + 1) ↔ 2 ^ 63 ≤ (Mont.word m B (d + 8 * k)).toNat := by
  rw [wordsVal_succ_top, show 2 ^ (64 * (k + 1)) / 2 = 2 ^ (64 * k) * 2 ^ 63 by
    rw [Nat.mul_succ, Nat.pow_add, show (2 : Nat) ^ 64 = 2 ^ 63 * 2 from rfl, ← Nat.mul_assoc,
      Nat.mul_div_cancel _ (by decide)]]
  have hl := wordsVal_lt m B d k
  have hp := Nat.two_pow_pos (64 * k)
  generalize wordsVal m B d k = l at hl ⊢
  generalize (Mont.word m B (d + 8 * k)).toNat = t
  generalize 2 ^ (64 * k) = P at hl hp ⊢
  constructor
  · intro h
    refine Nat.le_of_not_lt fun ht => ?_
    have := Nat.mul_le_mul_left P (show t + 1 ≤ 2 ^ 63 by omega_using [ht])
    rw [Nat.mul_add, Nat.mul_one] at this
    omega_using [h, hl, this]
  · intro h
    have := Nat.mul_le_mul_left P h
    omega_using [this]

theorem ea_add (B : Addr) (d w : Nat) : BitVec.ofNat 64 (2 * w) <<< 2 + off B d = off B (d + 8 * w) := by
  rw [ofNat_shl2', off, off, BitVec.add_comm, BitVec.add_assoc, ← BitVec.ofNat_add,
    show d + 4 * (2 * w) = d + 8 * w by omega_using []]

/-- `addBack`, `n` (`w` words) at `dN` (`r10`), `x`'s `w + 1` words `t` at
`dA` (`r5`) and zero in `r20`: `t := t + n` modulo
`2^(64 (w + 1))` (with the carry `c`) if `t`'s top half is set. -/
theorem addBack_ok {s : State} {B : Addr} {Z dA dN w : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B dA) (h10 : s.gpr .r10 = off B dN) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h20 : s.gpr .r20 = BitVec.ofNat 64 0) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : dA + 8 * (w + 1) ≤ Z)
    (hN : dN + 8 * w ≤ Z) (dNA : dN + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dN) :
    WP isa addBack s fun t =>
      (∃ c < 2, wordsVal t.mem B dA (w + 1) + 2 ^ (64 * (w + 1)) * c = wordsVal s.mem B dA (w + 1) +
        if 2 ^ (64 * (w + 1)) / 2 ≤ wordsVal s.mem B dA (w + 1) then wordsVal s.mem B dN w else 0) ∧
      Mont.Outside B dA (8 * (w + 1)) s.mem t.mem ∧ Keep [.r0, .r3, .r12, .r14, .r15, .r17] s t := by
  have hnw := hs.nowrap
  unfold addBack
  refine WP.seq ?_
  simp only [top_half]
  have hpre : WP isa (.block [.lsl .r14 .r11 2, .add .r14 .r14 .r5, .load .d .r0 .r14 0, .lsr .d .r0 .r0 63,
      .sub .r12 .r20 .r0, .addi .r14 .r5 0, .addi .r15 .r10 0, .lsr .d .r17 .r11 1, .addc .r0 .r20 .r20]) s fun s₁ =>
      (s₁.gpr .r14 = off B dA ∧ s₁.gpr .r15 = off B dN ∧ s₁.gpr .r17 = BitVec.ofNat 64 w ∧
        s₁.gpr .r12 = (if 2 ^ 63 ≤ (Mont.word s.mem B (dA + 8 * w)).toNat then BitVec.allOnes 64 else 0) ∧ s₁.ca = false ∧ s₁.mem = s.mem) ∧
        Keep [.r0, .r3, .r12, .r14, .r15, .r17] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    mcrun [h5, h10, h11, h20, BitVec.add_zero, mont_ofNat_shr1 (show w < 2 ^ 63 by omega), ea_add,
      hs.ld (show dA + 8 * w + 8 ≤ Z by omega), sign_mask]
    decide
  refine WP.mono hpre fun s₁ ⟨⟨i14, i15, i17, i12, ica, im⟩, k₁⟩ => ?_
  have q20 : s₁.gpr .r20 = BitVec.ofNat 64 0 := (k₁.gpr _ (by decide)).trans h20
  generalize hm : (if 2 ^ 63 ≤ (Mont.word s.mem B (dA + 8 * w)).toNat then 1 else 0) = m
  have hmN : (if 2 ^ 63 ≤ (Mont.word s.mem B (dA + 8 * w)).toNat then wordsVal s.mem B dN w else 0) =
      m * wordsVal s.mem B dN w := by
    rw [← hm]; split <;> simp
  have hmn : ∀ n : BitVec 64, (n &&& s₁.gpr .r12).toNat = m * n.toNat := fun n => by
    rw [i12, and_mask, ← hm]; split <;> simp
  rw [hmN]
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (dA + 8 * i) ∧ t.gpr .r15 = off B (dN + 8 * i) ∧ t.gpr .r12 = s₁.gpr .r12 ∧
      t.gpr .r20 = BitVec.ofNat 64 0 ∧ Mont.Outside B dA (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dA i + 2 ^ (64 * i) * t.ca.toNat = wordsVal s.mem B dA i + m * wordsVal s.mem B dN i ∧
      Keep [.r0, .r3, .r12, .r14, .r15, .r17] s t
  refine WP.seq (WP.mono (wp_countdown (body := .block ([.load .d .r0 .r15 0, .logic .and .r0 .r0 .r12,
      .load .d .r3 .r14 0, .adde .r3 .r3 .r0, .store .d .r3 .r14 0, .addi .r14 .r14 8, .addi .r15 .r15 8] ++
      ([.subi .r17 .r17 1] : List Instr)))
    (cnt := .r17) (N := w) (by omega) (by omega) Inv (fun i hi t ⟨j14, j15, j12, j20, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [i14]; rfl, by rw [i15]; rfl, rfl, q20, by rw [← im]; exact Mont.Outside.refl _ _ _ _,
      by rw [ica]; simp [wordsVal], k₁⟩ i17)
    fun t ⟨j14, _, _, j20, jout, jeq, jk⟩ => ?_)
  · have hst : WP isa (.block [.load .d .r0 .r15 0, .logic .and .r0 .r0 .r12, .load .d .r3 .r14 0,
        .adde .r3 .r3 .r0, .store .d .r3 .r14 0, .addi .r14 .r14 8, .addi .r15 .r15 8, .subi .r17 .r17 1]) t
        fun t' => (t'.gpr .r14 = off B (dA + 8 * i + 8) ∧ t'.gpr .r15 = off B (dN + 8 * i + 8) ∧
          t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧
          t'.mem = t.mem.writeW (off B (dA + 8 * i)) (BitVec.ofNat 64 ((Mont.word t.mem B (dA + 8 * i)).toNat +
            (Mont.word t.mem B (dN + 8 * i) &&& t.gpr .r12).toNat + t.ca.toNat)) ∧
          t'.ca = decide (2 ^ 64 ≤ (Mont.word t.mem B (dA + 8 * i)).toNat +
            (Mont.word t.mem B (dN + 8 * i) &&& t.gpr .r12).toNat + t.ca.toNat)) ∧
        Keep [.r0, .r3, .r14, .r15, .r17] t t' := by
      refine WP.keep _ ?_ (by decide)
      mcrun [exec_adde, j14, j15, (hs.congr jk.wr).ld (show dN + 8 * i + 8 ≤ Z by omega),
        (hs.congr jk.wr).ld (show dA + 8 * i + 8 ≤ Z by omega),
        (hs.congr jk.wr).st (show dA + 8 * i + 8 ≤ Z by omega)]
    refine WP.mono hst fun t' ⟨⟨l14, l15, l17, lm, lca⟩, lk⟩ =>
      ⟨⟨?_, ?_, by rw [lk.gpr .r12 (by decide), j12], by rw [lk.gpr .r20 (by decide), j20], ?_, ?_,
        jk.trans' (lk.mono (by decide))⟩, l17⟩
    · rw [l14, show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega]
    · rw [l15, show dN + 8 * i + 8 = dN + 8 * (i + 1) by omega]
    · rw [lm]
      exact (jout.mono (Nat.le_refl _) (by omega)).trans
        ((writeW_outside _ B (d := dA + 8 * i) _ (by omega)).mono (by omega) (by omega))
    · have wa : Mont.word t.mem B (dA + 8 * i) = Mont.word s.mem B (dA + 8 * i) := jout.word (by omega) (by omega)
      have wn : Mont.word t.mem B (dN + 8 * i) = Mont.word s.mem B (dN + 8 * i) := jout.word (by omega) (by omega)
      have hm1 : m ≤ 1 := by rw [← hm]; split <;> decide
      have hv : (Mont.word t.mem B (dA + 8 * i)).toNat + (Mont.word t.mem B (dN + 8 * i) &&& t.gpr .r12).toNat +
          t.ca.toNat < 2 ^ 65 := by
        have := (Mont.word t.mem B (dA + 8 * i)).isLt
        have := (Mont.word t.mem B (dN + 8 * i) &&& t.gpr .r12).isLt
        have := Bool.toNat_le t.ca
        omega_using [this]
      have k := add64_arith hv
      rw [← lca, j12, hmn, wa, wn] at k
      rw [lm, fios_wordsVal_write_top _ _ _ _ _ (by omega), wordsVal_succ_top s.mem B dA i,
        wordsVal_succ_top s.mem B dN i, Nat.mul_succ, Nat.pow_add, wa, wn, j12, hmn]
      have e : 2 ^ (64 * i) * (BitVec.ofNat 64 ((Mont.word s.mem B (dA + 8 * i)).toNat +
          m * (Mont.word s.mem B (dN + 8 * i)).toNat + t.ca.toNat)).toNat + 2 ^ (64 * i) * 2 ^ 64 * t'.ca.toNat =
          2 ^ (64 * i) * (Mont.word s.mem B (dA + 8 * i)).toNat +
            m * (2 ^ (64 * i) * (Mont.word s.mem B (dN + 8 * i)).toNat) + 2 ^ (64 * i) * t.ca.toNat := by
        rw [Nat.mul_assoc, ← Nat.mul_add, k, Nat.mul_add, Nat.mul_add, Nat.mul_left_comm]
      rw [Nat.mul_add m]
      generalize 2 ^ (64 * i) * (BitVec.ofNat 64 ((Mont.word s.mem B (dA + 8 * i)).toNat +
          m * (Mont.word s.mem B (dN + 8 * i)).toNat + t.ca.toNat)).toNat = a at e ⊢
      generalize 2 ^ (64 * i) * 2 ^ 64 * t'.ca.toNat = b at e ⊢
      generalize 2 ^ (64 * i) * (Mont.word s.mem B (dA + 8 * i)).toNat = c at e ⊢
      generalize m * (2 ^ (64 * i) * (Mont.word s.mem B (dN + 8 * i)).toNat) = d at e ⊢
      generalize 2 ^ (64 * i) * t.ca.toNat = f at e jeq ⊢
      generalize m * wordsVal s.mem B dN i = g at jeq ⊢
      omega_using [e, jeq]
  · have hst : WP isa (.block [.load .d .r3 .r14 0, .adde .r3 .r3 .r20, .store .d .r3 .r14 0]) t fun t' =>
        (t'.mem = t.mem.writeW (off B (dA + 8 * w)) (BitVec.ofNat 64 ((Mont.word t.mem B (dA + 8 * w)).toNat +
            (t.gpr .r20).toNat + t.ca.toNat)) ∧
          t'.ca = decide (2 ^ 64 ≤ (Mont.word t.mem B (dA + 8 * w)).toNat + (t.gpr .r20).toNat + t.ca.toNat)) ∧
        Keep [.r3] t t' := by
      refine WP.keep _ ?_ (by decide)
      mcrun [exec_adde, j14, (hs.congr jk.wr).ld (show dA + 8 * w + 8 ≤ Z by omega),
        (hs.congr jk.wr).st (show dA + 8 * w + 8 ≤ Z by omega)]
    refine WP.mono hst fun t' ⟨⟨lm, lca⟩, lk⟩ => ⟨⟨t'.ca.toNat, by cases t'.ca <;> decide, ?_⟩, ?_,
      jk.trans' (lk.mono (by decide))⟩
    · have wa : Mont.word t.mem B (dA + 8 * w) = Mont.word s.mem B (dA + 8 * w) := jout.word (by omega) (by omega)
      have h0 : (t.gpr .r20).toNat = 0 := by rw [j20]; rfl
      have hv : (Mont.word t.mem B (dA + 8 * w)).toNat + (t.gpr .r20).toNat + t.ca.toNat < 2 ^ 65 := by
        have := (Mont.word t.mem B (dA + 8 * w)).isLt
        have := Bool.toNat_le t.ca
        omega_using [this, h0]
      have k := add64_arith hv
      rw [← lca, wa, h0] at k
      rw [lm, fios_wordsVal_write_top _ _ _ _ _ (by omega), wordsVal_succ_top s.mem B dA w, wa, h0,
        show 2 ^ (64 * (w + 1)) = 2 ^ (64 * w) * 2 ^ 64 by rw [Nat.mul_succ, Nat.pow_add]]
      have e : 2 ^ (64 * w) * (BitVec.ofNat 64 ((Mont.word s.mem B (dA + 8 * w)).toNat + 0 + t.ca.toNat)).toNat +
          2 ^ (64 * w) * 2 ^ 64 * t'.ca.toNat =
          2 ^ (64 * w) * (Mont.word s.mem B (dA + 8 * w)).toNat + 2 ^ (64 * w) * t.ca.toNat := by
        rw [Nat.mul_assoc, ← Nat.mul_add, k, Nat.add_zero, Nat.mul_add]
      generalize 2 ^ (64 * w) * (BitVec.ofNat 64 ((Mont.word s.mem B (dA + 8 * w)).toNat + 0 +
          t.ca.toNat)).toNat = a at e ⊢
      generalize 2 ^ (64 * w) * 2 ^ 64 * t'.ca.toNat = b at e ⊢
      generalize 2 ^ (64 * w) * (Mont.word s.mem B (dA + 8 * w)).toNat = c at e ⊢
      generalize 2 ^ (64 * w) * t.ca.toNat = f at e jeq ⊢
      generalize m * wordsVal s.mem B dN w = g at jeq ⊢
      omega_using [e, jeq]
    · rw [lm]
      exact (jout.mono (Nat.le_refl _) (by omega)).trans
        ((writeW_outside _ B (d := dA + 8 * w) _ (by omega)).mono (by omega) (by omega))

/-! ## The 3-by-2 estimate -/

/-- `quot3Sub`: `t = U - q̂ D` over three words, with its borrow `b`. -/
theorem sub3w_ok (s : State) : WP isa (.block quot3Sub) s fun t => ((∃ b < 2,
      (t.gpr .r15).toNat * 2 ^ 128 + (t.gpr .r16).toNat * 2 ^ 64 + (t.gpr .r0).toNat +
        ((s.gpr .r6).toNat * 2 ^ 128 + (s.gpr .r17).toNat * 2 ^ 64 + (s.gpr .r12).toNat) =
      (s.gpr .r15).toNat * 2 ^ 128 + (s.gpr .r16).toNat * 2 ^ 64 + (s.gpr .r0).toNat + 2 ^ 192 * b) ∧
      t.mem = s.mem) ∧ Keep [.r0, .r15, .r16] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold quot3Sub
  mcrun [exec_adde]
  have := (s.gpr .r15).isLt; have := (s.gpr .r16).isLt; have := (s.gpr .r0).isLt
  have := (s.gpr .r6).isLt; have := (s.gpr .r17).isLt; have := (s.gpr .r12).isLt
  simp only [BitVec.toNat_ofNat, toNat_decide]
  generalize (s.gpr .r15).toNat = a2 at *
  generalize (s.gpr .r16).toNat = a1 at *
  generalize (s.gpr .r0).toNat = a0 at *
  generalize (s.gpr .r6).toNat = h at *
  generalize (s.gpr .r17).toNat = m at *
  generalize (s.gpr .r12).toNat = l at *
  have eh : (18446744073709551616 - 1 - h) + h = 18446744073709551615 := by omega
  have em : (18446744073709551616 - 1 - m) + m = 18446744073709551615 := by omega
  have el : (18446744073709551616 - 1 - l) + l = 18446744073709551615 := by omega
  generalize 18446744073709551616 - 1 - h = hc at *
  generalize 18446744073709551616 - 1 - m = mc at *
  generalize 18446744073709551616 - 1 - l = lc at *
  rcases (show a2 + hc + 2 ≤ 18446744073709551616 ∨ 18446744073709551616 ≤ a2 + hc ∨
      a2 + hc = 18446744073709551615 by omega) with hg | hg | hg <;>
    (repeat' split) <;> first | exact ⟨0, by decide, by omega⟩ | exact ⟨1, by decide, by omega⟩

/-- `quot3Fix`, zero in `r20`: `q̂ := q̂ - 1` and `t := t + D` (`D = (d', d'ₗ)`
in `r7`, `r22`), with its carry `c`, if `t` (`r15`, `r16`, `r0`) is negative. -/
theorem fix3w_ok (s : State) (h20 : s.gpr .r20 = BitVec.ofNat 64 0) : WP isa (.block quot3Fix) s fun t =>
      (t.gpr .r18 = s.gpr .r18 - s.gpr .r15 >>> 63 ∧ (∃ c < 2,
      (t.gpr .r15).toNat * 2 ^ 128 + (t.gpr .r16).toNat * 2 ^ 64 + (t.gpr .r0).toNat + 2 ^ 192 * c =
      (s.gpr .r15).toNat * 2 ^ 128 + (s.gpr .r16).toNat * 2 ^ 64 + (s.gpr .r0).toNat +
        if 2 ^ 63 ≤ (s.gpr .r15).toNat then (s.gpr .r7).toNat * 2 ^ 64 + (s.gpr .r22).toNat else 0) ∧
      t.mem = s.mem) ∧ Keep [.r0, .r3, .r12, .r15, .r16, .r17, .r18] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold quot3Fix
  mcrun [exec_adde, h20, sign_mask, and_mask]
  have := (s.gpr .r15).isLt; have := (s.gpr .r16).isLt; have := (s.gpr .r0).isLt
  have := (s.gpr .r7).isLt; have := (s.gpr .r22).isLt
  simp only [BitVec.toNat_ofNat, toNat_decide]
  generalize (s.gpr .r15).toNat = a2 at *
  generalize (s.gpr .r16).toNat = a1 at *
  generalize (s.gpr .r0).toNat = a0 at *
  generalize (s.gpr .r7).toNat = d1 at *
  generalize (s.gpr .r22).toNat = d0 at *
  rcases (show a2 + 1 < 18446744073709551616 ∨ a2 = 18446744073709551615 by omega) with hg | hg <;>
    (repeat' split) <;> first | exact ⟨0, by decide, by omega⟩ | exact ⟨1, by decide, by omega⟩

/-- `quot3Mul`, `x`'s word `w - 3` at `r14` and the temporary at `r9`: `u₀ =
x₀ P + ⌊x₋₁ P / 2^64⌋` (`r0`) for `P` in `r6`, `d'ₗ` (`r22`), and `q̂ D` over
three words (`r6`, `r17`, `r12`), for `q̂` in `r18` and `D = (d', d'ₗ)` (`r7`,
`r22`). -/
theorem mul3_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (h14 : s.gpr .r14 = off B (slot w 1 + 8 * (w - 3))) (h9 : s.gpr .r9 = off B (slot w 3))
    (hw : 4 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z) :
    WP isa (.block quot3Mul) s fun t => (t.gpr .r0 = Mont.word s.mem B (slot w 1 + 8 * (w - 3)) * s.gpr .r6 +
        BitVec.ofNat 64 ((Mont.word s.mem B (slot w 1 + 8 * (w - 4))).toNat * (s.gpr .r6).toNat / 2 ^ 64) ∧
      t.gpr .r22 = Mont.word s.mem B (slot w 3 + 24) ∧
      (t.gpr .r6).toNat * 2 ^ 128 + (t.gpr .r17).toNat * 2 ^ 64 + (t.gpr .r12).toNat =
        (s.gpr .r18).toNat * ((s.gpr .r7).toNat * 2 ^ 64 + (Mont.word s.mem B (slot w 3 + 24)).toNat) ∧
      t.mem = s.mem) ∧ Keep [.r0, .r3, .r6, .r12, .r17, .r22] s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e1 := e 1; have e3 := e 3; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  have ea : off B (slot w 1 + 8 * (w - 3)) - BitVec.ofNat 64 8 = off B (slot w 1 + 8 * (w - 4)) := by
    rw [show slot w 1 + 8 * (w - 3) = slot w 1 + 8 * (w - 4) + 8 by omega]
    simp only [off, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_sub_cancel]
  generalize hx0 : Mont.word s.mem B (slot w 1 + 8 * (w - 3)) = x0
  generalize hxm : Mont.word s.mem B (slot w 1 + 8 * (w - 4)) = xm
  generalize hd0 : Mont.word s.mem B (slot w 3 + 24) = d0
  have r0 : s.mem.readW (Mont.off B (slot w 1 + 8 * (w - 3))) 64 = x0 := hx0
  have rm : s.mem.readW (Mont.off B (slot w 1 + 8 * (w - 4))) 64 = xm := hxm
  have rd : s.mem.readW (Mont.off B (slot w 3 + 24)) 64 = d0 := hd0
  refine WP.keep _ ?_ (by decide)
  unfold quot3Mul
  mcrun [h14, h9, ea, r0, rm, rd, hs.ld (show slot w 3 + 24 + 8 ≤ Z by omega),
    hs.ld (show slot w 1 + 8 * (w - 3) + 8 ≤ Z by omega), hs.ld (show slot w 1 + 8 * (w - 4) + 8 ≤ Z by omega)]
  have hq := (s.gpr .r18).isLt; have hd1 := (s.gpr .r7).isLt; have hd0' := d0.isLt
  rw [Nat.mul_add, ← Nat.mul_assoc]
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, toNat_decide]
  generalize (s.gpr .r18).toNat = q at *
  generalize (s.gpr .r7).toNat = d1 at *
  generalize d0.toNat = e at *
  have b1 : q * d1 / 2 ^ 64 ≤ 2 ^ 64 - 2 := Nat.le_trans (Nat.div_le_div_right (c := 2 ^ 64)
    (Nat.mul_le_mul (show q ≤ 2 ^ 64 - 1 by omega) (show d1 ≤ 2 ^ 64 - 1 by omega))) (by decide)
  have b0 : q * e / 2 ^ 64 ≤ 2 ^ 64 - 2 := Nat.le_trans (Nat.div_le_div_right (c := 2 ^ 64)
    (Nat.mul_le_mul (show q ≤ 2 ^ 64 - 1 by omega) (show e ≤ 2 ^ 64 - 1 by omega))) (by decide)
  have A := Nat.div_add_mod (q * d1) (2 ^ 64)
  have A' := Nat.mod_lt (q * d1) (show 0 < 2 ^ 64 by decide)
  have C := Nat.div_add_mod (q * e) (2 ^ 64)
  have C' := Nat.mod_lt (q * e) (show 0 < 2 ^ 64 by decide)
  generalize q * d1 = P1 at *
  generalize q * e = P0 at *
  generalize P1 / 2 ^ 64 = hi at *
  generalize P1 % 2 ^ 64 = ml at *
  generalize P0 / 2 ^ 64 = lh at *
  generalize P0 % 2 ^ 64 = l at *
  split <;> omega

/-- The registers `quot3` writes. -/
def quot3Regs : List Reg := [.r0, .r3, .r6, .r12, .r15, .r16, .r17, .r18, .r22]

theorem val3_lt' (a b c : BitVec 64) : a.toNat * 2 ^ 128 + b.toNat * 2 ^ 64 + c.toNat < 2 ^ 192 := by
  have := a.isLt; have := b.isLt; have := c.isLt
  omega

theorem val2_quarter (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : 4 * (a * 2 ^ 64 + b) < 2 ^ 192 / 2 := by
  omega

/-- The top half of three words: their top word's top bit. -/
theorem top3_half (a b c : Nat) (hb : b < 2 ^ 64) (hc : c < 2 ^ 64) :
    (2 ^ 192 / 2 ≤ a * 2 ^ 128 + b * 2 ^ 64 + c) = (2 ^ 63 ≤ a) := by
  apply propext; omega

/-- `quot3`, after `quot` (`x`'s word `w - 3` at `r14`, the top two words
`(u₂, u₁)` of `U = ⌊x P / 2^(64 (w - 3))⌋` in `r15`, `r16`, `P` in `r6` and
`d'` in `r7`), with `D = (d', d'ₗ)` (`d'ₗ` in the temporary's word 3) and an
estimate `q̂` in `r18` at most 2 above `Q = min(⌊U / D⌋, 2^64 - 1)`: `Q` in
`r18` (`WordStep.quot3_val`). -/
theorem quot3_ok {s : State} {B : Addr} {Z w z D : Nat} (hs : Scr s B Z)
    (h14 : s.gpr .r14 = off B (slot w 1 + 8 * (w - 3))) (h9 : s.gpr .r9 = off B (slot w 3))
    (h20 : s.gpr .r20 = BitVec.ofNat 64 0) (hw : 4 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z)
    (hP : (s.gpr .r6).toNat = 2 ^ z) (hz : z ≤ 63)
    (hU : (s.gpr .r15).toNat * 2 ^ 64 + (s.gpr .r16).toNat =
      wordsVal s.mem B (slot w 1) w * 2 ^ z / 2 ^ (64 * (w - 2)))
    (hD : (s.gpr .r7).toNat * 2 ^ 64 + (Mont.word s.mem B (slot w 3 + 24)).toNat = D) (hD0 : 0 < D)
    (hUD : wordsVal s.mem B (slot w 1) w * 2 ^ z / 2 ^ (64 * (w - 3)) < (2 ^ 64 + 1) * D)
    (hge : min (wordsVal s.mem B (slot w 1) w * 2 ^ z / 2 ^ (64 * (w - 3)) / D) (2 ^ 64 - 1) ≤ (s.gpr .r18).toNat)
    (hle : (s.gpr .r18).toNat ≤ min (wordsVal s.mem B (slot w 1) w * 2 ^ z / 2 ^ (64 * (w - 3)) / D) (2 ^ 64 - 1) + 2) :
    WP isa (.block quot3) s fun t => ((t.gpr .r18).toNat =
      min (wordsVal s.mem B (slot w 1) w * 2 ^ z / 2 ^ (64 * (w - 3)) / D) (2 ^ 64 - 1) ∧ t.mem = s.mem) ∧
      Keep quot3Regs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e1 := e 1; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  -- `U = (u₂, u₁, u₀)`, `u₀ = x₀ P + ⌊x₋₁ P / 2^64⌋ mod 2^64`.
  generalize hx0 : Mont.word s.mem B (slot w 1 + 8 * (w - 3)) = x0
  generalize hxm : Mont.word s.mem B (slot w 1 + 8 * (w - 4)) = xm
  generalize hK : 64 * (w - 4) = K
  have hk3 : 64 * (w - 3) = K + 64 := by omega
  have hk2 : 64 * (w - 2) = K + 64 + 64 := by omega
  rw [hk3] at hUD hge hle ⊢
  rw [hk2] at hU
  generalize hX : wordsVal s.mem B (slot w 1) w = X at hU hUD hge hle ⊢
  have hXe : X = (Mont.word s.mem B (slot w 1 + 8 * (w - 1))).toNat * 2 ^ 64 * 2 ^ (K + 64 + 64) +
      (Mont.word s.mem B (slot w 1 + 8 * (w - 2))).toNat * 2 ^ (K + 64 + 64) +
      x0.toNat * 2 ^ (K + 64) + xm.toNat * 2 ^ K + wordsVal s.mem B (slot w 1) (w - 4) := by
    have f1 := wordsVal_succ_top s.mem B (slot w 1) (w - 1)
    have f1' := wordsVal_succ_top s.mem B (slot w 1) (w - 2)
    have f2 := wordsVal_succ_top s.mem B (slot w 1) (w - 3)
    have f3 := wordsVal_succ_top s.mem B (slot w 1) (w - 4)
    rw [show w - 1 + 1 = w by omega, hX, show 64 * (w - 1) = K + 64 + 64 + 64 by omega] at f1
    rw [show w - 2 + 1 = w - 1 by omega, show 64 * (w - 2) = K + 64 + 64 by omega] at f1'
    rw [show w - 3 + 1 = w - 2 by omega, hx0, hk3] at f2
    rw [show w - 4 + 1 = w - 3 by omega, hxm, hK] at f3
    rw [f1, f1', f2, f3, Nat.mul_comm (2 ^ (K + 64)), Nat.mul_comm (2 ^ K), Nat.mul_comm (2 ^ (K + 64 + 64 + 64)),
      Nat.mul_comm (2 ^ (K + 64 + 64)), Nat.mul_assoc _ (2 ^ 64), ← Nat.pow_add,
      show 64 + (K + 64 + 64) = K + 64 + 64 + 64 by omega]
    generalize (Mont.word s.mem B (slot w 1 + 8 * (w - 1))).toNat * 2 ^ (K + 64 + 64 + 64) = a
    generalize (Mont.word s.mem B (slot w 1 + 8 * (w - 2))).toNat * 2 ^ (K + 64 + 64) = b
    generalize x0.toNat * 2 ^ (K + 64) = c
    generalize xm.toNat * 2 ^ K = d
    omega
  have hlow := wordsVal_lt s.mem B (slot w 1) (w - 4)
  rw [hK] at hlow
  have hU3 : X * 2 ^ z / 2 ^ (K + 64) = ((Mont.word s.mem B (slot w 1 + 8 * (w - 1))).toNat * 2 ^ 64 +
      (Mont.word s.mem B (slot w 1 + 8 * (w - 2))).toNat) * 2 ^ z * 2 ^ 64 +
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
  have hu0 : (x0 * s.gpr .r6 + BitVec.ofNat 64 (xm.toNat * (s.gpr .r6).toNat / 2 ^ 64)).toNat = U % 2 ^ 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, hP, Nat.mod_eq_of_lt hfm, Nat.mod_add_mod, hU3,
      Nat.add_comm _ (x0.toNat * 2 ^ z + _), Nat.add_mul_mod_self_right]
  have hUe : U = (s.gpr .r15).toNat * 2 ^ 128 + (s.gpr .r16).toNat * 2 ^ 64 + U % 2 ^ 64 := by
    have := Nat.div_add_mod U (2 ^ 64)
    rw [hUu, ← hU, Nat.mul_add, Nat.mul_comm (2 ^ 64) (_ * 2 ^ 64), Nat.mul_comm (2 ^ 64) (s.gpr .r16).toNat,
      Nat.mul_assoc, ← Nat.pow_add] at this
    exact this.symm
  have hDW : 4 * D < 2 ^ 192 / 2 := by
    rw [← hD]; exact val2_quarter _ _ (s.gpr .r7).isLt (Mont.word s.mem B (slot w 3 + 24)).isLt
  clear hXe hU3 hUu hfm hlow hU3d hX hU
  -- The blocks.
  unfold quot3
  refine WP.block_append (WP.mono (mul3_ok hs h14 h9 hw hw' hZ) fun s₁ ⟨⟨u0, d0e, pq, m1⟩, k1⟩ => ?_)
  refine WP.block_append (WP.mono (sub3w_ok s₁) fun s₂ ⟨⟨⟨b, hb, tb⟩, m2⟩, k2⟩ => ?_)
  have h20' : s₂.gpr .r20 = BitVec.ofNat 64 0 := (k2.gpr .r20 (by decide)).trans ((k1.gpr .r20 (by decide)).trans h20)
  refine WP.block_append (WP.mono (fix3w_ok s₂ h20') fun s₃ ⟨⟨q3e, ⟨c, hc, tc⟩, m3⟩, k3⟩ => ?_)
  refine WP.mono (WP.keep [.r3, .r18] (Q := fun t => t.gpr .r18 = s₃.gpr .r18 - s₃.gpr .r15 >>> 63 ∧
    t.mem = s₃.mem) (by mcrun []) (by decide)) fun t ⟨⟨t18, tm⟩, kt⟩ =>
    ⟨⟨?_, by rw [tm, m3, m2, m1]⟩, (((k1.trans k2).trans k3).trans kt).mono (by decide)⟩
  have g15 : s₁.gpr .r15 = s.gpr .r15 := k1.gpr .r15 (by decide)
  have g16 : s₁.gpr .r16 = s.gpr .r16 := k1.gpr .r16 (by decide)
  have g18 : s₂.gpr .r18 = s.gpr .r18 := (k2.gpr .r18 (by decide)).trans (k1.gpr .r18 (by decide))
  have g7 : s₂.gpr .r7 = s.gpr .r7 := (k2.gpr .r7 (by decide)).trans (k1.gpr .r7 (by decide))
  have g22 : s₂.gpr .r22 = s₁.gpr .r22 := k2.gpr .r22 (by decide)
  rw [g15, g16, u0, hx0, hxm, hu0, ← hUe, pq, hD] at tb
  rw [g7, g22, d0e, hD] at tc
  simp only [← top3_half _ _ _ (s₂.gpr .r16).isLt (s₂.gpr .r0).isLt] at tc
  have hv := WordStep.quot3_val (W := 2 ^ 192) hD0 hDW hUD hge hle (s.gpr .r18).isLt (val3_lt' _ _ _) hb
    tb (val3_lt' _ _ _) hc tc
  simp only [top3_half _ _ _ (s₂.gpr .r16).isLt (s₂.gpr .r0).isLt,
    top3_half _ _ _ (s₃.gpr .r16).isLt (s₃.gpr .r0).isLt] at hv
  clear tb tc pq
  rw [t18, q3e, g18, BitVec.toNat_sub, BitVec.toNat_sub, shr63_val, shr63_val]
  generalize min (U / D) (2 ^ 64 - 1) = Q at hv ⊢
  have q18 := (s.gpr .r18).isLt; have q2 := (s₂.gpr .r15).isLt; have q3 := (s₃.gpr .r15).isLt
  by_cases e1 : 2 ^ 63 ≤ (s₂.gpr .r15).toNat <;> by_cases e2 : 2 ^ 63 ≤ (s₃.gpr .r15).toNat <;>
    simp only [e1, e2, ite_true, ite_false] at hv <;> omega_using [hv, q18, q2, q3, e1, e2]

/-! ## A word step -/

/-- `wordStep`, in the arrays of `vg_rsa_mont_mul` (`n` in array 0, `x < n`
in array 1, `P = 2^z`, `d' = ⌊n P / 2^(64 (w - 1))⌋ ≥ 2^63`, `v = ⌊(2^128 -
1) / d'⌋ - 2^64` and `d'ₗ`, `(d', d'ₗ) = ⌊n P / 2^(64 (w - 2))⌋`, in the
temporary): `x := x 2^64 mod n`, changing only arrays 1 and 2. -/
theorem wordStep_ok {s : State} {B : Addr} {Z w z : Nat} (hs : Scr s B Z)
    (h9 : s.gpr .r9 = off B (slot w 3))
    (h10 : s.gpr .r10 = off B (slot w 0)) (h5 : s.gpr .r5 = off B (slot w 1))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 4 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z)
    (hP : (Mont.word s.mem B (slot w 3)).toNat = 2 ^ z) (hz : z ≤ 63)
    (hd : (Mont.word s.mem B (slot w 3 + 8)).toNat = wordsVal s.mem B (slot w 0) w * 2 ^ z / 2 ^ (64 * (w - 1)))
    (hd63 : 2 ^ 63 ≤ wordsVal s.mem B (slot w 0) w * 2 ^ z / 2 ^ (64 * (w - 1)))
    (hv : (Mont.word s.mem B (slot w 3 + 16)).toNat =
      (2 ^ 128 - 1) / (Mont.word s.mem B (slot w 3 + 8)).toNat - 2 ^ 64)
    (hdl : (Mont.word s.mem B (slot w 3 + 8)).toNat * 2 ^ 64 + (Mont.word s.mem B (slot w 3 + 24)).toNat =
      wordsVal s.mem B (slot w 0) w * 2 ^ z / 2 ^ (64 * (w - 2)))
    (hx : wordsVal s.mem B (slot w 1) w < wordsVal s.mem B (slot w 0) w) :
    WP isa wordStep s fun t =>
      wordsVal t.mem B (slot w 1) w = wordsVal s.mem B (slot w 1) w * 2 ^ 64 % wordsVal s.mem B (slot w 0) w ∧
      Mont.Outside B (slot w 1) (16 * (w + 2)) s.mem t.mem ∧ Keep quotRegs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  generalize hX : wordsVal s.mem B (slot w 1) w = X at hx ⊢
  generalize hN : wordsVal s.mem B (slot w 0) w = N at hx hd hd63 hdl ⊢
  have hXd : wordsVal s.mem B (slot w 1) w * 2 ^ z / 2 ^ (64 * (w - 1)) ≤ (Mont.word s.mem B (slot w 3 + 8)).toNat := by
    rw [hd, hX]; exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.le_of_lt hx))
  -- The estimates (`WordStep.qhat3_norm`), for `U = ⌊x P / 2^(64 (w - 3))⌋` and `D = ⌊n P / 2^(64 (w - 2))⌋`.
  have hk3 : 64 * (w - 3) + 64 = 64 * (w - 2) := by omega
  have hk2 : 64 * (w - 2) + 64 = 64 * (w - 1) := by omega
  obtain ⟨hUD, hq1, hq2, hge, hle⟩ := qhat3_norm (X := X) (M := N) (P := 2 ^ z) (K := 64 * (w - 3))
    (Nat.two_pow_pos z) hx (by rw [hk3, Nat.div_div_eq_div_mul, ← Nat.pow_add, hk2]; exact hd63)
  rw [hk3] at hUD hq1 hq2 hge hle
  have hUu : X * 2 ^ z / 2 ^ (64 * (w - 3)) / 2 ^ 64 = X * 2 ^ z / 2 ^ (64 * (w - 2)) := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, hk3]
  have hDu : N * 2 ^ z / 2 ^ (64 * (w - 2)) / 2 ^ 64 = (Mont.word s.mem B (slot w 3 + 8)).toNat := by
    rw [← hdl, Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos 64),
      Nat.div_eq_of_lt (Mont.word s.mem B (slot w 3 + 24)).isLt, Nat.add_zero]
  rw [hUu, hDu] at hq1 hq2
  have hD0 : 0 < N * 2 ^ z / 2 ^ (64 * (w - 2)) := by
    have := Nat.mul_le_mul_right (2 ^ 64) (show 1 ≤ (Mont.word s.mem B (slot w 3 + 8)).toNat by omega)
    omega
  unfold wordStep
  -- `q̂`, then corrected.
  refine WP.seq (WP.block_append (WP.mono (quot_ok hs h5 h9 h11 (by omega) hw' hZ hP hz (by rw [hd]; exact hd63)
    hv hXd) fun s₀ ⟨⟨q0, m0, t14, tu, t7, t6, t20⟩, k0⟩ => ?_))
  rw [hX] at q0 tu
  refine WP.mono (quot3_ok (D := N * 2 ^ z / 2 ^ (64 * (w - 2))) (hs.congr k0.wr) t14
    ((k0.gpr .r9 (by decide)).trans h9) t20 hw hw' hZ (by rw [t6]; exact hP) hz (by rw [m0, hX]; exact tu)
    (by rw [t7, m0]; exact hdl) hD0 (by rw [m0, hX]; exact hUD)
    (by rw [m0, hX, q0]; exact hq1) (by rw [m0, hX, q0]; exact hq2)) fun s₁ ⟨⟨q1, m1⟩, k1'⟩ => ?_
  rw [m0, hX] at q1
  rw [m0] at m1
  have k1 : Keep quotRegs s s₁ := k0.trans' (k1'.mono (by decide))
  have z1 : s₁.gpr .r20 = BitVec.ofNat 64 0 := (k1'.gpr .r20 (by decide)).trans t20
  have g1 : ∀ r ∈ [Reg.r5, .r8, .r9, .r10, .r11], s₁.gpr r = s.gpr r := fun r hr => k1.gpr r (by revert r hr; decide)
  -- `t = x 2^64 - q̂ n`.
  refine WP.seq (WP.mono (mulSub_ok (dX := slot w 1) (dN := slot w 0) (hs.congr k1.wr)
    ((g1 .r5 (by decide)).trans h5) ((g1 .r10 (by decide)).trans h10) ((g1 .r11 (by decide)).trans h11) z1
    (by omega) hw' (by omega) (by omega) (by omega)) fun s₂ ⟨⟨b, hb, a2⟩, o2, k2⟩ => ?_)
  rw [m1, hN, q1, hX] at a2
  have k12 := k1.trans' (k2.mono (by decide))
  have g2 : ∀ r ∈ [Reg.r5, .r10, .r11], s₂.gpr r = s.gpr r := fun r hr => k12.gpr r (by revert r hr; decide)
  have z2 : s₂.gpr .r20 = BitVec.ofNat 64 0 := (k2.gpr .r20 (by decide)).trans z1
  have n2 : wordsVal s₂.mem B (slot w 0) w = N := by rw [o2.wordsVal (by omega) (by omega), m1, hN]
  -- `n` added once if negative.
  refine WP.mono (addBack_ok (dA := slot w 1) (dN := slot w 0) (hs.congr k12.wr)
    ((g2 .r5 (by decide)).trans h5) ((g2 .r10 (by decide)).trans h10) ((g2 .r11 (by decide)).trans h11)
    z2 (by omega) hw' (by omega) (by omega) (by omega)) fun t ⟨⟨c, hc, a3⟩, o3, k3⟩ =>
    ⟨?_, ?_, k12.trans' (k3.mono (by decide))⟩
  · rw [n2] at a3
    -- `x 2^64 mod n`.
    have hN0 : 0 < N := by omega
    have hNlt : N < 2 ^ (64 * w) := hN ▸ wordsVal_lt _ _ _ _
    have hW : 2 * N < 2 ^ (64 * (w + 1)) / 2 := by
      rw [show 2 ^ (64 * (w + 1)) / 2 = 2 ^ (64 * w) * 2 ^ 63 by
        rw [Nat.mul_succ, Nat.pow_add, show (2 : Nat) ^ 64 = 2 ^ 63 * 2 from rfl, ← Nat.mul_assoc,
          Nat.mul_div_cancel _ (by decide)]]
      have := Nat.mul_le_mul_left (2 ^ (64 * w)) (show 2 ≤ 2 ^ 63 by decide)
      omega
    have hT := wordStepQ1_val hN0 hW hge hle (wordsVal_lt _ _ _ _) hb a2 (wordsVal_lt _ _ _ _) hc a3
    have e5 := wordsVal_succ_top t.mem B (slot w 1) w
    have hr := Nat.mod_lt (X * 2 ^ 64) hN0
    rw [hT] at e5
    rcases Nat.eq_zero_or_pos (Mont.word t.mem B (slot w 1 + 8 * w)).toNat with h | h
    · rw [h, Nat.mul_zero, Nat.add_zero] at e5; exact e5.symm
    · have := Nat.le_mul_of_pos_right (2 ^ (64 * w)) h
      omega
  · rw [m1] at o2
    exact (o2.mono (by omega) (by omega)).trans (o3.mono (by omega) (by omega))

/-- `wordSteps`, from `x = 2^(64 (w - 1)) < n` and `norm`'s `P` and `d'` in
the temporary: `x := 2^(128 w) mod n`, changing only arrays 1 and 2. -/
theorem wordSteps_ok {s : State} {B : Addr} {Z w z : Nat} (hs : Scr s B Z)
    (h9 : s.gpr .r9 = off B (slot w 3))
    (h10 : s.gpr .r10 = off B (slot w 0)) (h5 : s.gpr .r5 = off B (slot w 1))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 4 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z)
    (hP : (Mont.word s.mem B (slot w 3)).toNat = 2 ^ z) (hz : z ≤ 63)
    (hd : (Mont.word s.mem B (slot w 3 + 8)).toNat = wordsVal s.mem B (slot w 0) w * 2 ^ z / 2 ^ (64 * (w - 1)))
    (hd63 : 2 ^ 63 ≤ wordsVal s.mem B (slot w 0) w * 2 ^ z / 2 ^ (64 * (w - 1)))
    (hv : (Mont.word s.mem B (slot w 3 + 16)).toNat =
      (2 ^ 128 - 1) / (Mont.word s.mem B (slot w 3 + 8)).toNat - 2 ^ 64)
    (hdl : (Mont.word s.mem B (slot w 3 + 8)).toNat * 2 ^ 64 + (Mont.word s.mem B (slot w 3 + 24)).toNat =
      wordsVal s.mem B (slot w 0) w * 2 ^ z / 2 ^ (64 * (w - 2)))
    (hx : wordsVal s.mem B (slot w 1) w = 2 ^ (64 * (w - 1)))
    (hxN : 2 ^ (64 * (w - 1)) < wordsVal s.mem B (slot w 0) w) :
    WP isa wordSteps s fun t =>
      wordsVal t.mem B (slot w 1) w = 2 ^ (128 * w) % wordsVal s.mem B (slot w 0) w ∧
      Mont.Outside B (slot w 1) (16 * (w + 2)) s.mem t.mem ∧ Keep (.r4 :: quotRegs) s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  generalize hN : wordsVal s.mem B (slot w 0) w = N at hd hd63 hdl hxN ⊢
  have hN0 : 0 < N := by omega
  unfold wordSteps
  refine WP.seq (WP.mono (WP.keep [.r4] (Q := fun t => t.gpr .r4 = BitVec.ofNat 64 (w + 1) ∧ t.mem = s.mem)
    (by
      prun [h11, mont_ofNat_shr1 (show w < 2 ^ 63 by omega)]
      exact (BitVec.ofNat_add _ _).symm) (by decide)) fun s₁ ⟨⟨a4, m1⟩, k1⟩ => ?_)
  let Inv : Nat → State → Prop := fun j t =>
    wordsVal t.mem B (slot w 1) w = 2 ^ (64 * (w - 1) + 64 * j) % N ∧
      Mont.Outside B (slot w 1) (16 * (w + 2)) s.mem t.mem ∧ Keep (.r4 :: quotRegs) s t
  refine WP.mono (wp_countdown (body := .seq wordStep (.block [.subi .r4 .r4 1])) (cnt := .r4) (N := w + 1)
    (by omega) (by omega) Inv (fun j _ t ⟨tx, to, tk⟩ _ => ?_)
    ⟨by rw [m1, hx, Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hxN], by rw [m1]; exact Mont.Outside.refl _ _ _ _,
      k1.mono (by decide)⟩ a4)
    fun t ⟨tx, to, tk⟩ => ⟨by rw [tx, show 64 * (w - 1) + 64 * (w + 1) = 128 * w by omega], to, tk⟩
  have g : ∀ r ∈ [Reg.r5, .r8, .r9, .r10, .r11], t.gpr r = s.gpr r := fun r hr => tk.gpr r (by revert r hr; decide)
  have n0 : wordsVal t.mem B (slot w 0) w = N := by rw [to.wordsVal (by omega) (by omega), hN]
  have w3 : Mont.word t.mem B (slot w 3) = Mont.word s.mem B (slot w 3) := to.word (by omega) (by omega)
  have w38 : Mont.word t.mem B (slot w 3 + 8) = Mont.word s.mem B (slot w 3 + 8) := to.word (by omega) (by omega)
  have w316 : Mont.word t.mem B (slot w 3 + 16) = Mont.word s.mem B (slot w 3 + 16) := to.word (by omega) (by omega)
  have w324 : Mont.word t.mem B (slot w 3 + 24) = Mont.word s.mem B (slot w 3 + 24) := to.word (by omega) (by omega)
  refine WP.seq (WP.mono (wordStep_ok (z := z) (hs.congr tk.wr)
    ((g .r9 (by decide)).trans h9) ((g .r10 (by decide)).trans h10) ((g .r5 (by decide)).trans h5)
    ((g .r11 (by decide)).trans h11) hw hw' hZ (by rw [w3]; exact hP) hz (by rw [w38, n0]; exact hd)
    (by rw [n0]; exact hd63) (by rw [w316, w38]; exact hv) (by rw [w38, w324, n0]; exact hdl)
    (by rw [tx, n0]; exact Nat.mod_lt _ hN0)) fun t₁ ⟨x1, o1, k1⟩ => ?_)
  refine WP.mono (subi_ok t₁ .r4 (by decide)) fun t₂ e2 => ?_
  subst e2
  refine ⟨⟨?_, by rw [mem_write]; exact to.trans o1, ((tk.trans k1).trans (Keep.write _ _ _)).mono (by decide)⟩, ?_⟩
  · rw [mem_write, x1, tx, n0, Nat.mod_mul_mod, ← Nat.pow_add, Nat.mul_succ, Nat.add_assoc]
  · gsimp; rw [k1.gpr .r4 (by decide)]

end VG.Proof.Bignum.PPC64LE
