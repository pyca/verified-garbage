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
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCopy
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.WordStepNorm
import VerifiedGarbage.Proof.Bignum.WordStep
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `R² mod n` by word steps of long division on PPC64LE

`r2Words_ok`: `vg_rsa_public_precompute`'s `R² mod n` (`r2Fast`) for any `n`
of `w ≥ 3` words whose top word is not zero, in the working space of
`vg_rsa_mont_mul` (`n` in array 0, `x` in array 1, the accumulator and the
temporary in arrays 2 and 3), from its pieces:

* `norm_ok`: `P = 2^z` and `d' = ⌊n P / 2^(64 (w - 1))⌋ ≥ 2^63` in the
  temporary;
* `quot_ok`: the estimate `q̂` of `⌊x 2^64 / n⌋` from the top words of `x P`
  and `d'` (`WordStep.qhat_norm`), by restoring division;
* `mulRow_ok`, `subPass_ok`, `addBack_ok`: `t = x 2^64 - q̂ n`, then `n`
  added twice while it is negative (`WordStep.wordStepQ_val`);
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

/-- `4 (2 w) + d - c`: a word near the top of `w` words at `d`. -/
theorem ea_top (B : Addr) {d w c : Nat} (hc : c ≤ 8 * w) :
    BitVec.ofNat 64 (2 * w) <<< 2 + off B d - BitVec.ofNat 64 c = off B (d + 8 * w - c) := by
  rw [BitVec.sub_eq_iff_eq_add, ofNat_shl2', off, off, BitVec.add_assoc, ← BitVec.ofNat_add,
    Nat.sub_add_cancel (by omega_using [hc]), BitVec.add_comm, BitVec.add_assoc, ← BitVec.ofNat_add,
    show d + 4 * (2 * w) = d + 8 * w by omega_using []]

/-- The registers `norm` writes. -/
def normRegs : List Reg := [.r0, .r3, .r6, .r14, .r15, .r16, .r17, .r20, .r22]

/-- `norm`, `n` (`w ≥ 2` words, its top word not zero) at `r10` and the
temporary at `r9`: `P = 2^z` and `d' = ⌊n P / 2^(64 (w - 1))⌋ ≥ 2^63` in the
temporary's words 0 and 1. -/
theorem norm_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (h9 : s.gpr .r9 = off B (slot w 3)) (h10 : s.gpr .r10 = off B (slot w 0))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z)
    (hT : 2 ^ (64 * (w - 1)) ≤ wordsVal s.mem B (slot w 0) w) :
    WP isa norm s fun t => (∃ z ≤ 63, (Mont.word t.mem B (slot w 3)).toNat = 2 ^ z ∧
      (Mont.word t.mem B (slot w 3 + 8)).toNat = wordsVal s.mem B (slot w 0) w * 2 ^ z / 2 ^ (64 * (w - 1)) ∧
      2 ^ 63 ≤ wordsVal s.mem B (slot w 0) w * 2 ^ z / 2 ^ (64 * (w - 1))) ∧
      Mont.Outside B (slot w 3) 16 s.mem t.mem ∧ Keep normRegs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e3 := e 3; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  -- `n`'s top two words.
  generalize hTw : Mont.word s.mem B (slot w 0 + 8 * (w - 1)) = T
  generalize hLw : Mont.word s.mem B (slot w 0 + 8 * (w - 2)) = L
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
        t.gpr .r22 = BitVec.ofNat 64 1 ∧ t.gpr .r17 = BitVec.ofNat 64 63 ∧ t.mem = s.mem) (by
      unfold normHead
      prun [h10, h11, ea, hs.ld (show slot w 0 + 8 * (w - 2) + 8 + 8 ≤ Z by omega),
        hs.ld (show slot w 0 + 8 * (w - 2) + 8 ≤ Z by omega)]
      exact ⟨by rw [← hTw, show slot w 0 + 8 * (w - 2) + 8 = slot w 0 + 8 * (w - 1) by omega], hLw⟩) (by decide)) fun s₁ ⟨⟨a15, a16, a6, a20, a22, a17, m1⟩, k1⟩ => ?_)
  -- 63 steps of `normStep`.
  let Inv : Nat → State → Prop := fun i t =>
    (∃ j ≤ i, (t.gpr .r6).toNat = 2 ^ j ∧ (t.gpr .r15).toNat = T.toNat * 2 ^ j ∧
      (j = i ∨ 2 ^ 63 ≤ T.toNat * 2 ^ j)) ∧ t.gpr .r16 = L ∧ t.gpr .r20 = BitVec.ofNat 64 0 ∧
      t.gpr .r22 = BitVec.ofNat 64 1 ∧ t.mem = s.mem ∧ Keep normRegs s₁ t
  refine WP.seq (WP.mono (wp_countdown (body := .block (normStep ++ ([.subi .r17 .r17 1] : List Instr)))
    (cnt := .r17) (N := 63) (by decide) (by decide) Inv (fun i hi t ⟨⟨j, hj, jp, jx, jc⟩, j16, j20, j22, jm, jk⟩ hc => ?_)
    ⟨⟨0, Nat.le_refl _, by rw [a6]; rfl, by rw [a15, Nat.pow_zero, Nat.mul_one], Or.inl rfl⟩, a16, a20, a22, m1,
      Keep.refl _ _⟩ a17) fun t ⟨⟨j, hj, jp, jx, jc⟩, j16, _, _, jm, jk⟩ => ?_)
  · have hst : WP isa (.block (normStep ++ ([.subi .r17 .r17 1] : List Instr))) t fun t' =>
        (t'.gpr .r6 = (if (t.gpr .r15).toNat < 2 ^ 63 then t.gpr .r6 + t.gpr .r6 else t.gpr .r6) ∧
          t'.gpr .r15 = (if (t.gpr .r15).toNat < 2 ^ 63 then t.gpr .r15 + t.gpr .r15 else t.gpr .r15) ∧
          t'.mem = t.mem ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1) ∧ Keep [.r0, .r3, .r6, .r15, .r17] t t' := by
      refine WP.keep _ ?_ (by decide)
      unfold normStep
      prun [j20, j22, norm_mask, mask_add]
    refine WP.mono hst fun t' ⟨⟨u6, u15, um, u17⟩, uk⟩ => ⟨⟨?_, ?_, ?_, ?_, by rw [um, jm], jk.trans' (uk.mono (by decide))⟩, u17⟩
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
  generalize hd' : t.gpr .r15 + BitVec.ofNat 64 (L.toNat * (t.gpr .r6).toNat / 2 ^ 64) = D
  refine WP.mono (WP.keep [.r0, .r15] (Q := fun u => u.mem = (t.mem.writeW (off B (slot w 3)) (t.gpr .r6)).writeW
      (off B (slot w 3 + 8)) D) (by
    unfold normTail
    mcrun [j16, t9, hd', hs₂.st (show slot w 3 + 8 ≤ Z by omega), hs₂.st (show slot w 3 + 8 + 8 ≤ Z by omega)])
    (by decide)) fun u ⟨um, uk⟩ => ⟨⟨j, hj63, ?_, ?_⟩, ?_, (k1.trans (jk.trans uk)).mono (by decide)⟩
  · rw [um, Mont.Outside.word (writeW_outside _ B _ (by omega)) (by omega) (by omega), Mont.word_writeW_self, jp]
  · have hNv : wordsVal s.mem B (slot w 0) w * 2 ^ j / 2 ^ (64 * (w - 1)) =
        T.toNat * 2 ^ j + L.toNat * 2 ^ j / 2 ^ 64 := by
      rw [hN, show 64 * (w - 1) = 64 * (w - 2) + 64 by omega]
      exact top_shift (by omega) (wordsVal_lt _ _ _ _)
    have hD : D.toNat = T.toNat * 2 ^ j + L.toNat * 2 ^ j / 2 ^ 64 := by
      have hlt := shl_add_lt (by omega) (show T.toNat * 2 ^ j < 2 ^ 64 by rw [← jx]; exact (t.gpr .r15).isLt) hLP
      rw [← hd', BitVec.toNat_add, BitVec.toNat_ofNat, jx, jp, Nat.mod_eq_of_lt (by omega_using [hLP, hpj] :
        L.toNat * 2 ^ j / 2 ^ 64 < 2 ^ 64), Nat.mod_eq_of_lt hlt]
    rw [hNv]
    refine ⟨?_, by omega_using [hTP]⟩
    rw [um, Mont.word_writeW_self, hD]
  · rw [um, ← jm]
    exact ((writeW_outside _ B _ (by omega)).mono (by omega) (by omega)).trans
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

/-- The registers `quot` writes. -/
def quotRegs : List Reg := [.r0, .r3, .r6, .r7, .r12, .r14, .r15, .r16, .r17, .r18, .r20, .r22]

/-- `quot`, `x` (`w ≥ 3` words) at `r5` and the temporary at `r9`, holding
`P = 2^z` and `d'`, with `⌊x P / 2^(64 (w - 1))⌋ ≤ d'`: `q̂ = min(⌊u / d'⌋,
2^64 - 1)` in `r18` for the top two words `u = ⌊x P / 2^(64 (w - 2))⌋` of
`x P`. -/
theorem quot_ok {s : State} {B : Addr} {Z w z : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B (slot w 1)) (h9 : s.gpr .r9 = off B (slot w 3))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 3 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z)
    (hP : (Mont.word s.mem B (slot w 3)).toNat = 2 ^ z) (hz : z ≤ 63)
    (hd0 : 0 < (Mont.word s.mem B (slot w 3 + 8)).toNat)
    (hXd : wordsVal s.mem B (slot w 1) w * 2 ^ z / 2 ^ (64 * (w - 1)) ≤ (Mont.word s.mem B (slot w 3 + 8)).toNat) :
    WP isa quot s fun t => (t.gpr .r18).toNat =
      min (wordsVal s.mem B (slot w 1) w * 2 ^ z / 2 ^ (64 * (w - 2)) / (Mont.word s.mem B (slot w 3 + 8)).toNat)
        (2 ^ 64 - 1) ∧ t.mem = s.mem ∧ Keep quotRegs s t ∧ t.gpr .r20 = BitVec.ofNat 64 0 := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e1 := e 1; have e3 := e 3; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  generalize hDw : Mont.word s.mem B (slot w 3 + 8) = D at hd0 hXd ⊢
  generalize hPw : Mont.word s.mem B (slot w 3) = P at hP
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
  unfold quot
  have ea := ea_top B (d := slot w 1) (w := w) (c := 24) (by omega)
  rw [show slot w 1 + 8 * w - 24 = slot w 1 + 8 * (w - 3) by omega] at ea
  refine WP.seq (WP.mono (WP.keep quotRegs (Q := fun t =>
      (t.gpr .r15).toNat = U / 2 ^ 64 ∧ (t.gpr .r16).toNat = U % 2 ^ 64 ∧ t.gpr .r7 = D ∧
        t.gpr .r22 = D - t.gpr .r15 ∧ t.gpr .r18 = BitVec.ofNat 64 0 ∧ t.gpr .r20 = BitVec.ofNat 64 0 ∧
        t.gpr .r17 = BitVec.ofNat 64 64 ∧ t.mem = s.mem) (by
      unfold quotHead
      mcrun [h5, h9, h11, ea, hs.ld (show slot w 1 + 8 * (w - 3) + 16 + 8 ≤ Z by omega),
        hs.ld (show slot w 1 + 8 * (w - 3) + 8 + 8 ≤ Z by omega), hs.ld (show slot w 1 + 8 * (w - 3) + 8 ≤ Z by omega),
        hs.ld (show slot w 3 + 8 ≤ Z by omega), hs.ld (show slot w 3 + 8 + 8 ≤ Z by omega)]
      have r2 : s.mem.readW (Mont.off B (slot w 1 + 8 * (w - 3) + 16)) 64 = x2 := by
        rw [← hx2, show slot w 1 + 8 * (w - 3) + 16 = slot w 1 + 8 * (w - 1) by omega]
      have r1 : s.mem.readW (Mont.off B (slot w 1 + 8 * (w - 3) + 8)) 64 = x1 := by
        rw [← hx1, show slot w 1 + 8 * (w - 3) + 8 = slot w 1 + 8 * (w - 2) by omega]
      have r0 : s.mem.readW (Mont.off B (slot w 1 + 8 * (w - 3))) 64 = x0 := hx0
      have rP : s.mem.readW (Mont.off B (slot w 3)) 64 = P := hPw
      have rD : s.mem.readW (Mont.off B (slot w 3 + 8)) 64 = D := hDw
      rw [r2, r1, r0, rP, rD, show (18446744073709551616 : Nat) = 2 ^ 64 from rfl]
      refine ⟨?_, ?_, rfl, rfl⟩
      · rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, hP, Nat.mod_eq_of_lt hf1, Nat.mod_add_mod,
          hUu, hu2]
        exact Nat.mod_eq_of_lt (by omega_using [hu2, hXd, hDlt])
      · rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, hP,
          Nat.mod_eq_of_lt (by omega_using [hf0, hpz] : x0.toNat * 2 ^ z / 2 ^ 64 < 2 ^ 64), Nat.mod_add_mod, hU,
          Nat.add_comm (x2.toNat * 2 ^ z * 2 ^ 64), Nat.add_mul_mod_self_right]) (by decide)) fun s₁ ⟨⟨a15, a16, a7, a22, a18, a20, a17, m1⟩, k1⟩ => ?_)
  have hu2D : U / 2 ^ 64 ≤ D.toNat := by rw [hUu]; exact hXd
  -- 64 bits of restoring division.
  let Inv : Nat → State → Prop := fun i t =>
    (t.gpr .r16).toNat = U * 2 ^ i % 2 ^ 64 ∧ t.gpr .r7 = D ∧ t.gpr .r20 = BitVec.ofNat 64 0 ∧
      t.gpr .r22 = s₁.gpr .r22 ∧ t.mem = s.mem ∧ Keep quotRegs s₁ t ∧
      (U / 2 ^ 64 < D.toNat → (t.gpr .r15).toNat < D.toNat ∧ (t.gpr .r18).toNat < 2 ^ i ∧
        U * 2 ^ i / 2 ^ 64 = (t.gpr .r18).toNat * D.toNat + (t.gpr .r15).toNat)
  refine WP.seq (WP.mono (wp_countdown (body := .block (divBit ++ ([.subi .r17 .r17 1] : List Instr)))
    (cnt := .r17) (N := 64) (by decide) (by decide) Inv (fun i hi t ⟨j16, j7, j20, j22, jm, jk, jq⟩ hc => ?_)
    ⟨by rw [Nat.pow_zero, Nat.mul_one, a16], a7, a20, rfl, m1, Keep.refl _ _,
      fun h => ⟨by rw [a15]; exact h, by rw [a18]; decide, by
        rw [a18, a15]; show U * 2 ^ 0 / 2 ^ 64 = 0 * D.toNat + U / 2 ^ 64
        rw [Nat.pow_zero, Nat.mul_one, Nat.zero_mul, Nat.zero_add]⟩⟩ a17)
    fun t ⟨_, _, j20, j22, jm, jk, jq⟩ => ?_)
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
      by rw [uk.gpr .r20 (by decide), j20], by rw [uk.gpr .r22 (by decide), j22], by rw [um, jm],
      jk.trans' (uk.mono (by decide)), fun h => ?_⟩, u17⟩
    · rw [u16, BitVec.toNat_add, j16, show U * 2 ^ (i + 1) = U * 2 ^ i + U * 2 ^ i by
        rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]]
      exact (Nat.add_mod _ _ _).symm
    · obtain ⟨hr, hq, hv⟩ := jq h
      have hpi : 2 ^ i ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
      have v := divBit_val (t.gpr .r15) (t.gpr .r16) (t.gpr .r7) (t.gpr .r18) (by rw [j7]; exact hr)
        (by omega_using [hq, hpi])
      rw [← u15, ← u18, j7, j16] at v
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
  -- `q̂`, all ones if `u₂ = d'`.
  have hst : WP isa (.block quotFix) t fun t' =>
      (t'.gpr .r18 = (if s₁.gpr .r22 = 0#64 then BitVec.allOnes 64 else t.gpr .r18) ∧ t'.mem = t.mem) ∧
        Keep [.r12, .r18] t t' := by
    refine WP.keep _ ?_ (by decide)
    unfold quotFix
    mcrun [j20, j22, quotFix_val]
  refine WP.mono hst fun t' ⟨⟨u18, um⟩, uk⟩ => ⟨?_, by rw [um, jm], (k1.trans (jk.trans uk)).mono (by decide),
    (uk.gpr .r20 (by decide)).trans j20⟩
  have hfix := qhat_fix hd0 hu2D (Nat.mod_lt U (show 0 < 2 ^ 64 by decide))
  rw [Nat.div_add_mod'] at hfix
  rw [← hfix, u18]
  by_cases hc : U / 2 ^ 64 = D.toNat
  · have : s₁.gpr .r22 = 0#64 := by
      rw [a22, bv_sub_eq_zero]; exact BitVec.eq_of_toNat_eq (by rw [a15, hc])
    rw [ite_eq_left_iff.mpr fun h => absurd this h, ite_eq_left_iff.mpr fun h => absurd hc h, BitVec.toNat_allOnes]
  · have : ¬ s₁.gpr .r22 = 0#64 := by
      rw [a22, bv_sub_eq_zero]; intro h; exact hc (by rw [← a15, h])
    rw [ite_eq_right_iff.mpr fun h => absurd h this, ite_eq_right_iff.mpr fun h => absurd h hc]
    obtain ⟨hr, _, hv⟩ := jq (Nat.lt_of_le_of_ne hu2D hc)
    rw [Nat.mul_div_cancel _ (Nat.two_pow_pos 64)] at hv
    rw [hv, Nat.add_comm, Nat.add_mul_div_right _ _ hd0, Nat.div_eq_of_lt hr, Nat.zero_add]

/-! ## `t = x 2^64 - q̂ n` -/

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

/-- `mulRow`, `n` (`w` words) at `dN` (`r10`), the accumulator at `dA`
(`r8`) and `q̂` in `r18`: the accumulator's `w + 1` words := `q̂ n`. -/
theorem mulRow_ok {s : State} {B : Addr} {Z dA dN w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B dA) (h10 : s.gpr .r10 = off B dN) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : dA + 8 * (w + 1) ≤ Z) (hN : dN + 8 * w ≤ Z)
    (dNA : dN + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dN) :
    WP isa mulRow s fun t =>
      wordsVal t.mem B dA (w + 1) = (s.gpr .r18).toNat * wordsVal s.mem B dN w ∧
      Mont.Outside B dA (8 * (w + 1)) s.mem t.mem ∧ Keep [.r0, .r3, .r12, .r14, .r15, .r17] s t := by
  have hnw := hs.nowrap
  unfold mulRow
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .r14 .r8 0, .addi .r15 .r10 0, .lsr .d .r17 .r11 1, .li .r3 0]) s fun s₁ =>
      (s₁.gpr .r14 = off B dA ∧ s₁.gpr .r15 = off B dN ∧ s₁.gpr .r17 = BitVec.ofNat 64 w ∧
        s₁.gpr .r3 = BitVec.ofNat 64 0 ∧ s₁.mem = s.mem) ∧ Keep [.r0, .r3, .r12, .r14, .r15, .r17] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun [h8, h10, h11, BitVec.add_zero, mont_ofNat_shr1 (show w < 2 ^ 63 by omega)]
  refine WP.mono hpre fun s₁ ⟨⟨i14, i15, i17, i3, im⟩, k₁⟩ => ?_
  have q18 : s₁.gpr .r18 = s.gpr .r18 := k₁.gpr _ (by decide)
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (dA + 8 * i) ∧ t.gpr .r15 = off B (dN + 8 * i) ∧ t.gpr .r18 = s.gpr .r18 ∧
      Mont.Outside B dA (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dA i + 2 ^ (64 * i) * (t.gpr .r3).toNat = (s.gpr .r18).toNat * wordsVal s.mem B dN i ∧
      Keep [.r0, .r3, .r12, .r14, .r15, .r17] s t
  refine WP.seq (WP.mono (wp_countdown (body := .block ([.load .d .r0 .r15 0, .mul .r12 .r0 .r18,
      .mulhu .r0 .r0 .r18, .addc .r12 .r12 .r3, .addze .r3 .r0, .store .d .r12 .r14 0, .addi .r14 .r14 8,
      .addi .r15 .r15 8] ++ ([.subi .r17 .r17 1] : List Instr)))
    (cnt := .r17) (N := w) (by omega) (by omega) Inv (fun i hi t ⟨j14, j15, j18, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [i14]; rfl, by rw [i15]; rfl, q18, by rw [← im]; exact Mont.Outside.refl _ _ _ _,
      by rw [i3]; simp [wordsVal], k₁⟩ i17)
    fun t ⟨j14, _, _, jout, jeq, jk⟩ => ?_)
  · have hst : WP isa (.block [.load .d .r0 .r15 0, .mul .r12 .r0 .r18, .mulhu .r0 .r0 .r18, .addc .r12 .r12 .r3,
        .addze .r3 .r0, .store .d .r12 .r14 0, .addi .r14 .r14 8, .addi .r15 .r15 8, .subi .r17 .r17 1]) t fun t' =>
        (t'.gpr .r14 = off B (dA + 8 * i + 8) ∧ t'.gpr .r15 = off B (dN + 8 * i + 8) ∧
          t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧
          t'.mem = t.mem.writeW (off B (dA + 8 * i)) (BitVec.ofNat 64
            ((Mont.word t.mem B (dN + 8 * i) * t.gpr .r18).toNat + (t.gpr .r3).toNat)) ∧
          t'.gpr .r3 = BitVec.ofNat 64 ((BitVec.ofNat 64 ((Mont.word t.mem B (dN + 8 * i)).toNat *
            (t.gpr .r18).toNat / 2 ^ 64)).toNat + (decide (2 ^ 64 ≤ (Mont.word t.mem B (dN + 8 * i) *
              t.gpr .r18).toNat + (t.gpr .r3).toNat)).toNat)) ∧
        Keep [.r0, .r3, .r12, .r14, .r15, .r17] t t' := by
      refine WP.keep _ ?_ (by decide)
      mcrun [j14, j15, (hs.congr jk.wr).ld (show dN + 8 * i + 8 ≤ Z by omega),
        (hs.congr jk.wr).st (show dA + 8 * i + 8 ≤ Z by omega)]
    refine WP.mono hst fun t' ⟨⟨l14, l15, l17, lm, l3⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, jk.trans' lk⟩, l17⟩
    · rw [l14, show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega]
    · rw [l15, show dN + 8 * i + 8 = dN + 8 * (i + 1) by omega]
    · rw [lk.gpr .r18 (by decide), j18]
    · rw [lm]
      exact (jout.mono (Nat.le_refl _) (by omega)).trans
        ((writeW_outside _ B (d := dA + 8 * i) _ (by omega)).mono (by omega) (by omega))
    · have wn : Mont.word t.mem B (dN + 8 * i) = Mont.word s.mem B (dN + 8 * i) := jout.word (by omega) (by omega)
      have k := mul64_arith (Mont.word t.mem B (dN + 8 * i)) (t.gpr .r18) (t.gpr .r3)
      rw [← l3, wn, j18] at k
      rw [lm, fios_wordsVal_write_top _ _ _ _ _ (by omega), wordsVal_succ_top s.mem B dN i, Nat.mul_succ,
        Nat.pow_add, wn, j18]
      have e : 2 ^ (64 * i) * (BitVec.ofNat 64 ((Mont.word s.mem B (dN + 8 * i) * s.gpr .r18).toNat +
          (t.gpr .r3).toNat)).toNat + 2 ^ (64 * i) * 2 ^ 64 * (t'.gpr .r3).toNat =
          2 ^ (64 * i) * ((Mont.word s.mem B (dN + 8 * i)).toNat * (s.gpr .r18).toNat) +
            2 ^ (64 * i) * (t.gpr .r3).toNat := by
        rw [Nat.mul_assoc, ← Nat.mul_add, k, Nat.mul_add]
      rw [Nat.mul_add, ← jeq]
      generalize 2 ^ (64 * i) * (BitVec.ofNat 64 ((Mont.word s.mem B (dN + 8 * i) * s.gpr .r18).toNat +
          (t.gpr .r3).toNat)).toNat = a at e ⊢
      generalize 2 ^ (64 * i) * 2 ^ 64 * (t'.gpr .r3).toNat = b at e ⊢
      rw [show (s.gpr .r18).toNat * (2 ^ (64 * i) * (Mont.word s.mem B (dN + 8 * i)).toNat) =
        2 ^ (64 * i) * ((Mont.word s.mem B (dN + 8 * i)).toNat * (s.gpr .r18).toNat) by
          rw [Nat.mul_comm (s.gpr .r18).toNat, Nat.mul_assoc]]
      omega_using [e]
  · have hfin : WP isa (.block [.store .d .r3 .r14 0]) t fun t' =>
        t' = { t with mem := t.mem.writeW (off B (dA + 8 * w)) (t.gpr .r3) } := by
      prun [j14, (hs.congr jk.wr).st (show dA + 8 * w + 8 ≤ Z by omega)]
    refine WP.mono hfin fun t' e => ?_
    subst e
    refine ⟨?_, ?_, (jk.trans (Keep.mem _ _)).mono⟩
    · show wordsVal (t.mem.writeW (off B (dA + 8 * w)) (t.gpr .r3)) B dA (w + 1) = _
      rw [fios_wordsVal_write_top _ _ _ _ _ (by omega), ← jeq]
    · exact (jout.mono (Nat.le_refl _) (by omega)).trans
        ((writeW_outside t.mem B (d := dA + 8 * w) _ (by omega)).mono (by omega) (by omega))

/-- `subPass`, `x` (`w` words) at `dX` (`r5`), the accumulator's `w + 1`
words `a` at `dA` (`r8`) and zero in `r20`: the accumulator := `x 2^64 - a`
modulo `2^(64 (w + 1))`, with its borrow `b`. -/
theorem subPass_ok {s : State} {B : Addr} {Z dA dX w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B dA) (h5 : s.gpr .r5 = off B dX) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h20 : (s.gpr .r20).toNat = 0) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : dA + 8 * (w + 1) ≤ Z)
    (hX : dX + 8 * w ≤ Z) (dXA : dX + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dX) :
    WP isa subPass s fun t =>
      (∃ b < 2, wordsVal t.mem B dA (w + 1) + wordsVal s.mem B dA (w + 1) =
        wordsVal s.mem B dX w * 2 ^ 64 + 2 ^ (64 * (w + 1)) * b) ∧
      Mont.Outside B dA (8 * (w + 1)) s.mem t.mem ∧ Keep [.r0, .r3, .r14, .r15, .r17] s t := by
  have hnw := hs.nowrap
  unfold subPass
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .r14 .r8 0, .addi .r15 .r5 0, .load .d .r0 .r14 0, .subc .r0 .r20 .r0,
      .store .d .r0 .r14 0, .addi .r14 .r14 8, .lsr .d .r17 .r11 1]) s fun s₁ =>
      (s₁.gpr .r14 = off B (dA + 8) ∧ s₁.gpr .r15 = off B dX ∧ s₁.gpr .r17 = BitVec.ofNat 64 w ∧
        s₁.mem = s.mem.writeW (off B dA) (BitVec.ofNat 64 ((s.gpr .r20).toNat +
          (2 ^ 64 - 1 - (Mont.word s.mem B dA).toNat) + 1)) ∧
        s₁.ca = decide (2 ^ 64 ≤ (s.gpr .r20).toNat + (2 ^ 64 - 1 - (Mont.word s.mem B dA).toNat) + 1)) ∧
        Keep [.r0, .r3, .r14, .r15, .r17] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    mcrun [h8, h5, h11, BitVec.add_zero, mont_ofNat_shr1 (show w < 2 ^ 63 by omega),
      hs.ld (show dA + 8 ≤ Z by omega), hs.st (show dA + 8 ≤ Z by omega)]
  refine WP.mono hpre fun s₁ ⟨⟨i14, i15, i17, im, ica⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (dA + 8 * (i + 1)) ∧ t.gpr .r15 = off B (dX + 8 * i) ∧
      Mont.Outside B dA (8 * (i + 1)) s.mem t.mem ∧
      wordsVal t.mem B dA (i + 1) + wordsVal s.mem B dA (i + 1) =
        2 ^ 64 * wordsVal s.mem B dX i + 2 ^ (64 * (i + 1)) * (!t.ca).toNat ∧
      Keep [.r0, .r3, .r14, .r15, .r17] s t
  have I0 : Inv 0 s₁ := by
    refine ⟨by rw [i14], by rw [i15]; rfl, ?_, ?_, k₁⟩
    · rw [im]; exact (writeW_outside _ B (d := dA) _ (by omega)).mono (by omega) (by omega)
    · have k := sub64_arith (s.gpr .r20) (Mont.word s.mem B dA) true
      simp only [Bool.toNat_true, Bool.not_true, Bool.toNat_false, Nat.add_zero] at k
      show wordsVal s₁.mem B dA (0 + 1) + wordsVal s.mem B dA (0 + 1) =
        2 ^ 64 * wordsVal s.mem B dX 0 + 2 ^ (64 * (0 + 1)) * (!s₁.ca).toNat
      rw [im, ica, Nat.zero_add]
      simp only [wordsVal, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
      rw [Mont.word_writeW_self, k, h20, Nat.zero_add]
  refine WP.mono (wp_countdown (body := .block ([.load .d .r3 .r15 0, .load .d .r0 .r14 0, .sube .r0 .r3 .r0,
      .store .d .r0 .r14 0, .addi .r14 .r14 8, .addi .r15 .r15 8] ++ ([.subi .r17 .r17 1] : List Instr)))
    (cnt := .r17) (N := w) (by omega) (by omega) Inv (fun i hi t ⟨j14, j15, jout, jeq, jk⟩ hc => ?_) I0 i17)
    fun t ⟨_, _, tout, teq, tk⟩ => ⟨⟨(!t.ca).toNat, by cases t.ca <;> decide, by rw [teq, Nat.mul_comm]⟩, tout, tk⟩
  have hst : WP isa (.block [.load .d .r3 .r15 0, .load .d .r0 .r14 0, .sube .r0 .r3 .r0, .store .d .r0 .r14 0,
      .addi .r14 .r14 8, .addi .r15 .r15 8, .subi .r17 .r17 1]) t fun t' =>
      (t'.gpr .r14 = off B (dA + 8 * (i + 1) + 8) ∧ t'.gpr .r15 = off B (dX + 8 * i + 8) ∧
        t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dA + 8 * (i + 1))) (BitVec.ofNat 64 ((Mont.word t.mem B (dX + 8 * i)).toNat +
          (2 ^ 64 - 1 - (Mont.word t.mem B (dA + 8 * (i + 1))).toNat) + t.ca.toNat)) ∧
        t'.ca = decide (2 ^ 64 ≤ (Mont.word t.mem B (dX + 8 * i)).toNat +
          (2 ^ 64 - 1 - (Mont.word t.mem B (dA + 8 * (i + 1))).toNat) + t.ca.toNat)) ∧
      Keep [.r0, .r3, .r14, .r15, .r17] t t' := by
    refine WP.keep _ ?_ (by decide)
    mcrun [j14, j15, (hs.congr jk.wr).ld (show dX + 8 * i + 8 ≤ Z by omega),
      (hs.congr jk.wr).ld (show dA + 8 * (i + 1) + 8 ≤ Z by omega),
      (hs.congr jk.wr).st (show dA + 8 * (i + 1) + 8 ≤ Z by omega)]
  refine WP.mono hst fun t' ⟨⟨l14, l15, l17, lm, lca⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, jk.trans' lk⟩, l17⟩
  · rw [l14, show dA + 8 * (i + 1) + 8 = dA + 8 * (i + 1 + 1) by omega]
  · rw [l15, show dX + 8 * i + 8 = dX + 8 * (i + 1) by omega]
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega)).trans
      ((writeW_outside _ B (d := dA + 8 * (i + 1)) _ (by omega)).mono (by omega) (by omega))
  · have wa : Mont.word t.mem B (dA + 8 * (i + 1)) = Mont.word s.mem B (dA + 8 * (i + 1)) :=
      jout.word (by omega) (by omega)
    have wx : Mont.word t.mem B (dX + 8 * i) = Mont.word s.mem B (dX + 8 * i) := jout.word (by omega) (by omega)
    have k := sub64_arith (Mont.word t.mem B (dX + 8 * i)) (Mont.word t.mem B (dA + 8 * (i + 1))) t.ca
    rw [← lca, wa, wx] at k
    rw [lm, fios_wordsVal_write_top _ _ _ _ _ (by omega), wordsVal_succ_top s.mem B dA (i + 1),
      wordsVal_succ_top s.mem B dX i, wa, wx]
    have e : 2 ^ (64 * (i + 1)) * (BitVec.ofNat 64 ((Mont.word s.mem B (dX + 8 * i)).toNat +
        (2 ^ 64 - 1 - (Mont.word s.mem B (dA + 8 * (i + 1))).toNat) + t.ca.toNat)).toNat +
        2 ^ (64 * (i + 1)) * (Mont.word s.mem B (dA + 8 * (i + 1))).toNat + 2 ^ (64 * (i + 1)) * (!t.ca).toNat =
        2 ^ (64 * (i + 1)) * (Mont.word s.mem B (dX + 8 * i)).toNat +
          2 ^ (64 * (i + 1)) * 2 ^ 64 * (!t'.ca).toNat := by
      rw [← Nat.mul_add, ← Nat.mul_add, Nat.mul_assoc, ← Nat.mul_add, k]
    rw [show 2 ^ (64 * (i + 1 + 1)) = 2 ^ (64 * (i + 1)) * 2 ^ 64 by rw [Nat.mul_succ, Nat.pow_add],
      Nat.mul_add (2 ^ 64), ← Nat.mul_assoc (2 ^ 64), show 2 ^ 64 * 2 ^ (64 * i) = 2 ^ (64 * (i + 1)) by
        rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]]
    generalize 2 ^ (64 * (i + 1)) * (BitVec.ofNat 64 ((Mont.word s.mem B (dX + 8 * i)).toNat +
        (2 ^ 64 - 1 - (Mont.word s.mem B (dA + 8 * (i + 1))).toNat) + t.ca.toNat)).toNat = a at e ⊢
    generalize 2 ^ (64 * (i + 1)) * (Mont.word s.mem B (dA + 8 * (i + 1))).toNat = b at e ⊢
    generalize 2 ^ (64 * (i + 1)) * (!t.ca).toNat = c at e jeq ⊢
    generalize 2 ^ (64 * (i + 1)) * (Mont.word s.mem B (dX + 8 * i)).toNat = d at e ⊢
    generalize 2 ^ (64 * (i + 1)) * 2 ^ 64 * (!t'.ca).toNat = f at e ⊢
    omega_using [e, jeq]

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

/-- `addBack`, `n` (`w` words) at `dN` (`r10`), the accumulator's `w + 1`
words `t` at `dA` (`r8`) and zero in `r20`: `t := t + n` modulo
`2^(64 (w + 1))` (with the carry `c`) if `t`'s top half is set. -/
theorem addBack_ok {s : State} {B : Addr} {Z dA dN w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B dA) (h10 : s.gpr .r10 = off B dN) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
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
  have hpre : WP isa (.block [.lsl .r14 .r11 2, .add .r14 .r14 .r8, .load .d .r0 .r14 0, .lsr .d .r0 .r0 63,
      .sub .r12 .r20 .r0, .addi .r14 .r8 0, .addi .r15 .r10 0, .lsr .d .r17 .r11 1, .addc .r0 .r20 .r20]) s fun s₁ =>
      (s₁.gpr .r14 = off B dA ∧ s₁.gpr .r15 = off B dN ∧ s₁.gpr .r17 = BitVec.ofNat 64 w ∧
        s₁.gpr .r12 = (if 2 ^ 63 ≤ (Mont.word s.mem B (dA + 8 * w)).toNat then BitVec.allOnes 64 else 0) ∧ s₁.ca = false ∧ s₁.mem = s.mem) ∧
        Keep [.r0, .r3, .r12, .r14, .r15, .r17] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    mcrun [h8, h10, h11, h20, BitVec.add_zero, mont_ofNat_shr1 (show w < 2 ^ 63 by omega), ea_add,
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

/-! ## A word step -/

theorem wordsVal_copy {m m' : Mem} {B : Addr} {a b : Nat} :
    ∀ k, (∀ i < k, Mont.word m' B (b + 8 * i) = Mont.word m B (a + 8 * i)) → wordsVal m' B b k = wordsVal m B a k
  | 0, _ => rfl
  | k + 1, h => by
    rw [wordsVal_succ_top, wordsVal_succ_top, wordsVal_copy k fun i hi => h i (by omega), h k (by omega)]

/-- `wordStep`, in the arrays of `vg_rsa_mont_mul` (`n` in array 0, `x < n`
in array 1, `P = 2^z` and `d' = ⌊n P / 2^(64 (w - 1))⌋ ≥ 2^63` in the
temporary): `x := x 2^64 mod n`, changing only arrays 1 and 2. -/
theorem wordStep_ok {s : State} {B : Addr} {Z w z : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B (slot w 2)) (h9 : s.gpr .r9 = off B (slot w 3))
    (h10 : s.gpr .r10 = off B (slot w 0)) (h5 : s.gpr .r5 = off B (slot w 1))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 3 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z)
    (hP : (Mont.word s.mem B (slot w 3)).toNat = 2 ^ z) (hz : z ≤ 63)
    (hd : (Mont.word s.mem B (slot w 3 + 8)).toNat = wordsVal s.mem B (slot w 0) w * 2 ^ z / 2 ^ (64 * (w - 1)))
    (hd63 : 2 ^ 63 ≤ wordsVal s.mem B (slot w 0) w * 2 ^ z / 2 ^ (64 * (w - 1)))
    (hx : wordsVal s.mem B (slot w 1) w < wordsVal s.mem B (slot w 0) w) :
    WP isa wordStep s fun t =>
      wordsVal t.mem B (slot w 1) w = wordsVal s.mem B (slot w 1) w * 2 ^ 64 % wordsVal s.mem B (slot w 0) w ∧
      Mont.Outside B (slot w 1) (16 * (w + 2)) s.mem t.mem ∧ Keep quotRegs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  generalize hX : wordsVal s.mem B (slot w 1) w = X at hx ⊢
  generalize hN : wordsVal s.mem B (slot w 0) w = N at hx hd hd63 ⊢
  have hXd : wordsVal s.mem B (slot w 1) w * 2 ^ z / 2 ^ (64 * (w - 1)) ≤ (Mont.word s.mem B (slot w 3 + 8)).toNat := by
    rw [hd, hX]; exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.le_of_lt hx))
  unfold wordStep
  -- `q̂`.
  refine WP.seq (WP.mono (quot_ok hs h5 h9 h11 hw hw' hZ hP hz (by omega) hXd) fun s₁ ⟨q1, m1, k1, z1⟩ => ?_)
  rw [hX, hd] at q1
  have g1 : ∀ r ∈ [Reg.r5, .r8, .r9, .r10, .r11], s₁.gpr r = s.gpr r := fun r hr => k1.gpr r (by revert r hr; decide)
  -- `q̂ n`.
  refine WP.seq (WP.mono (mulRow_ok (dA := slot w 2) (dN := slot w 0) (hs.congr k1.wr)
    ((g1 .r8 (by decide)).trans h8) ((g1 .r10 (by decide)).trans h10) ((g1 .r11 (by decide)).trans h11)
    (by omega) hw' (by omega) (by omega) (by omega)) fun s₂ ⟨a2, o2, k2⟩ => ?_)
  rw [m1, hN, q1] at a2
  have g2 : ∀ r ∈ [Reg.r5, .r8, .r9, .r10, .r11, .r20], s₂.gpr r = s₁.gpr r :=
    fun r hr => k2.gpr r (by revert r hr; decide)
  have x2 : wordsVal s₂.mem B (slot w 1) w = X := by rw [o2.wordsVal (by omega) (by omega), m1, hX]
  -- `x 2^64 - q̂ n`.
  refine WP.seq (WP.mono (subPass_ok (dA := slot w 2) (dX := slot w 1) (hs.congr (k1.trans k2).wr)
    ((g2 .r8 (by decide)).trans ((g1 .r8 (by decide)).trans h8))
    ((g2 .r5 (by decide)).trans ((g1 .r5 (by decide)).trans h5))
    ((g2 .r11 (by decide)).trans ((g1 .r11 (by decide)).trans h11))
    (by rw [g2 .r20 (by decide), z1]; rfl) (by omega) hw' (by omega) (by omega) (by omega))
    fun s₃ ⟨⟨b, hb, a3⟩, o3, k3⟩ => ?_)
  rw [a2, x2] at a3
  have k13 := (k1.trans k2).trans k3
  have g3 : ∀ r ∈ [Reg.r5, .r8, .r9, .r10, .r11], s₃.gpr r = s.gpr r :=
    fun r hr => k13.gpr r (by revert r hr; decide)
  have z3 : s₃.gpr .r20 = BitVec.ofNat 64 0 := ((k2.trans k3).gpr .r20 (by decide)).trans z1
  have n3 : wordsVal s₃.mem B (slot w 0) w = N := by
    rw [o3.wordsVal (by omega) (by omega), o2.wordsVal (by omega) (by omega), m1, hN]
  -- `n` added twice while negative.
  refine WP.seq (WP.mono (addBack_ok (dA := slot w 2) (dN := slot w 0) (hs.congr k13.wr)
    ((g3 .r8 (by decide)).trans h8) ((g3 .r10 (by decide)).trans h10) ((g3 .r11 (by decide)).trans h11)
    z3 (by omega) hw' (by omega)
    (by omega) (by omega)) fun s₄ ⟨⟨c1, hc1, a4⟩, o4, k4⟩ => ?_)
  have z4 : s₄.gpr .r20 = BitVec.ofNat 64 0 := (k4.gpr .r20 (by decide)).trans z3
  have g4 : ∀ r ∈ [Reg.r5, .r8, .r9, .r10, .r11], s₄.gpr r = s.gpr r :=
    fun r hr => (k4.gpr r (by revert r hr; decide)).trans (g3 r hr)
  have n4 : wordsVal s₄.mem B (slot w 0) w = N := by rw [o4.wordsVal (by omega) (by omega), n3]
  rw [n3] at a4
  refine WP.seq (WP.mono (addBack_ok (dA := slot w 2) (dN := slot w 0) (hs.congr (k13.trans k4).wr)
    ((g4 .r8 (by decide)).trans h8) ((g4 .r10 (by decide)).trans h10) ((g4 .r11 (by decide)).trans h11)
    z4 (by omega) hw' (by omega) (by omega) (by omega)) fun s₅ ⟨⟨c2, hc2, a5⟩, o5, k5⟩ => ?_)
  rw [n4] at a5
  have k15 := (k13.trans k4).trans k5
  have g5 : ∀ r ∈ [Reg.r5, .r8, .r9, .r10, .r11], s₅.gpr r = s.gpr r :=
    fun r hr => (k5.gpr r (by revert r hr; decide)).trans (g4 r hr)
  -- `x 2^64 mod n`.
  have hN0 : 0 < N := by omega
  have hNlt : N < 2 ^ (64 * w) := hN ▸ wordsVal_lt _ _ _ _
  have hW : 4 * N < 2 ^ (64 * (w + 1)) / 2 := by
    rw [show 2 ^ (64 * (w + 1)) / 2 = 2 ^ (64 * w) * 2 ^ 63 by
      rw [Nat.mul_succ, Nat.pow_add, show (2 : Nat) ^ 64 = 2 ^ 63 * 2 from rfl, ← Nat.mul_assoc,
        Nat.mul_div_cancel _ (by decide)]]
    have := Nat.mul_le_mul_left (2 ^ (64 * w)) (show 8 ≤ 2 ^ 63 by decide)
    omega
  obtain ⟨hge, hle⟩ := qhat_norm (X := X) (M := N) (P := 2 ^ z) (K := 64 * (w - 2)) (Nat.two_pow_pos z) hx
    (by rw [show 64 * (w - 2) + 64 = 64 * (w - 1) by omega]; exact hd63)
  rw [show 64 * (w - 2) + 64 = 64 * (w - 1) by omega] at hge hle
  have hT := wordStepQ_val hN0 hW hge hle (wordsVal_lt _ _ _ _) hb a3 (wordsVal_lt _ _ _ _) hc1 a4
    (wordsVal_lt _ _ _ _) hc2 a5
  -- The low `w` words of the accumulator into `x`.
  have hlow : wordsVal s₅.mem B (slot w 2) w = X * 2 ^ 64 % N := by
    have e5 := wordsVal_succ_top s₅.mem B (slot w 2) w
    have hr := Nat.mod_lt (X * 2 ^ 64) hN0
    rw [hT] at e5
    rcases Nat.eq_zero_or_pos (Mont.word s₅.mem B (slot w 2 + 8 * w)).toNat with h | h
    · rw [h, Nat.mul_zero, Nat.add_zero] at e5; exact e5.symm
    · have := Nat.le_mul_of_pos_right (2 ^ (64 * w)) h
      omega
  refine WP.seq (WP.mono (WP.keep [.r14, .r15] (Q := fun t => t.gpr .r14 = off B (slot w 1) ∧
      t.gpr .r15 = off B (slot w 2) ∧ t.mem = s₅.mem)
    (by prun [g5 .r5 (by decide), g5 .r8 (by decide), h5, h8, BitVec.add_zero]) (by decide))
    fun s₆ ⟨⟨a14, a15, m6⟩, k6⟩ => ?_)
  refine WP.mono (Crt.copySub_ok (a := slot w 2) (b := slot w 1) (w := w) (hs.congr (k15.trans k6).wr) a15 a14
    ((k6.gpr _ (by decide)).trans ((g5 .r11 (by decide)).trans h11)) (by omega) hw' (by omega) (by omega)
    (by omega)) fun t ⟨⟨tc, tout⟩, tk⟩ => ⟨?_, ?_, (k15.trans (k6.trans tk)).mono (by decide)⟩
  · rw [wordsVal_copy w tc, m6, hlow]
  · have tout' : Mont.Outside B (slot w 1) (8 * w) s₆.mem t.mem := fun x hx => tout x hx
    rw [m6] at tout'
    rw [m1] at o2
    exact ((((o2.mono (by omega) (by omega)).trans (o3.mono (by omega) (by omega))).trans
      (o4.mono (by omega) (by omega))).trans (o5.mono (by omega) (by omega))).trans (tout'.mono (by omega) (by omega))

/-- `wordSteps`, from `x = 2^(64 (w - 1)) < n` and `norm`'s `P` and `d'` in
the temporary: `x := 2^(128 w) mod n`, changing only arrays 1 and 2. -/
theorem wordSteps_ok {s : State} {B : Addr} {Z w z : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B (slot w 2)) (h9 : s.gpr .r9 = off B (slot w 3))
    (h10 : s.gpr .r10 = off B (slot w 0)) (h5 : s.gpr .r5 = off B (slot w 1))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 3 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z)
    (hP : (Mont.word s.mem B (slot w 3)).toNat = 2 ^ z) (hz : z ≤ 63)
    (hd : (Mont.word s.mem B (slot w 3 + 8)).toNat = wordsVal s.mem B (slot w 0) w * 2 ^ z / 2 ^ (64 * (w - 1)))
    (hd63 : 2 ^ 63 ≤ wordsVal s.mem B (slot w 0) w * 2 ^ z / 2 ^ (64 * (w - 1)))
    (hx : wordsVal s.mem B (slot w 1) w = 2 ^ (64 * (w - 1)))
    (hxN : 2 ^ (64 * (w - 1)) < wordsVal s.mem B (slot w 0) w) :
    WP isa wordSteps s fun t =>
      wordsVal t.mem B (slot w 1) w = 2 ^ (128 * w) % wordsVal s.mem B (slot w 0) w ∧
      Mont.Outside B (slot w 1) (16 * (w + 2)) s.mem t.mem ∧ Keep (.r4 :: quotRegs) s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  generalize hN : wordsVal s.mem B (slot w 0) w = N at hd hd63 hxN ⊢
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
  refine WP.seq (WP.mono (wordStep_ok (z := z) (hs.congr tk.wr) ((g .r8 (by decide)).trans h8)
    ((g .r9 (by decide)).trans h9) ((g .r10 (by decide)).trans h10) ((g .r5 (by decide)).trans h5)
    ((g .r11 (by decide)).trans h11) hw hw' hZ (by rw [w3]; exact hP) hz (by rw [w38, n0]; exact hd)
    (by rw [n0]; exact hd63) (by rw [tx, n0]; exact Nat.mod_lt _ hN0)) fun t₁ ⟨x1, o1, k1⟩ => ?_)
  refine WP.mono (subi_ok t₁ .r4 (by decide)) fun t₂ e2 => ?_
  subst e2
  refine ⟨⟨?_, by rw [mem_write]; exact to.trans o1, ((tk.trans k1).trans (Keep.write _ _ _)).mono (by decide)⟩, ?_⟩
  · rw [mem_write, x1, tx, n0, Nat.mod_mul_mod, ← Nat.pow_add, Nat.mul_succ, Nat.add_assoc]
  · gsimp; rw [k1.gpr .r4 (by decide)]

end VG.Proof.Bignum.PPC64LE
