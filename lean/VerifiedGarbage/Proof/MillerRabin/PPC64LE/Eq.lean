module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry

/-!
# The Miller–Rabin round on PPC64LE: comparisons

`eqMask_ok`: `eqMask d a b` leaves in `d` the mask of the `w` words of
arrays `a` and `b` being equal: the `or` of their `xor`s is zero exactly
when every word is equal (`wordsVal_eq_iff`), and `0 −` it does not borrow
exactly when it is zero.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE
open VG.Proof.Bignum (slot slot_sep)

/-- The mask of `b`: all ones if `b`, else 0. -/
abbrev mask (b : Bool) : BitVec 64 := BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0)

/-- Two numbers of 64-bit words are equal exactly when their words are. -/
theorem wordsVal_eq_iff (m : Mem) (B : Addr) (da db : Nat) :
    ∀ n, wordsVal m B da n = wordsVal m B db n ↔ ∀ k < n, word m B (da + 8 * k) = word m B (db + 8 * k)
  | 0 => ⟨fun _ _ h => absurd h (by omega_arith), fun _ => rfl⟩
  | n + 1 => by
    rw [wordsVal_succ_top, wordsVal_succ_top]
    have ha := wordsVal_lt m B da n
    have hb := wordsVal_lt m B db n
    constructor
    · intro h
      have hd : (word m B (da + 8 * n)).toNat = (word m B (db + 8 * n)).toNat := by
        have := congrArg (· / 2 ^ (64 * n)) h
        rwa [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
          Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb, Nat.zero_add, Nat.zero_add] at this
      rw [hd, Nat.add_right_cancel_iff] at h
      intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact (wordsVal_eq_iff m B da db n).mp h k hk
      · exact BitVec.eq_of_toNat_eq hd
    · intro h
      rw [(wordsVal_eq_iff m B da db n).mpr fun k hk => h k (by omega_arith), h n (by omega_arith)]

/-- `(x | (a ⊕ b))` is zero exactly when `x` is and `a = b`. -/
theorem or_xor_zero (x a b : BitVec 64) : (x ||| (b ^^^ a) = 0) ↔ (x = 0 ∧ a = b) := by
  rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]
  exact and_congr Iff.rfl eq_comm

/-- `0 − x` borrows exactly when `x ≠ 0`: the mask of `x = 0`. -/
theorem zero_mask (x : BitVec 64) :
    0#64 - BitVec.ofNat 64 ((0#64).toNat + (decide (18446744073709551615 ≤ (0#64).toNat +
      (18446744073709551616 - 1 - x.toNat))).toNat) = mask (decide (x = 0)) := by
  have e : x = 0 ↔ x.toNat = 0 := ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
  have hx := x.isLt
  have hd : decide (18446744073709551615 ≤ (0#64).toNat + (18446744073709551616 - 1 - x.toNat)) =
      decide (x = 0) := by
    simp only [BitVec.toNat_zero, decide_eq_decide, e]; omega_arith
  rw [hd]
  cases decide (x = 0) <;> rfl

/-- The registers `eqMask d` writes. -/
def eqRegs (d : Reg) : List Reg := [.r0, .r3, .r4, .r14, .r15, .r17, d]

theorem sub1_sign {x : BitVec 64} (hx : x.toNat < 2 ^ 32) :
    (x - BitVec.ofNat 64 1) >>> 63 = BitVec.ofNat 64 (if x = 0 then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  have : x = 0 ↔ x.toNat = 0 := ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    this]
  split <;> omega_arith

theorem eqMask_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) (d : Reg) {a b : Nat} (ha : a < 28) (hb : b < 28) :
    WP isa (eqMask d a b) s fun t =>
      (t.gpr d = mask (decide (val32 s.mem B (slot w a) (2 * w) = val32 s.mem B (slot w b) (2 * w))) ∧
        t.mem = s.mem) ∧ Keep (eqRegs d) s t := by
  have hnw := h.hs.nowrap
  have hA := h.arr ha
  have hB := h.arr hb
  have hw := h.hw
  have hw' := h.hw'
  unfold eqMask
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .r14) (by decide) (by decide) a) fun t₁ ⟨⟨a14, m1⟩, k1⟩ => ?_
  have e1 := h.keep k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (e1.base (rd := .r15) (by decide) (by decide) b) fun t₂ ⟨⟨a15, m2⟩, k2⟩ => ?_
  have e2 := e1.keep k2 (by decide)
  have hpre : WP isa (.block [.lsr .d .r17 .r11 1, .li .r3 0]) t₂ fun t₃ =>
      (t₃.gpr .r17 = BitVec.ofNat 64 w ∧ t₃.gpr .r3 = 0 ∧ t₃.mem = t₂.mem) ∧ Keep [.r17, .r3] t₂ t₃ := by
    refine WP.keep _ ?_ (by decide)
    prun [e2.h11, mont_ofNat_shr1 (show w < 2 ^ 63 by omega_arith)]
    rfl
  refine WP.mono hpre fun t₃ ⟨⟨a17, a3, m3⟩, k3⟩ => ?_
  have k13 := ((k1.trans k2).trans k3)
  have hm3 : t₃.mem = s.mem := by rw [m3, m2, m1]
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (slot w a + 8 * i) ∧ t.gpr .r15 = off B (slot w b + 8 * i) ∧
      (t.gpr .r3 = 0 ↔ ∀ k < i, word s.mem B (slot w a + 8 * k) = word s.mem B (slot w b + 8 * k)) ∧
      t.mem = s.mem ∧ Keep [.r0, .r3, .r4, .r14, .r15, .r17] s t
  refine WP.seq (WP.mono (wp_countdown (body := .block ([.load .d .r0 .r14 0, .load .d .r4 .r15 0,
      .logic .xor .r0 .r0 .r4, .logic .or .r3 .r3 .r0, .addi .r14 .r14 8, .addi .r15 .r15 8] ++
      ([.subi .r17 .r17 1] : List Instr))) (cnt := .r17) (N := w) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j14, j15, j3, jm, jk⟩ _ => ?_)
    ⟨by rw [k3.gpr .r14 (by decide), k2.gpr .r14 (by decide), a14]; rfl, by rw [k3.gpr .r15 (by decide), a15]; rfl,
      ⟨fun _ _ hk => absurd hk (by omega_arith), fun _ => a3⟩, hm3, k13.mono (by decide)⟩ a17)
    fun t hI => ?_)
  · have hs := h.hs.congr jk.wr
    have hst : WP isa (.block [.load .d .r0 .r14 0, .load .d .r4 .r15 0, .logic .xor .r0 .r0 .r4,
        .logic .or .r3 .r3 .r0, .addi .r14 .r14 8, .addi .r15 .r15 8, .subi .r17 .r17 1]) t fun t' =>
        (t'.gpr .r14 = off B (slot w a + 8 * i + 8) ∧ t'.gpr .r15 = off B (slot w b + 8 * i + 8) ∧
          t'.gpr .r3 = t.gpr .r3 ||| (word t.mem B (slot w b + 8 * i) ^^^ word t.mem B (slot w a + 8 * i)) ∧
          t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧ t'.mem = t.mem) ∧
        Keep [.r0, .r3, .r4, .r14, .r15, .r17] t t' := by
      refine WP.keep _ ?_ (by decide)
      prun [j14, j15, hs.ld (show slot w a + 8 * i + 8 ≤ Z by omega_arith),
        hs.ld (show slot w b + 8 * i + 8 ≤ Z by omega_arith)]
      rw [BitVec.xor_comm]
    refine WP.mono hst fun t' ⟨⟨l14, l15, l3, l17, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, lm.trans jm, (jk.trans lk).mono
      (by decide)⟩, l17⟩
    · rw [l14, show slot w a + 8 * i + 8 = slot w a + 8 * (i + 1) by omega_arith]
    · rw [l15, show slot w b + 8 * i + 8 = slot w b + 8 * (i + 1) by omega_arith]
    · rw [l3, or_xor_zero, j3, jm]
      constructor
      · rintro ⟨hk, he⟩ k hk'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with hk' | rfl
        · exact hk k hk'
        · exact he
      · intro hk
        exact ⟨fun k hk' => hk k (by omega_arith), hk i (by omega_arith)⟩
  · obtain ⟨_, _, j3, jm, jk⟩ := hI
    refine WP.mono (WP.keep [.r0, .r3, d] (Q := fun t' => t'.gpr d = mask (decide (val32 s.mem B (slot w a) (2 * w) =
        val32 s.mem B (slot w b) (2 * w))) ∧ t'.mem = t.mem) ?_ (by simp [writesOnly, instrs, dstOf, Instr.writesLr]))
      fun t' ⟨⟨hd', hm'⟩, k'⟩ => ⟨⟨hd', hm'.trans jm⟩, (jk.trans k').mono (by simp [eqRegs])⟩
    have hv : (val32 s.mem B (slot w a) (2 * w) = val32 s.mem B (slot w b) (2 * w)) ↔ t.gpr .r3 = 0 := by
      rw [← wordsVal_eq_val32, ← wordsVal_eq_val32, wordsVal_eq_iff, j3]
    mcrun []
    rw [zero_mask]
    simp only [hv]

end VG.Proof.MillerRabin.PPC64LE
