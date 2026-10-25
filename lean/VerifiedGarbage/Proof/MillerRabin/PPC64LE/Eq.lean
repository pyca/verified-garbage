module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The Miller–Rabin round on PPC64LE: comparisons

`eqMask_ok`: `eqMask d a b` leaves in `d` the mask of the `2 w` digits of
arrays `a` and `b` being equal: the `or` of their `xor`s, below `2^32`, is
zero exactly when every digit is equal (`val32_eq_iff`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE
open VG.Proof.Bignum (slot slot_sep)

/-- The mask of `b`: all ones if `b`, else 0. -/
abbrev mask (b : Bool) : BitVec 64 := BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0)

/-- Two numbers of 32-bit digits are equal exactly when their digits are. -/
theorem val32_eq_iff (m : Mem) (B : Addr) (da db : Nat) :
    ∀ n, val32 m B da n = val32 m B db n ↔ ∀ k < n, w32 m B (da + 4 * k) = w32 m B (db + 4 * k)
  | 0 => ⟨fun _ _ h => absurd h (by omega_arith), fun _ => rfl⟩
  | n + 1 => by
    rw [val32_succ, val32_succ]
    have ha := val32_lt m B da n
    have hb := val32_lt m B db n
    constructor
    · intro h
      have hd : w32 m B (da + 4 * n) = w32 m B (db + 4 * n) := by
        have := congrArg (· / 2 ^ (32 * n)) h
        rwa [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
          Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb, Nat.zero_add, Nat.zero_add] at this
      rw [hd, Nat.add_right_cancel_iff] at h
      intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact (val32_eq_iff m B da db n).mp h k hk
      · exact hd
    · intro h
      rw [(val32_eq_iff m B da db n).mpr fun k hk => h k (by omega_arith), h n (by omega_arith)]

/-- `(x | (a ⊕ b))` is zero exactly when `x` is and `a = b`. -/
theorem or_xor_zero (x : BitVec 64) (a b : BitVec 32) :
    (x ||| (b.setWidth 64 ^^^ a.setWidth 64) = 0) ↔ (x = 0 ∧ a = b) := by
  rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h => by rw [h]⟩
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth] at this
  rw [Nat.mod_eq_of_lt (by have := b.isLt; omega_arith), Nat.mod_eq_of_lt (by have := a.isLt; omega_arith)] at this
  exact this.symm

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
  have hpre : WP isa (.block [.addi .r17 .r11 0, .li .r3 0]) t₂ fun t₃ =>
      (t₃.gpr .r17 = BitVec.ofNat 64 (2 * w) ∧ t₃.gpr .r3 = 0 ∧ t₃.mem = t₂.mem) ∧ Keep [.r17, .r3] t₂ t₃ := by
    refine WP.keep _ ?_ (by decide)
    prun [e2.h11, BitVec.add_zero]
    rfl
  refine WP.mono hpre fun t₃ ⟨⟨a17, a3, m3⟩, k3⟩ => ?_
  have k13 := ((k1.trans k2).trans k3)
  have hm3 : t₃.mem = s.mem := by rw [m3, m2, m1]
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (slot w a + 4 * i) ∧ t.gpr .r15 = off B (slot w b + 4 * i) ∧
      (t.gpr .r3).toNat < 2 ^ 32 ∧
      (t.gpr .r3 = 0 ↔ ∀ k < i, w32 s.mem B (slot w a + 4 * k) = w32 s.mem B (slot w b + 4 * k)) ∧
      t.mem = s.mem ∧ Keep [.r0, .r3, .r4, .r14, .r15, .r17] s t
  refine WP.seq (WP.mono (wp_countdown (body := .block ([.load .w .r0 .r14 0, .load .w .r4 .r15 0,
      .logic .xor .r0 .r0 .r4, .logic .or .r3 .r3 .r0, .addi .r14 .r14 4, .addi .r15 .r15 4] ++
      ([.subi .r17 .r17 1] : List Instr))) (cnt := .r17) (N := 2 * w) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j14, j15, j3l, j3, jm, jk⟩ _ => ?_)
    ⟨by rw [k3.gpr .r14 (by decide), k2.gpr .r14 (by decide), a14]; rfl, by rw [k3.gpr .r15 (by decide), a15]; rfl,
      by rw [a3]; decide, ⟨fun _ _ hk => absurd hk (by omega_arith), fun _ => a3⟩, hm3, k13.mono (by decide)⟩ a17)
    fun t hI => ?_)
  · have hs := h.hs.congr jk.wr
    have hst : WP isa (.block [.load .w .r0 .r14 0, .load .w .r4 .r15 0, .logic .xor .r0 .r0 .r4,
        .logic .or .r3 .r3 .r0, .addi .r14 .r14 4, .addi .r15 .r15 4, .subi .r17 .r17 1]) t fun t' =>
        (t'.gpr .r14 = off B (slot w a + 4 * i + 4) ∧ t'.gpr .r15 = off B (slot w b + 4 * i + 4) ∧
          t'.gpr .r3 = t.gpr .r3 ||| ((t.mem.readW (off B (slot w b + 4 * i)) 32).setWidth 64 ^^^
            (t.mem.readW (off B (slot w a + 4 * i)) 32).setWidth 64) ∧
          t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧ t'.mem = t.mem) ∧
        Keep [.r0, .r3, .r4, .r14, .r15, .r17] t t' := by
      refine WP.keep _ ?_ (by decide)
      prun [j14, j15, hs.ld (show slot w a + 4 * i + 4 ≤ Z by omega_arith),
        hs.ld (show slot w b + 4 * i + 4 ≤ Z by omega_arith)]
      rw [BitVec.xor_comm]
    refine WP.mono hst fun t' ⟨⟨l14, l15, l3, l17, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, lm.trans jm, (jk.trans lk).mono
      (by decide)⟩, l17⟩
    · rw [l14, show slot w a + 4 * i + 4 = slot w a + 4 * (i + 1) by omega_arith]
    · rw [l15, show slot w b + 4 * i + 4 = slot w b + 4 * (i + 1) by omega_arith]
    · rw [l3, BitVec.toNat_or, BitVec.toNat_xor, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
      exact Nat.or_lt_two_pow j3l (Nat.xor_lt_two_pow (by omega_arith) (by omega_arith))
    · rw [l3, or_xor_zero, j3, jm]
      constructor
      · rintro ⟨hk, he⟩ k hk'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with hk' | rfl
        · exact hk k hk'
        · exact congrArg BitVec.toNat he
      · intro hk
        exact ⟨fun k hk' => hk k (by omega_arith), BitVec.eq_of_toNat_eq (hk i (by omega_arith))⟩
  · obtain ⟨_, _, j3l, j3, jm, jk⟩ := hI
    refine WP.mono (WP.keep [.r0, .r3, d] (Q := fun t' => t'.gpr d = mask (decide (val32 s.mem B (slot w a) (2 * w) =
        val32 s.mem B (slot w b) (2 * w))) ∧ t'.mem = t.mem) ?_ (by simp [writesOnly, instrs, dstOf, Instr.writesLr]))
      fun t' ⟨⟨hd', hm'⟩, k'⟩ => ⟨⟨hd', hm'.trans jm⟩, (jk.trans k').mono (by simp [eqRegs])⟩
    have hv : (val32 s.mem B (slot w a) (2 * w) = val32 s.mem B (slot w b) (2 * w)) ↔ t.gpr .r3 = 0 := by
      rw [val32_eq_iff, j3]
    prun [sub1_sign j3l]
    by_cases hz : t.gpr .r3 = 0
    · simp [hz, hv.mpr hz]
    · simp [show t.gpr .r3 ≠ 0#64 from hz, show ¬ val32 s.mem B (slot w a) (2 * w) = val32 s.mem B (slot w b) (2 * w) from
        fun e => hz (hv.mp e)]

end VG.Proof.MillerRabin.PPC64LE
