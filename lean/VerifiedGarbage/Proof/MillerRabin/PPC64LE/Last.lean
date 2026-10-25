module

import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Exp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Eq
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Window
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCore
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont

/-!
# The Miller–Rabin round on PPC64LE: the last squarings

`last_ok j`: `y := y²` and the flag or'ed with `y = −1` under the mask of
`σ > j`, from the lowest set bit `l` of `c − 1`'s lowest nonzero word, after
`E` (`RsaKeyGen.sig_mask1`–`3`): `wSq c (σ > j)`.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE
open VG.Proof.Bignum (slot slot_sep)
open VG.Proof.RsaKeyGen (wSq mrSig mrA sigOf)

/-- `K` of `σ > j`, as `repeat16` builds it. -/
def sigK64 (j : Nat) : BitVec 64 :=
  if j = 1 then 0xDDDDDDDDDDDDDDDD#64 else if j = 2 then 0x9999999999999999#64 else 0x1111111111111111#64

theorem repeat16_val (j : Nat) (hj : j = 1 ∨ j = 2 ∨ j = 3) :
    ((((sigK j ++ (0 : BitVec 16)).signExtend 64 ||| (sigK j).setWidth 64) <<< 32 |||
      (sigK j).setWidth 64 <<< 16) ||| (sigK j).setWidth 64) = sigK64 j := by
  rcases hj with rfl | rfl | rfl <;> decide

theorem sig_mask (j : Nat) (hj : j = 1 ∨ j = 2 ∨ j = 3) {k : Nat} (hk : k < 64) :
    (BitVec.twoPow 64 k &&& sigK64 j = 0) = ¬ (j < sigOf k) := by
  rcases hj with rfl | rfl | rfl
  · exact VG.Proof.RsaKeyGen.sig_mask1 k hk
  · exact VG.Proof.RsaKeyGen.sig_mask2 k hk
  · exact VG.Proof.RsaKeyGen.sig_mask3 k hk

/-- The mask of a word being nonzero. -/
theorem nz64_mask (x : BitVec 64) :
    BitVec.ofNat 64 0 - (BitVec.ofNat 64 0 - (x >>> 1 ||| x &&& BitVec.ofNat 64 1)) >>> 63 =
      mask (decide (x ≠ 0)) := by
  have ht : (x >>> 1 ||| x &&& BitVec.ofNat 64 1).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_or]
    apply Nat.or_lt_two_pow
    · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := x.isLt; omega_arith
    · rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt (Nat.and_le_right) (by decide)
  have hz : (x >>> 1 ||| x &&& BitVec.ofNat 64 1) = 0 ↔ x = 0 := by
    rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.or_eq_zero_iff]
    constructor
    · rintro ⟨h1, h2⟩
      apply BitVec.eq_of_toNat_eq
      have a := congrArg BitVec.toNat h1
      have b := congrArg BitVec.toNat h2
      simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_and, BitVec.toNat_ofNat,
        Nat.reducePow, Nat.reduceMod, Nat.and_one_is_mod] at a b
      simp only [BitVec.toNat_ofNat]
      omega_arith
    · rintro rfl; decide
  by_cases e : x = 0
  · subst e; decide
  · have hne : (x >>> 1 ||| x &&& BitVec.ofNat 64 1).toNat ≠ 0 :=
      fun h => e (hz.mp (BitVec.eq_of_toNat_eq h))
    have hs : (BitVec.ofNat 64 0 - (x >>> 1 ||| x &&& BitVec.ofNat 64 1)) >>> 63 = BitVec.ofNat 64 1 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      omega_arith
    rw [hs, show decide (x ≠ 0) = true from decide_eq_true e]
    rfl

theorem mask_and (p q : Bool) : mask p &&& mask q = mask (p && q) := by cases p <;> cases q <;> rfl

/-- The mask of `σ > j` from the word after `E`. -/
theorem sig_word {c j : Nat} (hj : j = 1 ∨ j = 2 ∨ j = 3) :
    decide (BitVec.twoPow 64 (mrA c % 64) &&& sigK64 j ≠ 0) = decide (j < mrSig c) := by
  have h := sig_mask j hj (k := mrA c % 64) (Nat.mod_lt _ (by decide))
  rw [VG.Proof.RsaKeyGen.sigOf_mod] at h
  apply decide_eq_decide.mpr
  rw [show mrSig c = sigOf (mrA c) from rfl, ne_eq, h, Decidable.not_not]

/-- A squaring after the windows: `wSq c (σ > j)`. -/
theorem last_ok {rs : List Reg} {s₀ s : State} {B : Addr} {Z w c b Y : Nat} {P : Bool}
    (h : WSt rs s₀ s B Z w c b) (hc3 : 3 ≤ c) (hodd : c % 2 = 1)
    (hy : arr s.mem B w aY = Y * 2 ^ (64 * w) % c) (h23 : s.gpr .r23 = mask P) {j : Nat}
    (hj : j = 1 ∨ j = 2 ∨ j = 3) :
    WP isa (last j) s fun t => WSt rs s₀ t B Z w c b ∧
      arr t.mem B w aY = (wSq c (decide (j < mrSig c)) (Y, P)).1 * 2 ^ (64 * w) % c ∧
      (wSq c (decide (j < mrSig c)) (Y, P)).1 < c ∧ t.gpr .r23 = mask (wSq c (decide (j < mrSig c)) (Y, P)).2 := by
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  have hn : slot w 28 ≤ 2 ^ 64 := by have := h.ctx.hs.nowrap; have := h.ctx.hZ; omega_arith
  have hcc := h.consts.cand
  have hw' := h.ctx.hw'
  have hZ := h.ctx.hZ
  have hE := slot_lt (w := w) (show aE < 28 by decide)
  unfold last
  refine WP.seq (WP.mono (mont_ok h.ctx (o := 6) (a := 6) (b := 6) (by simp) (by simp) (by simp)
    (by rw [show (6 : Nat) = aY from rfl, hy, hcc]; exact Nat.mod_lt _ (by omega_arith)))
    fun u ⟨⟨hlt, heq, hout, h0⟩, ku⟩ => ?_)
  have fu := h.stepW (montRanges_win hout (by simp)) ku (by simp [Pub.montRegs, tailRegs, winRegs, tabRegs]) h0
  rw [hcc] at hlt heq
  have uy : arr u.mem B w aY = Y * Y % c * 2 ^ (64 * w) % c := VG.Proof.RsaKeyGen.mont_val hR hlt heq hy hy
  refine WP.seq (WP.mono (eqMask_ok fu.ctx.toEnv .r20 (a := aY) (b := aMinus) (by decide) (by decide))
    fun v ⟨⟨v20, vm⟩, kv⟩ => ?_)
  have fv := fu.stepW (by rw [vm]; exact Outs.refl _ _ _) kv (by decide) (by rw [vm])
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (fv.ctx.base (rd := .r3) (by decide) (by decide) aE) fun x ⟨⟨x3, xm⟩, kx⟩ => ?_
  have fx := fv.stepW (by rw [xm]; exact Outs.refl _ _ _) kx (by decide) (by rw [xm])
  have hl : x.mem.readW (off B (slot w aE + 8 * w)) 64 = BitVec.twoPow 64 (mrA c % 64) := fx.consts.l
  have hblk : WP isa (.block ([.lsr .d .r0 .r11 1, .lsl .r0 .r0 3, .add .r3 .r3 .r0, .load .d .r3 .r3 0] ++
      (repeat16 (sigK j) ++ [.logic .and .r3 .r3 .r4, .lsr .d .r4 .r3 1, .li .r0 1, .logic .and .r0 .r3 .r0,
        .logic .or .r3 .r4 .r0, .li .r0 0, .sub .r3 .r0 .r3, .lsr .d .r3 .r3 63, .sub .r3 .r0 .r3,
        .logic .and .r20 .r20 .r3, .logic .or .r23 .r23 .r20]))) x fun t =>
      (t.gpr .r23 = x.gpr .r23 ||| (x.gpr .r20 &&& mask (decide (BitVec.twoPow 64 (mrA c % 64) &&& sigK64 j ≠ 0))) ∧
        t.mem = x.mem) ∧ Keep [.r0, .r3, .r4, .r20, .r23] x t := by
    refine WP.keep _ ?_ (by rfl)
    unfold repeat16
    prun [fx.ctx.h11, shr1_ofNat w hw', shl3_ofNat w, x3, fx.ctx.hs.ld (show slot w aE + 8 * w + 8 ≤ Z by omega_arith),
      hl, exec_lis, exec_ori, exec_oris, repeat16_val j hj, nz64_mask]
  refine WP.mono hblk fun t ⟨⟨t23, tm⟩, kt⟩ => ⟨fx.stepW (by rw [tm]; exact Outs.refl _ _ _) kt (by decide)
    (by rw [tm]), ?_, Nat.mod_lt _ (by omega_arith), ?_⟩
  · rw [tm, xm, vm, uy]; rfl
  · have e : decide (arr u.mem B w aY = arr u.mem B w aMinus) = decide (Y * Y % c = c - 1) := by
      have u10 : arr u.mem B w aMinus = c - 2 ^ (64 * w) % c := by
        rw [Outs.arrEq_mont hout (by decide) (by decide) (by decide) (by decide) hn]; exact h.consts.minus
      rw [uy, u10]
      exact decide_eq_decide.mpr (VG.Proof.RsaKeyGen.mont_eq_m1 hR (by omega_arith) (Nat.mod_lt _ (by omega_arith)))
    rw [t23, kx.gpr .r23 (by decide), kv.gpr .r23 (by decide), ku.gpr .r23 (by simp [Pub.montRegs, tailRegs]),
      h23, kx.gpr .r20 (by decide), v20, e, sig_word hj, mask_and, mask_or]
    simp only [wSq, Bool.and_comm]

end VG.Proof.MillerRabin.PPC64LE
