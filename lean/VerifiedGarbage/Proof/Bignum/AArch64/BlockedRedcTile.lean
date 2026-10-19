module
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcWord

import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcRow
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)

abbrev tailRegs := VG.Impl.Bignum.AArch64.BlockedRedc.aa ++
  VG.Impl.Bignum.AArch64.BlockedRedc.tt ++ [.x1, .x27, .x16]

/-- The complete value and frame after a prefix of a register-block tile. -/
structure TailInv (s : State) (B : Addr) (eQ eT eN j : Nat) (t : State) : Prop where
  value : wv t.mem B eT j + 2 ^ (64 * j) *
      (blockValue (accumulator t) + (2 ^ 64) ^ 8 * t.c.toNat) =
    blockValue (accumulator s) + (2 ^ 64) ^ 8 * s.c.toNat +
      wv s.mem B eQ j * blockValue (operand s (word s.mem B eN))
  ptr : t.gpr .x16 = off B (eT + 8 * j)
  frame : Outside B eT (8 * j) s.mem t.mem
  keep : Keep tailRegs s t

theorem tailStep_ok {s t : State} {B : Addr} {Z eQ eT eN j : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eQ)
    (h17 : s.gpr .x17 = off B eN) (h7 : s.gpr .x7 = 0)
    (hQ : eQ + 64 ≤ Z) (hT : eT + 64 ≤ Z) (hN : eN + 8 ≤ Z)
    (hQT : eQ + 64 ≤ eT ∨ eT + 64 ≤ eQ)
    (hNT : eN + 8 ≤ eT ∨ eT + 64 ≤ eN)
    (hj : j < 8) (hI : TailInv s B eQ eT eN j t) :
    WP isa (.block (VG.Impl.Bignum.AArch64.BlockedRedc.tail j)) t
      fun u => TailInv s B eQ eT eN (j + 1) u := by
  have hnw := hs.nowrap
  have hq := hI.frame.word (d := eQ + 8 * j) (by omega) (by omega)
  have hn := hI.frame.word (d := eN) (by omega) (by omega)
  have hop := (keep_operand hI.keep (by decide) (word t.mem B eN)).trans
    (congrArg (operand s) hn)
  have hopV := congrArg blockValue hop
  refine WP.mono (tailRow_ok (hs.congr hI.keep.wr)
    ((hI.keep.gpr .x8 (by decide)).trans h8) hI.ptr
    ((hI.keep.gpr .x17 (by decide)).trans h17)
    ((hI.keep.gpr .x7 (by decide)).trans h7)
    (by omega) (by omega) hN hj) fun u ⟨lo, hv, hm, hp, ku⟩ => ?_
  have hqV := congrArg BitVec.toNat hq
  have hv' : lo.toNat + 2 ^ 64 *
      (blockValue (accumulator u) + (2 ^ 64) ^ 8 * u.c.toNat) =
        (blockValue (accumulator t) + (2 ^ 64) ^ 8 * t.c.toNat) +
          (word s.mem B (eQ + 8 * j)).toNat * blockValue (operand s (word s.mem B eN)) :=
    hv.trans (by rewrite [hqV, hopV]; omega)
  have hstep := rows_step hI.value hv'
  have hmem := (congrArg (fun m : Mem => wv m B eT (j + 1)) hm).trans
    (wv_writeW_top t.mem B eT j lo (by omega))
  refine ⟨?_, ?_, ?_, (hI.keep.trans ku).mono (by decide)⟩
  · have hqnext : wv s.mem B eQ (j + 1) = wv s.mem B eQ j +
        2 ^ (64 * j) * (word s.mem B (eQ + 8 * j)).toNat := rfl
    rewrite [hmem, pow64_succ, hqnext]
    exact hstep
  · exact hp.trans (congrArg (off B) (by omega))
  · have ho := writeW_outside t.mem B lo (d := eT + 8 * j) (by omega)
    have hm' : Outside B (eT + 8 * j) 8 t.mem u.mem := by
      intro x hx
      exact (congrArg (fun m : Mem => m x) hm).trans (ho x hx)
    exact (hI.frame.mono (by omega) (by omega)).trans (hm'.mono (by omega) (by omega))

/-- Compose any prefix of the eight unrolled rows using the same invariant. -/
theorem tailPrefix_ok {s : State} {B : Addr} {Z eQ eT eN k : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eQ)
    (h16 : s.gpr .x16 = off B eT)
    (h17 : s.gpr .x17 = off B eN) (h7 : s.gpr .x7 = 0)
    (hQ : eQ + 64 ≤ Z) (hT : eT + 64 ≤ Z) (hN : eN + 8 ≤ Z)
    (hQT : eQ + 64 ≤ eT ∨ eT + 64 ≤ eQ)
    (hNT : eN + 8 ≤ eT ∨ eT + 64 ≤ eN) (hk : k ≤ 8) :
    WP isa (.block ((List.range k).flatMap VG.Impl.Bignum.AArch64.BlockedRedc.tail)) s
      fun t => TailInv s B eQ eT eN k t := by
  induction k with
  | zero =>
    apply WP.block_nil
    refine ⟨?_, h16, Outside.refl _ _ _ _, Keep.refl _ _⟩
    simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add,
      Nat.zero_mul, Nat.add_zero]
  | succ k ih =>
    rewrite [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    apply WP.block_append
    exact WP.mono (ih (by omega)) fun t hI =>
      tailStep_ok hs h8 h17 h7 hQ hT hN hQT hNT (by omega) hI

/-- The complete eight-row machine block has no ninth carry limb when its
incoming accumulator is the sum of two bounded blocks. -/
theorem tailTile_ok {s : State} {B : Addr} {Z eQ eT eN a x : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eQ)
    (h16 : s.gpr .x16 = off B eT)
    (h17 : s.gpr .x17 = off B eN) (h7 : s.gpr .x7 = 0)
    (hQ : eQ + 64 ≤ Z) (hT : eT + 64 ≤ Z) (hN : eN + 8 ≤ Z)
    (hQT : eQ + 64 ≤ eT ∨ eT + 64 ≤ eQ)
    (hNT : eN + 8 ≤ eT ∨ eT + 64 ≤ eN)
    (hin : blockValue (accumulator s) + (2 ^ 64) ^ 8 * s.c.toNat = a + x)
    (ha : a < (2 ^ 64) ^ 8) (hx : x < (2 ^ 64) ^ 8) :
    WP isa (.block ((List.range 8).flatMap VG.Impl.Bignum.AArch64.BlockedRedc.tail)) s
      fun t => TailInv s B eQ eT eN 8 t ∧ t.c = false := by
  refine WP.mono (tailPrefix_ok hs h8 h16 h17 h7 hQ hT hN hQT hNT (Nat.le_refl 8))
    fun t hI => ?_
  have hR : 2 ^ (64 * 8) = (2 ^ 64) ^ 8 := Nat.pow_mul 2 64 8
  have hq := Nat.lt_of_lt_of_le (wv_lt s.mem B eQ 8) (Nat.le_of_eq hR)
  have hv : wv t.mem B eT 8 + (2 ^ 64) ^ 8 *
      (blockValue (accumulator t) + (2 ^ 64) ^ 8 * t.c.toNat) =
      a + x + wv s.mem B eQ 8 * blockValue (operand s (word s.mem B eN)) :=
    (congrArg (fun r => wv t.mem B eT 8 + r *
      (blockValue (accumulator t) + (2 ^ 64) ^ 8 * t.c.toNat)) hR.symm).trans
      (hI.value.trans (congrArg (· + wv s.mem B eQ 8 *
        blockValue (operand s (word s.mem B eN))) hin))
  have hc0 := tile_carry_zero (by decide) ha hx hq
    (blockValue_lt (operand s (word s.mem B eN))) hv
  refine ⟨hI, ?_⟩
  cases he : t.c with
  | false => rfl
  | true => simp only [he, Bool.toNat_true] at hc0; omega

end VG.Proof.Bignum.AArch64.BlockedRedc
