module
public import VerifiedGarbage.Impl.Bignum.AArch64.Square
public import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd

import VerifiedGarbage.Proof.Bignum.AArch64.SquareMac
import VerifiedGarbage.Proof.Framework.Range
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Numerical invariant for the four-word deferred-carry MAC prefix. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.Square
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure PrefixInv (s₀ : State) (B : Addr) (Z eA eb j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x2, .x3, .x4] s₀ t
  out : Outside B eA (8*j) s₀.mem t.mem
  val : wv t.mem B eA j + 2 ^ (64*j) * carry t =
    wv s₀.mem B eA j + (s₀.gpr .x1).toNat * wv s₀.mem B eb j + carry s₀
  carry_lt : carry t < 2 ^ 64

theorem prefixStep_ok {s₀ : State} {B : Addr} {Z eA eb j : Nat}
    (h16 : s₀.gpr .x16 = off B eA) (h17 : s₀.gpr .x17 = off B eb)
    (h7 : s₀.gpr .x7 = 0) (hA : eA + 32 ≤ Z) (hb : eb + 32 ≤ Z)
    (hsep : eA + 32 ≤ eb ∨ eb + 32 ≤ eA) (hj : j < 4)
    {t : State} (hI : PrefixInv s₀ B Z eA eb j t) :
    WP isa (.block (VG.Impl.Bignum.AArch64.Square.macAt j)) t
      (PrefixInv s₀ B Z eA eb (j+1)) := by
  have hn := hI.scr.nowrap
  have t7 : t.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans h7
  have t1 : t.gpr .x1 = s₀.gpr .x1 := hI.keep.gpr .x1 (by decide)
  have t16 : t.gpr .x16 = off B eA := (hI.keep.gpr .x16 (by decide)).trans h16
  have t17 : t.gpr .x17 = off B eb := (hI.keep.gpr .x17 (by decide)).trans h17
  refine WP.mono (macAt_ok t j hI.scr t16 t17 t7 (by omega) (by omega) hI.carry_lt hj)
    fun t' ⟨⟨lo, hm, hv, hc⟩, k⟩ => ?_
  have hx : word t.mem B (eA + 8*j) = word s₀.mem B (eA + 8*j) :=
    hI.out.word (Or.inr (Nat.le_refl _)) (by omega)
  have hy : word t.mem B (eb + 8*j) = word s₀.mem B (eb + 8*j) :=
    hI.out.word (by omega) (by omega)
  refine ⟨hI.scr.congr k.wr, (hI.keep.trans k).mono (by decide), ?_, ?_, hc⟩
  · rw [hm]
    intro x hx'
    rw [writeW_outside t.mem B lo (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm, wv_writeW_top _ _ _ _ _ (by omega)]
    simp only [wv]
    rw [hx, hy, t1] at hv
    have hval := hI.val
    rw [pow64_succ]
    grind

/-- All four products, including the incoming carry, before pointers advance. -/
theorem prefix4_ok {s : State} {B : Addr} {Z eA eb : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B eA)
    (h17 : s.gpr .x17 = off B eb) (h7 : s.gpr .x7 = 0)
    (hA : eA + 32 ≤ Z) (hb : eb + 32 ≤ Z)
    (hsep : eA + 32 ≤ eb ∨ eb + 32 ≤ eA) (hc : carry s < 2 ^ 64) :
    WP isa (.block ((List.range 4).flatMap VG.Impl.Bignum.AArch64.Square.macAt)) s
      (PrefixInv s B Z eA eb 4) := by
  have h0 : PrefixInv s B Z eA eb 0 s :=
    ⟨hs, Keep.refl _ _, Outside.refl _ _ _ _, by simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.zero_add, Nat.add_zero, Nat.one_mul], hc⟩
  exact wp_range_flatMap (M := isa)
    (f := VG.Impl.Bignum.AArch64.Square.macAt) (N := 4) (PrefixInv s B Z eA eb)
    (fun k t hk hI => prefixStep_ok h16 h17 h7 hA hb hsep hk hI) 4 (by omega) s h0

theorem advance4_ok (s : State) :
    WP isa (.block [.addImm .x .x16 .x16 32, .addImm .x .x17 .x17 32]) s fun t =>
      (t.mem = s.mem ∧ carry t = carry s ∧
        t.gpr .x16 = s.gpr .x16 + BitVec.ofNat 64 32 ∧
        t.gpr .x17 = s.gpr .x17 + BitVec.ofNat 64 32) ∧ Keep [.x16, .x17] s t := by
  refine WP.keep [.x16, .x17] ?_ rfl rfl rfl
  unfold carry
  brun

/-- A four-word block's complete value, carry bound, write frame and pointers. -/
theorem mac4_ok {s : State} {B : Addr} {Z eA eb : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B eA)
    (h17 : s.gpr .x17 = off B eb) (h7 : s.gpr .x7 = 0)
    (hA : eA + 32 ≤ Z) (hb : eb + 32 ≤ Z)
    (hsep : eA + 32 ≤ eb ∨ eb + 32 ≤ eA) (hc : carry s < 2 ^ 64) :
    WP isa (.block VG.Impl.Bignum.AArch64.Square.mac4) s fun t =>
      wv t.mem B eA 4 + 2 ^ 256 * carry t =
        wv s.mem B eA 4 + (s.gpr .x1).toNat * wv s.mem B eb 4 + carry s ∧
      Outside B eA 32 s.mem t.mem ∧ carry t < 2 ^ 64 ∧
      t.gpr .x16 = off B (eA + 32) ∧ t.gpr .x17 = off B (eb + 32) ∧
      Keep [.x2, .x3, .x4, .x16, .x17] s t := by
  unfold VG.Impl.Bignum.AArch64.Square.mac4
  rw [WP.block_append_iff]
  refine WP.mono (prefix4_ok hs h16 h17 h7 hA hb hsep hc) fun u hI => ?_
  refine WP.mono (advance4_ok u) fun t ⟨⟨hm, hcarry, ht16, ht17⟩, k⟩ => ?_
  have u16 := (hI.keep.gpr .x16 (by decide)).trans h16
  have u17 := (hI.keep.gpr .x17 (by decide)).trans h17
  refine ⟨?_, ?_, ?_, ?_, ?_, (hI.keep.trans k).mono (by decide)⟩
  · rw [hm, hcarry]
    exact hI.val
  · rw [hm]; exact hI.out
  · rw [hcarry]; exact hI.carry_lt
  · rw [ht16, u16, off_add]
  · rw [ht17, u17, off_add]

end VG.Proof.Bignum.AArch64.Square
