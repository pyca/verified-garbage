module

import VerifiedGarbage.Proof.Bignum.AArch64.Csub
public import VerifiedGarbage.Impl.Bignum.AArch64.WindowLazy
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowLazy
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The pointers stay at the tile's start while its four words are processed. -/
structure TileInv (s₀ : State) (B : Addr) (Z eA eN eT j k : Nat) (bit : Bool) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x5, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (eA + 8*j)
  x17 : t.gpr .x17 = off B (eN + 8*j)
  x5 : t.gpr .x5 = off B (eT + 8*j)
  mask : t.gpr .x15 = if bit then -1 else 0
  out : Outside B eT (8*(j+k)) s₀.mem t.mem
  val : wv t.mem B eT (j+k) + bit.toNat * wv s₀.mem B eN (j+k) =
    wv s₀.mem B eA (j+k) + 2 ^ (64*(j+k)) * (!t.c).toNat

theorem word_ok {s₀ : State} {B : Addr} {Z w eA eN eT j k : Nat}
    (hA : eA+8*w ≤ Z) (hN : eN+8*w ≤ Z) (hT : eT+8*w ≤ Z)
    (sA : eT+8*w ≤ eA ∨ eA+8*w ≤ eT) (sN : eT+8*w ≤ eN ∨ eN+8*w ≤ eT)
    (hk : k < 4) (hj : j+k < w) {bit : Bool} {t : State} (hI : TileInv s₀ B Z eA eN eT j k bit t) :
    WP isa (.block (VG.Impl.Bignum.AArch64.WindowLazy.word k)) t fun t' =>
      TileInv s₀ B Z eA eN eT j (k+1) bit t' := by
  have hn := hI.scr.nowrap
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun u =>
    u.mem = t.mem.writeW (off B (eT+8*(j+k)))
      (word t.mem B (eA+8*(j+k)) + ~~~(word t.mem B (eN+8*(j+k)) &&& (if bit then -1 else 0)) + BitVec.ofNat 64 t.c.toNat) ∧
    u.c = decide (2 ^ 64 ≤ (word t.mem B (eA+8*(j+k))).toNat +
      (~~~(word t.mem B (eN+8*(j+k)) &&& (if bit then -1 else 0))).toNat + t.c.toNat)) ?_ rfl rfl rfl)
    fun u ⟨⟨hm, hc⟩, ku⟩ => ?_
  · unfold VG.Impl.Bignum.AArch64.WindowLazy.word
    have enc : (8*k) % 8 = 0 ∧ 8*k < 32768 := by omega
    have eAEq : eA+8*j+8*k = eA+8*(j+k) := by omega
    have eNEq : eN+8*j+8*k = eN+8*(j+k) := by omega
    have eTEq : eT+8*j+8*k = eT+8*(j+k) := by omega
    brun [hI.x16, hI.x17, hI.x5, hI.mask, enc,
      hI.scr.ld (show eA+8*j+8*k+8 ≤ Z by omega),
      hI.scr.ld (show eN+8*j+8*k+8 ≤ Z by omega),
      hI.scr.st (show eT+8*j+8*k+8 ≤ Z by omega)]
    all_goals simp only [eAEq, eNEq, eTEq, and_self]
  have hx : word t.mem B (eA+8*(j+k)) = word s₀.mem B (eA+8*(j+k)) :=
    hI.out.word (by omega) (by omega)
  have hy : word t.mem B (eN+8*(j+k)) = word s₀.mem B (eN+8*(j+k)) :=
    hI.out.word (by omega) (by omega)
  refine ⟨hI.scr.congr ku.wr, (hI.keep.trans ku).mono (by decide),
    (ku.gpr .x16 (by decide)).trans hI.x16, (ku.gpr .x17 (by decide)).trans hI.x17,
    (ku.gpr .x5 (by decide)).trans hI.x5,
    (ku.gpr .x15 (by decide)).trans hI.mask, ?_, ?_⟩
  · rw [hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [show j+(k+1) = (j+k)+1 by omega, hm, wv_writeW_top _ _ _ _ _ (by omega), hc]
    have hs := sbcs_toNat (word t.mem B (eA+8*(j+k))) (word t.mem B (eN+8*(j+k)) &&& (if bit then -1 else 0)) t.c
    rw [hx, hy] at hs
    have hv := hI.val
    simp only [wv]
    rw [pow64_succ, hx, hy]
    cases bit <;>
      simp only [Bool.false_eq_true, Bool.toNat_false, Bool.toNat_true, ite_false, ite_true,
        show (-1 : BitVec 64) = BitVec.allOnes 64 from rfl, BitVec.and_allOnes,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero] at hs hv ⊢ <;> grind

end VG.Proof.Bignum.AArch64.WindowLazy
