module
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Contract

/-! # Fixed-count borrow propagation for modulus-minus constants -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure MinusInv (s₀ : State) (B : Addr) (Z eN eY amount : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x14, .x16, .x17] s₀ t
  source : t.gpr .x16 = off B (eN + 8 * j)
  dest : t.gpr .x17 = off B (eY + 8 * j)
  out : Outside B eY (8 * j) s₀.mem t.mem
  val : wv t.mem B eY j + amount = wv s₀.mem B eN j + 2 ^ (64 * j) * (!t.c).toNat

abbrev minusTail : List Instr :=
  [ld .x3 .x16, .sbcs .x .x3 .x3 .x7, st .x3 .x17, next .x16, next .x17]

theorem minus_word (a z : BitVec 64) (c : Bool) (hz : z.toNat = 0) :
    (a + ~~~z + BitVec.ofNat 64 c.toNat).toNat + (!c).toNat =
      a.toNat + 2 ^ 64 * (!decide (2 ^ 64 ≤ a.toNat + (~~~z).toNat + c.toNat)).toNat := by
  have h := sbcs_toNat a z c
  rw [hz, Nat.add_zero] at h
  exact h

theorem minusStep_ok {s₀ : State} {B : Addr} {Z w eN eY amount : Nat}
    (h7 : s₀.gpr .x7 = 0) (hY : eY + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z)
    (hsep : eY + 8 * w ≤ eN ∨ eN + 8 * w ≤ eY) {j : Nat} (hj : j < w) {t : State}
    (hI : MinusInv s₀ B Z eN eY amount j t) :
    WP isa (.block (minusTail ++ ([.subImm .x .x14 .x14 1] : List Instr))) t
      fun t' => MinusInv s₀ B Z eN eY amount (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have t7 := (hI.keep.gpr .x7 (by decide)).trans h7
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x16, .x17] (Q := fun u =>
    ∃ r : BitVec 64, u.mem = t.mem.writeW (off B (eY + 8 * j)) r ∧
      r.toNat + (!t.c).toNat = (word t.mem B (eN + 8 * j)).toNat + 2 ^ 64 * (!u.c).toNat ∧
      u.gpr .x16 = off B (eN + 8 * j + 8) ∧ u.gpr .x17 = off B (eY + 8 * j + 8)) ?_ rfl rfl rfl)
    fun u ⟨⟨r, hm, hr, hp, hq⟩, hk⟩ => ?_
  · unfold minusTail
    brun [hI.source, hI.dest, hI.scr.ld (show eN + 8 * j + 8 ≤ Z by omega),
      hI.scr.st (show eY + 8 * j + 8 ≤ Z by omega)]
    refine ⟨_, rfl, ?_⟩
    exact minus_word _ _ t.c (by rw [t7]; rfl)

  refine WP.mono (dec_ok u .x14) fun v ⟨⟨h14, hvm, hc⟩, hkv⟩ => ⟨?_, by rw [h14, hk.gpr .x14 (by decide)]⟩
  have hx : word t.mem B (eN + 8 * j) = word s₀.mem B (eN + 8 * j) := hI.out.word (by omega) (by omega)
  rw [hx] at hr
  refine ⟨hI.scr.congr (hkv.wr.trans hk.wr), ((hI.keep.trans hk).trans hkv).mono (by decide),
    ?_, ?_, ?_, ?_⟩
  · rw [hkv.gpr .x16 (by decide), hp, Nat.mul_succ, Nat.add_assoc]
  · rw [hkv.gpr .x17 (by decide), hq, Nat.mul_succ, Nat.add_assoc]
  · rw [hvm, hm]
    intro x hx'
    rw [writeW_outside t.mem B r (by omega) x (by omega)]
    exact hI.out x (by omega)
  · have hlow : wv t.mem B eY j = wv (t.mem.writeW (off B (eY + 8 * j)) r) B eY j :=
      ((writeW_outside t.mem B r (by omega)).wv (Or.inl (by omega)) (by omega)).symm
    rw [hvm, hm, hc]
    simp only [wv]
    rw [← hlow, word_writeW_self, pow64_succ]
    have hv := hI.val
    have hh := congrArg (fun x : Nat => 2 ^ (64 * j) * x) hr
    simp only [Nat.mul_add] at hh
    simp only [Nat.mul_assoc]
    omega

end VG.Proof.Dsa.AArch64
