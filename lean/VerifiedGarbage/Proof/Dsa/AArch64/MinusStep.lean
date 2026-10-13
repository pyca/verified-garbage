module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Borrow propagation when forming DSA modulus-minus constants -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- One word of `modulusMinus`'s loop: subtract the borrow. -/
abbrev minusTail : List Instr := [ld .x3 .x16, .sbcs .x .x3 .x3 .x7, st .x3 .x17, next .x16, next .x17]

/-- `modulusMinus`'s loop over the words after the first. -/
abbrev minusLoop : Prog isa := countLoop .x14 minusTail

/-- After `j` words of `modulusMinus`: `Y_j + amount = N_j + 2^(64 j) (!C)`
for the carry flag `C`. -/
structure MinusInv (s₀ : State) (B : Addr) (Z eN eY amount : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (eN + 8 * j)
  x17 : t.gpr .x17 = off B (eY + 8 * j)
  out : Outside B eY (8 * j) s₀.mem t.mem
  val : wv t.mem B eY j + amount = wv s₀.mem B eN j + 2 ^ (64 * j) * (!t.c).toNat

theorem minus_arith {Y N a P r c x Q b : Nat} (hv : Y + a = N + P * c) (hs : r + c = x + Q * b) :
    Y + P * r + a = N + P * x + P * Q * b := by
  have hP := congrArg (P * ·) hs
  simp only [Nat.mul_add, ← Nat.mul_assoc] at hP
  omega

/-- `sbcs` (`sbcs_toNat`, stated with this file's instances): the
difference, the subtrahend and the borrow in (`!C`) are the minuend and the
borrow out. -/
theorem sbcs_toNat' (a b : BitVec 64) (C : Bool) :
    (a + ~~~b + BitVec.ofNat 64 C.toNat).toNat + b.toNat + (!C).toNat =
      a.toNat + 2 ^ 64 * (!decide (2 ^ 64 ≤ a.toNat + (~~~b).toNat + C.toNat)).toNat := by
  have ha := a.isLt; have hb := b.isLt
  have hnb : (~~~b).toNat = 2 ^ 64 - 1 - b.toNat := by rw [BitVec.toNat_not]
  have hnc : (!C).toNat = 1 - C.toNat := by cases C <;> rfl
  have hc1 := Bool.toNat_le C
  rw [hnb, hnc]
  generalize C.toNat = c at *
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hnb]
  by_cases h : 2 ^ 64 ≤ a.toNat + (2 ^ 64 - 1 - b.toNat) + c <;>
  simp only [h, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.toNat_true,
    Bool.toNat_false] <;> omega

theorem pow64_succ' (k : Nat) : 2 ^ (64 * (k + 1)) = 2 ^ (64 * k) * 2 ^ 64 := by
  rw [Nat.mul_succ, Nat.pow_add]

theorem minusStep_ok {s₀ : State} {B : Addr} {Z w eN eY amount : Nat}
    (h7 : s₀.gpr .x7 = 0) (hY : eY + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z)
    (hsep : eY + 8 * w ≤ eN ∨ eN + 8 * w ≤ eY) {j : Nat} (hj : j < w) {t : State}
    (hI : MinusInv s₀ B Z eN eY amount j t) :
    WP isa (.block (minusTail ++ ([.subImm .x .x14 .x14 1] : List Instr))) t
      fun t' => MinusInv s₀ B Z eN eY amount (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have t7 : t.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans h7
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x16, .x17] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (eY + 8 * j)) (word t.mem B (eN + 8 * j) + ~~~(t.gpr .x7) + BitVec.ofNat 64 t.c.toNat) ∧
      t₁.c = decide (2 ^ 64 ≤ (word t.mem B (eN + 8 * j)).toNat + (~~~(t.gpr .x7)).toNat + t.c.toNat) ∧
      t₁.gpr .x16 = off B (eN + 8 * j + 8) ∧ t₁.gpr .x17 = off B (eY + 8 * j + 8))
    (by brun [hI.x16, hI.x17, hI.scr.ld (show eN + 8 * j + 8 ≤ Z by omega_arith),
      hI.scr.st (show eY + 8 * j + 8 ≤ Z by omega_arith)]) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨hm, hc, h16, h17⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', hc'⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  have hx : word t.mem B (eN + 8 * j) = word s₀.mem B (eN + 8 * j) := hI.out.word (by omega_arith) (by omega_arith)
  have hs := sbcs_toNat' (word t.mem B (eN + 8 * j)) (t.gpr .x7) t.c
  have h0 : (t.gpr .x7).toNat = 0 := by rw [t7]; rfl
  rw [hx] at hs hm hc
  generalize (word s₀.mem B (eN + 8 * j) + ~~~(t.gpr .x7) + BitVec.ofNat 64 t.c.toNat) = r at hs hm
  rw [h0, Nat.add_zero] at hs
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), ((hI.keep.trans k₁).trans k').mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B r (by omega_arith) x (by omega_arith)]
    exact hI.out x (by omega_arith)
  · have hlow : wv t.mem B eY j = wv (t.mem.writeW (off B (eY + 8 * j)) r) B eY j :=
      ((writeW_outside t.mem B r (by omega_arith)).wv (Or.inl (by omega_arith)) (by omega_arith)).symm
    have hv := hI.val
    rw [← hc] at hs
    rw [hm', hm, hc']
    simp only [wv]
    rw [← hlow, word_writeW_self, pow64_succ']
    exact minus_arith hv hs

end VG.Proof.Dsa.AArch64
