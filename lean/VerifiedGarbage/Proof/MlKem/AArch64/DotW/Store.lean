module
public import VerifiedGarbage.Impl.MlKem.AArch64.DotW
public import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
public import VerifiedGarbage.Proof.MlKem.AArch64.DotW.Lane

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem

/-!
# ML-KEM's fused dot product of polynomials stored with 16 bits, on AArch64: the store

`storeW`: the even and odd results of pairs `0 … 3` (`v21`, `v23`) and
`4 … 7` (`v25`, `v27`), words less than `q`, narrowed to halfwords (UZP1)
and interleaved (ZIP1, ZIP2) into sixteen coefficients (`storeW_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DotW

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem

/-- The low halfwords of the words of `x`, then of `y`. -/
theorem narrow_lanes {x y : BitVec 128} {A B : Nat → Nat} (hx : Lanes x A) (hy : Lanes y B)
    (ba : ∀ e < 4, A e < 2 ^ 16) (bb : ∀ e < 4, B e < 2 ^ 16) :
    HLanes (VPermOp.eval .uzp1 .h8 x y) (fun e => if e < 4 then A e else B (e - 4)) := fun e he => by
  rw [Ntt16.vhalf_perm_h8 _ _ _ he]
  dsimp only
  by_cases c : e < 4
  · rw [ite_eq_left c, ite_eq_left c, ← Ntt16.vword_lo, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
      hx e c, Nat.mod_eq_of_lt (ba e c)]
  · rw [ite_eq_right c, ite_eq_right c, show 2 * e - 8 = 2 * (e - 4) by omega, ← Ntt16.vword_lo,
      BitVec.extractLsb'_toNat, Nat.shiftRight_zero, hy _ (by omega), Nat.mod_eq_of_lt (bb _ (by omega))]

/-- The sixteen coefficients from the even (`A`, `A'`) and odd (`B`, `B'`) results of pairs
`0 … 3` and `4 … 7`. -/
def outW (A B A' B' : Nat → Nat) (e : Nat) : Nat :=
  if e < 8 then (if e % 2 = 0 then A (e / 2) else B (e / 2))
  else (if e % 2 = 0 then A' ((e - 8) / 2) else B' ((e - 8) / 2))

theorem storeW_ok {s : State} {p : Addr} {j : Nat} {A B A' B' : Nat → Nat}
    (hx0 : s.gpr .x0 = p + BitVec.ofNat 64 (2 * j)) (hj : j + 16 ≤ 256)
    (hw : ∀ i < 2, InRegions s.wr (p + BitVec.ofNat 64 (2 * (j + 8 * i))) 16)
    (hc : VConsts s) (ha : Lanes (s.v .v21) A) (hb : Lanes (s.v .v23) B)
    (ha' : Lanes (s.v .v25) A') (hb' : Lanes (s.v .v27) B')
    (ba : ∀ e < 4, A e < 3329) (bb : ∀ e < 4, B e < 3329)
    (ba' : ∀ e < 4, A' e < 3329) (bb' : ∀ e < 4, B' e < 3329)
    {O old : Nat → BitVec 16} (ho : CoeffsInW s.mem p (· < j) O old)
    (hv : ∀ e < 16, (O (j + e)).toNat = outW A B A' B' e) :
    WP isa (.block Impl.MlKem.AArch64.DotW.storeW) s fun s' => Keep [] s s' ∧ VConsts s' ∧
      Frame [⟨p, 512⟩] s.mem s'.mem ∧ CoeffsInW s'.mem p (· < j + 16) O old := by
  simp only [Impl.MlKem.AArch64.DotW.storeW]
  refine wp_vop (d := .v0) rfl fun s₁ h₁ => wp_vop (d := .v1) rfl fun s₂ h₂ =>
    wp_vop (d := .v2) rfl fun s₃ h₃ => wp_vop (d := .v3) rfl fun s₄ h₄ => ?_
  have E := narrow_lanes ha ha' (fun e he => by have := ba e he; omega) (fun e he => by have := ba' e he; omega)
  have Od := narrow_lanes hb hb' (fun e he => by have := bb e he; omega) (fun e he => by have := bb' e he; omega)
  have v0 : s₄.v .v0 = VPermOp.eval .uzp1 .h8 (s.v .v21) (s.v .v25) := by
    rw [h₄.get .v0, h₃.get .v0, h₂.get .v0, h₁.v]
  have v1 : s₄.v .v1 = VPermOp.eval .uzp1 .h8 (s.v .v23) (s.v .v27) := by
    rw [h₄.get .v1, h₃.get .v1, h₂.v, h₁.get .v23, h₁.get .v27]
  refine wp_strq (a := p + BitVec.ofNat 64 (2 * j)) (by decide)
    (by rw [h₄.gpr, h₃.gpr, h₂.gpr, h₁.gpr, hx0, BitVec.add_zero])
    (by rw [h₄.wr, h₃.wr, h₂.wr, h₁.wr]; simpa only [Nat.mul_zero, Nat.add_zero] using hw 0 (by decide))
    fun s₅ h₅ => ?_
  refine wp_strq (a := p + BitVec.ofNat 64 (2 * (j + 8))) (by decide)
    (by rw [h₅.gpr, h₄.gpr, h₃.gpr, h₂.gpr, h₁.gpr, hx0, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2)
    (by rw [h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr]; exact hw 1 (by decide)) fun s₆ h₆ => wp_nil ?_
  have x2 : ∀ e < 8, vhalf (s₄.v .v2) e = O (j + e) := fun e he => by
    apply BitVec.eq_of_toNat_eq
    rw [h₄.get .v2, h₃.v, Ntt16.vhalf_perm_h8 _ _ _ he, hv e (by omega), outW, ite_eq_left he]
    dsimp only
    rw [← h₃.get .v0, ← h₄.get .v0, ← h₃.get .v1, ← h₄.get .v1, v0, v1]
    split
    · rw [E _ (by omega)]; dsimp only; rw [ite_eq_left (show e / 2 < 4 by omega)]
    · rw [Od _ (by omega)]; dsimp only; rw [ite_eq_left (show e / 2 < 4 by omega)]
  have x3 : ∀ e < 8, vhalf (s₄.v .v3) e = O (j + 8 + e) := fun e he => by
    apply BitVec.eq_of_toNat_eq
    rw [h₄.v, Ntt16.vhalf_perm_h8 _ _ _ he, Nat.add_assoc, hv (8 + e) (by omega), outW,
      ite_eq_right (show ¬(8 + e < 8) by omega), show 8 + e - 8 = e by omega,
      show (8 + e) % 2 = e % 2 by omega]
    dsimp only
    rw [← h₄.get .v0, ← h₄.get .v1, v0, v1]
    split
    · rw [E _ (by omega)]; dsimp only
      rw [ite_eq_right (show ¬(4 + e / 2 < 4) by omega), show 4 + e / 2 - 4 = e / 2 by omega]
    · rw [Od _ (by omega)]; dsimp only
      rw [ite_eq_right (show ¬(4 + e / 2 < 4) by omega), show 4 + e / 2 - 4 = e / 2 by omega]
  have hm : s₆.mem = (s.mem.write (p + BitVec.ofNat 64 (2 * j)) 16 (s₄.v .v2)).write
      (p + BitVec.ofNat 64 (2 * (j + 8))) 16 (s₄.v .v3) := by
    rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem, h₅.v]
  refine ⟨(((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).trans h₆.keep).mono,
    ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [h₆.v, h₅.v, h₄.get .v16, h₃.get .v16, h₂.get .v16, h₁.get .v16]; exact hc.q
  · rw [h₆.v, h₅.v, h₄.get .v17, h₃.get .v17, h₂.get .v17, h₁.get .v17]; exact hc.m
  · rw [hm]
    exact ((Frame.refl _ _).write (List.mem_singleton_self _) _ (contains_off (by omega) (by decide))).write
      (List.mem_singleton_self _) _ (contains_off (by omega) (by decide))
  · rw [hm]
    exact (ho.write16 (S' := (· < j + 8)) (by omega) x2 fun i _ => by omega).write16 (by omega)
      (fun e he => by rw [x3 e he, Nat.add_assoc]) fun i _ => by omega

end VG.Proof.MlKem.AArch64.DotW
