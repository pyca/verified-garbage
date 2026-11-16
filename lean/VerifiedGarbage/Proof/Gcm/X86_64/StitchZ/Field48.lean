module

public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Gh48
public import VerifiedGarbage.Proof.Gcm.Poly
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Ghash
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Gh
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# Interleaved counter mode and GHASH with AVX-512: 48 blocks in the field

`finZ48`: with powers `x · T g k l = H⁴⁸⁻¹⁶ᵍ⁻⁴ᵏ⁻ˡ`, the products of 48 blocks
added and reduced as `body48` does are `GHASH` over them (`FinOk48`); and
`φ_lanemul`: the products `pow48` stores are the powers it says.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZ
open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduceB φ_reduceB)
open VG.Spec.Gcm (Block mul ghashFrom)

/-- A product of two powers, reduced, is their product. -/
theorem φ_lanemul {H a b : Block} {i j : Nat} (ha : x * φ a = φ H ^ i) (hb : x * φ b = φ H ^ j) :
    x * φ (reduceB (Prod.zero.acc a b)) = φ H ^ (i + j) := by
  rw [φ_reduceB, Prod.val_acc, Prod.val_zero, pow_add, ← ha, ← hb]; ring

/-- The products of 48 blocks, for powers `x · T g k l = H⁴⁸⁻¹⁶ᵍ⁻⁴ᵏ⁻ˡ`. -/
theorem finZ48 {H : Block} {T : Nat → Nat → Nat → Block}
    (hT : ∀ g < 3, ∀ k < 4, ∀ l < 4, x * φ (T g k l) = φ H ^ (48 - 16 * g - 4 * k - l)) : FinOk48 H T := by
  intro X yl hy
  obtain h000 := hT 0 (by decide) 0 (by decide) 0 (by decide)
  obtain h001 := hT 0 (by decide) 0 (by decide) 1 (by decide)
  obtain h002 := hT 0 (by decide) 0 (by decide) 2 (by decide)
  obtain h003 := hT 0 (by decide) 0 (by decide) 3 (by decide)
  obtain h010 := hT 0 (by decide) 1 (by decide) 0 (by decide)
  obtain h011 := hT 0 (by decide) 1 (by decide) 1 (by decide)
  obtain h012 := hT 0 (by decide) 1 (by decide) 2 (by decide)
  obtain h013 := hT 0 (by decide) 1 (by decide) 3 (by decide)
  obtain h020 := hT 0 (by decide) 2 (by decide) 0 (by decide)
  obtain h021 := hT 0 (by decide) 2 (by decide) 1 (by decide)
  obtain h022 := hT 0 (by decide) 2 (by decide) 2 (by decide)
  obtain h023 := hT 0 (by decide) 2 (by decide) 3 (by decide)
  obtain h030 := hT 0 (by decide) 3 (by decide) 0 (by decide)
  obtain h031 := hT 0 (by decide) 3 (by decide) 1 (by decide)
  obtain h032 := hT 0 (by decide) 3 (by decide) 2 (by decide)
  obtain h033 := hT 0 (by decide) 3 (by decide) 3 (by decide)
  obtain h100 := hT 1 (by decide) 0 (by decide) 0 (by decide)
  obtain h101 := hT 1 (by decide) 0 (by decide) 1 (by decide)
  obtain h102 := hT 1 (by decide) 0 (by decide) 2 (by decide)
  obtain h103 := hT 1 (by decide) 0 (by decide) 3 (by decide)
  obtain h110 := hT 1 (by decide) 1 (by decide) 0 (by decide)
  obtain h111 := hT 1 (by decide) 1 (by decide) 1 (by decide)
  obtain h112 := hT 1 (by decide) 1 (by decide) 2 (by decide)
  obtain h113 := hT 1 (by decide) 1 (by decide) 3 (by decide)
  obtain h120 := hT 1 (by decide) 2 (by decide) 0 (by decide)
  obtain h121 := hT 1 (by decide) 2 (by decide) 1 (by decide)
  obtain h122 := hT 1 (by decide) 2 (by decide) 2 (by decide)
  obtain h123 := hT 1 (by decide) 2 (by decide) 3 (by decide)
  obtain h130 := hT 1 (by decide) 3 (by decide) 0 (by decide)
  obtain h131 := hT 1 (by decide) 3 (by decide) 1 (by decide)
  obtain h132 := hT 1 (by decide) 3 (by decide) 2 (by decide)
  obtain h133 := hT 1 (by decide) 3 (by decide) 3 (by decide)
  obtain h200 := hT 2 (by decide) 0 (by decide) 0 (by decide)
  obtain h201 := hT 2 (by decide) 0 (by decide) 1 (by decide)
  obtain h202 := hT 2 (by decide) 0 (by decide) 2 (by decide)
  obtain h203 := hT 2 (by decide) 0 (by decide) 3 (by decide)
  obtain h210 := hT 2 (by decide) 1 (by decide) 0 (by decide)
  obtain h211 := hT 2 (by decide) 1 (by decide) 1 (by decide)
  obtain h212 := hT 2 (by decide) 1 (by decide) 2 (by decide)
  obtain h213 := hT 2 (by decide) 1 (by decide) 3 (by decide)
  obtain h220 := hT 2 (by decide) 2 (by decide) 0 (by decide)
  obtain h221 := hT 2 (by decide) 2 (by decide) 1 (by decide)
  obtain h222 := hT 2 (by decide) 2 (by decide) 2 (by decide)
  obtain h223 := hT 2 (by decide) 2 (by decide) 3 (by decide)
  obtain h230 := hT 2 (by decide) 3 (by decide) 0 (by decide)
  obtain h231 := hT 2 (by decide) 3 (by decide) 1 (by decide)
  obtain h232 := hT 2 (by decide) 3 (by decide) 2 (by decide)
  obtain h233 := hT 2 (by decide) 3 (by decide) 3 (by decide)
  simp only [Nat.reduceMul, Nat.reduceSub] at *
  apply φ_inj
  simp only [yNew48, acc48, List.range_succ, List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons,
    List.foldl_nil, pa, inp48, Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, and_self, and_false,
    Nat.one_ne_zero, false_and, ↓reduceIte, Nat.reduceEqDiff, hy 1 (by decide) (by decide), hy 2 (by decide) (by decide),
    hy 3 (by decide) (by decide), Stitch.zero_xor_b, φ_xor, φ_reduceB, Prod.val_acc, Prod.val_zero,
    ghashFrom, List.map_append, List.map_cons, List.map_nil, φ_mul]
  linear_combination (φ (yl 0) + φ (X 0)) * h000 + φ (X 1) * h001 + φ (X 2) * h002 + φ (X 3) * h003 + φ (X 4) * h010 + φ (X 5) * h011 + φ (X 6) * h012 + φ (X 7) * h013 + φ (X 8) * h020 + φ (X 9) * h021 + φ (X 10) * h022 + φ (X 11) * h023 + φ (X 12) * h030 + φ (X 13) * h031 + φ (X 14) * h032 + φ (X 15) * h033 + φ (X 16) * h100 + φ (X 17) * h101 + φ (X 18) * h102 + φ (X 19) * h103 + φ (X 20) * h110 + φ (X 21) * h111 + φ (X 22) * h112 + φ (X 23) * h113 + φ (X 24) * h120 + φ (X 25) * h121 + φ (X 26) * h122 + φ (X 27) * h123 + φ (X 28) * h130 + φ (X 29) * h131 + φ (X 30) * h132 + φ (X 31) * h133 + φ (X 32) * h200 + φ (X 33) * h201 + φ (X 34) * h202 + φ (X 35) * h203 + φ (X 36) * h210 + φ (X 37) * h211 + φ (X 38) * h212 + φ (X 39) * h213 + φ (X 40) * h220 + φ (X 41) * h221 + φ (X 42) * h222 + φ (X 43) * h223 + φ (X 44) * h230 + φ (X 45) * h231 + φ (X 46) * h232 + φ (X 47) * h233

end VG.Proof.Gcm.X86_64.StitchZ
