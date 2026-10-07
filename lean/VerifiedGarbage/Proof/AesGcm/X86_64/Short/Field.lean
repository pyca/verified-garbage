import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Pow
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Gcm.Split
import Mathlib.Tactic.LinearCombination

/-!
# AES-GCM's short path on x86-64: GHASH of the buffer, in the field

Untrusted: everything here is checked by Lean. With the table of powers
(`TabOk`), the four lanes' sums that `ghash_ok` reduces and adds are `GHASH`
over the `4 g` blocks of the buffer (`gacc_ghash`): lane `l` of group `j` of
the buffer is multiplied by `H⁴ᵍ⁻⁴ʲ⁻ˡ`, which is what `GHASH` from 0 does
with block `4 j + l` of `4 g`. With `Pow.lean`, this is all the short path
needs from the field (`shortFacts`), which the other modules take as an
argument so as not to import its algebra.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduceB φ_reduceB)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul)
open VG.Proof.Gcm (ghashFrom_append ghashFrom_nil blocksAt_add)

theorem φ_ghashFrom4 (H y a b c d : Block) :
    φ (ghashFrom H y [a, b, c, d]) =
      φ y * φ H ^ 4 + φ a * φ H ^ 4 + φ b * φ H ^ 3 + φ c * φ H ^ 2 + φ d * φ H := by
  simp only [ghashFrom, List.foldl_cons, List.foldl_nil, φ_mul, φ_xor]
  ring

/-- After `n` groups, the four lanes' sums are `GHASH` over the first `4 n`
blocks, times the powers of `H` the other groups bring. -/
theorem gacc_field {m : Mem} {G T : Addr} {H : Block} {g : Nat} (hT : TabOk m T H g) :
    ∀ n, n ≤ g → (gacc m G T g 0 n).val + (gacc m G T g 2 n).val + ((gacc m G T g 1 n).val + (gacc m G T g 3 n).val) =
      φ (ghashFrom H 0 (blocksAt m G (4 * n))) * φ H ^ (4 * (g - n))
  | 0, _ => by
    simp only [gacc, List.range_zero, List.foldl_nil, Prod.val_zero, Nat.mul_zero, blocksAt, List.map_nil,
      ghashFrom_nil, φ_zero, zero_mul, add_zero]
  | n + 1, h => by
    have ih := gacc_field (G := G) hT n (by omega)
    obtain ⟨k, rfl⟩ : ∃ k, g = n + 1 + k := ⟨g - (n + 1), by omega⟩
    have t := F_of_tabOk hT k (by omega)
    simp only [gacc_succ, Prod.val_acc]
    rw [show n + 1 + k - 1 - n = k by omega, show 4 * (n + 1) = 4 * n + 4 by omega, blocksAt_add,
      ghashFrom_append, show n + 1 + k - (n + 1) = k by omega]
    rw [show n + 1 + k - n = k + 1 by omega] at ih
    have hb : blocksAt m (G + BitVec.ofNat 64 (16 * (4 * n))) 4 =
        [blockAt m (G + BitVec.ofNat 64 (64 * n + 16 * 0)), blockAt m (G + BitVec.ofNat 64 (64 * n + 16 * 1)),
         blockAt m (G + BitVec.ofNat 64 (64 * n + 16 * 2)), blockAt m (G + BitVec.ofNat 64 (64 * n + 16 * 3))] := by
      simp only [blocksAt, List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
        List.map_nil, add_ofNat_ofNat]
      refine List.cons_eq_cons.mpr ⟨by congr 3; omega, List.cons_eq_cons.mpr ⟨by congr 3; omega,
        List.cons_eq_cons.mpr ⟨by congr 3; omega, List.cons_eq_cons.mpr ⟨by congr 3; omega, rfl⟩⟩⟩⟩
    rw [hb, φ_ghashFrom4]
    have t0 := t 0 (by decide)
    have t1 := t 1 (by decide)
    have t2 := t 2 (by decide)
    have t3 := t 3 (by decide)
    rw [show 4 * k + 4 - 0 = 4 * k + 4 by omega] at t0
    rw [show 4 * k + 4 - 1 = 4 * k + 3 by omega] at t1
    rw [show 4 * k + 4 - 2 = 4 * k + 2 by omega] at t2
    rw [show 4 * k + 4 - 3 = 4 * k + 1 by omega] at t3
    linear_combination ih + φ (blockAt m (G + BitVec.ofNat 64 (64 * n + 16 * 0))) * t0 +
      φ (blockAt m (G + BitVec.ofNat 64 (64 * n + 16 * 1))) * t1 +
      φ (blockAt m (G + BitVec.ofNat 64 (64 * n + 16 * 2))) * t2 +
      φ (blockAt m (G + BitVec.ofNat 64 (64 * n + 16 * 3))) * t3

/-- The four lanes' sums, reduced and added, are `GHASH` over the `4 g`
blocks of the buffer. -/
theorem gacc_ghash {m : Mem} {G T : Addr} {H : Block} {g : Nat} (hT : TabOk m T H g) :
    (reduceB (gacc m G T g 0 g) ^^^ reduceB (gacc m G T g 2 g)) ^^^
      (reduceB (gacc m G T g 1 g) ^^^ reduceB (gacc m G T g 3 g)) = ghashFrom H 0 (blocksAt m G (4 * g)) := by
  apply φ_inj
  rw [φ_xor, φ_xor, φ_xor, φ_reduceB, φ_reduceB, φ_reduceB, φ_reduceB, gacc_field hT g (Nat.le_refl _),
    Nat.sub_self, Nat.mul_zero, pow_zero, mul_one]

/-- What the short path's proofs need from the algebra of the field. -/
theorem shortFacts : ShortFacts := ⟨powers_ok, powHead_ok, gacc_ghash⟩

end VG.Proof.AesGcm.X86_64.Short
