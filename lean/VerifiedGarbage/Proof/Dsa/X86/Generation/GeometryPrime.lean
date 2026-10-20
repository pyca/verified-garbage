module
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryTape
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReady
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Dsa.BitLengthBounds -- shake: keep (proof fields of exposed definitions)
public import VerifiedGarbage.Proof.Dsa.Generation.Primality -- shake: keep (proof fields of exposed definitions)
public import VerifiedGarbage.Proof.Rsa.RecoverMath -- shake: keep (proof fields of exposed definitions)

/-! # Instantiate the native primality engine for any full-width odd candidate -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.Proof.Mont VG.Impl.Dsa.Generation.Layout
open VG.Impl.Dsa.X86.Generation

def GenerationGeometry.prime (G : GenerationGeometry) (T : GenerationTape G) (len m : Nat)
    (lo : 4 ≤ len) (hi : len ≤ 384) (words : len % 4 = 0)
    (bits : Spec.RsaKeyGen.bitLength m = 8 * len) (odd : m % 2 = 1) : PrimeConfig := by
  have bounds := (VG.Proof.Dsa.bitLength_iff_bounds (by omega : 0 < 8 * len)).mp bits
  have gtOne : 1 < m := by
    have small := Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 2 ≤ 8 * len - 1)
    have four : (2 : Nat) ^ 2 = 4 := by decide
    rw [four] at small
    omega
  have witnessStart : witness < usedBytes G.pLen := by unfold witness usedBytes domainCheck; omega
  have witnessRoom : witness + len ≤ usedBytes G.pLen := by unfold witness usedBytes domainCheck; omega
  have arithmeticRoom : arithmetic + arithmeticBytes ≤ usedBytes G.pLen := by unfold arithmetic arithmeticBytes usedBytes domainCheck; omega
  refine ⟨off G.base arithmetic, arithmeticBytes, len, m, T.pointer, T.bytes.length, G.pointer witness,
    lo, hi, words, bits, ?_, ?_, ?_, ?_, T.size, T.fit, ?_, T.part arithmeticRoom, ?_, ?_⟩
  · exact VG.Proof.Dsa.Generation.predecessor_bits (by omega) odd bits
  · have even : (m - 1) % 2 = 0 := by omega
    rw [VG.Proof.Rsa.splitTwos_even (by omega) even]
    dsimp only
    omega
  · rw [bits]
    exact Nat.le_of_lt (VG.Proof.Rsa.splitTwos_lt (by omega) (by omega))
  · unfold primeExponent arithmeticBytes; omega
  · rw [G.pointer_toNat witnessStart]
    have := G.arenaBound
    omega
  · rw [G.pointer_addr witnessStart]
    exact G.parts_disjoint witnessRoom arithmeticRoom (.inl (by unfold witness arithmetic; omega))
  · rw [G.pointer_addr witnessStart]
    exact T.part witnessRoom
end VG.Proof.Dsa.X86.Generation
