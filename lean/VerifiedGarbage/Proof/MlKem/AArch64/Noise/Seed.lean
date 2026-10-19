module

public import VerifiedGarbage.Proof.MlKem.KPke
import Mathlib.Tactic.Conv

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Noise.Seed
open VG VG.Spec.Sha3
open VG.Proof.Sha3 (Rep byteOf xorByte byteOf_xorByte byteOf_xorBytes absorb_pad iterF iterF_keccakF)
open VG.Proof.MlKem (padded xofByte)

/-- The state whose permutation is the absorbed padded seed. -/
def A0 (Bs : List Byte) : Spec.Sha3.State := xorByte (xorByte (Rep 136 Bs) 33 0x1f) 135 0x80

theorem padded_A0 {Bs : List Byte} (h : Bs.length = 33) :
    padded 136 Spec.Sha3.shakeSuffix Bs = keccakF (A0 Bs) := by
  rw [padded, absorb_pad (by decide) (by decide), h]; rfl

theorem byteOf_A0 {Bs : List Byte} (h : Bs.length = 33) {q : Nat} (hq : q < 200) :
    byteOf (A0 Bs) q = if q < 33 then Bs.getD q 0 else if q = 33 then 0x1f else if q = 135 then 0x80 else 0 := by
  have hz : byteOf Spec.Sha3.zero q = 0 := by
    simp only [byteOf, Spec.Sha3.zero, getElem!_pos (Vector.replicate 25 (0 : BitVec 64)) (q / 8) (by omega),
      Vector.getElem_replicate]
    apply BitVec.eq_of_getLsbD_eq; intro j _; simp
  have ha : Spec.Sha3.absorb 136 Bs = Spec.Sha3.zero := by simp [Spec.Sha3.absorb, h]
  have hr : byteOf (Rep 136 Bs) q = Bs.getD q 0 := by
    rw [Rep, ha, byteOf_xorBytes _ _ hq, hz, h, show 136 * (33 / 136) = 0 from rfl, List.drop_zero]
    exact BitVec.zero_xor
  have hd : ∀ q, 33 ≤ q → Bs.getD q 0 = 0 := fun q hq' => by
    rw [List.getD, List.getElem?_eq_none (by omega)]; rfl
  rw [A0, byteOf_xorByte _ _ _ hq, byteOf_xorByte _ _ _ hq, hr]
  by_cases e1 : q < 33
  · rw [ite_eq_right (show ¬ q = 135 by omega), ite_eq_right (show ¬ q = 33 by omega), ite_eq_left e1]
  · rw [ite_eq_right e1, hd q (by omega)]
    by_cases e2 : q = 33
    · rw [ite_eq_right (show ¬ q = 135 by omega), ite_eq_left e2, ite_eq_left e2]; exact BitVec.zero_xor
    · rw [ite_eq_right e2, ite_eq_right e2]
      by_cases e3 : q = 135
      · rw [ite_eq_left e3, ite_eq_left e3]; exact BitVec.zero_xor
      · rw [ite_eq_right e3, ite_eq_right e3]


/-- The 128-byte noise PRF fits entirely in the first SHAKE256 block. -/
theorem prf_get {seed : List Byte} (hs : seed.length = 32) (nonce : Byte)
    {i : Nat} (hi : i < 128) :
    (Spec.MlKem.prf 2 seed nonce).getD i 0 =
      byteOf (keccakF (A0 (seed ++ [nonce]))) i := by
  have hlen : (seed ++ [nonce]).length = 33 := by simp [hs]
  change (squeeze 136 (padded 136 shakeSuffix (seed ++ [nonce])) 128).getD i 0 = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [Proof.Sha3.length_squeeze (by decide) (by decide)]; exact hi), Option.getD_some]
  rw [Proof.Sha3.squeeze_getElem (by decide) (by decide) _ hi, padded_A0 hlen,
    show i / 136 = 0 by omega, show i % 136 = i by omega]
  rfl

end VG.Proof.MlKem.AArch64.Noise.Seed
