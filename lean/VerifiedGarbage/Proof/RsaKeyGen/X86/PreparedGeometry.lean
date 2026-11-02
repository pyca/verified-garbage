module

public import VerifiedGarbage.Proof.MillerRabin.X86.Context

/-! # Complete padded-array bounds for candidate preparation -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Prepared
open VG VG.Proof.MillerRabin.X86

theorem paddedBefore (g : Geometry) {i j : Nat} (index : i < j) :
    g.array i + 8 * (g.w + 2) ≤ g.array j := by
  have step := Nat.mul_le_mul_right (8 * (g.w + 2)) index
  unfold Geometry.array Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes
  rw [Nat.succ_mul] at step
  omega

theorem paddedFit {g : Geometry} (v : g.Valid) {j : Nat} (index : j < 28) :
    g.array j + 8 * (g.w + 2) ≤ g.L := Nat.le_trans (paddedBefore g index) v.arraysFit

end VG.Proof.RsaKeyGen.X86.Prepared
