module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryTape
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeState
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Impl.Dsa.Generation.Layout
import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
public import VerifiedGarbage.Proof.Dsa.Generation.Primality
public import VerifiedGarbage.Proof.Dsa.Generation.QCandidate

/-! # Instantiate the shared probable-prime engine for each shaped q -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

 theorem GenerationGeometry.qShape (p : GenerationGeometry) (seed : List Byte) :
    (Spec.Dsa.qCandidate (8 * p.qLen) seed) % 2 = 1 ∧
      3 ≤ Spec.Dsa.qCandidate (8 * p.qLen) seed := by
  have hn : 2 ≤ 8 * p.qLen := by rcases p.qWidth with h | h <;> omega
  have shape := VG.Proof.Dsa.Generation.qCandidate_shape hn seed
  refine ⟨shape.1, Nat.le_trans ?_ shape.2.1⟩
  rcases p.qWidth with h | h <;> rw [h] <;> decide

def GenerationGeometry.qPrime (p : GenerationGeometry) (rand : GenerationTape p)
    (seed : List Byte) : PrimeParams where
  B := VG.Proof.Bignum.off p.B arithmetic
  p := VG.Proof.Bignum.off p.B witness
  rp := rand.ptr
  Z := arithmeticBytes
  w := 4
  N := Spec.Dsa.qCandidate (8 * p.qLen) seed
  len := p.qLen
  drawBytes := if p.qLen = 20 then 24 else 32
  checks := 64
  rand := rand.bytes
  w4 := by decide
  w128 := by decide
  room := by decide
  len2 := by rcases p.qWidth with h | h <;> omega
  lenDraw := by rcases p.qWidth with h | h <;> rw [h] <;> decide
  drawMax := by split <;> decide
  drawMin := by split <;> decide
  lenWords := by rcases p.qWidth with h | h <;> rw [h] <;> decide
  predBits := VG.Proof.Dsa.Generation.predecessor_bits
    (by rcases p.qWidth with h | h <;> omega) (p.qShape seed).1
    (VG.Proof.Dsa.Generation.qCandidate_bitLength (by rcases p.qWidth with h | h <;> omega) seed)
  drawWidth := by
    rw [VG.Proof.Dsa.Generation.witness_width
      (by rcases p.qWidth with h | h <;> omega) (p.qShape seed).1
      (VG.Proof.Dsa.Generation.qCandidate_bitLength (by rcases p.qWidth with h | h <;> omega) seed)]
    rcases p.qWidth with h | h <;> rw [h] <;> decide
  odd := (p.qShape seed).1
  n3 := (p.qShape seed).2
  checksMax := by decide
  randMax := rand.size
  bufferSeparate := p.parts_disjoint
    (by rcases p.width with h | h | h <;> rw [h] <;> decide)
    (by rcases p.lengths with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rw [h1,h2] <;> decide)
    (by right; rcases p.qWidth with h | h <;> rw [h] <;> decide)
  bufferOutside := by
    intro i hi
    apply out_scr (p.parts_disjoint (d := witness) (n := p.qLen) (e := arithmetic) (k := arithmeticBytes)
      (by rcases p.lengths with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rw [h1,h2] <;> decide)
      (by rcases p.width with h | h | h <;> rw [h] <;> decide)
      (by left; rcases p.qWidth with h | h <;> rw [h] <;> decide))
    exact Offset.contains_base _ (by omega) (by rcases p.qWidth with h | h <;> omega)
  tapeBuffer := rand.part (by rcases p.lengths with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rw [h1,h2] <;> decide)

end VG.Proof.Dsa.AArch64.Generation
