module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.SigMask
public import VerifiedGarbage.Proof.RsaKeyGen.MrWindow

/-! # Period-four alignment masks work identically on both native halves -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.SigMask
open VG VG.Impl.RsaKeyGen.X86.SigMask VG.Proof.RsaKeyGen

def combined (x : BitVec 64) : BitVec 32 := x.setWidth 32 ||| (x >>> 32).setWidth 32

theorem mask1 : ∀ k < 64, ((combined (BitVec.twoPow 64 k) &&& constant 1).toNat ≠ 0) ↔ 1 < sigOf k := by
  decide

theorem mask2 : ∀ k < 64, ((combined (BitVec.twoPow 64 k) &&& constant 2).toNat ≠ 0) ↔ 2 < sigOf k := by
  decide

theorem mask3 : ∀ k < 64, ((combined (BitVec.twoPow 64 k) &&& constant 3).toNat ≠ 0) ↔ 3 < sigOf k := by
  decide

theorem combined_pair (low high : BitVec 32) : combined (high ++ low) = low ||| high := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [combined, BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_append]
  simp [hi, show ¬ 32 + i < 32 by omega, show 32 + i - 32 = i by omega]

end VG.Proof.RsaKeyGen.X86.SigMask
