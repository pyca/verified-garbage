import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedSpecPre
import VerifiedGarbage.Proof.Framework.ConstMem

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

def pairedSatMem : Mem := constMem 65536 expandedWords

theorem pairedSat_held : ∀i<512,pairedSatMem.readW (65536+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0 := by
  intro i hi
  exact constMem_held 65536 expandedWords (by rw [PairedTable.expandedWords_length]; decide)
    i (by rw [PairedTable.expandedWords_length]; exact hi)

theorem pairedSat_coeff_zero {p : Nat} (hp : p≤32768) {i : Nat} (hi : i<n) :
    coeffAt pairedSatMem (BitVec.ofNat 64 p) i=0 := by
  simp only [pairedSatMem,coeffAt,Mem.readW,BitVec.setWidth_eq]
  rw [Mem.read_eq_of_bytes (v := (0#32)) ?_]
  · rfl
  · intro j hj
    have ha : ¬ ((BitVec.ofNat 64 p+BitVec.ofNat 64 (4*i)+BitVec.ofNat 64 j)-65536).toNat<8*expandedWords.length := by
      rw [PairedTable.expandedWords_length]
      have hi' : i<256 := hi
      simp only [BitVec.toNat_sub,BitVec.toNat_add,BitVec.toNat_ofNat,
        show (65536:BitVec 64).toNat=65536 by decide]
      omega
    simp only [constMem,ha,ite_false]
    simp

theorem pairedSat_reduced {p : Nat} (hp : p≤32768) : Reduced pairedSatMem (BitVec.ofNat 64 p) := by
  intro i hi
  rw [pairedSat_coeff_zero hp hi]
  decide

theorem pairedSat_positive {p : Nat} (hp : p≤32768) : PositiveReduced pairedSatMem (BitVec.ofNat 64 p) := by
  intro i hi
  rw [pairedSat_coeff_zero hp hi]
  decide

end VG.Proof.MlDsa.AArch64.Optimized.Paired
