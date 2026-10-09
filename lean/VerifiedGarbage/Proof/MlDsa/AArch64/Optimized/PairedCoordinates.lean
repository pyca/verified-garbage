import VerifiedGarbage.Spec.MlDsa.PairedResponse
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedProductField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckSlot

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa

/-- The final paired pass visits each coefficient in the public strided order. -/
theorem checkAddr_coeff (m : Mem) (out : Addr) (u : Nat) (i : Fin 2 × Fin 8)
    {e : Nat} (he : e<4) :
    vword (m.read (checkAddr (out+BitVec.ofNat 64 (16*u)) i) 16) e=
      coeffAt m (pairPolyPtr out i.1.val) (4*u+32*i.2.val+e) := by
  rw [VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he]
  simp only [checkAddr,coeffAt,pairPolyPtr,BitVec.add_assoc,←BitVec.ofNat_add]
  rw [show 16*u+(1024*i.1.val+128*i.2.val)+4*e=
    1024*i.1.val+4*(4*u+32*i.2.val+e) by omega]

theorem paired_coordinate {k : Nat} (hk : k<n) :
    k=4*(k%32/4)+32*(k/32)+k%4 ∧ k%32/4<8 ∧ k/32<8 ∧ k%4<4 := by
  change k<256 at hk
  omega

end VG.Proof.MlDsa.AArch64.Optimized.Paired
