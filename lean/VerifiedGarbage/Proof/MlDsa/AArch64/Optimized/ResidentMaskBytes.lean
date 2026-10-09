import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentSeed66
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackSpec

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Spec.Sha3 (bytesAt)

/-- Five resident SHAKE256 blocks provide exactly the 576 or 640 bytes
consumed by the corresponding ExpandMask parser. -/
theorem stream_mask_bytes {m : Mem} {o : Addr} {Bs : List Byte} {d : Nat}
    (hd : d=18 ∨ d=20) (hlen : Bs.length=66)
    (h : Resident.StreamOutput m o 8 5 (ResidentSeed66.A0 Bs)) :
    bytesAt m o (32*d)=Spec.MlDsa.H Bs (32*d) := by
  have hb : (32*d+136-1)/136=5 := by rcases hd with rfl | rfl <;> decide
  have hc : 32*d≤136*5 := by omega
  have he : Spec.MlDsa.H Bs (32*d) =
      (Spec.Sha3.squeezeBlocks 136 (Spec.Sha3.keccakF (ResidentSeed66.A0 Bs)) 5).take (32*d) := by
    change Spec.Sha3.squeeze 136 (VG.Proof.MlKem.padded 136 Spec.Sha3.shakeSuffix Bs) (32*d)=_
    rw [ResidentSeed66.padded_A0 hlen,Spec.Sha3.squeeze,hb]
  rw [he]
  apply List.ext_getElem
  · rw [VG.Proof.MlKem.bytesAt_length,List.length_take,VG.Proof.Sha3.length_squeezeBlocks (by decide)]
    omega
  · intro j hj hj'
    rw [VG.Proof.MlKem.bytesAt_getElem,List.getElem_take]
    exact h.byte (by decide) (by rw [VG.Proof.MlKem.bytesAt_length] at hj; omega)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
