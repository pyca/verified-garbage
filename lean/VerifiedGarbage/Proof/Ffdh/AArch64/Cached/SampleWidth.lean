module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SampleMask
public import VerifiedGarbage.Proof.Ffdh.VettedPolicy
import VerifiedGarbage.Proof.Framework.Omega

/-! The native mask and byte count encode exactly the reviewed sampler width. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG
open VG.Proof.Ffdh

theorem sample_width {N : Nat} (positive : 0<N) : ScalarWidth.width N=(N+7)/8 := by
 unfold ScalarWidth.width
 omega

theorem sample_headBits {N : Nat} (positive : 0<N) : ScalarWidth.headBits N=(N-1)%8+1 := by
 unfold ScalarWidth.headBits
 rw [sample_width positive]
 omega

theorem sample_mask {N : Nat} (positive : 0<N) : (sampleMask N).setWidth 8=ScalarWidth.mask N := by
 unfold sampleMask ScalarWidth.mask
 rw [sample_headBits positive]
 apply BitVec.eq_of_toNat_eq
 simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
 omega

theorem sample_octets {a : Spec.Ffdh.Parameters} {r : List Byte}
 (positive : 0<Spec.Ffdh.generationScalarBits a) :
 KeyScalar.cut r (r.length-(Spec.Ffdh.generationScalarBits a+7)/8)
  ((sampleMask (Spec.Ffdh.generationScalarBits a)).setWidth 8)=VettedPolicy.octets a r := by
 rw [sample_mask positive]
 unfold VettedPolicy.octets
 rw [sample_width positive]

end VG.Proof.Ffdh.AArch64.Cached
