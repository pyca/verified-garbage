import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointAbi
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointCT

/-! The joint implementation satisfies the unchanged shared verification contract. -/
namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64

section
variable (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds)
include hL hT hI

theorem jointVerify_verified : Verified X86_64.target jointVerifyP256
    (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256.combConsts)) := by
  refine ⟨fun s hs => ?_,jointVerify_ct hL hT hI,implies.sat⟩
  obtain ⟨t,s',he,ha,hp⟩ := jointVerify_x86 hL hT hI s (implies.pre _ hs)
  exact ⟨t,s',he,ha,implies.post s s' hs hp⟩

theorem jointVerify_verified_adx : Verified X86_64.target jointVerifyP256Adx
    (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256.combConsts)) := by
  refine ⟨fun s hs => ?_,jointVerify_adx_ct hL hT hI,implies.sat⟩
  obtain ⟨t,s',he,ha,hp⟩ := jointVerify_x86_adx hL hT hI s (implies.pre _ hs)
  exact ⟨t,s',he,ha,implies.post s s' hs hp⟩

end
end VG.Proof.Ecdsa.Verify.X86_64
