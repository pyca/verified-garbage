module

public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P384
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P384Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEC 1 point conversion with P384's existing field backend -/

@[expose] public section

namespace VG.Generic.P384.Arm.EcCompressedP384

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.P384.code
    verified := Proof.EcKey.Compressed.Arm.P384.verified },
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.P384Decompress.code
    verified := Proof.EcKey.Compressed.Arm.P384Decompress.verified h.law },
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    notes := ["Field multiplications are calls of `vg_p384_mul_mod_p_umaal` (and `vg_p384_mul_mod_n_umaal`), which multiply the numbers' 32-bit words with one `umaal` per word of each Montgomery row (`hi:lo = n m + hi + lo`)."]
    code := Proof.EcKey.Compressed.Arm.P384.codeU
    verified := Proof.EcKey.Compressed.Arm.P384.verifiedU
    features := ["umaal"] },
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    notes := ["Field multiplications are calls of `vg_p384_mul_mod_p_umaal` (and `vg_p384_mul_mod_n_umaal`), which multiply the numbers' 32-bit words with one `umaal` per word of each Montgomery row (`hi:lo = n m + hi + lo`)."]
    code := Proof.EcKey.Compressed.Arm.P384Decompress.codeU
    verified := Proof.EcKey.Compressed.Arm.P384Decompress.verifiedU h.law
    features := ["umaal"] }]

end VG.Generic.P384.Arm.EcCompressedP384
