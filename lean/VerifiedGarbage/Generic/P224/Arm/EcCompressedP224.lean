module

public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P224
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P224Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEC 1 point conversion with P224's existing field backend -/

@[expose] public section

namespace VG.Generic.P224.Arm.EcCompressedP224

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact := [
  Spec.EcKey.P224.inst.compressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.P224.code
    verified := Proof.EcKey.Compressed.Arm.P224.verified },
  Spec.EcKey.P224.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.P224Decompress.code
    verified := Proof.EcKey.Compressed.Arm.P224Decompress.verified h.law },
  Spec.EcKey.P224.inst.compressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    notes := ["Field multiplications are calls of `vg_p224_mul_mod_p_umaal` (and `vg_p224_mul_mod_n_umaal`), which multiply the numbers' 32-bit words with one `umaal` per word of each Montgomery row (`hi:lo = n m + hi + lo`)."]
    code := Proof.EcKey.Compressed.Arm.P224.codeU
    verified := Proof.EcKey.Compressed.Arm.P224.verifiedU
    features := ["umaal"] },
  Spec.EcKey.P224.inst.decompressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    notes := ["Field multiplications are calls of `vg_p224_mul_mod_p_umaal` (and `vg_p224_mul_mod_n_umaal`), which multiply the numbers' 32-bit words with one `umaal` per word of each Montgomery row (`hi:lo = n m + hi + lo`)."]
    code := Proof.EcKey.Compressed.Arm.P224Decompress.codeU
    verified := Proof.EcKey.Compressed.Arm.P224Decompress.verifiedU h.law
    features := ["umaal"] }]

end VG.Generic.P224.Arm.EcCompressedP224
