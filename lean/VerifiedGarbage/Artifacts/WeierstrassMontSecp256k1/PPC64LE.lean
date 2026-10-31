module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontSecp256k1
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery arithmetic modulo secp256k1's `p` and `n` on PPC64LE

The functions of `Artifacts/WeierstrassMont/PPC64LE.lean` for secp256k1's moduli, in four 64-bit words. -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMontSecp256k1.PPC64LE

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.PPC64LE.Mont VG.Proof.Weierstrass.PPC64LE.Mont

def artifacts : List Artifact := [
  secp256k1p.mulApi.artifact PPC64LE.target {
    code := mulFn secp256k1p.k secp256k1p.m
    verified := secp256k1p_mul_verified },
  secp256k1p.addApi.artifact PPC64LE.target {
    code := addFn secp256k1p.k secp256k1p.m
    verified := secp256k1p_add_verified },
  secp256k1p.subApi.artifact PPC64LE.target {
    code := subFn secp256k1p.k secp256k1p.m
    verified := secp256k1p_sub_verified },
  secp256k1n.mulApi.artifact PPC64LE.target {
    code := mulFn secp256k1n.k secp256k1n.m
    verified := secp256k1n_mul_verified },
  secp256k1n.addApi.artifact PPC64LE.target {
    code := addFn secp256k1n.k secp256k1n.m
    verified := secp256k1n_add_verified },
  secp256k1n.subApi.artifact PPC64LE.target {
    code := subFn secp256k1n.k secp256k1n.m
    verified := secp256k1n_sub_verified }]

end VG.Artifacts.WeierstrassMontSecp256k1.PPC64LE
