module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.FieldVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Products and powers in curve25519's field, in radix `2^32`, on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Gf25519R32.PPC64LE

open VG.Spec.X25519.Field32 VG.Impl.Ed25519.PPC64LE VG.Proof.Ed25519.PPC64LE

def artifacts : List Artifact := [
  mulApi.artifact PPC64LE.target {
    code := mulFn
    verified := mulFn_verified },
  pow250Api.artifact PPC64LE.target {
    code := pow250Fn
    verified := pow250Fn_verified }]

end VG.Artifacts.Gf25519R32.PPC64LE
