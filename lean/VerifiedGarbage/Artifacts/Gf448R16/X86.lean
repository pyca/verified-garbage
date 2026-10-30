module

public import VerifiedGarbage.Proof.X448.X86.FnVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.X448.X86.FnLit

/-! # Arithmetic in curve448's field, in radix `2^16`, on x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Gf448R16.X86

open VG.Spec.X448.Field16 VG.Impl.X448.X86 VG.Proof.X448.X86

def artifacts : List Artifact := [
  mulApi.artifact X86.target {
    code := mulFn
    verified := mulFn_verified },
  addApi.artifact X86.target {
    code := addFn
    verified := addFn_verified },
  subApi.artifact X86.target {
    code := subFn
    verified := subFn_verified },
  mulA24Api.artifact X86.target {
    code := mulA24Fn
    verified := mulA24Fn_verified }]

end VG.Artifacts.Gf448R16.X86
