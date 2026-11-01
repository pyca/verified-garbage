module

import VerifiedGarbage.Proof.Gcm.X86_64.Vpclmul.Lit
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Lit
import VerifiedGarbage.Proof.Gcm.X86_64.Lit
public import VerifiedGarbage.Proof.Gcm.X86_64.Ghash
public import VerifiedGarbage.Proof.Gcm.X86_64.Vpclmul.Ghash
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Ok
public import VerifiedGarbage.Proof.Gcm.X86_64.PrepareZ
public import VerifiedGarbage.Proof.Gcm.X86_64.PrepareAvx.Ok
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepare16
public import VerifiedGarbage.Proof.Framework.Registration

/-! # GHASH on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Gcm.X86_64

def artifacts : List Artifact := [
  Spec.Gcm.prepareApi.artifact X86_64.target {
    suffix := "_vpclmul_avx512"
    code := Impl.Gcm.X86_64.PrepareZ.prepare
    verified := Proof.Gcm.X86_64.PrepareZ.prepare_verified
    features := ["avx", "avx2", "pclmulqdq", "ssse3", "vpclmulqdq", "avx512f"] },
  Spec.Gcm.prepare16Api.artifact X86_64.target {
    suffix := "_vpclmul"
    written := [("ctx", 512)]
    code := Impl.Gcm.X86_64.Prepare16.prepare16
    verified := Proof.Gcm.X86_64.Prepare16.prepare16_verified
    writtenOk := Proof.Gcm.X86_64.Prepare16.prepare16_written
    features := ["avx", "avx2", "ssse3", "vpclmulqdq"] },
  Spec.Gcm.prepare16Api.artifact X86_64.target {
    suffix := "_pclmul_avx"
    written := [("ctx", 512)]
    code := Impl.Gcm.X86_64.PrepareAvx.prepare16
    verified := Proof.Gcm.X86_64.PrepareAvx.prepare16_verified
    writtenOk := Proof.Gcm.X86_64.PrepareAvx.prepare16_written
    features := ["avx", "pclmulqdq"] }]

end VG.Artifacts.Gcm.X86_64
