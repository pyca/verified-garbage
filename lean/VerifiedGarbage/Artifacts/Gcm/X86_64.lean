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
public import VerifiedGarbage.TCB.X86_64.Print

/-! # GHASH on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Gcm.X86_64

def artifacts : List Artifact := [
  Spec.Gcm.prepareApi.artifact X86_64.target {
    suffix := "_vpclmul_avx512"
    code := Impl.Gcm.X86_64.Flag.prepareFlagged 48 Impl.Gcm.X86_64.PrepareZ.prepare
    verified := Proof.Gcm.X86_64.PrepareZ.prepareFlagged_verified
    features := ["avx", "avx2", "pclmulqdq", "ssse3", "vpclmulqdq", "avx512f"] },
  Spec.Gcm.prepareApi.artifact X86_64.target {
    suffix := "_vpclmul"
    code := Impl.Gcm.X86_64.Flag.prepareFlagged 16 Impl.Gcm.X86_64.Prepare16.prepare16
    verified := Proof.Gcm.X86_64.Prepare16.prepareFlagged_verified
    features := ["avx", "avx2", "ssse3", "vpclmulqdq"] },
  Spec.Gcm.prepareApi.artifact X86_64.target {
    suffix := "_pclmul_avx"
    code := Impl.Gcm.X86_64.Flag.prepareFlagged 16 Impl.Gcm.X86_64.PrepareAvx.prepare16
    verified := Proof.Gcm.X86_64.PrepareAvx.prepareFlagged_verified
    features := ["avx", "pclmulqdq"] },
  Spec.Gcm.prepareApi.artifact X86_64.target {
    suffix := ""
    code := Impl.Gcm.X86_64.Flag.prepareAbsent
    verified := Proof.Gcm.X86_64.Prepare.absent_verified },
  Spec.Gcm.wipePreparedApi.artifact X86_64.target {
    suffix := "_avx"
    code := Impl.Gcm.X86_64.Flag.wipe true
    verified := Proof.Gcm.X86_64.Prepare.wipe_verified true
    features := ["avx"] },
  Spec.Gcm.wipePreparedApi.artifact X86_64.target {
    code := Impl.Gcm.X86_64.Flag.wipe false
    verified := Proof.Gcm.X86_64.Prepare.wipe_verified false }]

end VG.Artifacts.Gcm.X86_64
