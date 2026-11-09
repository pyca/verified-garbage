module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Verified
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512VL
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Xor
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Stream.Init
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.LitSplit
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
public import VerifiedGarbage.Proof.Aes.X86_64.Lit
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Stream.ApplyCT
public import VerifiedGarbage.Proof.Variants.ChaCha20Xor.X86_64

/-! # Streaming ChaCha20 (RFC 8439) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.ChaCha20.X86_64

def direct : List Artifact := [
  Spec.ChaCha20.initApi.artifact X86_64.target {
    code := Impl.ChaCha20.X86_64.Stream.init
    verified := Proof.ChaCha20.X86_64.Stream.init_verified },
  Spec.ChaCha20.setNonceApi.artifact X86_64.target {
    code := Impl.ChaCha20.X86_64.Stream.setNonce
    verified := Proof.ChaCha20.X86_64.Stream.setNonce_verified }]

end VG.Artifacts.ChaCha20.X86_64

-- Streaming ChaCha20 (RFC 8439) on x86-64: `vg_chacha20_apply`
namespace VG.Artifacts.ChaCha20.X86_64.ChaCha20Xor

def artifacts (v : Proof.ChaCha20.X86_64.XorImpl) : List Artifact :=
  if v.polyOnly then [] else [
  Spec.ChaCha20.applyApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.ChaCha20.X86_64.Stream.apply v.callee
    stack := 24
    verified := Proof.ChaCha20.X86_64.Stream.apply_verified v
    spSafe := Proof.ChaCha20.X86_64.Stream.apply_spSafe v
    features := v.features }]

end VG.Artifacts.ChaCha20.X86_64.ChaCha20Xor

namespace VG.Artifacts.ChaCha20.X86_64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.ChaCha20Xor.X86_64.variants.flatMap fun v => ChaCha20Xor.artifacts v)

end VG.Artifacts.ChaCha20.X86_64
