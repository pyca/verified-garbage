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

/-! # Streaming ChaCha20 (RFC 8439) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.ChaCha20.X86_64

def artifacts : List Artifact := [
  Spec.ChaCha20.initApi.artifact X86_64.target {
    code := Impl.ChaCha20.X86_64.Stream.init
    verified := Proof.ChaCha20.X86_64.Stream.init_verified },
  Spec.ChaCha20.setNonceApi.artifact X86_64.target {
    code := Impl.ChaCha20.X86_64.Stream.setNonce
    verified := Proof.ChaCha20.X86_64.Stream.setNonce_verified }]

end VG.Artifacts.ChaCha20.X86_64
