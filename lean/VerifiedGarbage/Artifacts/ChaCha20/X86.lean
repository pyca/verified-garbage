module

public import VerifiedGarbage.Proof.ChaCha20.X86.Xor
public import VerifiedGarbage.Proof.ChaCha20.X86.Stream.Init
import VerifiedGarbage.Proof.ChaCha20.X86.Lit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # The ChaCha20 block function (RFC 8439) on x86 -/

@[expose] public section

namespace VG.Artifacts.ChaCha20.X86

def artifacts : List Artifact := [
  Spec.ChaCha20.blockApi.artifact X86.target {
    code := Impl.ChaCha20.X86.block
    verified := Proof.ChaCha20.X86.block_verified },
  Spec.ChaCha20.xorApi.artifact X86.target {
    notes := ["Four blocks at a time with SSE2 while more than \
      64 bytes remain (the last four for all that is left), keeping seven of the sixteen words of \
      the four states in XMM registers during the rounds; then, for the last 64 bytes or fewer, \
      calls `vg_chacha20_block` and XORs its output 16 bytes at a time."]
    code := Impl.ChaCha20.X86.Xor.xor
    stack := 12
    verified := Proof.ChaCha20.X86.Xor.xor_verified },
  Spec.ChaCha20.xorApi.artifact X86.target {
    suffix := "_ssse3"
    notes := ["Uses SSSE3: as `vg_chacha20_xor`, but rotates by 16 \
      and 8 bits with `pshufb` (its controls stored in `buf`)."]
    code := Impl.ChaCha20.X86.Xor.xorSsse3
    stack := 12
    verified := Proof.ChaCha20.X86.Xor.xorSsse3_verified
    features := ["ssse3"] },
  Spec.ChaCha20.initApi.artifact X86.target {
    code := Impl.ChaCha20.X86.Stream.init
    verified := Proof.ChaCha20.X86.Stream.init_verified },
  Spec.ChaCha20.setNonceApi.artifact X86.target {
    code := Impl.ChaCha20.X86.Stream.setNonce
    verified := Proof.ChaCha20.X86.Stream.setNonce_verified } ]

end VG.Artifacts.ChaCha20.X86
