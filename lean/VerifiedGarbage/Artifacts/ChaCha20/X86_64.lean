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

/-! # The ChaCha20 block function (RFC 8439) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.ChaCha20.X86_64

def artifacts : List Artifact := [
  Spec.ChaCha20.blockApi.artifact X86_64.target {
    code := Impl.ChaCha20.X86_64.block
    verified := Proof.ChaCha20.X86_64.block_verified },
  Spec.ChaCha20.xorApi.artifact X86_64.target {
    notes := ["Calls `vg_chacha20_block` for each 64 bytes."]
    code := Impl.ChaCha20.X86_64.Xor.xor
    stack := 8
    verified := Proof.ChaCha20.X86_64.Xor.xor_verified },
  Spec.ChaCha20.xorApi.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["Uses AVX2: eight blocks at a time while at least 512 bytes remain, then \
        at most two computations of four or two blocks, two to a set of `ymm` registers, for \
        the rest, or `vg_chacha20_xor` for at most 64 bytes."]
    code := Impl.ChaCha20.X86_64.Avx2.xor
    stack := 16
    verified := Proof.ChaCha20.X86_64.Avx2.xor_verified
    features := ["avx", "avx2"] },
  Spec.ChaCha20.xorApi.artifact X86_64.target {
    suffix := "_avx512"
    notes := ["Uses AVX-512: sixteen blocks at a time while at least 1024 bytes remain; then \
        twelve blocks in three sets of `zmm` registers, four blocks to a set, for 513 to 768 \
        bytes left, one more pass of sixteen for 769 to 1023, and at most two computations of \
        eight or four blocks for fewer; for 257 to 320 bytes left, five blocks: the second set \
        on 128-bit registers (AVX-512VL's `vprold`)."]
    code := Impl.ChaCha20.X86_64.Avx512.xor
    stack := 16
    verified := Proof.ChaCha20.X86_64.Avx512.xor_verified
    features := ["avx", "avx512f", "avx512vl"] },
  Spec.ChaCha20.xorApi.artifact X86_64.target {
    suffix := "_avx512vl"
    notes := ["For CPUs with AVX-512 whose clock a 512-bit instruction lowers for a while \
        (Skylake-SP, Cascade Lake): fewer than 513 bytes on `ymm` registers, as \
        `vg_chacha20_xor_avx2` does but with AVX-512VL's `vprold` for every rotation (eight \
        blocks with every word in a register, or at most six), so that the code after a short \
        call keeps its speed; more as `vg_chacha20_xor_avx512` does."]
    code := Impl.ChaCha20.X86_64.Avx512VL.xorBy
    stack := 16
    verified := Proof.ChaCha20.X86_64.Avx512VL.xor_verified
    features := ["avx", "avx2", "avx512f", "avx512vl"] },
  Spec.ChaCha20.initApi.artifact X86_64.target {
    code := Impl.ChaCha20.X86_64.Stream.init
    verified := Proof.ChaCha20.X86_64.Stream.init_verified },
  Spec.ChaCha20.setNonceApi.artifact X86_64.target {
    code := Impl.ChaCha20.X86_64.Stream.setNonce
    verified := Proof.ChaCha20.X86_64.Stream.setNonce_verified }]

end VG.Artifacts.ChaCha20.X86_64
