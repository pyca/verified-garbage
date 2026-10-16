module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Verified
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512VL
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Xor
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.XorSplitVerified
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Stream.Init
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.LitSplit
public import VerifiedGarbage.Proof.Framework.Registration

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
    notes := ["Uses AVX-512: sixteen blocks at a time while at least 1024 bytes remain, then \
        at most two computations of eight or four blocks, four to a set of `zmm` registers, for \
        the rest, or `vg_chacha20_xor` for at most 64 bytes."]
    code := Impl.ChaCha20.X86_64.Avx512.xor
    stack := 16
    verified := Proof.ChaCha20.X86_64.Avx512.xor_verified
    features := ["avx", "avx512f"] },
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
    verified := Proof.ChaCha20.X86_64.Stream.setNonce_verified },
  Spec.ChaCha20.xorSplitApi.artifact X86_64.target {
    suffix := "_avx512"
    notes := ["Uses AVX-512, as `vg_chacha20_xor_avx512` does on `dst`, but each block of 64 \
        bytes of the input within the first `src_len` bytes, rounded down to a multiple of 64, is \
        loaded from `src`, by a comparison of lengths; the bytes of `src` after them (or, when \
        fewer than 513 bytes follow the whole 1024-byte passes, those from the last pass on) are \
        first copied to `dst`. Fewer than 513 bytes left after the whole 1024-byte passes are \
        XORed in place by a call of `vg_chacha20_xor_avx512`."]
    code := Impl.ChaCha20.X86_64.Avx512.xorSplit
    stack := 24
    verified := Proof.ChaCha20.X86_64.Avx512Split.xorSplit_verified
    features := ["avx", "avx512f"] }]

end VG.Artifacts.ChaCha20.X86_64
