module

public import VerifiedGarbage.Proof.TripleDes.X86_64.VerifiedBlock
public import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Verified
public import VerifiedGarbage.Proof.TripleDes.X86_64.Frame
import VerifiedGarbage.Proof.TripleDes.X86_64.SpSafe
public import VerifiedGarbage.Proof.TripleDes.X86_64.EcbCall.Verified
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.Lit

@[expose] public section

namespace VG.Artifacts.TripleDes.X86_64

def artifacts : List Artifact := [
  Spec.TripleDes.expandKeyApi.artifact X86_64.target {
    notes := ["Baseline x86-64 scalar key expansion with fixed permutations and public round-count branches."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 520 .rcx 64 Impl.TripleDes.X86_64.Key.expandKey
    stack := 520
    verified := Proof.TripleDes.X86_64.expandKey_framed },
  Spec.TripleDes.encryptBlockApi.artifact X86_64.target {
    notes := ["Baseline x86-64 scalar Boolean S-box circuits; IP and FP shared across all three DES passes."]
    code := Impl.TripleDes.X86_64.encryptBlock
    stack := 0
    verified := Proof.TripleDes.X86_64.encrypt_verified },
  Spec.TripleDes.decryptBlockApi.artifact X86_64.target {
    notes := ["Baseline x86-64 scalar Boolean S-box circuits with reverse EDE key order."]
    code := Impl.TripleDes.X86_64.decryptBlock
    stack := 0
    verified := Proof.TripleDes.X86_64.decrypt_verified },
  Spec.TripleDes.ecbEncryptCoreApi.artifact X86_64.target {
    notes := ["Bitsliced on baseline x86-64: 128 blocks at a time in SSE2 registers while that many are left, then 64 at a time in general-purpose registers, one block in each bit position of 64 state words, through Boolean S-box circuits."]
    code := Impl.TripleDes.X86_64.BitsliceSse.encrypt
    stack := 0
    verified := Proof.TripleDes.X86_64.BitslicedSse.encrypt_verified
    spSafe := Code.all_of_allInstrs (Proof.TripleDes.X86_64.sse_ecb_sp .encrypt) },
  Spec.TripleDes.ecbDecryptCoreApi.artifact X86_64.target {
    notes := ["Bitsliced on baseline x86-64: 128 blocks at a time in SSE2 registers while that many are left, then 64 at a time in general-purpose registers, one block in each bit position of 64 state words, through Boolean S-box circuits."]
    code := Impl.TripleDes.X86_64.BitsliceSse.decrypt
    stack := 0
    verified := Proof.TripleDes.X86_64.BitslicedSse.decrypt_verified
    spSafe := Code.all_of_allInstrs (Proof.TripleDes.X86_64.sse_ecb_sp .decrypt) },
  Spec.TripleDes.ecbEncryptApi.artifact X86_64.target {
    notes := ["Allocates the working space on the stack and calls the core, the SSE2 code, for every block; zeroes the working space before returning."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1032 .rcx 128
      (Impl.TripleDes.X86_64.EcbCall.sse .encrypt)
    stack := 1040
    verified := Proof.TripleDes.X86_64.ecb_framed (Proof.TripleDes.X86_64.EcbCall.sse_verified .encrypt)
      (Code.all_of_allInstrs (Proof.TripleDes.X86_64.EcbCall.sse_sp .encrypt))
      (Proof.TripleDes.X86_64.EcbCall.sse_depth .encrypt)
    spSafe := Proof.TripleDes.X86_64.ecb_spSafe (Proof.TripleDes.X86_64.EcbCall.sse_sp .encrypt) },
  Spec.TripleDes.ecbDecryptApi.artifact X86_64.target {
    notes := ["Allocates the working space on the stack and calls the core, the SSE2 code, for every block; zeroes the working space before returning."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1032 .rcx 128
      (Impl.TripleDes.X86_64.EcbCall.sse .decrypt)
    stack := 1040
    verified := Proof.TripleDes.X86_64.ecb_framed (Proof.TripleDes.X86_64.EcbCall.sse_verified .decrypt)
      (Code.all_of_allInstrs (Proof.TripleDes.X86_64.EcbCall.sse_sp .decrypt))
      (Proof.TripleDes.X86_64.EcbCall.sse_depth .decrypt)
    spSafe := Proof.TripleDes.X86_64.ecb_spSafe (Proof.TripleDes.X86_64.EcbCall.sse_sp .decrypt) },
  Spec.TripleDes.ecbEncryptApi.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["Bitsliced with AVX2: 256 blocks at a time, in place in the data, in 256-bit words; then calls the core (the SSE2 and 64-block code) for the rest."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1032 .rcx 128
      (Impl.TripleDes.X86_64.EcbCall.avx2 .encrypt)
    stack := 1040
    verified := Proof.TripleDes.X86_64.ecb_framed (Proof.TripleDes.X86_64.EcbCall.avx2_verified .encrypt)
      (Code.all_of_allInstrs (Proof.TripleDes.X86_64.EcbCall.avx2_sp .encrypt))
      (Proof.TripleDes.X86_64.EcbCall.avx2_depth .encrypt)
    features := ["avx", "avx2"]
    spSafe := Proof.TripleDes.X86_64.ecb_spSafe (Proof.TripleDes.X86_64.EcbCall.avx2_sp .encrypt) },
  Spec.TripleDes.ecbDecryptApi.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["Bitsliced with AVX2: 256 blocks at a time, in place in the data, in 256-bit words; then calls the core (the SSE2 and 64-block code) for the rest."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1032 .rcx 128
      (Impl.TripleDes.X86_64.EcbCall.avx2 .decrypt)
    stack := 1040
    verified := Proof.TripleDes.X86_64.ecb_framed (Proof.TripleDes.X86_64.EcbCall.avx2_verified .decrypt)
      (Code.all_of_allInstrs (Proof.TripleDes.X86_64.EcbCall.avx2_sp .decrypt))
      (Proof.TripleDes.X86_64.EcbCall.avx2_depth .decrypt)
    features := ["avx", "avx2"]
    spSafe := Proof.TripleDes.X86_64.ecb_spSafe (Proof.TripleDes.X86_64.EcbCall.avx2_sp .decrypt) },
  Spec.TripleDes.ecbEncryptApi.artifact X86_64.target {
    suffix := "_avx512"
    notes := ["Bitsliced with AVX-512: 512 blocks at a time, in place in the data, in 512-bit words, the S-box circuits fused into `vpternlogd` functions of up to three words; then the AVX2 batches, and the core (the SSE2 and 64-block code) for the rest."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1032 .rcx 128
      (Impl.TripleDes.X86_64.EcbCall.avx512 .encrypt)
    stack := 1040
    verified := Proof.TripleDes.X86_64.ecb_framed (Proof.TripleDes.X86_64.EcbCall.avx512_verified .encrypt)
      (Code.all_of_allInstrs (Proof.TripleDes.X86_64.EcbCall.avx512_sp .encrypt))
      (Proof.TripleDes.X86_64.EcbCall.avx512_depth .encrypt)
    features := ["avx", "avx2", "avx512f"]
    spSafe := Proof.TripleDes.X86_64.ecb_spSafe (Proof.TripleDes.X86_64.EcbCall.avx512_sp .encrypt) },
  Spec.TripleDes.ecbDecryptApi.artifact X86_64.target {
    suffix := "_avx512"
    notes := ["Bitsliced with AVX-512: 512 blocks at a time, in place in the data, in 512-bit words, the S-box circuits fused into `vpternlogd` functions of up to three words; then the AVX2 batches, and the core (the SSE2 and 64-block code) for the rest."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1032 .rcx 128
      (Impl.TripleDes.X86_64.EcbCall.avx512 .decrypt)
    stack := 1040
    verified := Proof.TripleDes.X86_64.ecb_framed (Proof.TripleDes.X86_64.EcbCall.avx512_verified .decrypt)
      (Code.all_of_allInstrs (Proof.TripleDes.X86_64.EcbCall.avx512_sp .decrypt))
      (Proof.TripleDes.X86_64.EcbCall.avx512_depth .decrypt)
    features := ["avx", "avx2", "avx512f"]
    spSafe := Proof.TripleDes.X86_64.ecb_spSafe (Proof.TripleDes.X86_64.EcbCall.avx512_sp .decrypt) }]

end VG.Artifacts.TripleDes.X86_64
