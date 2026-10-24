module
import VerifiedGarbage.Proof.TripleDes.X86_64.FunctionsLit

public import VerifiedGarbage.Proof.TripleDes.X86_64.VerifiedBlock
public import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Verified
public import VerifiedGarbage.Proof.TripleDes.X86_64.Frame
import VerifiedGarbage.Proof.TripleDes.X86_64.SpSafe
public import VerifiedGarbage.Proof.TripleDes.X86_64.EcbCall.Verified
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.Lit
public import VerifiedGarbage.Proof.TripleDes.X86_64.SpSafe
import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Verified
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.Verified
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.Verified
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.X86_64.StraightX
import VerifiedGarbage.Proof.Framework.X86_64.StraightZ
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.X86_64.Words
public import VerifiedGarbage.Proof.Rc2.Word
public import VerifiedGarbage.Proof.Rc2.X86_64.Sse2Finish
public import VerifiedGarbage.Proof.TripleDes.Bytes
public import VerifiedGarbage.Proof.TripleDes.Permutation
public import VerifiedGarbage.Proof.TripleDes.X86_64.Box
public import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Component
public import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Copy
public import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Correct
public import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Loop
public import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Rotation
public import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Verified
public import VerifiedGarbage.Proof.TripleDes.X86_64.KeySteps
public import VerifiedGarbage.Proof.TripleDes.X86_64.RoundBody
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.Rc2.Word
import VerifiedGarbage.Proof.Rc2.X86_64.Sse2Finish
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.TripleDes.Permutation
import VerifiedGarbage.Proof.TripleDes.X86_64.Box
import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Component
import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Copy
import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Correct
import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Loop
import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Rotation
import VerifiedGarbage.Proof.TripleDes.X86_64.KeySteps
import VerifiedGarbage.Proof.TripleDes.X86_64.RoundBody
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified

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
