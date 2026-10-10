import VerifiedGarbage.Proof.TripleDes.X86_64.VerifiedBlock
import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Verified
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Verified
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.Verified
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.Verified
import VerifiedGarbage.Proof.TripleDes.X86_64.Frame
import VerifiedGarbage.Proof.TripleDes.X86_64.SpSafe
import VerifiedGarbage.Proof.TripleDes.X86_64.EcbCall.Verified

namespace VG.Artifacts.TripleDes.X86_64

def artifacts : List Artifact := [
  { Spec.TripleDes.expandKeyApi with
    target := X86_64.target
    doc := Spec.TripleDes.expandKeyApi.doc
      (notes := ["Baseline x86-64 scalar key expansion with fixed permutations and public round-count branches."])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 520 .rcx 64 Impl.TripleDes.X86_64.Key.expandKey
    contract := Spec.TripleDes.expandKeyContract X86_64.abi 520
    stack := 520
    verified := Proof.TripleDes.X86_64.expandKey_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.TripleDes.encryptBlockApi with
    target := X86_64.target
    doc := Spec.TripleDes.encryptBlockApi.doc
      (notes := ["Baseline x86-64 scalar Boolean S-box circuits; IP and FP shared across all three DES passes."])
    code := Impl.TripleDes.X86_64.encryptBlock
    contract := Spec.TripleDes.encryptBlockContract X86_64.abi
    stack := 0
    verified := Proof.TripleDes.X86_64.encrypt_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.TripleDes.decryptBlockApi with
    target := X86_64.target
    doc := Spec.TripleDes.decryptBlockApi.doc
      (notes := ["Baseline x86-64 scalar Boolean S-box circuits with reverse EDE key order."])
    code := Impl.TripleDes.X86_64.decryptBlock
    contract := Spec.TripleDes.decryptBlockContract X86_64.abi
    stack := 0
    verified := Proof.TripleDes.X86_64.decrypt_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.TripleDes.ecbEncryptCoreApi with
    target := X86_64.target
    doc := Spec.TripleDes.ecbEncryptCoreApi.doc
      (notes := ["Bitsliced on baseline x86-64: 128 blocks at a time in SSE2 registers while that many are left, then 64 at a time in general-purpose registers, one block in each bit position of 64 state words, through Boolean S-box circuits."])
    code := Impl.TripleDes.X86_64.BitsliceSse.encrypt
    contract := Spec.TripleDes.ecbEncryptCoreContract X86_64.abi
    stack := 0
    ofSig := ⟨_, _, _, by unfold Spec.TripleDes.ecbEncryptCoreContract Spec.TripleDes.ecbCoreContract; rfl⟩
    verified := Proof.TripleDes.X86_64.BitslicedSse.encrypt_verified
    spSafe := Code.all_of_allInstrs (Proof.TripleDes.X86_64.sse_ecb_sp .encrypt) },
  { Spec.TripleDes.ecbDecryptCoreApi with
    target := X86_64.target
    doc := Spec.TripleDes.ecbDecryptCoreApi.doc
      (notes := ["Bitsliced on baseline x86-64: 128 blocks at a time in SSE2 registers while that many are left, then 64 at a time in general-purpose registers, one block in each bit position of 64 state words, through Boolean S-box circuits."])
    code := Impl.TripleDes.X86_64.BitsliceSse.decrypt
    contract := Spec.TripleDes.ecbDecryptCoreContract X86_64.abi
    stack := 0
    ofSig := ⟨_, _, _, by unfold Spec.TripleDes.ecbDecryptCoreContract Spec.TripleDes.ecbCoreContract; rfl⟩
    verified := Proof.TripleDes.X86_64.BitslicedSse.decrypt_verified
    spSafe := Code.all_of_allInstrs (Proof.TripleDes.X86_64.sse_ecb_sp .decrypt) },
  { Spec.TripleDes.ecbEncryptApi with
    target := X86_64.target
    doc := Spec.TripleDes.ecbEncryptApi.doc
      (notes := ["Allocates the working space on the stack and calls the core, the SSE2 code, for every block; zeroes the working space before returning."])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1032 .rcx 128
      (Impl.TripleDes.X86_64.EcbCall.sse .encrypt)
    contract := Spec.TripleDes.ecbEncryptContract X86_64.abi 1040
    stack := 1040
    ofSig := ⟨_, _, _, by unfold Spec.TripleDes.ecbEncryptContract Spec.TripleDes.ecbContract; rfl⟩
    verified := Proof.TripleDes.X86_64.ecb_framed (Proof.TripleDes.X86_64.EcbCall.sse_verified .encrypt)
      (Code.all_of_allInstrs (Proof.TripleDes.X86_64.EcbCall.sse_sp .encrypt))
      (Proof.TripleDes.X86_64.EcbCall.sse_depth .encrypt)
    spSafe := Proof.TripleDes.X86_64.ecb_spSafe (Proof.TripleDes.X86_64.EcbCall.sse_sp .encrypt) },
  { Spec.TripleDes.ecbDecryptApi with
    target := X86_64.target
    doc := Spec.TripleDes.ecbDecryptApi.doc
      (notes := ["Allocates the working space on the stack and calls the core, the SSE2 code, for every block; zeroes the working space before returning."])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1032 .rcx 128
      (Impl.TripleDes.X86_64.EcbCall.sse .decrypt)
    contract := Spec.TripleDes.ecbDecryptContract X86_64.abi 1040
    stack := 1040
    ofSig := ⟨_, _, _, by unfold Spec.TripleDes.ecbDecryptContract Spec.TripleDes.ecbContract; rfl⟩
    verified := Proof.TripleDes.X86_64.ecb_framed (Proof.TripleDes.X86_64.EcbCall.sse_verified .decrypt)
      (Code.all_of_allInstrs (Proof.TripleDes.X86_64.EcbCall.sse_sp .decrypt))
      (Proof.TripleDes.X86_64.EcbCall.sse_depth .decrypt)
    spSafe := Proof.TripleDes.X86_64.ecb_spSafe (Proof.TripleDes.X86_64.EcbCall.sse_sp .decrypt) },
  { Spec.TripleDes.ecbEncryptApi with
    name := Spec.TripleDes.ecbEncryptApi.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.TripleDes.ecbEncryptApi.doc
      (notes := ["Bitsliced with AVX2: 256 blocks at a time, in place in the data, in 256-bit words; then calls the core (the SSE2 and 64-block code) for the rest."])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1032 .rcx 128
      (Impl.TripleDes.X86_64.EcbCall.avx2 .encrypt)
    contract := Spec.TripleDes.ecbEncryptContract X86_64.abi 1040
    stack := 1040
    ofSig := ⟨_, _, _, by unfold Spec.TripleDes.ecbEncryptContract Spec.TripleDes.ecbContract; rfl⟩
    verified := Proof.TripleDes.X86_64.ecb_framed (Proof.TripleDes.X86_64.EcbCall.avx2_verified .encrypt)
      (Code.all_of_allInstrs (Proof.TripleDes.X86_64.EcbCall.avx2_sp .encrypt))
      (Proof.TripleDes.X86_64.EcbCall.avx2_depth .encrypt)
    features := ["avx", "avx2"]
    spSafe := Proof.TripleDes.X86_64.ecb_spSafe (Proof.TripleDes.X86_64.EcbCall.avx2_sp .encrypt) },
  { Spec.TripleDes.ecbDecryptApi with
    name := Spec.TripleDes.ecbDecryptApi.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.TripleDes.ecbDecryptApi.doc
      (notes := ["Bitsliced with AVX2: 256 blocks at a time, in place in the data, in 256-bit words; then calls the core (the SSE2 and 64-block code) for the rest."])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1032 .rcx 128
      (Impl.TripleDes.X86_64.EcbCall.avx2 .decrypt)
    contract := Spec.TripleDes.ecbDecryptContract X86_64.abi 1040
    stack := 1040
    ofSig := ⟨_, _, _, by unfold Spec.TripleDes.ecbDecryptContract Spec.TripleDes.ecbContract; rfl⟩
    verified := Proof.TripleDes.X86_64.ecb_framed (Proof.TripleDes.X86_64.EcbCall.avx2_verified .decrypt)
      (Code.all_of_allInstrs (Proof.TripleDes.X86_64.EcbCall.avx2_sp .decrypt))
      (Proof.TripleDes.X86_64.EcbCall.avx2_depth .decrypt)
    features := ["avx", "avx2"]
    spSafe := Proof.TripleDes.X86_64.ecb_spSafe (Proof.TripleDes.X86_64.EcbCall.avx2_sp .decrypt) },
  { Spec.TripleDes.ecbEncryptApi with
    name := Spec.TripleDes.ecbEncryptApi.name ++ "_avx512"
    target := X86_64.target
    doc := Spec.TripleDes.ecbEncryptApi.doc
      (notes := ["Bitsliced with AVX-512: 512 blocks at a time, in place in the data, in 512-bit words, the S-box circuits fused into `vpternlogd` functions of up to three words; then the AVX2 batches, and the core (the SSE2 and 64-block code) for the rest."])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1032 .rcx 128
      (Impl.TripleDes.X86_64.EcbCall.avx512 .encrypt)
    contract := Spec.TripleDes.ecbEncryptContract X86_64.abi 1040
    stack := 1040
    ofSig := ⟨_, _, _, by unfold Spec.TripleDes.ecbEncryptContract Spec.TripleDes.ecbContract; rfl⟩
    verified := Proof.TripleDes.X86_64.ecb_framed (Proof.TripleDes.X86_64.EcbCall.avx512_verified .encrypt)
      (Code.all_of_allInstrs (Proof.TripleDes.X86_64.EcbCall.avx512_sp .encrypt))
      (Proof.TripleDes.X86_64.EcbCall.avx512_depth .encrypt)
    features := ["avx", "avx2", "avx512f"]
    spSafe := Proof.TripleDes.X86_64.ecb_spSafe (Proof.TripleDes.X86_64.EcbCall.avx512_sp .encrypt) },
  { Spec.TripleDes.ecbDecryptApi with
    name := Spec.TripleDes.ecbDecryptApi.name ++ "_avx512"
    target := X86_64.target
    doc := Spec.TripleDes.ecbDecryptApi.doc
      (notes := ["Bitsliced with AVX-512: 512 blocks at a time, in place in the data, in 512-bit words, the S-box circuits fused into `vpternlogd` functions of up to three words; then the AVX2 batches, and the core (the SSE2 and 64-block code) for the rest."])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1032 .rcx 128
      (Impl.TripleDes.X86_64.EcbCall.avx512 .decrypt)
    contract := Spec.TripleDes.ecbDecryptContract X86_64.abi 1040
    stack := 1040
    ofSig := ⟨_, _, _, by unfold Spec.TripleDes.ecbDecryptContract Spec.TripleDes.ecbContract; rfl⟩
    verified := Proof.TripleDes.X86_64.ecb_framed (Proof.TripleDes.X86_64.EcbCall.avx512_verified .decrypt)
      (Code.all_of_allInstrs (Proof.TripleDes.X86_64.EcbCall.avx512_sp .decrypt))
      (Proof.TripleDes.X86_64.EcbCall.avx512_depth .decrypt)
    features := ["avx", "avx2", "avx512f"]
    spSafe := Proof.TripleDes.X86_64.ecb_spSafe (Proof.TripleDes.X86_64.EcbCall.avx512_sp .decrypt) }]

end VG.Artifacts.TripleDes.X86_64
