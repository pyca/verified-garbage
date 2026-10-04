import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.ChaCha20.X86.Xor
import VerifiedGarbage.Impl.ChaCha20.X86.Xor
import VerifiedGarbage.Proof.ChaCha20.X86.Lit
import VerifiedGarbage.Proof.ChaCha20.X86.Stream.Init

/-! # The ChaCha20 block function (RFC 8439) on x86 -/

namespace VG.Artifacts.ChaCha20.X86

def artifacts : List Artifact := [
  { Spec.ChaCha20.blockApi with
    target := X86.target
    doc := Spec.ChaCha20.blockApi.doc
    code := Impl.ChaCha20.X86.block
    contract := Spec.ChaCha20.blockContract X86.abi
    verified := Proof.ChaCha20.X86.block_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.ChaCha20.xorApi with
    target := X86.target
    doc := Spec.ChaCha20.xorApi.doc (notes := ["Four blocks at a time with SSE2 while more than \
      64 bytes remain (the last four for all that is left), keeping seven of the sixteen words of \
      the four states in XMM registers during the rounds; then, for the last 64 bytes or fewer, \
      calls `vg_chacha20_block` and XORs its output 16 bytes at a time."])
    code := Impl.ChaCha20.X86.Xor.xor
    contract := Spec.ChaCha20.xorContract X86.abi 12
    stack := 12
    verified := Proof.ChaCha20.X86.Xor.xor_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.ChaCha20.xorApi with
    name := "vg_chacha20_xor_ssse3"
    target := X86.target
    doc := Spec.ChaCha20.xorApi.doc (notes := ["Uses SSSE3: as `vg_chacha20_xor`, but rotates by 16 \
      and 8 bits with `pshufb` (its controls stored in `buf`)."])
    code := Impl.ChaCha20.X86.Xor.xorSsse3
    contract := Spec.ChaCha20.xorContract X86.abi 12
    stack := 12
    verified := Proof.ChaCha20.X86.Xor.xorSsse3_verified
    features := ["ssse3"]
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.ChaCha20.initApi with
    target := X86.target
    doc := Spec.ChaCha20.initApi.doc
    code := Impl.ChaCha20.X86.Stream.init
    contract := Spec.ChaCha20.initContract X86.abi
    verified := Proof.ChaCha20.X86.Stream.init_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.ChaCha20.setNonceApi with
    target := X86.target
    doc := Spec.ChaCha20.setNonceApi.doc
    code := Impl.ChaCha20.X86.Stream.setNonce
    contract := Spec.ChaCha20.setNonceContract X86.abi
    verified := Proof.ChaCha20.X86.Stream.setNonce_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) } ]

end VG.Artifacts.ChaCha20.X86
