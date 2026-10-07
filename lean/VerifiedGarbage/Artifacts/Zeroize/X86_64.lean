import VerifiedGarbage.Proof.Zeroize.X86_64Avx

namespace VG.Artifacts.Zeroize.X86_64
open VG.X86_64

def artifacts : List Artifact := [
  { Spec.Zeroize.zeroizeApi with
    target := target
    doc := Spec.Zeroize.zeroizeApi.doc
    code := Impl.Zeroize.X86_64.zeroize
    contract := Spec.Zeroize.zeroizeContract abi
    verified := Proof.Zeroize.X86_64.verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Zeroize.zeroizeApi with
    name := Spec.Zeroize.zeroizeApi.name ++ "_avx"
    target := target
    doc := Spec.Zeroize.zeroizeApi.doc (notes := ["It stores 64 bytes at a time from `ymm0`, and clears the \
      upper halves of the vector registers (`vzeroupper`) before returning."])
    code := Impl.Zeroize.X86_64.zeroizeAvx
    contract := Spec.Zeroize.zeroizeContract abi
    verified := Proof.Zeroize.X86_64.verifiedAvx
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    features := ["avx"] }]
end VG.Artifacts.Zeroize.X86_64
