import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseVerified

namespace VG.Artifacts.Ed25519ScalarBase.X86

def artifacts : List Artifact := [
  { Spec.Ed25519.scalarBaseApi with
    target := X86.target
    doc := Spec.Ed25519.scalarBaseApi.doc (notes := ["Multiplies with a comb of precomputed multiples of \
      the base point (64 signed radix-16 digits, 32 tables of 8 points, every entry of a table read \
      and masked), then writes a canonical compressed point. \
      Callee-saved registers are saved in the first 16 bytes of `scratch`."])
    code := Impl.Ed25519.X86.scalarBase
    contract := Spec.Ed25519.scalarBaseContract X86.abi
    verified := Proof.Ed25519.X86.scalarBase_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]
end VG.Artifacts.Ed25519ScalarBase.X86
