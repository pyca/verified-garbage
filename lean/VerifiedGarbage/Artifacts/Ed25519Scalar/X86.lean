module

public import VerifiedGarbage.Proof.Ed25519.X86.ScalarVerified
import VerifiedGarbage.Proof.Ed25519.X86.ScalarLit
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Ed25519Scalar.X86

def artifacts : List Artifact := [
  Spec.Ed25519.scalarReduceApi.artifact X86.target {
    notes := ["Processes all 512 input bits using \
      eight 32-bit remainder words, a fixed byte loop, and masked subtraction of the subgroup order. \
      Callee-saved registers are saved in the first 16 bytes of `scratch`."]
    code := Impl.Ed25519.X86.scalarReduce
    stack := 8
    verified := Proof.Ed25519.X86.scalarReduce_verified }]
end VG.Artifacts.Ed25519Scalar.X86
