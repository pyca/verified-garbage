module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's reduction of a 64-byte scalar modulo `L`, on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Ed25519Scalar.PPC64LE

def artifacts : List Artifact := [
  Spec.Ed25519.scalarReduceApi.artifact PPC64LE.target {
    notes := ["Uses baseline integer instructions. The function reduces all 512 input bits from \
      the top, one at a time, in eight 32-bit limbs: the remainder doubled with the bit as the \
      carry in, then `L` subtracted (as an addition of `2^256 - L`, whose carry out says whether \
      the remainder was at least `L`) and selected with a mask. The nonvolatile registers it uses \
      are saved at bytes 1024 to 1119 of `scratch`."]
    code := Impl.Ed25519.PPC64LE.scalarReduce
    verified := Proof.Ed25519.PPC64LE.scalarReduce_verified }]

end VG.Artifacts.Ed25519Scalar.PPC64LE
