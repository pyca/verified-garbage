module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's `(r + k s) mod L`, on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Ed25519MulAdd.PPC64LE

def artifacts : List Artifact := [
  Spec.Ed25519.scalarMulAddApi.artifact PPC64LE.target {
    notes := ["Uses baseline integer instructions. The function computes the 512-bit `k s` row by \
      row with `mulld` (X25519's PPC64LE product, without its reduction), adds `r`, and reduces \
      the sum bit by bit as `vg_ed25519_scalar_reduce` does. The nonvolatile registers it uses \
      are saved at bytes 1024 to 1119 of `scratch`."]
    code := Impl.Ed25519.PPC64LE.scalarMulAdd
    verified := Proof.Ed25519.PPC64LE.scalarMulAdd_verified }]

end VG.Artifacts.Ed25519MulAdd.PPC64LE
