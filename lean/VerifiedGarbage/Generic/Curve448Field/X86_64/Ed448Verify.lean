module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Verified
public import VerifiedGarbage.Proof.Ed448.X86_64.VariantVerified
public import VerifiedGarbage.Proof.Ed448.Facts

/-!
# Ed448 verification on x86-64

The signature and documentation come from the reviewed Ed448 API. The proof
of `vg_ed448_verify_equation` is passed to the caller's here, so that only
this file imports it, with the reference computations' agreement with the
specification (`Proof/Ed448/Facts.lean`).
-/

@[expose] public section

namespace VG.Generic.Curve448Field.X86_64.Ed448Verify

def artifacts (v : Impl.Ed448.X86_64.FieldVariant) : List Artifact := [
  { Spec.Ed448.verifyApi with
    name := Spec.Ed448.verifyApi.name ++ v.suffix
    features := v.features
    target := X86_64.target
    doc := Spec.Ed448.verifyApi.doc (notes := ["Uses the selected field backend and baseline integer instructions elsewhere. Returns 0 \
      at once for a context of 256 bytes or more. Otherwise writes the first ten bytes of \
      dom4(0, C) into a stack frame, hashes them, the context, R, the public key and the \
      message with `vg_keccak_absorb`, `vg_keccak_pad` and `vg_keccak_squeeze` (SHAKE256, \
      with the Keccak state and the sponge functions' working space in `scratch`) into the \
      frame, reduces the hash modulo L there with `vg_ed448_scalar_reduce`, and returns \
      `vg_ed448_verify_equation`'s result. The frame (the hash and k) is not cleared: \
      verification has no secrets."])
    code := Impl.Ed448.X86_64.Verify.verifyFor v
    contract := Spec.Ed448.verifyContract X86_64.abi 272
    stack := 272
    verified := Proof.Ed448.X86_64.Verify.verify_verified
      (Proof.Ed448.X86_64.verifyEquationFor_ok v Proof.Ed448.recover_ok Proof.Ed448.verifyEq_ok)
      (Proof.Ed448.X86_64.verifyEquationFor_ct v Proof.Ed448.recover_ok Proof.Ed448.verifyEq_ok)
    spSafe := Code.all_of_allInstrs (by cases v <;> lit_decide) }]

end VG.Generic.Curve448Field.X86_64.Ed448Verify
