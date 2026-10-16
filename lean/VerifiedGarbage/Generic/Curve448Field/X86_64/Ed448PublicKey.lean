module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Ed448.X86_64.PublicKey.Verified
public import VerifiedGarbage.Proof.Ed448.Facts
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Ed448 public-key derivation on x86-64

The signature and documentation come from the reviewed Ed448 API. The
reference ladder's agreement with the specification (`Proof/Ed448/Facts.lean`)
is passed to the proof here, so that only registration files import it.
-/

@[expose] public section

namespace VG.Generic.Curve448Field.X86_64.Ed448PublicKey

def artifacts (v : Impl.Ed448.X86_64.FieldVariant) : List Artifact := [
  Spec.Ed448.publicKeyApi.artifact X86_64.target {
    suffix := v.suffix
    features := v.features
    notes := ["Uses the selected field backend and baseline integer instructions elsewhere. \
      Hashes the private key with `vg_keccak_absorb`, `vg_keccak_pad` and \
      `vg_keccak_squeeze` (SHAKE256, into `scratch`), prunes the first 57 bytes of the hash \
      into a stack frame, encodes `[s]B` with `vg_ed448_scalar_base`, and clears the frame's \
      copy of the scalar. The rest of the hash, and the base-point multiplication's working \
      values, are left in `scratch`."]
    code := Impl.Ed448.X86_64.publicKeyFor v
    stack := 104
    verified := Proof.Ed448.X86_64.PublicKey.publicKey_verified (v := v)
      Proof.Ed448.baseLadder_ok
    spSafe := Code.all_of_allInstrs (by cases v <;> lit_decide) }]

end VG.Generic.Curve448Field.X86_64.Ed448PublicKey
