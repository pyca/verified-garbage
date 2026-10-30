module

public import VerifiedGarbage.Proof.Scrypt.X86.Whole.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# scrypt (RFC 7914 §6) on x86, over SHA-256

A generic file (see `TCB/Emit.lean`): `vg_scrypt`, calling the
`vg_pbkdf2_hmac_sha256_scratch` made with the backend's SHA-256 functions (and
`vg_scrypt_romix`), is emitted for every x86 SHA-256 backend, named with its
suffix (e.g. `vg_scrypt_shani`), and needs its CPU features.

The stack is 116 bytes: a 36-byte frame, the return address of a call, and
the 76 bytes `vg_pbkdf2_hmac_sha256_scratch` uses.
-/

@[expose] public section

namespace VG.Generic.Sha256.X86.Scrypt

open VG.Proof.Scrypt.X86.Whole (pbkName pbkOf scrypt_verified scrypt_spSafe)

def artifacts (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := [
  Spec.Scrypt.scryptApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.Scrypt.X86.scrypt (pbkName v) (pbkOf v)
    stack := 116
    verified := scrypt_verified v
    spSafe := scrypt_spSafe v
    features := v.features }]

end VG.Generic.Sha256.X86.Scrypt
