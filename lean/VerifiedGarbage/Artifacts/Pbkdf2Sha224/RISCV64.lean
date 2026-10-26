module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Sha224
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# PBKDF2-HMAC-SHA-224 (RFC 8018) on RISC-V: the iteration and the whole derivation

The iteration is the one for every Merkle–Damgård hash function
(`Impl/Pbkdf2/RISCV64.lean`): each step is two calls of SHA-224's verified
compression function (`vg_sha256_compress`), on a block laid out once in
`scratch`, with the padding of a `B + D`-byte message written before the
loop. It keeps our caller's registers in `scratch` and uses no stack.

The whole derivation, `pbkdf2`, is the one for every streaming hash function
(`Impl/Pbkdf2/Whole/RISCV64.lean`), calling SHA-224's streaming `update`,
HMAC's `init` and `finalize` and the iteration above, in two frames of its
own: `iterate`'s working space, then our caller's registers, the key's
states, `U`, `T` and `INT (i)`. `stack` adds the stack HMAC's functions use
below them.
-/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Sha224.RISCV64

def artifacts : List Artifact := [
  Spec.Hmac.sha224I.iterateApi.artifact RISCV64.target {
    notes := ["The key, `u` and `t` are read and written a byte at a time, since the contract states no \
        alignment for them; `scratch` is rounded up to a multiple of 8."]
    code := Proof.Pbkdf2.RISCV64.Sha224.code
    verified := Proof.Pbkdf2.RISCV64.Sha224.iterate },
  Spec.Hmac.sha224I.pbkdf2Api.artifact RISCV64.target {
    notes := ["The password, the salt and `out` are read and written a byte at a time, since the \
        contract states no alignment for them."]
    code := Proof.Pbkdf2.Whole.RISCV64.Sha224.F.pbkdf2
    stack := Proof.Pbkdf2.Whole.RISCV64.Sha224.F.itB + Proof.Pbkdf2.Whole.RISCV64.Sha224.F.frB +
      Proof.Pbkdf2.Whole.RISCV64.Sha224.F.X
    verified := Proof.Pbkdf2.Whole.RISCV64.Sha224.pbkdf2 }]

end VG.Artifacts.Pbkdf2Sha224.RISCV64
