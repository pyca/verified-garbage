module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Md5
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# PBKDF2-HMAC-MD5 (RFC 8018) on RISC-V: the iteration and the whole derivation

The iteration is the one for every Merkle–Damgård hash function
(`Impl/Pbkdf2/RISCV64.lean`): each step is two calls of MD5's verified
compression function (`vg_md5_compress`), on a block laid out once in
`scratch`, with the padding of a `B + D`-byte message written before the
loop. It keeps our caller's registers in `scratch` and uses no stack.

The whole derivation, `pbkdf2`, is the one for every streaming hash function
(`Impl/Pbkdf2/Whole/RISCV64.lean`), calling MD5's streaming `update`,
HMAC's `init` and `finalize` and the iteration above, in two frames of its
own: `iterate`'s working space, then our caller's registers, the key's
states, `U`, `T` and `INT (i)`. `stack` adds the stack HMAC's functions use
below them.
-/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Md5.RISCV64

def artifacts : List Artifact := [
  Spec.Hmac.md5I.iterateApi.artifact RISCV64.target {
    code := Proof.Pbkdf2.RISCV64.Md5.code
    verified := Proof.Pbkdf2.RISCV64.Md5.iterate },
  Spec.Hmac.md5I.pbkdf2Api.artifact RISCV64.target {
    code := Proof.Pbkdf2.Whole.RISCV64.Md5.F.pbkdf2
    stack := Proof.Pbkdf2.Whole.RISCV64.Md5.F.itB + Proof.Pbkdf2.Whole.RISCV64.Md5.F.frB +
      Proof.Pbkdf2.Whole.RISCV64.Md5.F.X
    verified := Proof.Pbkdf2.Whole.RISCV64.Md5.pbkdf2 }]

end VG.Artifacts.Pbkdf2Md5.RISCV64
