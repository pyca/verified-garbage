module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Sha1
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# PBKDF2-HMAC-SHA-1 (RFC 8018) on RISC-V: the iteration and the whole derivation

The iteration is SHA-1's own (`Impl/Pbkdf2/Sha1/RISCV64.lean`): each step
is two compressions inlined, of a block held in registers as words, since
`U`'s 20 bytes and the padding of a `64 + 20`-byte message fill one block,
and SHA-1's output words are the next block's first five; the key's hash
values and `T` are kept in `scratch` as words. It keeps our caller's
registers in `scratch` and uses no stack.

The whole derivation, `pbkdf2`, is the one for every streaming hash function
(`Impl/Pbkdf2/Whole/RISCV64.lean`), calling SHA-1's streaming `update`,
HMAC's `init` and `finalize` and the iteration above, in two frames of its
own: `iterate`'s working space, then our caller's registers, the key's
states, `U`, `T` and `INT (i)`. `stack` adds the stack HMAC's functions use
below them.
-/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Sha1.RISCV64

def artifacts : List Artifact := [
  Spec.Hmac.sha1I.iterateApi.artifact RISCV64.target {
    notes := ["The key, `u` and `t` are read and written a byte at a time, since the contract states no \
        alignment for them; `scratch` is rounded up to a multiple of 8.",
      "SHA-1's compression is inlined, the 16 words of the block in registers, two per step: each \
        step does about 40% fewer instructions than two calls of `vg_sha1_compress`."]
    code := Impl.Pbkdf2.Sha1.RISCV64.iterate
    verified := Proof.Pbkdf2.Sha1.RISCV64.iterate_verified },
  Spec.Hmac.sha1I.pbkdf2Api.artifact RISCV64.target {
    notes := ["The password, the salt and `out` are read and written a byte at a time, since the \
        contract states no alignment for them."]
    code := Proof.Pbkdf2.Whole.RISCV64.Sha1.F.pbkdf2
    stack := Proof.Pbkdf2.Whole.RISCV64.Sha1.F.itB + Proof.Pbkdf2.Whole.RISCV64.Sha1.F.frB +
      Proof.Pbkdf2.Whole.RISCV64.Sha1.F.X
    verified := Proof.Pbkdf2.Whole.RISCV64.Sha1.pbkdf2 }]

end VG.Artifacts.Pbkdf2Sha1.RISCV64
