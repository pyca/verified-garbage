module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Md5
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# HMAC-MD5 (RFC 2104) on RISC-V

The code for every Merkle–Damgård hash function with verified RISC-V
streaming functions (`Impl/Hmac/Stream/RISCV64.lean`), calling MD5's.
`init` takes a key of any length (`initAnyKeyApi`): a key longer than a
block is first hashed with the streaming functions into its frame, and its
digest used as the key; then it sets both states' hash values with the
streaming `init` and absorbs `K₀ ⊕ ipad` and `K₀ ⊕ opad` with `update`,
and zeroes the part of its frame that held the long key's state and digest.
`finalize` finalizes the inner state into its frame, makes it represent the
outer block, absorbs the inner digest and finalizes again into `out`. Each
keeps our caller's registers in a frame of its own; `stack` adds the stack
the streaming functions use below it.
-/

@[expose] public section

namespace VG.Artifacts.HmacMd5.RISCV64

def artifacts : List Artifact := [
  Spec.Hmac.md5I.initAnyKeyApi.artifact RISCV64.target {
    code := Proof.Hmac.Stream.RISCV64.Md5.hash.init
    stack := Proof.Hmac.Stream.RISCV64.Md5.hash.ibytes + Proof.Hmac.Stream.RISCV64.Md5.hash.F
    verified := Proof.Hmac.Stream.RISCV64.Md5.init },
  Spec.Hmac.md5I.finalizeApi.artifact RISCV64.target {
    code := Proof.Hmac.Stream.RISCV64.Md5.hash.finalize
    stack := Proof.Hmac.Stream.RISCV64.Md5.hash.fbytes + Proof.Hmac.Stream.RISCV64.Md5.hash.F
    verified := Proof.Hmac.Stream.RISCV64.Md5.finalize }]

end VG.Artifacts.HmacMd5.RISCV64
