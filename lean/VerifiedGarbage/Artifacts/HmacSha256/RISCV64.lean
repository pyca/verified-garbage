module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# HMAC-SHA-256 (RFC 2104) on RISC-V

The code for every Merkle–Damgård hash function with verified RISC-V
streaming functions (`Impl/Hmac/Stream/RISCV64.lean`), calling SHA-256's.
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

namespace VG.Artifacts.HmacSha256.RISCV64

def artifacts : List Artifact := [
  Spec.Hmac.sha256I.initAnyKeyApi.artifact RISCV64.target {
    notes := ["The key and the states are read and written a byte at a time, since the contract \
        states no alignment for them."]
    code := Proof.Hmac.Stream.RISCV64.Sha256Family.hash256.init
    stack := Proof.Hmac.Stream.RISCV64.Sha256Family.hash256.ibytes + Proof.Hmac.Stream.RISCV64.Sha256Family.hash256.F
    verified := Proof.Hmac.Stream.RISCV64.Sha256.init },
  Spec.Hmac.sha256I.finalizeApi.artifact RISCV64.target {
    notes := ["The states are read and written a byte at a time, since the contract states no \
        alignment for them."]
    code := Proof.Hmac.Stream.RISCV64.Sha256Family.hash256.finalize
    stack := Proof.Hmac.Stream.RISCV64.Sha256Family.hash256.fbytes + Proof.Hmac.Stream.RISCV64.Sha256Family.hash256.F
    verified := Proof.Hmac.Stream.RISCV64.Sha256.finalize }]

end VG.Artifacts.HmacSha256.RISCV64
