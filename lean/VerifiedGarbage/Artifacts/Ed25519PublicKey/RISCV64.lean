module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.PublicKeyVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's public key from a seed, on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ed25519PublicKey.RISCV64

def artifacts : List Artifact := [
  Spec.Ed25519.publicKeyApi.artifact RISCV64.target {
    notes := ["Includes SHA-512 of the seed (calls of SHA-512's streaming functions, their state and \
      working space in `scratch`), RFC 8032 pruning, and base-point multiplication (a call of \
      `vg_ed25519_scalar_base`). The digest, the scalar, the saved callee-saved registers and `ra` \
      are in a frame of 144 bytes on the stack, whose first 136 are cleared before returning."]
    code := Impl.Ed25519.RISCV64.Whole.publicKeyCode
    stack := 352
    verified := Proof.Ed25519.RISCV64.Whole.publicKey_framed }]

end VG.Artifacts.Ed25519PublicKey.RISCV64
