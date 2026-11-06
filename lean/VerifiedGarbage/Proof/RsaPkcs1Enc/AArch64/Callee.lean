module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.Depth

/-!
# RSAES-PKCS1-v1_5 encryption on AArch64: the public-key operation, as a callee

Encryption calls `vg_rsa_public_checked`. A `PubImpl` is any implementation
of it verified against its shared contract
`Proof.Rsa.publicCheckedContract` with `stack` bytes of stack, whose frames
fit in them; the proof of encryption is written for any of them.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64

open VG VG.AArch64

/-- An implementation of `vg_rsa_public_checked`: its symbol and code,
verified against the shared contract with `stack` bytes of stack, which
its frames fit in. -/
structure PubImpl where
  name : String
  code : Prog isa
  stack : Nat
  verified : Verified AArch64.target code (Proof.Rsa.publicCheckedContract AArch64.abi stack)
  pos : 0 < stack
  depth : 16 * code.aarch64Depth ≤ stack
  spSafe : code.all (fun i => !isa.writesSp i) = true

end VG.Proof.RsaPkcs1Enc.AArch64
