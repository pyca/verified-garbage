module

public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Key
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.RISCV64.InvLaw
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.Correct
import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.KeyCT

/-! # `vg_rsa_keygen_key` on RISC-V: verified against the shared contract

Correct (`key_verified_of`, `Correct.lean`) and constant time (`key_ct`, `KeyCT.lean`). -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Key

open VG VG.RISCV64

/-- `vg_rsa_keygen_key`. -/
theorem key_verified [VG.Proof.Rsa.RISCV64.InvLaw] :
    Verified RISCV64.target VG.Impl.RsaKeyGen.RISCV64.Key.code (Spec.RsaKeyGen.keyContract RISCV64.abi) :=
  key_verified_of key_ct

end VG.Proof.RsaKeyGen.RISCV64.Key
