module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.Framework.Registration

import VerifiedGarbage.Proof.Gcm.RISCV64.Lit

/-! # GHASH on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Gcm.RISCV64

def artifacts : List Artifact := [
  Spec.Gcm.ghashApi.artifact RISCV64.target {
    code := Impl.Gcm.RISCV64.ghash
    stack := 2048
    verified := Proof.Gcm.RISCV64.ghash_verified }]

end VG.Artifacts.Gcm.RISCV64
