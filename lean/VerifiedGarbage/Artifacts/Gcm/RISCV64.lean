module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.Framework.Registration

import VerifiedGarbage.Proof.Gcm.RISCV64.Lit

/-! # GHASH on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Gcm.RISCV64

def artifacts : List Artifact := [
  ]

end VG.Artifacts.Gcm.RISCV64
