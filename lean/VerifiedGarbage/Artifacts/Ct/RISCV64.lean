module

public import VerifiedGarbage.Proof.Ct.RISCV64
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Constant-time byte comparison on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ct.RISCV64

def artifacts : List Artifact := [
  Spec.Ct.eqApi.artifact RISCV64.target {
    notes := ["The bytes are loaded one at a time, so that every load is naturally aligned."]
    code := Impl.Ct.RISCV64.eq
    verified := Proof.Ct.RISCV64.verified }]

end VG.Artifacts.Ct.RISCV64
