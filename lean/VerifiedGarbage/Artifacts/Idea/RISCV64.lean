module

public import VerifiedGarbage.Proof.Idea.RISCV64.Invert
public import VerifiedGarbage.Proof.Idea.RISCV64.Key
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.RISCV64.Lit

/-! # IDEA artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.Idea.RISCV64

def artifacts : List Artifact := [
  Spec.Idea.expandKeyApi.artifact RISCV64.target {
    notes := ["The key, as a 128-bit number, is held in two registers and rotated left by 25 bits between groups of eight subkeys with shifts; each subkey is a 16-bit window of one of them, without branches. The key and the schedule are accessed a byte at a time, since the contract states no alignment for them."]
    code := Impl.Idea.RISCV64.expandKey
    verified := Proof.Idea.RISCV64.expandKey_verified },
  Spec.Idea.invertKeyApi.artifact RISCV64.target {
    notes := ["Each inverse is `a ^ (2^16 - 1)` modulo 2^16 + 1, fifteen squarings and multiplications by `mul`, each reduced without branches. The subkeys are accessed a byte at a time."]
    code := Impl.Idea.RISCV64.invertKey
    verified := Proof.Idea.RISCV64.invertKey_verified },
  Spec.Idea.ecbApi.artifact RISCV64.target {
    notes := ["A block at a time in temporaries and argument registers: each multiplication modulo 2^16 + 1 is a `mul` of the residues and a reduction of the product from its halves, without branches. Subkeys and data are accessed a byte at a time, since the contract states no alignment for them."]
    code := Impl.Idea.RISCV64.ecb
    verified := Proof.Idea.RISCV64.ecb_verified }]

end VG.Artifacts.Idea.RISCV64
