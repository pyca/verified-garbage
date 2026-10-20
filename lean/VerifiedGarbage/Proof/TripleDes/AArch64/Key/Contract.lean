module

public import VerifiedGarbage.Proof.TripleDes.AArch64.ConstantTime
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.TripleDes.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

@[expose] public section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64

def contract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let output : Region := ⟨s.gpr .x2, 384⟩
    let scratch : Region := ⟨s.gpr .x3, 512⟩
    s.rd = [key] ∧ s.wr = [output, scratch] ∧ key.Disjoint output ∧ key.Disjoint scratch ∧
      output.Disjoint scratch ∧
      Spec.TripleDes.validKey (s.gpr .x1).toNat
  post s s' := Spec.TripleDes.scheduleAt s'.mem (s.gpr .x2) =
    Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
  pub := PublicRegs [.x0, .x1, .x2, .x3]

end VG.Proof.TripleDes.AArch64.Key
