module

public import VerifiedGarbage.Proof.TripleDes.AArch64.ConstantTime
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.AArch64.Lit

@[expose] public section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64

def contract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let output : Region := ⟨s.gpr .x2, 384⟩
    s.rd = [key] ∧ s.wr = [output] ∧ key.Disjoint output ∧
      Spec.TripleDes.validKey (s.gpr .x1).toNat
  post s s' := Spec.TripleDes.scheduleAt s'.mem (s.gpr .x2) =
    Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
  pub := PublicRegs [.x0, .x1, .x2]

end VG.Proof.TripleDes.AArch64.Key
