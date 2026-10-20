module
public import VerifiedGarbage.Impl.StackScratch.X86_64

import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/-!
# Lemmas for x86-64 registration files

Forms of framework lemmas whose side conditions on literals are decided by
default, so that a registration file (`Artifacts/`, `Generic/`) binds the
proofs of its code without tactics.
-/

@[expose] public section

namespace VG.X86_64

/-- `withStackScratch_spSafe`, with `r ≠ rsp` decided. -/
theorem withStackScratch_spSafe_of {bytes : Nat} {r : Reg} {c : Prog isa}
    (h : c.all (fun i => !isa.writesSp i) = true) (hr : r ≠ .rsp := by decide) :
    (Impl.StackScratch.X86_64.withStackScratch bytes r c).all (fun i => !isa.writesSp i) = true :=
  withStackScratch_spSafe hr h

end VG.X86_64
