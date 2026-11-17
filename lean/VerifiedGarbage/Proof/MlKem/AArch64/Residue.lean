module

public import VerifiedGarbage.Proof.MlKem.AArch64.CheckEk
public meta import VerifiedGarbage.Proof.MlKem.AArch64.CheckEk
public import VerifiedGarbage.Proof.MlKem1024.AArch64.CheckEk
public meta import VerifiedGarbage.Proof.MlKem1024.AArch64.CheckEk
public import VerifiedGarbage.Impl.Residue.AArch64
public meta import VerifiedGarbage.Impl.Residue.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Clears
meta import VerifiedGarbage.Proof.Framework.AArch64.Clears
import VerifiedGarbage.Proof.Framework.AArch64.ResidueTaint
meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueTaint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# Checking ML-KEM encapsulation keys on AArch64: returning without secret residue

The functions leave coefficients of the key in registers and vector registers: each is run with them cleared
before it returns (`Impl.Residue.AArch64.withClears`), which keeps it verified
(`Clears.Verified.withClears`), and which the residue analysis then proves leaves
nothing secret (`RTaint.noResidue_of_check`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Residue

open VG.AArch64

/-- `checkEk`, then what it leaves cleared. -/
abbrev checkEk768Cleared : Prog isa :=
  Impl.Residue.AArch64.withClears [.x9, .x10]
    [.v0, .v1, .v2, .v3, .v16, .v19, .v20] none Impl.MlKem.AArch64.checkEk

theorem checkEk768Cleared_verified : Verified AArch64.target checkEk768Cleared (Spec.MlKem.checkEkContract AArch64.abi) :=
  Clears.Verified.withClears (Proof.MlKem.AArch64.CheckEk.checkEk_verified) (by decide)

theorem checkEk768Cleared_noResidue (k : Contract isa) : NoResidue checkEk768Cleared k 32 :=
  RTaint.noResidue_of_check ⟨_, by taint_decide⟩ k

/-- `checkEk`, then what it leaves cleared. -/
abbrev checkEk1024Cleared : Prog isa :=
  Impl.Residue.AArch64.withClears [.x9, .x10]
    [.v0, .v1, .v2, .v3, .v16, .v19, .v20] none Impl.MlKem1024.AArch64.checkEk

theorem checkEk1024Cleared_verified : Verified AArch64.target checkEk1024Cleared (Spec.MlKem1024.checkEkContract AArch64.abi) :=
  Clears.Verified.withClears (Proof.MlKem1024.AArch64.CheckEk.checkEk_verified) (by decide)

theorem checkEk1024Cleared_noResidue (k : Contract isa) : NoResidue checkEk1024Cleared k 32 :=
  RTaint.noResidue_of_check ⟨_, by taint_decide⟩ k

end VG.Proof.MlKem.AArch64.Residue
