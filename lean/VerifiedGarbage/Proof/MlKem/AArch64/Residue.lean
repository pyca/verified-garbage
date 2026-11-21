module

public import VerifiedGarbage.Proof.MlKem.AArch64.CheckEk
public meta import VerifiedGarbage.Proof.MlKem.AArch64.CheckEk
public import VerifiedGarbage.Proof.MlKem1024.AArch64.CheckEk
public meta import VerifiedGarbage.Proof.MlKem1024.AArch64.CheckEk
public import VerifiedGarbage.Impl.Scrub.AArch64
public meta import VerifiedGarbage.Impl.Scrub.AArch64
public import VerifiedGarbage.Impl.MlKem.AArch64.Fn
public meta import VerifiedGarbage.Impl.MlKem.AArch64.Fn
public import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Proof.Framework.AArch64.Clears
meta import VerifiedGarbage.Proof.Framework.AArch64.Clears
import VerifiedGarbage.Proof.Framework.AArch64.ResidueTaint
meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueTaint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# Checking ML-KEM encapsulation keys on AArch64: returning without secret residue

The functions leave coefficients of the key in registers and vector registers: each is run with them cleared
before it returns (`Impl.Scrub.AArch64.withClears`), which keeps it verified
(`Clears.Verified.withClears`), and which the residue analysis then proves leaves
nothing secret (`RTaint.noResidue_of_check`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Residue

open VG.AArch64

/-- `checkEk`, then what it leaves cleared. -/
abbrev checkEk768Cleared : Prog isa := Impl.MlKem.AArch64.Fn.checkEk

theorem checkEk768Cleared_verified : Verified AArch64.target checkEk768Cleared (Spec.MlKem.checkEkContract AArch64.abi) :=
  Clears.Verified.withClears (Proof.MlKem.AArch64.CheckEk.checkEk_verified) (by decide)

theorem checkEk768Cleared_noResidue (k : Contract isa) : NoResidue checkEk768Cleared k 32 :=
  RTaint.noResidue_of_check ⟨_, by taint_decide⟩ k

/-- `checkEk`, then what it leaves cleared. -/
abbrev checkEk1024Cleared : Prog isa := Impl.MlKem.AArch64.Fn.checkEk1024

theorem checkEk1024Cleared_verified : Verified AArch64.target checkEk1024Cleared (Spec.MlKem1024.checkEkContract AArch64.abi) :=
  Clears.Verified.withClears (Proof.MlKem1024.AArch64.CheckEk.checkEk_verified) (by decide)

theorem checkEk1024Cleared_noResidue (k : Contract isa) : NoResidue checkEk1024Cleared k 32 :=
  RTaint.noResidue_of_check ⟨_, by taint_decide⟩ k

/-- `vg_mlkem768_check_ek` as emitted (`Impl.MlKem.AArch64.Fn.checkEk`) meets
its contract in constant time and returns without secret residue. -/
theorem checkEk_scrubbed :
    VerifiedScrubbed AArch64.target Impl.MlKem.AArch64.Fn.checkEk (Spec.MlKem.checkEkContract AArch64.abi) 32 :=
  ⟨checkEk768Cleared_verified, checkEk768Cleared_noResidue _⟩

/-- `vg_mlkem1024_check_ek` as emitted (`Impl.MlKem.AArch64.Fn.checkEk1024`)
meets its contract in constant time and returns without secret residue. -/
theorem checkEk1024_scrubbed :
    VerifiedScrubbed AArch64.target Impl.MlKem.AArch64.Fn.checkEk1024 (Spec.MlKem1024.checkEkContract AArch64.abi)
      32 :=
  ⟨checkEk1024Cleared_verified, checkEk1024Cleared_noResidue _⟩

end VG.Proof.MlKem.AArch64.Residue
