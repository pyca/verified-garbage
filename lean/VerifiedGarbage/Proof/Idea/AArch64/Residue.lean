module

public import VerifiedGarbage.Impl.Idea.AArch64.Fn
public meta import VerifiedGarbage.Impl.Idea.AArch64.Fn
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.Idea.AArch64.Key
public meta import VerifiedGarbage.Proof.Idea.AArch64.Key
public import VerifiedGarbage.Proof.Idea.AArch64.Invert
public meta import VerifiedGarbage.Proof.Idea.AArch64.Invert
public import VerifiedGarbage.Proof.Idea.AArch64.Ecb
public meta import VerifiedGarbage.Proof.Idea.AArch64.Ecb
public import VerifiedGarbage.Impl.Residue.AArch64
public meta import VerifiedGarbage.Impl.Residue.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Clears
meta import VerifiedGarbage.Proof.Framework.AArch64.Clears
import VerifiedGarbage.Proof.Framework.AArch64.ResidueTaint
meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueTaint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# IDEA on AArch64: returning without secret residue

The functions leave words of the key schedule and the data in registers: each is run with them cleared
before it returns (`Impl.Residue.AArch64.withClears`), which keeps it verified
(`Clears.Verified.withClears`), and which the residue analysis then proves leaves
nothing secret (`RTaint.noResidue_of_check`).
-/

@[expose] public section

namespace VG.Proof.Idea.AArch64.Residue

open VG.AArch64

/-- `expandKey`, then what it leaves cleared. -/
abbrev expandKeyCleared : Prog isa := Impl.Idea.AArch64.Fn.expandKey

theorem expandKeyCleared_verified : Verified AArch64.target expandKeyCleared (Spec.Idea.expandKeyContract AArch64.abi) :=
  Clears.Verified.withClears (Proof.Idea.AArch64.expandKey_verified) (by decide)

theorem expandKeyCleared_noResidue (k : Contract isa) : NoResidue expandKeyCleared k 0 :=
  RTaint.noResidue_of_check ⟨_, by taint_decide⟩ k

/-- `invertKey`, then what it leaves cleared. -/
abbrev invertKeyCleared : Prog isa := Impl.Idea.AArch64.Fn.invertKey

theorem invertKeyCleared_verified : Verified AArch64.target invertKeyCleared (Spec.Idea.invertKeyContract AArch64.abi) :=
  Clears.Verified.withClears (Proof.Idea.AArch64.invertKey_verified) (by decide)

theorem invertKeyCleared_noResidue (k : Contract isa) : NoResidue invertKeyCleared k 0 :=
  RTaint.noResidue_of_check ⟨_, by taint_decide⟩ k

/-- `ecb`, then what it leaves cleared. -/
abbrev ecbCleared : Prog isa := Impl.Idea.AArch64.Fn.ecb

theorem ecbCleared_verified : Verified AArch64.target ecbCleared (Spec.Idea.ecbContract AArch64.abi 0) :=
  Clears.Verified.withClears (Proof.Idea.AArch64.ecb_verified) (by decide)

theorem ecbCleared_noResidue (k : Contract isa) : NoResidue ecbCleared k 0 :=
  RTaint.noResidue_of_check ⟨_, by taint_decide⟩ k

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Idea.AArch64.Residue.expandKeyCleared_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Idea.AArch64.Fn.expandKey
      (Spec.Idea.expandKeyContract AArch64.abi) 0 :=
  ⟨Proof.Idea.AArch64.Residue.expandKeyCleared_verified,
    Proof.Idea.AArch64.Residue.expandKeyCleared_noResidue _⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Idea.AArch64.Residue.invertKeyCleared_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Idea.AArch64.Fn.invertKey
      (Spec.Idea.invertKeyContract AArch64.abi) 0 :=
  ⟨Proof.Idea.AArch64.Residue.invertKeyCleared_verified,
    Proof.Idea.AArch64.Residue.invertKeyCleared_noResidue _⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Idea.AArch64.Residue.ecbCleared_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Idea.AArch64.Fn.ecb
      (Spec.Idea.ecbContract AArch64.abi) 0 :=
  ⟨Proof.Idea.AArch64.Residue.ecbCleared_verified,
    Proof.Idea.AArch64.Residue.ecbCleared_noResidue _⟩

end VG.Proof.Idea.AArch64.Residue
