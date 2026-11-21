module

public import VerifiedGarbage.Impl.Rc4.AArch64.Fn
public meta import VerifiedGarbage.Impl.Rc4.AArch64.Fn
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.Rc4.AArch64.VerifiedApply
public meta import VerifiedGarbage.Proof.Rc4.AArch64.VerifiedApply
public import VerifiedGarbage.Impl.Scrub.AArch64
public meta import VerifiedGarbage.Impl.Scrub.AArch64
public import VerifiedGarbage.TCB.AArch64.Residue
public meta import VerifiedGarbage.TCB.AArch64.Residue
import VerifiedGarbage.Proof.Framework.AArch64.Clears
meta import VerifiedGarbage.Proof.Framework.AArch64.Clears
import VerifiedGarbage.Proof.Framework.AArch64.ResidueCT
meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueCT
import VerifiedGarbage.Proof.Rc4.AArch64.Lit
meta import VerifiedGarbage.Proof.Rc4.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

-- separate module: only the registration needs it, and it imports the proof of `apply`, which the residue analysis would otherwise be built with

/-!
# RC4 on AArch64: `apply` returns without secret residue

`applyCleared` is `apply`, then what it leaves secret cleared: the
registers that held the state, the keystream and the data, and the high
halves of the vector registers whose low halves it restores, which the
calling convention does not preserve, from `x4`, zeroed first. The residue
analysis for two runs that leak the same (`RTaintCT.noResidue_of_verified`)
proves it leaves nothing secret: the table it reads through `adrSym`, at an
address the two runs need not share, it reads at the same address in both.
-/

@[expose] public section

namespace VG.Proof.Rc4.AArch64

open VG VG.AArch64

abbrev applyCleared : Prog isa := Impl.Rc4.AArch64.Fn.apply

theorem applyCleared_verified :
    Verified AArch64.target applyCleared (Spec.Rc4.applyContract AArch64.abi) :=
  Clears.Verified.withClears apply_verified (by decide)

theorem applyCleared_noResidue :
    NoResidue applyCleared (Spec.Rc4.applyContract AArch64.abi) 0 :=
  RTaintCT.noResidue_of_verified applyCleared_verified ⟨_, by taint_decide_ct⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Rc4.AArch64.applyCleared_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Rc4.AArch64.Fn.apply
      (Spec.Rc4.applyContract AArch64.abi) 0 :=
  ⟨Proof.Rc4.AArch64.applyCleared_verified,
    Proof.Rc4.AArch64.applyCleared_noResidue⟩

end VG.Proof.Rc4.AArch64
