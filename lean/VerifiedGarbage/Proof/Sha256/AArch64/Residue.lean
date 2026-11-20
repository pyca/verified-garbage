module

public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.Sha256.AArch64.Shared
public import VerifiedGarbage.Impl.Sha256.AArch64.Stream
public meta import VerifiedGarbage.Impl.Sha256.AArch64.Stream
public import VerifiedGarbage.TCB.AArch64.Residue
public meta import VerifiedGarbage.TCB.AArch64.Residue
import VerifiedGarbage.Proof.Framework.AArch64.ResidueTaint
meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueTaint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

-- separate module: only the registration needs it, and the residue analysis it imports would otherwise be rebuilt with the streaming proofs that HMAC and PBKDF2 import

/-!
# Streaming SHA-256 on AArch64: `init` returns without secret residue

`init` and `init224` load the initial hash value from its table, which no
run makes secret, through `x9`, which holds the table's address, and clear
`x9` before they return (`Impl.Sha256.AArch64.Stream.init`): the residue
analysis then proves they leave nothing secret (`RTaint.noResidue_of_check`).
-/

@[expose] public section

namespace VG.Proof.Sha256.AArch64.Residue

open VG.AArch64

theorem init_noResidue (k : Contract isa) : NoResidue Impl.Sha256.AArch64.Stream.init k 0 :=
  RTaint.noResidue_of_check ⟨_, by taint_decide⟩ k

theorem init224_noResidue (k : Contract isa) : NoResidue Impl.Sha256.AArch64.Stream.init224 k 0 :=
  RTaint.noResidue_of_check ⟨_, by taint_decide⟩ k

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Sha256.AArch64.Residue.init224_scrubbed :
    VerifiedScrubbed _root_.VG.AArch64.target Impl.Sha256.AArch64.Stream.init224
      (Spec.Sha256.init224Contract AArch64.abi) 0 :=
  ⟨Proof.Sha256.AArch64.Shared.init224,
    Proof.Sha256.AArch64.Residue.init224_noResidue _⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Sha256.AArch64.Residue.init_scrubbed :
    VerifiedScrubbed _root_.VG.AArch64.target Impl.Sha256.AArch64.Stream.init
      (Spec.Sha256.initContract AArch64.abi) 0 :=
  ⟨Proof.Sha256.AArch64.Shared.init,
    Proof.Sha256.AArch64.Residue.init_noResidue _⟩

end VG.Proof.Sha256.AArch64.Residue
