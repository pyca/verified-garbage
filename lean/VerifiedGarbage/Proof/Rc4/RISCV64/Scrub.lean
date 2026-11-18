module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Rc4.Contract
public import VerifiedGarbage.Proof.Rc4.RISCV64.Verified

import VerifiedGarbage.Proof.Rc4.Scratch
import VerifiedGarbage.Proof.Rc4.RISCV64.Lit

meta import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Rc4.Contract
meta import VerifiedGarbage.Proof.Rc4.RISCV64.Verified
meta import VerifiedGarbage.Proof.Rc4.Scratch
meta import VerifiedGarbage.Proof.Rc4.RISCV64.Lit
/-!
# Rc4 on RISC-V, without secret residue

Each function, followed by `Impl.Scrub.RISCV64.scrubTail`
(`RISCV64.Scrub.withScrub`), which clears the caller-saved registers and the
stack its frames used. Their postconditions read the memory on return only
within their buffers (`RISCV64.Scrub.PostOut`), as on x86-64
(`Proof/Rc4/X86_64/Scrub.lean`).

Every function instead clears only the runs of doublewords that the residue
analysis (`RISCV64.rtaint`) finds may differ between two runs
(`RISCV64.Scrub.withScrubSel`, `scrubSel_noResidue`). Their code wipes most of
its own scratch space, which leaves few such doublewords, or none.
-/

@[expose] public section

namespace VG.Proof.Rc4.RISCV64.Scrub

open VG.Spec.Rc4 VG.RISCV64 VG.RISCV64.Scrub

/-! ## Postconditions -/

theorem initOut (stack : Nat) : PostOut (Spec.Rc4.initContract RISCV64.abi stack) (Spec.Rc4.initSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Rc4.initPostOut_local _)

theorem applyOut (stack : Nat) : PostOut (Spec.Rc4.applyContract RISCV64.abi stack) (Spec.Rc4.applySig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain (Proof.Rc4.applyPostOut_local _)

/-! ## The registrations -/

/-- `Spec.Rc4.initApi`. -/
def initReg : Registration Spec.Rc4.initApi RISCV64.target :=
  withScrubSel { code := Impl.Rc4.RISCV64.init, verified := Proof.Rc4.RISCV64.init_verified } []
    (initOut _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (initOut _) (hbp_nil _)
      (Impl.Rc4.RISCV64.init) 256 32
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `Spec.Rc4.applyApi`. -/
def applyReg : Registration Spec.Rc4.applyApi RISCV64.target :=
  withScrubSel { code := Impl.Rc4.RISCV64.apply, verified := Proof.Rc4.RISCV64.apply_verified } []
    (applyOut _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (applyOut _) (hbp_nil _)
      (Impl.Rc4.RISCV64.apply) 256 0
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

end VG.Proof.Rc4.RISCV64.Scrub
