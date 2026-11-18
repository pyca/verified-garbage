module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Rc4.Contract
public import VerifiedGarbage.Proof.Rc4.RISCV64.Verified

import VerifiedGarbage.Proof.Rc4.Scratch
import VerifiedGarbage.Proof.Rc4.RISCV64.Lit

/-!
# Rc4 on RISC-V, without secret residue

Each function, followed by `Impl.Scrub.RISCV64.scrubTail`
(`RISCV64.Scrub.withScrub`), which clears the caller-saved registers and the
stack its frames used. Their postconditions read the memory on return only
within their buffers (`RISCV64.Scrub.PostOut`), as on x86-64
(`Proof/Rc4/X86_64/Scrub.lean`).
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
  withScrub { code := Impl.Rc4.RISCV64.init, verified := Proof.Rc4.RISCV64.init_verified }
    (initOut _)

/-- `Spec.Rc4.applyApi`. -/
def applyReg : Registration Spec.Rc4.applyApi RISCV64.target :=
  withScrub { code := Impl.Rc4.RISCV64.apply, verified := Proof.Rc4.RISCV64.apply_verified }
    (applyOut _)

end VG.Proof.Rc4.RISCV64.Scrub
