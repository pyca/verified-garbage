module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Rc2.Contract
public import VerifiedGarbage.Proof.Rc2.RISCV64.Block
public import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Chained
public import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Verified
public import VerifiedGarbage.Proof.Rc2.RISCV64.KeyVerified
public import VerifiedGarbage.Proof.Rc2.RISCV64.Stream.Frame

import VerifiedGarbage.Proof.Rc2.Scratch
import VerifiedGarbage.Proof.Rc2.CbcScratch
import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Lit
import VerifiedGarbage.Proof.Rc2.RISCV64.Lit
import VerifiedGarbage.Proof.Rc2.RISCV64.Stream.Lit

meta import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Rc2.Contract
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Block
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Chained
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Verified
meta import VerifiedGarbage.Proof.Rc2.RISCV64.KeyVerified
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Stream.Frame
meta import VerifiedGarbage.Proof.Rc2.Scratch
meta import VerifiedGarbage.Proof.Rc2.CbcScratch
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Lit
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Lit
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Stream.Lit
/-!
# Rc2 on RISC-V, without secret residue

Each function, followed by `Impl.Scrub.RISCV64.scrubTail`
(`RISCV64.Scrub.withScrub`), which clears the caller-saved registers and the
stack its frames used. Their postconditions read the memory on return only
within their buffers (`RISCV64.Scrub.PostOut`), as on x86-64
(`Proof/Rc2/X86_64/Scrub.lean`).

Every function instead clears only the runs of doublewords that the residue
analysis (`RISCV64.rtaint`) finds may differ between two runs
(`RISCV64.Scrub.withScrubSel`, `scrubSel_noResidue`). Their code wipes most of
its own scratch space, which leaves few such doublewords, or none.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Scrub

open VG.Spec.Rc2 VG.RISCV64 VG.RISCV64.Scrub

/-! ## Postconditions -/

theorem cbcInitOut (stack : Nat) : PostOut (Spec.Rc2.cbcInitContract RISCV64.abi stack) (Spec.Rc2.cbcInitSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Rc2.cbcInitPostOut_local _)

theorem cbcEncryptChainedOut (stack : Nat) : PostOut (Spec.Rc2.cbcEncryptChainedContract RISCV64.abi stack) (Spec.Rc2.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Rc2.cbcEncChainedPostOut_local (pb := 64))

theorem cbcDecryptChainedOut (stack : Nat) : PostOut (Spec.Rc2.cbcDecryptChainedContract RISCV64.abi stack) (Spec.Rc2.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Rc2.cbcDecChainedPostOut_local (pb := 64))

/-! ## The registrations -/

/-- `Spec.Rc2.cbcInitApi`. -/
def cbcInitReg : Registration Spec.Rc2.cbcInitApi RISCV64.target :=
  withScrubSel { code := Impl.StackScratch.RISCV64.withStackScratchWiped 608 .a6 72 Impl.Rc2.RISCV64.Stream.init, verified := Proof.Rc2.RISCV64.Stream.init_framed } [(608, [(72, 4)])]
    (cbcInitOut _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (cbcInitOut _) (hbp_nil _)
      (Impl.StackScratch.RISCV64.withStackScratchWiped 608 .a6 72 Impl.Rc2.RISCV64.Stream.init) 608 32
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `Spec.Rc2.cbcEncryptChainedApi`. -/
def cbcEncryptChainedReg : Registration Spec.Rc2.cbcEncryptChainedApi RISCV64.target :=
  withScrubSel { code := Impl.StackScratch.RISCV64.withStackScratchWiped 512 .a4 64 Impl.Rc2.RISCV64.Cbc.encrypt, verified := Proof.Rc2.RISCV64.Cbc.encryptChained_framed } []
    (cbcEncryptChainedOut _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (cbcEncryptChainedOut _) (hbp_nil _)
      (Impl.StackScratch.RISCV64.withStackScratchWiped 512 .a4 64 Impl.Rc2.RISCV64.Cbc.encrypt) 512 0
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `Spec.Rc2.cbcDecryptChainedApi`. -/
def cbcDecryptChainedReg : Registration Spec.Rc2.cbcDecryptChainedApi RISCV64.target :=
  withScrubSel { code := Impl.StackScratch.RISCV64.withStackScratchWiped 512 .a4 64 Impl.Rc2.RISCV64.Cbc.decrypt, verified := Proof.Rc2.RISCV64.Cbc.decryptChained_framed } []
    (cbcDecryptChainedOut _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (cbcDecryptChainedOut _) (hbp_nil _)
      (Impl.StackScratch.RISCV64.withStackScratchWiped 512 .a4 64 Impl.Rc2.RISCV64.Cbc.decrypt) 512 0
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

end VG.Proof.Rc2.RISCV64.Scrub
