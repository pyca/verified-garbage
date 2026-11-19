module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Verified
public import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Gather.Verified
import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
import VerifiedGarbage.Proof.ChaCha20Poly1305.OpenToScratch
import VerifiedGarbage.Proof.ChaCha20Poly1305.GatherOut

meta import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Verified
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Gather.Verified
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.OpenToScratch
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.GatherOut
/-!
# ChaCha20-Poly1305 on RISC-V, without secret residue

`vg_chacha20_poly1305_seal`, `vg_chacha20_poly1305_open`,
`vg_chacha20_poly1305_open_to` and `vg_chacha20_poly1305_seal_gather`, each
followed by `Impl.Scrub.RISCV64.scrubTail` (`RISCV64.Scrub.scrubOf`),
which clears the caller-saved registers and the stack its frames used.
Their postconditions read the memory on return only within the data and the
tag (`RISCV64.Scrub.PostOut`), as on x86-64
(`Proof/ChaCha20Poly1305/X86_64/Scrub.lean`). They call ChaCha20's and
Poly1305's code, and `vg_chacha20_poly1305_seal_gather` that of
`vg_chacha20_poly1305_seal`, as internal functions of their own
(`vg_poly1305_init_core`, …), since the exported ones now clear their stack.

`seal`, `open`, `open_to` and `seal_gather` instead clear only the runs of
doublewords that the residue analysis (`RISCV64.rtaint`) finds may differ
between two runs (`RISCV64.Scrub.scrubSelOf`, `scrubSel_noResidue`). Their
code wipes its working space, which leaves none, or two (`open_to`'s and
`seal_gather`'s).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub VG.Proof.ChaCha20Poly1305

/-! ## Postconditions -/

theorem sealOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.sealContract abi stack) (Spec.ChaCha20Poly1305.sealSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain (sealPost_out _)

theorem openOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.openZeroContract abi stack) (Spec.ChaCha20Poly1305.openSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain (openZeroPost_out _)

theorem openToOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.openToContract abi stack) (Spec.ChaCha20Poly1305.openToSig.retBits 64) :=
  postOut_of_local_pre ScrubAbi.plain (openToPost_out _)

theorem gatherOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.sealGatherContract abi stack)
      (Spec.ChaCha20Poly1305.sealGatherSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain (Proof.ChaCha20Poly1305.sealGatherPost_out _)

/-! ## The registrations -/

/-- `Spec.ChaCha20Poly1305.sealApi`. -/
def sealReg : Registration Spec.ChaCha20Poly1305.sealApi RISCV64.target :=
  scrubSelOf {
      code := Impl.StackScratch.RISCV64.withStackScratchWiped 624 .a7 78 (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«seal»)
      verified := Proof.ChaCha20Poly1305.RISCV64.seal_framed } []
    (sealOut _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (sealOut _) (hbp_nil _)
      (Impl.StackScratch.RISCV64.withStackScratchWiped 624 .a7 78 (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«seal»)) 624 0
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `Spec.ChaCha20Poly1305.openZeroApi`. -/
def openReg : Registration Spec.ChaCha20Poly1305.openZeroApi RISCV64.target :=
  scrubSelOf {
      code := Impl.StackScratch.RISCV64.withStackScratchWiped 624 .a7 78 (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«open»)
      verified := Proof.ChaCha20Poly1305.RISCV64.open_framed } []
    (openOut _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (openOut _) (hbp_nil _)
      (Impl.StackScratch.RISCV64.withStackScratchWiped 624 .a7 78 (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«open»)) 624 32
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `Spec.ChaCha20Poly1305.openToApi`. -/
def openToReg : Registration Spec.ChaCha20Poly1305.openToApi RISCV64.target :=
  scrubSelOf {
      code := Impl.StackScratch.RISCV64.withStackScratchArgsWiped 640 1 78 Impl.ChaCha20Poly1305.RISCV64.openTo
      verified := Proof.ChaCha20Poly1305.RISCV64.openTo_framed } [(640, [(0, 2)])]
    (openToOut _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (openToOut _) (hbp_nil _)
      (Impl.StackScratch.RISCV64.withStackScratchArgsWiped 640 1 78 Impl.ChaCha20Poly1305.RISCV64.openTo) 640 32
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `Spec.ChaCha20Poly1305.sealGatherApi`. -/
def sealGatherReg : Registration Spec.ChaCha20Poly1305.sealGatherApi RISCV64.target :=
  scrubSelOf {
      code := Impl.ChaCha20Poly1305.RISCV64.SealGather.sealGather
      verified := Proof.ChaCha20Poly1305.RISCV64.Gather.sealGather_verified } [(640, [(78, 2)])]
    (gatherOut _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (gatherOut _) (hbp_nil _)
      (Impl.ChaCha20Poly1305.RISCV64.SealGather.sealGather) 640 0
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

end VG.Proof.ChaCha20Poly1305.RISCV64.Scrub
