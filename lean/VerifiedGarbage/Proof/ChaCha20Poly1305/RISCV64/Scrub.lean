module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.ChaCha20Poly1305.RISCV64.Fn
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
`vg_chacha20_poly1305_open_to` and `vg_chacha20_poly1305_seal_gather` as
emitted (`Impl.ChaCha20Poly1305.RISCV64.Fn`), each followed by
`Impl.Scrub.RISCV64.scrubTailSel`, which clears the caller-saved registers
and, of the stack its frames used, only the runs of doublewords that the
residue analysis (`RISCV64.rtaint`) finds may differ between two runs. Their
code wipes its working space, which leaves none, or two (`open_to`'s and
`seal_gather`'s). Each theorem below states that one meets its contract in
constant time and returns without secret residue (`VerifiedScrubbed`, by
`RISCV64.Scrub.verifiedScrubbedSel`, whose analysis the kernel evaluates
here), which is what its registration binds. Their postconditions read the
memory on return only within the data and the tag (`RISCV64.Scrub.PostOut`),
as on x86-64 (`Proof/ChaCha20Poly1305/X86_64/ScrubFn.lean`). They call
ChaCha20's and Poly1305's code, and `vg_chacha20_poly1305_seal_gather` that
of `vg_chacha20_poly1305_seal`, as internal functions of their own
(`vg_poly1305_init_core`, …), since the exported ones now clear their stack.
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

/-! ## The functions as emitted -/

/-- `vg_chacha20_poly1305_seal` as emitted (`Impl.ChaCha20Poly1305.RISCV64.Fn.«seal»`) meets its
contract in constant time and returns without secret residue: the theorem its registration binds. -/
theorem seal_scrubbed :
    VerifiedScrubbed target Impl.ChaCha20Poly1305.RISCV64.Fn.«seal»
      (Spec.ChaCha20Poly1305.sealContract RISCV64.abi 624) 0 :=
  verifiedScrubbedSel (api := Spec.ChaCha20Poly1305.sealApi) (W := 624)
    { code := Impl.StackScratch.RISCV64.withStackScratchWiped 624 .a7 78
        (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«seal»)
      verified := Proof.ChaCha20Poly1305.RISCV64.seal_framed }
    [] [] (sealOut _) (by lit_decide) (hbp_nil _) ⟨_, by taint_decide_ct⟩

/-- `vg_chacha20_poly1305_open` as emitted (`Impl.ChaCha20Poly1305.RISCV64.Fn.«open»`) meets its
contract in constant time and returns without secret residue: the theorem its registration binds. -/
theorem open_scrubbed :
    VerifiedScrubbed target Impl.ChaCha20Poly1305.RISCV64.Fn.«open»
      (Spec.ChaCha20Poly1305.openZeroContract RISCV64.abi 624) 32 :=
  verifiedScrubbedSel (api := Spec.ChaCha20Poly1305.openZeroApi) (W := 624)
    { code := Impl.StackScratch.RISCV64.withStackScratchWiped 624 .a7 78
        (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«open»)
      verified := Proof.ChaCha20Poly1305.RISCV64.open_framed }
    [] [] (openOut _) (by lit_decide) (hbp_nil _) ⟨_, by taint_decide_ct⟩

/-- `vg_chacha20_poly1305_open_to` as emitted (`Impl.ChaCha20Poly1305.RISCV64.Fn.openTo`) meets its
contract in constant time and returns without secret residue: the theorem its registration binds. -/
theorem openTo_scrubbed :
    VerifiedScrubbed target Impl.ChaCha20Poly1305.RISCV64.Fn.openTo
      (Spec.ChaCha20Poly1305.openToContract RISCV64.abi 640) 32 :=
  verifiedScrubbedSel (api := Spec.ChaCha20Poly1305.openToApi) (W := 640)
    { code := Impl.StackScratch.RISCV64.withStackScratchArgsWiped 640 1 78 Impl.ChaCha20Poly1305.RISCV64.openTo
      verified := Proof.ChaCha20Poly1305.RISCV64.openTo_framed }
    [(640, [(0, 2)])] [] (openToOut _) (by lit_decide) (hbp_nil _) ⟨_, by taint_decide_ct⟩

/-- `vg_chacha20_poly1305_seal_gather` as emitted (`Impl.ChaCha20Poly1305.RISCV64.Fn.sealGather`)
meets its contract in constant time and returns without secret residue: the theorem its registration
binds. -/
theorem sealGather_scrubbed :
    VerifiedScrubbed target Impl.ChaCha20Poly1305.RISCV64.Fn.sealGather
      (Spec.ChaCha20Poly1305.sealGatherContract RISCV64.abi 640) 0 :=
  verifiedScrubbedSel (api := Spec.ChaCha20Poly1305.sealGatherApi) (W := 640)
    { code := Impl.ChaCha20Poly1305.RISCV64.SealGather.sealGather
      verified := Proof.ChaCha20Poly1305.RISCV64.Gather.sealGather_verified }
    [(640, [(78, 2)])] [] (gatherOut _) (by lit_decide) (hbp_nil _) ⟨_, by taint_decide_ct⟩

end VG.Proof.ChaCha20Poly1305.RISCV64.Scrub
