module

public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Frame
import VerifiedGarbage.Proof.CmacTripleDes.StreamScratch
import VerifiedGarbage.Proof.CmacTripleDes.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Frame
meta import VerifiedGarbage.Proof.CmacTripleDes.StreamScratch
meta import VerifiedGarbage.Proof.CmacTripleDes.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Streaming TDEA-CMAC on x86 (32-bit), without secret residue

`vg_cmac_triple_des_stream_init`, `vg_cmac_triple_des_absorb` and
`vg_cmac_triple_des_finish`, each followed by the zeroing of the stack below
`esp` that its contract reserves and by `Impl.Scrub.X86.tail`
(`X86.Scrub.scrubFOf`), which clears the registers a callee may change: they
keep their working space, the key schedule among it, in a frame they do not
wipe themselves (`withStackScratch`). Their postconditions read the memory on
return only within the 416-byte state and the tag, by the target-independent
lemmas of `Proof/CmacTripleDes/StreamScratch.lean`. What the scrub needs of
the code (its stack use within the contract's, no indirect call, no MMX
instruction) is one Boolean, `X86.Scrub.scrubFSide`, which `scrubFOf` proves
by evaluating the code once (`lit_decide`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86.Scrub

open VG.X86 VG.X86.Scrub

-- The streaming code as literals, for `scrubFSide`'s evaluation.
materialize_code Impl.CmacTripleDes.Stream.X86.streamInit
materialize_code Impl.CmacTripleDes.Stream.X86.absorb
materialize_code Impl.CmacTripleDes.Stream.X86.finish

/-! ## Postconditions -/

theorem initOut (stack : Nat) :
    PostOut (Spec.Cmac.tdesStreamInitContract X86.abi stack) (Spec.Cmac.tdesStreamInitSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.CmacTripleDes.Stream.streamInitPostOut_local _)

theorem absorbOut (stack : Nat) :
    PostOut (Spec.Cmac.tdesAbsorbContract X86.abi stack) (Spec.Cmac.tdesAbsorbSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.CmacTripleDes.Stream.absorbPostOut_local _)

theorem finishOut (stack : Nat) :
    PostOut (Spec.Cmac.tdesFinishContract X86.abi stack) (Spec.Cmac.tdesFinishSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.CmacTripleDes.Stream.finishPostOut_local _)

/-! ## The registrations -/

/-- `Spec.Cmac.tdesStreamInitApi`. -/
def initReg : Registration Spec.Cmac.tdesStreamInitApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratch 660 3 Impl.CmacTripleDes.Stream.X86.streamInit
      verified := Proof.CmacTripleDes.Stream.X86.init_framed }
    (initOut _)

/-- `Spec.Cmac.tdesAbsorbApi`. -/
def absorbReg : Registration Spec.Cmac.tdesAbsorbApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratch 716 5 Impl.CmacTripleDes.Stream.X86.absorb
      verified := Proof.CmacTripleDes.Stream.X86.absorb_framed }
    (absorbOut _)

/-- `Spec.Cmac.tdesFinishApi`. -/
def finishReg : Registration Spec.Cmac.tdesFinishApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratch 712 4 Impl.CmacTripleDes.Stream.X86.finish
      verified := Proof.CmacTripleDes.Stream.X86.finish_framed }
    (finishOut _)

end VG.Proof.CmacTripleDes.Stream.X86.Scrub
