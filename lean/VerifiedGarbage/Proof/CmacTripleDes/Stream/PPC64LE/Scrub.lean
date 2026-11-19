module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Frame
import VerifiedGarbage.Proof.CmacTripleDes.StreamScratch

/-!
# Streaming TDEA-CMAC on PPC64LE, without secret residue

`vg_cmac_triple_des_stream_init`, `vg_cmac_triple_des_absorb` and
`vg_cmac_triple_des_finish`, each followed by `Impl.Scrub.PPC64LE.scrubTail`
(`PPC64LE.Scrub.withScrub`), which clears the volatile registers they may
write and the stack their frames used: they keep their working space, the key
schedule among it, in a frame they do not wipe themselves
(`withStackScratch`). Their postconditions read the memory on return only
within the 416-byte state and the tag, by the target-independent lemmas of
`Proof/CmacTripleDes/StreamScratch.lean`.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub

/-! ## Postconditions -/

theorem initOut (stack : Nat) :
    PostOut (Spec.Cmac.tdesStreamInitContract PPC64LE.abi stack) (Spec.Cmac.tdesStreamInitSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.CmacTripleDes.Stream.streamInitPostOut_local _)

theorem absorbOut (stack : Nat) :
    PostOut (Spec.Cmac.tdesAbsorbContract PPC64LE.abi stack) (Spec.Cmac.tdesAbsorbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.CmacTripleDes.Stream.absorbPostOut_local _)

theorem finishOut (stack : Nat) :
    PostOut (Spec.Cmac.tdesFinishContract PPC64LE.abi stack) (Spec.Cmac.tdesFinishSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.CmacTripleDes.Stream.finishPostOut_local _)

/-! ## The registrations -/

/-- `Spec.Cmac.tdesStreamInitApi`. -/
def initReg : Registration Spec.Cmac.tdesStreamInitApi PPC64LE.target :=
  withScrub {
      code := Impl.StackScratch.PPC64LE.withStackScratch 672 .r6 Impl.CmacTripleDes.Stream.PPC64LE.streamInit
      verified := Proof.CmacTripleDes.Stream.PPC64LE.init_framed }
    (initOut _)

/-- `Spec.Cmac.tdesAbsorbApi`. -/
def absorbReg : Registration Spec.Cmac.tdesAbsorbApi PPC64LE.target :=
  withScrub {
      code := Impl.StackScratch.PPC64LE.withStackScratch 720 .r7 Impl.CmacTripleDes.Stream.PPC64LE.absorb
      verified := Proof.CmacTripleDes.Stream.PPC64LE.absorb_framed }
    (absorbOut _)

/-- `Spec.Cmac.tdesFinishApi`. -/
def finishReg : Registration Spec.Cmac.tdesFinishApi PPC64LE.target :=
  withScrub {
      code := Impl.StackScratch.PPC64LE.withStackScratch 672 .r6 Impl.CmacTripleDes.Stream.PPC64LE.finish
      verified := Proof.CmacTripleDes.Stream.PPC64LE.finish_framed }
    (finishOut _)

/-- All are scrubbed: the side conditions of `withScrub` hold. -/
example : initReg.residue.isSome ∧ absorbReg.residue.isSome ∧ finishReg.residue.isSome := by
  decide

end VG.Proof.CmacTripleDes.Stream.PPC64LE.Scrub
