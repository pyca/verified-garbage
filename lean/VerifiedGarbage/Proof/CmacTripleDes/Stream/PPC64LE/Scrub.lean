module

public import VerifiedGarbage.Impl.CmacTripleDes.Stream.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Frame
import VerifiedGarbage.Proof.CmacTripleDes.StreamScratch
import VerifiedGarbage.Proof.Framework.Lit

/-!
# Streaming TDEA-CMAC on PPC64LE, without secret residue

`vg_cmac_triple_des_stream_init`, `vg_cmac_triple_des_absorb` and
`vg_cmac_triple_des_finish`, each followed by `Impl.Scrub.PPC64LE.scrubTail`
(`PPC64LE.Scrub.verifiedScrubbedAll`), which clears the volatile registers they may
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

/-! ## The functions as emitted -/

/-- `vg_cmac_triple_des_stream_init` as emitted
(`Impl.CmacTripleDes.Stream.PPC64LE.Fn.init`) meets its contract in constant
time and returns without secret residue. -/
theorem init_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.CmacTripleDes.Stream.PPC64LE.Fn.init
      (Spec.Cmac.tdesStreamInitContract PPC64LE.abi 672) 0 :=
  verifiedScrubbedAll (api := Spec.Cmac.tdesStreamInitApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 672 .r6 Impl.CmacTripleDes.Stream.PPC64LE.streamInit
      verified := Proof.CmacTripleDes.Stream.PPC64LE.init_framed }
    672 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (initOut _)
    (by dsimp only; lit_decide)

/-- `vg_cmac_triple_des_absorb` as emitted
(`Impl.CmacTripleDes.Stream.PPC64LE.Fn.absorb`) meets its contract in constant
time and returns without secret residue. -/
theorem absorb_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.CmacTripleDes.Stream.PPC64LE.Fn.absorb
      (Spec.Cmac.tdesAbsorbContract PPC64LE.abi 720) 0 :=
  verifiedScrubbedAll (api := Spec.Cmac.tdesAbsorbApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 720 .r7 Impl.CmacTripleDes.Stream.PPC64LE.absorb
      verified := Proof.CmacTripleDes.Stream.PPC64LE.absorb_framed }
    720 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (absorbOut _)
    (by dsimp only; lit_decide)

/-- `vg_cmac_triple_des_finish` as emitted
(`Impl.CmacTripleDes.Stream.PPC64LE.Fn.finish`) meets its contract in constant
time and returns without secret residue. -/
theorem finish_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.CmacTripleDes.Stream.PPC64LE.Fn.finish
      (Spec.Cmac.tdesFinishContract PPC64LE.abi 672) 0 :=
  verifiedScrubbedAll (api := Spec.Cmac.tdesFinishApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 672 .r6 Impl.CmacTripleDes.Stream.PPC64LE.finish
      verified := Proof.CmacTripleDes.Stream.PPC64LE.finish_framed }
    672 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (finishOut _)
    (by dsimp only; lit_decide)

end VG.Proof.CmacTripleDes.Stream.PPC64LE.Scrub
