module

public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.Aes.X86.Variant
public import VerifiedGarbage.Impl.CmacAes.Stream.X86
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.CmacAes.Stream.X86.Frame
import VerifiedGarbage.Proof.CmacAes.Stream.Scratch
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.Aes.X86.Variant
meta import VerifiedGarbage.Impl.CmacAes.Stream.X86
meta import VerifiedGarbage.Impl.StackScratch.X86
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.CmacAes.Stream.X86.Frame
meta import VerifiedGarbage.Proof.CmacAes.Stream.Scratch

/-!
# What the cleanup of streaming AES-CMAC needs of its code (x86, 32-bit)

`vg_cmac_aes_init`, `vg_cmac_aes_absorb` and `vg_cmac_aes_finish` are
generic over the implementation of AES they call (`Ctr32Impl`,
`Proof/Variants/AesCtr32/X86.lean`). What `X86.Scrub.scrubFOf` needs of
their code over the stack of their contracts (`scrubFSide`) holds of every
implementation (`init_scrub`, `absorb_scrub`, `finish_scrub`): from their
code with a stub implementation, whose code is `.block []`, which the kernel
evaluates once here (`init_side`, …), the implementation's own facts
(`Ctr32Impl.scrub`, `expandScrub`, its stack), and `Fill`, which `fill_calls`
proves of any implementation by walking only CMAC's code. `vg_cmac_aes_update`
chains in a register with AES-NI and by calls otherwise
(`Impl.CmacAes.X86.hardware`), so `absorb` has a stub of each.

The functions as emitted (`Impl.CmacAes.Stream.X86.Fn`) return without
secret residue for each variant (`init_scrubbed`, `absorb_scrubbed`,
`finish_scrubbed`), from these as `X86.Scrub.verifiedScrubbedF`'s `hs`, with
the contract's stack as `W`: they evaluate no code. Their postconditions read the memory on return only within the
state and the tag, by the target-independent lemmas of
`Proof/CmacAes/Stream/Scratch.lean`.
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.X86.Scrub

open VG.X86 VG.X86.Scrub VG.Impl.CmacAes.Stream.X86
open Impl.StackScratch.X86 (withStackScratch)

/-- AES in counter mode with no code, by the name that chooses the
chaining by calls (`Impl.CmacAes.X86.hardware`). -/
def stubCtr : Impl.Aes.X86.Ctr32 := ⟨"", .block []⟩

/-- `stubCtr` by the name that chooses the chaining with AES-NI. -/
def stubCtrNi : Impl.Aes.X86.Ctr32 := ⟨"vg_aes_ctr32_to_aesni", .block []⟩

/-- AES's key expansion with no code. -/
def stubExpand : Impl.Aes.X86.ExpandKey := ⟨"", .block []⟩

-- CMAC's own code, with the stubs, as literals for the kernel's evaluation.
materialize_code initStub := withStackScratch 2324 3 (init stubExpand stubCtr "")
materialize_code absorbStub := withStackScratch 2336 6 (absorb stubCtr "")
materialize_code absorbStubNi := withStackScratch 2336 6 (absorb stubCtrNi "")
materialize_code finishStub := withStackScratch 2332 5 (finish stubCtr "")

theorem init_side : scrubFSide (withStackScratch 2324 3 (init stubExpand stubCtr "")) [] 2376 = true := by
  lit_decide

theorem absorb_side : scrubFSide (withStackScratch 2336 6 (absorb stubCtr "")) [] 2396 = true := by
  lit_decide

theorem absorbNi_side : scrubFSide (withStackScratch 2336 6 (absorb stubCtrNi "")) [] 2396 = true := by
  lit_decide

theorem finish_side : scrubFSide (withStackScratch 2332 5 (finish stubCtr "")) [] 2392 = true := by
  lit_decide

theorem init_fill (e : Impl.Aes.X86.ExpandKey) (c : Impl.Aes.X86.Ctr32) (sfx : String)
    (he : calleeSide e.code 0 = true) (hc : calleeSide c.code 0 = true) :
    Fill 0 (withStackScratch 2324 3 (init stubExpand stubCtr ""))
      (withStackScratch 2324 3 (init e c sfx)) := by
  fill_calls

theorem absorb_fill (c : Impl.Aes.X86.Ctr32) (sfx : String) (hc : calleeSide c.code 0 = true)
    (h : ¬Impl.CmacAes.X86.hardware c = true) :
    Fill 0 (withStackScratch 2336 6 (absorb stubCtr "")) (withStackScratch 2336 6 (absorb c sfx)) := by
  fill_calls

/-- With AES-NI, `vg_cmac_aes_update` chains in a register and calls nothing. -/
theorem absorbNi_fill (c : Impl.Aes.X86.Ctr32) (sfx : String) (h : Impl.CmacAes.X86.hardware c = true) :
    Fill 0 (withStackScratch 2336 6 (absorb stubCtrNi "")) (withStackScratch 2336 6 (absorb c sfx)) := by
  fill_calls

theorem finish_fill (c : Impl.Aes.X86.Ctr32) (sfx : String) (hc : calleeSide c.code 0 = true) :
    Fill 0 (withStackScratch 2332 5 (finish stubCtr "")) (withStackScratch 2332 5 (finish c sfx)) := by
  fill_calls

open Proof.Aes.X86 (Ctr32Impl)

/-- `scrubFSide` of `vg_cmac_aes_init`, whatever the implementation of AES. -/
theorem init_scrub (v : Ctr32Impl) :
    scrubFSide (withStackScratch 2324 3 (init v.expand v.callee v.suffix)) [] 2376 = true :=
  scrubFSide_of_fill (init_fill _ _ _ (calleeSide_of_eq v.expandStack v.expandScrub)
    (calleeSide_of_eq v.stack v.scrub)) init_side

/-- `scrubFSide` of `vg_cmac_aes_absorb`, whatever the implementation of AES. -/
theorem absorb_scrub (v : Ctr32Impl) :
    scrubFSide (withStackScratch 2336 6 (absorb v.callee v.suffix)) [] 2396 = true := by
  by_cases h : Impl.CmacAes.X86.hardware v.callee = true
  · exact scrubFSide_of_fill (absorbNi_fill _ _ h) absorbNi_side
  · exact scrubFSide_of_fill (absorb_fill _ _ (calleeSide_of_eq v.stack v.scrub) h) absorb_side

/-- `scrubFSide` of `vg_cmac_aes_finish`, whatever the implementation of AES. -/
theorem finish_scrub (v : Ctr32Impl) :
    scrubFSide (withStackScratch 2332 5 (finish v.callee v.suffix)) [] 2392 = true :=
  scrubFSide_of_fill (finish_fill _ _ (calleeSide_of_eq v.stack v.scrub)) finish_side

/-! ## Postconditions -/

theorem initOut (stack : Nat) :
    PostOut (Spec.Cmac.aesInitContract X86.abi stack) (Spec.Cmac.aesInitSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.CmacAes.Stream.initPostOut_local _)

theorem absorbOut (stack : Nat) :
    PostOut (Spec.Cmac.aesAbsorbContract X86.abi stack) (Spec.Cmac.aesAbsorbSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.CmacAes.Stream.absorbPostOut_local _)

theorem finishOut (stack : Nat) :
    PostOut (Spec.Cmac.aesFinishContract X86.abi stack) (Spec.Cmac.aesFinishSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.CmacAes.Stream.finishPostOut_local _)

/-! ## The functions as emitted -/

/-- `vg_cmac_aes_init` over `v` as emitted (`Impl.CmacAes.Stream.X86.Fn.init`)
meets its contract in constant time and returns without secret residue. -/
theorem init_scrubbed (v : Ctr32Impl) :
    VerifiedScrubbed X86.target (Impl.CmacAes.Stream.X86.Fn.init v.expand v.callee v.suffix)
      (Spec.Cmac.aesInitContract X86.abi 2376) 0 :=
  verifiedScrubbedF (api := Spec.Cmac.aesInitApi) {
      suffix := v.suffix
      code := withStackScratch 2324 3 (init v.expand v.callee v.suffix)
      verified := Proof.CmacAes.Stream.X86.init_framed v
      spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (Proof.CmacAes.Stream.X86.init_spSafe v) }
    (initOut _) (W := 2376) (hs := init_scrub v)

/-- `vg_cmac_aes_absorb` over `v` as emitted (`Impl.CmacAes.Stream.X86.Fn.absorb`)
meets its contract in constant time and returns without secret residue. -/
theorem absorb_scrubbed (v : Ctr32Impl) :
    VerifiedScrubbed X86.target (Impl.CmacAes.Stream.X86.Fn.absorb v.callee v.suffix)
      (Spec.Cmac.aesAbsorbContract X86.abi 2396) 0 :=
  verifiedScrubbedF (api := Spec.Cmac.aesAbsorbApi) {
      suffix := v.suffix
      code := withStackScratch 2336 6 (absorb v.callee v.suffix)
      verified := Proof.CmacAes.Stream.X86.absorb_framed v
      spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (Proof.CmacAes.Stream.X86.absorb_spSafe v) }
    (absorbOut _) (W := 2396) (hs := absorb_scrub v)

/-- `vg_cmac_aes_finish` over `v` as emitted (`Impl.CmacAes.Stream.X86.Fn.finish`)
meets its contract in constant time and returns without secret residue. -/
theorem finish_scrubbed (v : Ctr32Impl) :
    VerifiedScrubbed X86.target (Impl.CmacAes.Stream.X86.Fn.finish v.callee v.suffix)
      (Spec.Cmac.aesFinishContract X86.abi 2392) 0 :=
  verifiedScrubbedF (api := Spec.Cmac.aesFinishApi) {
      suffix := v.suffix
      code := withStackScratch 2332 5 (finish v.callee v.suffix)
      verified := Proof.CmacAes.Stream.X86.finish_framed v
      spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (Proof.CmacAes.Stream.X86.finish_spSafe v) }
    (finishOut _) (W := 2392) (hs := finish_scrub v)

/-- `Impl.CmacAes.Stream.X86.Fn.init` writes `esp` only in its frames and calls. -/
theorem init_fnSpSafe (v : Ctr32Impl) :
    (Impl.CmacAes.Stream.X86.Fn.init v.expand v.callee v.suffix).all (fun i => !X86.isa.writesSp i) = true :=
  scrubF_spSafe (Proof.CmacAes.Stream.X86.withStackScratch_spSafe (Proof.CmacAes.Stream.X86.init_spSafe v))

/-- `Impl.CmacAes.Stream.X86.Fn.absorb` writes `esp` only in its frames and calls. -/
theorem absorb_fnSpSafe (v : Ctr32Impl) :
    (Impl.CmacAes.Stream.X86.Fn.absorb v.callee v.suffix).all (fun i => !X86.isa.writesSp i) = true :=
  scrubF_spSafe (Proof.CmacAes.Stream.X86.withStackScratch_spSafe (Proof.CmacAes.Stream.X86.absorb_spSafe v))

/-- `Impl.CmacAes.Stream.X86.Fn.finish` writes `esp` only in its frames and calls. -/
theorem finish_fnSpSafe (v : Ctr32Impl) :
    (Impl.CmacAes.Stream.X86.Fn.finish v.callee v.suffix).all (fun i => !X86.isa.writesSp i) = true :=
  scrubF_spSafe (Proof.CmacAes.Stream.X86.withStackScratch_spSafe (Proof.CmacAes.Stream.X86.finish_spSafe v))

end VG.Proof.CmacAes.Stream.X86.Scrub
