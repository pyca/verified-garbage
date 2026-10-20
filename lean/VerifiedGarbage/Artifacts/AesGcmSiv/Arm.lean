module

public import VerifiedGarbage.Proof.AesGcmSiv.Arm.Verified
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-GCM-SIV (RFC 8452) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation.

Both functions run in a frame of 3792 bytes holding their working space
(`Proof/AesGcmSiv/Arm/Verified.lean`). In it they call `vg_aes_ctr32` and
`vg_ghash` in frames that push their two stack arguments
(`vg_aes_expand_key` takes no stack arguments): 3800 bytes of stack in all.
-/

@[expose] public section

namespace VG.Artifacts.AesGcmSiv.Arm

open VG.Proof.AesGcmSiv.Arm

/-- Which functions the implementation calls. -/
def note : String := "This implementation encrypts with `vg_aes_ctr32` (and expands keys with \
  `vg_aes_expand_key`) and computes POLYVAL with `vg_ghash`."

def artifacts : List Artifact := [
  Spec.GcmSiv.sealApi.artifact Arm.target {
    notes := [note]
    code := Impl.StackScratch.Arm.withStackScratch 3792 4 Impl.AesGcmSiv.Arm.«seal»
    stack := 3800
    verified := seal_framed },
  Spec.GcmSiv.openApi.artifact Arm.target {
    notes := [note,
      "It compares the tags and overwrites the data with zeros without a branch on the result."]
    code := Impl.StackScratch.Arm.withStackScratch 3792 4 Impl.AesGcmSiv.Arm.«open»
    stack := 3800
    verified := open_framed }]

end VG.Artifacts.AesGcmSiv.Arm
