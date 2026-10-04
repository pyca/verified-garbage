import VerifiedGarbage.Proof.AesGcmSiv.AArch64.FnCT
import VerifiedGarbage.Proof.GcmSiv.Polyval
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.GcmSiv.Contract

/-!
# AES-GCM-SIV on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementations `v` of `vg_aes_ctr32`, `vg_aes_expand_key` and
`vg_ghash`), with the tag input computed with GHASH equal to the RFC's
(`tagInput_eq`, from `Proof.GcmSiv.Polyval`, imported here only so that the
other proofs need not import its algebra), a state satisfying each
precondition, and the shared contracts of `Spec/GcmSiv/Contract.lean` (with
no stack: the calls keep the return address in `x30`, which each function
saves in the working space).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.Impl.AesGcmSiv.AArch64
open VG.Proof.AesGcm.AArch64 (GcmImpl)

/-- RFC 8452 Appendix A: POLYVAL with `H` is GHASH with `H · x`. -/
theorem tagInput_eq : TagInputEq := fun a n pt d => by
  rw [GcmSiv.tagInput_eq, Spec.GcmSiv.polyval, GcmSiv.Polyval.polyvalFrom_eq]
  rfl

/-! ## v8–v15 -/

theorem seal_keepsV (v : GcmImpl) : («seal» v.callees).allInstrs keepsV = true := by
  simp only [«seal», keys, derive, expand, polyval, absorb, absTail, absTailPre, chunk, chunkPre, chunkLen, revLoop,
    lens, tag, crypt, cryptBlock, cryptTail, callCtr, callKey, callGh, Impl.AesGcm.AArch64.copyLoop,
    Impl.AesGcm.AArch64.xorLoop, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]
  decide +kernel

theorem open_keepsV (v : GcmImpl) : («open» v.callees).allInstrs keepsV = true := by
  simp only [«open», keys, derive, expand, polyval, absorb, absTail, absTailPre, chunk, chunkPre, chunkLen, revLoop,
    lens, tag, crypt, cryptBlock, cryptTail, mask, callCtr, callKey, callGh, Impl.AesGcm.AArch64.copyLoop,
    Impl.AesGcm.AArch64.xorLoop, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]
  decide +kernel

/-! ## Correctness -/

theorem seal_correct (v : GcmImpl) (s : State) (hs : sealAArch64.pre s) :
    ∃ t s', Exec isa («seal» v.callees) s t s' ∧ abiPreserved s s' ∧ sealAArch64.post s s' :=
  WP.withPreservedV (seal_wp v tagInput_eq hs) (seal_keepsV v)

theorem open_correct (v : GcmImpl) (s : State) (hs : openAArch64.pre s) :
    ∃ t s', Exec isa («open» v.callees) s t s' ∧ abiPreserved s s' ∧ openAArch64.post s s' :=
  WP.withPreservedV (open_wp v tagInput_eq hs) (open_keepsV v)

/-! ## A state satisfying the precondition (with empty buffers) -/

def sealSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 0x3000 | .x5 => 0x4000 | .x7 => 0x8000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x8000, 4096⟩]

/-! ## The shared contracts -/

theorem seal_verified (v : GcmImpl) :
    Verified AArch64.target («seal» v.callees) (Spec.GcmSiv.sealContract AArch64.abi) :=
  Verified.of_correct (seal_correct v) (seal_ct v) (by
    sig_implies [Spec.GcmSiv.sealContract, Spec.GcmSiv.sealSig, sealAArch64, onePre, onePub, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [sealSat] using sealSat)

theorem open_verified (v : GcmImpl) :
    Verified AArch64.target («open» v.callees) (Spec.GcmSiv.openContract AArch64.abi) :=
  Verified.of_correct (open_correct v) (open_ct v)
    { pre := by sig_implies_pre [Spec.GcmSiv.openContract, Spec.GcmSiv.openSig, openAArch64, openResult, openPost,
        onePre, onePub, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD,
        List.range, List.range.loop]
      -- `h` and the goal match on the same outcome of `decryptWith` with
      -- different matchers (`openPost`'s and `openContract`'s): split on it
      -- rather than have `exact h` unfold both to unify them.
      post := by
        intro s s' _ h
        sig_post [Spec.GcmSiv.openContract, Spec.GcmSiv.openSig, openAArch64, openResult, openPost, onePre, onePub,
          rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
          List.range.loop]
        sig_reduce [Spec.GcmSiv.openContract, Spec.GcmSiv.openSig, openAArch64, openResult, openPost, onePre, onePub,
          rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
          List.range.loop] at h
        split at h <;> rename_i heq <;> rw [heq] <;> exact h
      pub := by sig_implies_pub [Spec.GcmSiv.openContract, Spec.GcmSiv.openSig, openAArch64, openResult, openPost,
        onePre, onePub, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD,
        List.range, List.range.loop]
      sat := by sig_implies_sat [Spec.GcmSiv.openContract, Spec.GcmSiv.openSig, openAArch64, openResult, openPost,
        onePre, onePub, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD,
        List.range, List.range.loop] [sealSat] using sealSat }

end VG.Proof.AesGcmSiv.AArch64
