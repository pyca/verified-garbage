import VerifiedGarbage.Proof.AesGcmSiv.AArch64.FnCT
import VerifiedGarbage.Proof.GcmSiv.Polyval
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.GcmSiv.Contract
import VerifiedGarbage.Proof.AesGcmSiv.Scratch
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch

/-!
# AES-GCM-SIV on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementations `v` of `vg_aes_ctr32`, `vg_aes_expand_key` and
`vg_ghash`), with the tag input computed with GHASH equal to the RFC's
(`tagInput_eq`, from `Proof.GcmSiv.Polyval`, imported here only so that the
other proofs need not import its algebra), a state satisfying each
precondition, and the shared contracts of `Spec/GcmSiv/Contract.lean` with
the working space as a last argument (`Proof/AesGcmSiv/Scratch.lean`, 476
words), with no stack: the calls keep the return address in `x30`, which
each function saves in the working space. The last section allocates the
working space.
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
    lens, tag, tagOut, crypt, cryptBlock, cryptTail, callCtr, callKey, callGh, Impl.AesGcm.AArch64.copyLoop,
    Impl.AesGcm.AArch64.xorLoop, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]
  decide +kernel

theorem open_keepsV (v : GcmImpl) : («open» v.callees).allInstrs keepsV = true := by
  simp only [«open», keys, derive, expand, polyval, absorb, absTail, absTailPre, chunk, chunkPre, chunkLen, revLoop,
    lens, tag, recv, crypt, cryptBlock, cryptTail, mask, callCtr, callKey, callGh, Impl.AesGcm.AArch64.copyLoop,
    Impl.AesGcm.AArch64.xorLoop, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]
  decide +kernel

/-! ## Correctness -/

theorem seal_correct (v : GcmImpl) (s : State) (hs : sealAArch64.pre s) :
    ∃ t s', Exec isa («seal» v.callees) s t s' ∧ abiPreserved s s' ∧ sealAArch64.post s s' :=
  WP.withPreservedV (seal_wp v tagInput_eq hs) (seal_keepsV v)

theorem open_correct (v : GcmImpl) (s : State) (hs : openAArch64.pre s) :
    ∃ t s', Exec isa («open» v.callees) s t s' ∧ abiPreserved s s' ∧ openAArch64.post s s' :=
  WP.withPreservedV (open_wp v tagInput_eq hs) (open_keepsV v)

/-! ## States satisfying the preconditions (with empty buffers) -/

/-- `seal`'s: the tag at `0x5000`, and `work` at `0x8000`, its address at
`sp`. -/
def sealSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 0x3000 | .x5 => 0x4000 | .x7 => 0x5000 | _ => 0
  sp := 0x10000
  mem a := if a = 0x10001 then 0x80 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x10000, 8⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 16⟩, ⟨0x8000, 3808⟩]

/-- `open`'s: as `seal`'s, with the tag read only. -/
def openSat : State := { sealSat with
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x10000, 8⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x8000, 3808⟩] }

/-! ## The shared contracts, with the working space as an argument -/

theorem seal_verified (v : GcmImpl) :
    Verified AArch64.target («seal» v.callees) (Proof.AesGcmSiv.sealScratchContract AArch64.abi 476) :=
  Verified.of_correct (seal_correct v) (seal_ct v) (by
    sig_implies [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig, Spec.GcmSiv.sealPre,
      Spec.GcmSiv.sealPost, sealAArch64, sealPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs,
      AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [sealSat] using sealSat)

theorem open_verified (v : GcmImpl) :
    Verified AArch64.target («open» v.callees) (Proof.AesGcmSiv.openScratchContract AArch64.abi 476) :=
  Verified.of_correct (open_correct v) (open_ct v)
    { pre := by sig_implies_pre [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, openAArch64, openResult, openPost,
        openPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      -- `h` and the goal match on the same outcome of `decryptWith` with
      -- different matchers (`openPost`'s and `openContract`'s): split on it
      -- rather than have `exact h` unfold both to unify them.
      post := by
        intro s s' _ h
        sig_post [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
          Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, openAArch64, openResult, openPost,
          openPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
          AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
        sig_reduce [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
          Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, openAArch64, openResult, openPost,
          openPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
          AArch64.stackArgAddr, List.getD, List.range, List.range.loop] at h
        intro _
        split at h <;> rename_i heq <;> rw [heq] <;> exact h
      pub := by sig_implies_pub [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, openAArch64, openResult, openPost,
        openPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      sat := by sig_implies_sat [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, openAArch64, openResult, openPost,
        openPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop] [openSat, sealSat] using openSat }

/-! ## With the working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (above), in a frame that allocates it
(`Verified.stackArgScratch`): their working space is their first stack
argument, as the eight argument registers are taken, so the frame of 3824
bytes holds the address of the working space and the working space, at the
next 16-byte boundary. The code itself uses no stack: its calls keep the
return address in `x30`. `open`'s leak, whether it succeeds, reads only its
buffers (`openLeak_local`).
-/

/-- A state satisfying `vg_aes_gcm_siv_seal`'s precondition, without the
working space. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩], wr := [⟨0x4000, 0⟩, ⟨0x5000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.GcmSiv.sealContract AArch64.abi 3824).pre s := by
  implies_sat [Spec.GcmSiv.sealContract, Spec.GcmSiv.sealSig, Spec.GcmSiv.sealPre, Spec.GcmSiv.sealPost,
    AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
    List.range.loop] [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 3824 0 («seal» v.callees))
      (Spec.GcmSiv.sealContract AArch64.abi 3824) :=
  AArch64.Verified.stackArgScratch (sig := Spec.GcmSiv.sealSig) (nm := "work") (e := .u64)
    (n := 476) (pre := Spec.GcmSiv.sealPre AArch64.abi.ptrBits)
    (post := Spec.GcmSiv.sealPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 3824)
    (seal_verified v) (by decide) (by decide) (sealPre_local _) (sealPost_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_gcm_siv_open`'s precondition, without the
working space. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x5000, 16⟩], wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.GcmSiv.openContract AArch64.abi 3824).pre s := by
  implies_sat [Spec.GcmSiv.openContract, Spec.GcmSiv.openSig, Spec.GcmSiv.openPre, Spec.GcmSiv.openPost,
    Spec.GcmSiv.openLeak, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD,
    List.range, List.range.loop] [openFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using openFrameSat

theorem open_framed (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 3824 0 («open» v.callees))
      (Spec.GcmSiv.openContract AArch64.abi 3824) :=
  AArch64.Verified.stackArgScratch (sig := Spec.GcmSiv.openSig) (nm := "work") (e := .u64)
    (n := 476) (pre := Spec.GcmSiv.openPre AArch64.abi.ptrBits)
    (post := Spec.GcmSiv.openPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 3824)
    (leak := some (Spec.GcmSiv.openLeak AArch64.abi.ptrBits))
    (open_verified v) (by decide) (by decide) (openPre_local _) (openPost_local _) openFrameSat_pre
    (hleak := openLeak_local _)

end VG.Proof.AesGcmSiv.AArch64
