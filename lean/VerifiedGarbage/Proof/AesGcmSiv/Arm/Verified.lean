import VerifiedGarbage.Proof.AesGcmSiv.Arm.FnCT
import VerifiedGarbage.Proof.GcmSiv.Polyval
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.GcmSiv.Contract
import VerifiedGarbage.Proof.AesGcmSiv.Scratch
import VerifiedGarbage.Proof.Framework.Arm.StackScratch

/-!
# AES-GCM-SIV on ARMv7: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, with the tag input computed with GHASH equal to the RFC's
(`tagInput_eq`, from `Proof.GcmSiv.Polyval`, imported here only so that the
other proofs need not import its algebra), a state satisfying each
precondition, and the shared contracts of `Spec/GcmSiv/Contract.lean` with
the working space as a last argument (`Proof/AesGcmSiv/Scratch.lean`, 470
words), with 8 bytes of stack: each call of `vg_aes_ctr32` or `vg_ghash`
pushes two words. The last section allocates the working space.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Impl.AesGcmSiv.Arm
open VG.Proof.AesGcm.Arm (bel arg args)

/-- RFC 8452 Appendix A: POLYVAL with `H` is GHASH with `H · x`. -/
theorem tagInput_eq : TagInputEq := fun a n pt d => by
  rw [GcmSiv.tagInput_eq, Spec.GcmSiv.polyval, GcmSiv.Polyval.polyvalFrom_eq]
  rfl

/-- `seal`'s state satisfying the precondition: no additional data, no
data, the tag at `0x4000` and `work` at `0x5000`, their addresses the stack
arguments at `sp + 12` and `sp + 16`. -/
def sealSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x800D then 0x40 else if a = 0x8011 then 0x50 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x8000, 20⟩]
  wr := [⟨0, 0⟩, ⟨0x4000, 16⟩, ⟨0x5000, 3760⟩]

/-- `open`'s: as `seal`'s, with the tag read only. -/
def openSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x4000, 16⟩, ⟨0x8000, 20⟩],
                 wr := [⟨0, 0⟩, ⟨0x5000, 3760⟩] }

theorem seal_verified : Verified Arm.target «seal» (Proof.AesGcmSiv.sealScratchContract Arm.abi 470 8) :=
  Verified.of_correct (fun _ hs => seal_wp tagInput_eq hs) seal_ct (by
    sig_implies [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig, Spec.GcmSiv.sealPre,
      Spec.GcmSiv.sealPost, sealArm, sealPre, oneLay, onePub, rounds, bel, arg, args, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sealSat)

theorem open_verified : Verified Arm.target «open» (Proof.AesGcmSiv.openScratchContract Arm.abi 470 8) :=
  Verified.of_correct (fun _ hs => open_wp tagInput_eq hs) open_ct
    { pre := by sig_implies_pre [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, openArm, openResult, openPost,
        openPre, oneLay, onePub, rounds, bel, arg, args, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
        Arm.State.addr]
      -- `h` and the goal match on the same outcome of `decryptWith` with
      -- different matchers (`openPost`'s and `openContract`'s): split on it
      -- rather than have `exact h` unfold both to unify them.
      post := by
        intro s s' _ h
        sig_post [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
          Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, openArm, openResult, openPost,
          openPre, oneLay, onePub, rounds, bel, arg, args, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
        sig_reduce [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
          Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, openArm, openResult, openPost,
          openPre, oneLay, onePub, rounds, bel, arg, args, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr] at h
        have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        simp only [e]
        intro _
        split at h <;> rename_i heq <;> rw [heq] <;> exact h
      pub := by sig_implies_pub [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, openArm, openResult, openPost,
        openPre, oneLay, onePub, rounds, bel, arg, args, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
        Arm.State.addr]
      sat := by sig_implies_sat [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, openArm, openResult, openPost,
        openPre, oneLay, onePub, rounds, bel, arg, args, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
        Arm.State.addr] [openSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using openSat }

/-! ## With the working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (above), in a frame that allocates it
(`Verified.stackScratch`): their working space is their fifth stack
argument, after `aad_len`, `data`, `len` and `tag`, so the frame of 3792
bytes holds a copy of those four words, the address of the working space,
the saved `lr` and the working space (3784 bytes, rounded up to an
immediate `sub` can encode). The copies are read only where the pre- and
postconditions read the buffers, and `open`'s leak, whether it succeeds,
reads only its buffers (`Proof/AesGcmSiv/Scratch.lean`).
-/

/-- A state satisfying `vg_aes_gcm_siv_seal`'s precondition, without the
working space: its four words of stack arguments at `0x8000`. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x8000, 16⟩],
                 wr := [⟨0, 0⟩, ⟨0x4000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.GcmSiv.sealContract Arm.abi 3800).pre s := by
  implies_sat [Spec.GcmSiv.sealContract, Spec.GcmSiv.sealSig, Spec.GcmSiv.sealPre, Spec.GcmSiv.sealPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [sealFrameSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 3792 4 «seal»)
      (Spec.GcmSiv.sealContract Arm.abi 3800) :=
  Arm.Verified.stackScratch (sig := Spec.GcmSiv.sealSig) (nm := "work") (e := .u64)
    (n := 470) (pre := Spec.GcmSiv.sealPre Arm.abi.ptrBits)
    (post := Spec.GcmSiv.sealPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (m := 4) seal_verified (by decide) (by decide) (by decide) (by decide)
    (sealPre_local _) (sealPost_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_gcm_siv_open`'s precondition, without the
working space: its four words of stack arguments at `0x8000`. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x4000, 16⟩, ⟨0x8000, 16⟩],
                 wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.GcmSiv.openContract Arm.abi 3800).pre s := by
  implies_sat [Spec.GcmSiv.openContract, Spec.GcmSiv.openSig, Spec.GcmSiv.openPre, Spec.GcmSiv.openPost,
    Spec.GcmSiv.openLeak, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [openFrameSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using openFrameSat

theorem open_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 3792 4 «open»)
      (Spec.GcmSiv.openContract Arm.abi 3800) :=
  Arm.Verified.stackScratch (sig := Spec.GcmSiv.openSig) (nm := "work") (e := .u64)
    (n := 470) (pre := Spec.GcmSiv.openPre Arm.abi.ptrBits)
    (post := Spec.GcmSiv.openPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (leak := some (Spec.GcmSiv.openLeak Arm.abi.ptrBits))
    (m := 4) (Proof.AesGcmSiv.Verified.of_openScratch open_verified) (by decide) (by decide) (by decide) (by decide)
    (openPre_local _) (openPost_local _) openFrameSat_pre
    (hleak := openLeak_local _)

end VG.Proof.AesGcmSiv.Arm
