import VerifiedGarbage.Proof.AesGcmSiv.Arm.FnCT
import VerifiedGarbage.Proof.GcmSiv.Polyval
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.GcmSiv.Contract

/-!
# AES-GCM-SIV on ARMv7: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, with the tag input computed with GHASH equal to the RFC's
(`tagInput_eq`, from `Proof.GcmSiv.Polyval`, imported here only so that the
other proofs need not import its algebra), a state satisfying each
precondition, and the shared contracts of `Spec/GcmSiv/Contract.lean`, with
8 bytes of stack: each call of `vg_aes_ctr32` or `vg_ghash` pushes two
words.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Impl.AesGcmSiv.Arm
open VG.Proof.AesGcm.Arm (bel arg args)

/-- RFC 8452 Appendix A: POLYVAL with `H` is GHASH with `H · x`. -/
theorem tagInput_eq : TagInputEq := fun a n pt d => by
  rw [GcmSiv.tagInput_eq, Spec.GcmSiv.polyval, GcmSiv.Polyval.polyvalFrom_eq]
  rfl

/-- A state with the given registers, the stack pointer at `0x8000`, memory
of zeros (so stack arguments of 0) and the given regions. -/
def mkSat (g : Reg → BitVec 32) (rd wr : List Region) : State where
  gpr := g
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := rd
  wr := wr

/-- A state satisfying the precondition (with no additional data, no data,
and `work` at 0). -/
def sealSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0)
    [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x8000, 16⟩] [⟨0, 0⟩, ⟨0, 4096⟩]

theorem seal_verified : Verified Arm.target «seal» (Spec.GcmSiv.sealContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => seal_wp tagInput_eq hs) seal_ct (by
    sig_implies [Spec.GcmSiv.sealContract, Spec.GcmSiv.sealSig, sealArm, onePre, onePub, rounds, bel, arg, args,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [sealSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sealSat)

theorem open_verified : Verified Arm.target «open» (Spec.GcmSiv.openContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => open_wp tagInput_eq hs) open_ct
    { pre := by sig_implies_pre [Spec.GcmSiv.openContract, Spec.GcmSiv.openSig, openArm, openResult, openPost,
        onePre, onePub, rounds, bel, arg, args, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
        Arm.State.addr]
      -- `h` and the goal match on the same outcome of `decryptWith` with
      -- different matchers (`openPost`'s and `openContract`'s): split on it
      -- rather than have `exact h` unfold both to unify them.
      post := by
        intro s s' _ h
        sig_post [Spec.GcmSiv.openContract, Spec.GcmSiv.openSig, openArm, openResult, openPost, onePre, onePub,
          rounds, bel, arg, args, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        sig_reduce [Spec.GcmSiv.openContract, Spec.GcmSiv.openSig, openArm, openResult, openPost, onePre, onePub,
          rounds, bel, arg, args, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
        have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        simp only [e]
        split at h <;> rename_i heq <;> rw [heq] <;> exact h
      pub := by sig_implies_pub [Spec.GcmSiv.openContract, Spec.GcmSiv.openSig, openArm, openResult, openPost,
        onePre, onePub, rounds, bel, arg, args, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
        Arm.State.addr]
      sat := by sig_implies_sat [Spec.GcmSiv.openContract, Spec.GcmSiv.openSig, openArm, openResult, openPost,
        onePre, onePub, rounds, bel, arg, args, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
        Arm.State.addr] [sealSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sealSat }

end VG.Proof.AesGcmSiv.Arm
