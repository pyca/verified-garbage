module

public import VerifiedGarbage.Proof.Rc2.PPC64LE.Stream.Verified
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rc2.PPC64LE.Stream.Verified
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Streaming RC2-CBC on PPC64LE, with its working space on the stack

`init` and the updates run their code, proved with the working space as an
argument (`Verified.lean`), in a frame of 608 bytes that allocates it
(`Verified.stackScratchWiped`), and zero its 576 bytes before returning.
-/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE.Stream

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE.Stream

/-- A state satisfying `vg_rc2_cbc_init`'s precondition, without the working
space. -/
noncomputable def initFrameSat : State := { initSat with wr := [⟨0x3000, 144⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Rc2.cbcInitContract abi 608).pre s := by
  implies_sat [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, Spec.Rc2.cbcInitPost, abi, argRegs]
    [initFrameSat, initSat] using initFrameSat

theorem init_framed :
    Verified target (Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r9 72 init)
      (Spec.Rc2.cbcInitContract abi 608) :=
  Verified.stackScratchWiped (sig := Spec.Rc2.cbcInitSig) (nm := "scratch") (e := .u64) (n := 72)
    (post := Spec.Rc2.cbcInitPost abi.ptrBits) (wa := true) (stack := 0) (bytes := 608) (words := 72)
    init_verified (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Rc2.cbcInitPost_local _)
    (Proof.Rc2.cbcInitPostOut_local _) initFrameSat_pre

/-- A state satisfying the update functions' precondition, without the
working space. -/
noncomputable def updateFrameSat : State := { updateSat with wr := [⟨0x1000, 144⟩, ⟨0x3000, 0⟩] }

theorem updateFrameSat_pre (d : Spec.Rc2.Direction) : ∃ s, (Spec.Rc2.cbcUpdateContract abi d 608).pre s := by
  implies_sat [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, Spec.Rc2.cbcUpdatePre, Spec.Rc2.cbcUpdatePost,
    abi, argRegs] [updateFrameSat, updateSat] using updateFrameSat

theorem encryptUpdate_framed :
    Verified target (Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r9 72 encryptUpdate)
      (Spec.Rc2.cbcEncryptUpdateContract abi 608) :=
  Verified.stackScratchWiped (sig := Spec.Rc2.cbcUpdateSig) (nm := "scratch") (e := .u64) (n := 72)
    (pre := Spec.Rc2.cbcUpdatePre abi.ptrBits) (post := Spec.Rc2.cbcUpdatePost .encrypt abi.ptrBits) (wa := true)
    (stack := 0) (bytes := 608) (words := 72) encryptUpdate_verified (by decide) (by decide) (by decide)
    (Proof.Rc2.cbcUpdatePre_local _) (Proof.Rc2.cbcUpdatePost_local _ _) (Proof.Rc2.cbcUpdatePostOut_local _ _)
    (updateFrameSat_pre .encrypt)

theorem decryptUpdate_framed :
    Verified target (Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r9 72 decryptUpdate)
      (Spec.Rc2.cbcDecryptUpdateContract abi 608) :=
  Verified.stackScratchWiped (sig := Spec.Rc2.cbcUpdateSig) (nm := "scratch") (e := .u64) (n := 72)
    (pre := Spec.Rc2.cbcUpdatePre abi.ptrBits) (post := Spec.Rc2.cbcUpdatePost .decrypt abi.ptrBits) (wa := true)
    (stack := 0) (bytes := 608) (words := 72) decryptUpdate_verified (by decide) (by decide) (by decide)
    (Proof.Rc2.cbcUpdatePre_local _) (Proof.Rc2.cbcUpdatePost_local _ _) (Proof.Rc2.cbcUpdatePostOut_local _ _)
    (updateFrameSat_pre .decrypt)

end VG.Proof.Rc2.PPC64LE.Stream
