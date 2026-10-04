import VerifiedGarbage.Proof.Rc2.X86.Stream.Verified
import VerifiedGarbage.Proof.Rc2.X86.Stream.Lit
import VerifiedGarbage.Proof.Rc2.Scratch
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe

/-!
# RC2-CBC's streaming functions on x86, with their working space on the stack

`init` and the updates run their code, proved with the working space as an
argument (`Verified.lean`), in a frame of 608 bytes that allocates it and
copies the six argument slots (`Verified.stackScratchWiped`), and zero it
before returning.
-/

namespace VG.Proof.Rc2.X86.Stream

open VG VG.X86

/-- A state satisfying `vg_rc2_cbc_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x3000, 144⟩, ⟨0x6004, 24⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Rc2.cbcInitContract X86.abi 632).pre s := by
  implies_sat [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, Spec.Rc2.cbcInitPost, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes]
    [initFrameSat, initSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using initFrameSat

theorem init_framed :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratchWiped 608 6 144 Impl.Rc2.X86.Stream.init)
      (Spec.Rc2.cbcInitContract X86.abi 632) :=
  X86.Verified.stackScratchWiped (sig := Spec.Rc2.cbcInitSig) (nm := "scratch") (e := .u64)
    (n := 72) (post := Spec.Rc2.cbcInitPost X86.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 608) (words := 144) init_verified (by decide) (by lit_decide) (by lit_decide)
    (by decide) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (cbcInitPost_local _)
    (cbcInitPostOut_local _) initFrameSat_pre

/-- A state satisfying the update functions' precondition, without the
working space. -/
def updateFrameSat : State := { updateSat with wr := [⟨0x1000, 144⟩, ⟨0x3000, 0⟩, ⟨0x6004, 24⟩] }

theorem updateFrameSat_pre (d : Spec.Rc2.Direction) :
    ∃ s, (Spec.Rc2.cbcUpdateContract X86.abi d 648).pre s := by
  implies_sat [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, Spec.Rc2.cbcUpdatePre,
    Spec.Rc2.cbcUpdatePost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [updateFrameSat, updateSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using updateFrameSat

theorem encryptUpdate_framed :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratchWiped 608 6 144 Impl.Rc2.X86.Stream.encryptUpdate)
      (Spec.Rc2.cbcEncryptUpdateContract X86.abi 648) :=
  X86.Verified.stackScratchWiped (sig := Spec.Rc2.cbcUpdateSig) (nm := "scratch") (e := .u64)
    (n := 72) (pre := Spec.Rc2.cbcUpdatePre X86.abi.ptrBits)
    (post := Spec.Rc2.cbcUpdatePost .encrypt X86.abi.ptrBits) (wa := true) (stack := 40)
    (bytes := 608) (words := 144) encryptUpdate_verified (by decide) (by lit_decide)
    (by lit_decide) (by decide) (cbcUpdatePre_local _) (cbcUpdatePost_local _ _)
    (cbcUpdatePostOut_local _ _) (updateFrameSat_pre .encrypt)

theorem decryptUpdate_framed :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratchWiped 608 6 144 Impl.Rc2.X86.Stream.decryptUpdate)
      (Spec.Rc2.cbcDecryptUpdateContract X86.abi 648) :=
  X86.Verified.stackScratchWiped (sig := Spec.Rc2.cbcUpdateSig) (nm := "scratch") (e := .u64)
    (n := 72) (pre := Spec.Rc2.cbcUpdatePre X86.abi.ptrBits)
    (post := Spec.Rc2.cbcUpdatePost .decrypt X86.abi.ptrBits) (wa := true) (stack := 40)
    (bytes := 608) (words := 144) decryptUpdate_verified (by decide) (by lit_decide)
    (by lit_decide) (by decide) (cbcUpdatePre_local _) (cbcUpdatePost_local _ _)
    (cbcUpdatePostOut_local _ _) (updateFrameSat_pre .decrypt)

end VG.Proof.Rc2.X86.Stream
