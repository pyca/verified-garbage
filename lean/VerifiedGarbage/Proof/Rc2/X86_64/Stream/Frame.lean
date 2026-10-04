import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Verified
import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Lit
import VerifiedGarbage.Proof.Rc2.Scratch
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe

/-!
# RC2-CBC's streaming functions on x86-64, with their working space on the stack

`init` and the updates have six argument words, so their working space was
their first stack argument. They run their code, proved with it as an
argument (`Verified.lean`), in a frame of 592 bytes that allocates it, after
a quadword standing for the return address and the buffer's address
(`Verified.stackArgScratchWiped`), and zero its 576 bytes before returning.
-/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64

/-- A state satisfying `vg_rc2_cbc_init`'s precondition, without the working
space. -/
def initFrameSat : State :=
  { initSatState with rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩], wr := [⟨0x3000, 144⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Rc2.cbcInitContract X86_64.abi 600).pre s := by
  implies_sat [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, Spec.Rc2.cbcInitPost, X86_64.abi,
    X86_64.argRegs] [initFrameSat, initSatState] using initFrameSat

theorem init_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratchWiped 592 0 72 Impl.Rc2.X86_64.Stream.init)
      (Spec.Rc2.cbcInitContract X86_64.abi 600) :=
  X86_64.Verified.stackArgScratchWiped (sig := Spec.Rc2.cbcInitSig) (nm := "scratch") (e := .u64)
    (n := 72) (post := Spec.Rc2.cbcInitPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 592) (words := 72) init_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (cbcInitPost_local _)
    (cbcInitPostOut_local _) initFrameSat_pre

/-- A state satisfying the update functions' precondition, without the
working space. -/
def updateFrameSat : State :=
  { updateSatState with rd := [⟨0x2000, 0⟩], wr := [⟨0x1000, 144⟩, ⟨0x3000, 0⟩] }

theorem updateFrameSat_pre (d : Spec.Rc2.Direction) :
    ∃ s, (Spec.Rc2.cbcUpdateContract X86_64.abi d 608).pre s := by
  implies_sat [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, Spec.Rc2.cbcUpdatePre,
    Spec.Rc2.cbcUpdatePost, X86_64.abi, X86_64.argRegs] [updateFrameSat, updateSatState]
    using updateFrameSat

theorem encryptUpdate_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratchWiped 592 0 72
        Impl.Rc2.X86_64.Stream.encryptUpdate)
      (Spec.Rc2.cbcEncryptUpdateContract X86_64.abi 608) :=
  X86_64.Verified.stackArgScratchWiped (sig := Spec.Rc2.cbcUpdateSig) (nm := "scratch") (e := .u64)
    (n := 72) (pre := Spec.Rc2.cbcUpdatePre X86_64.abi.ptrBits)
    (post := Spec.Rc2.cbcUpdatePost .encrypt X86_64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 592) (words := 72) encryptUpdate_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (cbcUpdatePre_local _) (cbcUpdatePost_local _ _) (cbcUpdatePostOut_local _ _)
    (updateFrameSat_pre .encrypt)

theorem decryptUpdate_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratchWiped 592 0 72
        Impl.Rc2.X86_64.Stream.decryptUpdate)
      (Spec.Rc2.cbcDecryptUpdateContract X86_64.abi 608) :=
  X86_64.Verified.stackArgScratchWiped (sig := Spec.Rc2.cbcUpdateSig) (nm := "scratch") (e := .u64)
    (n := 72) (pre := Spec.Rc2.cbcUpdatePre X86_64.abi.ptrBits)
    (post := Spec.Rc2.cbcUpdatePost .decrypt X86_64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 592) (words := 72) decryptUpdate_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (cbcUpdatePre_local _) (cbcUpdatePost_local _ _) (cbcUpdatePostOut_local _ _)
    (updateFrameSat_pre .decrypt)

end VG.Proof.Rc2.X86_64.Stream
