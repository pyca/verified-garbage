module

public import VerifiedGarbage.Proof.Rc2.X86.Stream.Verified
public import VerifiedGarbage.Impl.StackScratch.X86
import VerifiedGarbage.Proof.Rc2.X86.Stream.Lit
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# RC2-CBC's `init` on x86, with its working space on the stack

`init` runs its code, proved with the working space as an
argument (`Verified.lean`), in a frame of 608 bytes that allocates it and
copies the six argument slots (`Verified.stackScratchWiped`), and zero it
before returning.
-/

@[expose] public section

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

end VG.Proof.Rc2.X86.Stream
