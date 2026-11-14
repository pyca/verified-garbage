module

import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Verified
public import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Steps
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe
import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# RC2-CBC's `init` on x86-64, with its working space on the stack

`init` has six argument words, so its working space was its first stack
argument. It runs its code, proved with it as an argument (`Verified.lean`), in a frame of 592 bytes that allocates it, after
a quadword standing for the return address and the buffer's address
(`Verified.stackArgScratchWiped`), and zero its 576 bytes before returning.
-/

@[expose] public section

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

end VG.Proof.Rc2.X86_64.Stream
