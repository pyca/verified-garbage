module

public import VerifiedGarbage.Proof.Rc2.AArch64.Stream.Verified
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RC2-CBC's `init` on AArch64, with its working space on the stack

`init` runs its code, proved with the working space as an
argument (`Verified.lean`), in a frame of 576 bytes that allocates it
(`Verified.stackScratchWiped`), and zero it before returning.
-/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Stream

open VG VG.AArch64 VG.Impl.Rc2.AArch64.Stream

/-- A state satisfying `vg_rc2_cbc_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x3000, 144⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Rc2.cbcInitContract AArch64.abi 592).pre s := by
  implies_sat [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, Spec.Rc2.cbcInitPost, AArch64.abi,
    AArch64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 576 .x6 72 init)
      (Spec.Rc2.cbcInitContract AArch64.abi 592) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Rc2.cbcInitSig) (nm := "scratch") (e := .u64)
    (n := 72) (post := Spec.Rc2.cbcInitPost AArch64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 576) (words := 72) init_verified (by decide) (by decide) (by decide)
    (cbcInitPostOut_local _) initFrameSat_pre

end VG.Proof.Rc2.AArch64.Stream
