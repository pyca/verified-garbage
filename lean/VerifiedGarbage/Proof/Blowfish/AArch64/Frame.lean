module
public import VerifiedGarbage.Proof.Blowfish.Scratch
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.TCB.AArch64.Target

import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Blowfish.AArch64.Lit

/-!
# Blowfish ECB on AArch64, with its working space on the stack

ECB runs its code, proved with the working space as an argument, in a frame
that allocates it and zeroes it after the code (`Verified.stackScratchWiped`),
since it may hold the data: 256 bytes. The code uses no other stack.
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64

/-- An implementation `c` of ECB in the direction `d`, proved with its
working space as an argument and no stack, in its frame. -/
theorem ecb_framed {c : Prog isa} {d : Spec.Blowfish.Direction}
    (h : Verified AArch64.target c (Proof.Blowfish.ecbScratchContract AArch64.abi d 0)) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 256 .x3 32 c)
      (Spec.Blowfish.ecbContract AArch64.abi d 256) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Blowfish.ecbSig) (nm := "scratch") (e := .u64)
    (n := 32) (post := Spec.Blowfish.ecbPost d AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 256) h (by decide) (by decide) (by decide) (Proof.Blowfish.ecbPostOut_local _ d)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Blowfish.AArch64
