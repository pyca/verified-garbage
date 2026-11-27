module

public import VerifiedGarbage.Proof.TripleDes.Scratch
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.AArch64.Lit

/-!
# Triple DES ECB on AArch64, with its working space on the stack

ECB runs its code, proved with the working space as an argument, in a frame
that allocates it and zeroes it after the code (`Verified.stackScratchWiped`),
since it may hold the key schedule and the data: 1024 bytes. The code uses no
other stack.
-/

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64

/-- An implementation `c` of ECB in the direction `d`, proved with its
working space as an argument and no stack, in its frame. -/
theorem ecb_framed {c : Prog isa} {d : Spec.TripleDes.Direction}
    (h : Verified AArch64.target c (Proof.TripleDes.ecbScratchContract AArch64.abi d 0)) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 1024 .x3 128 c)
      (Spec.TripleDes.ecbContract AArch64.abi d 1024) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.TripleDes.ecbSig) (nm := "scratch") (e := .u64)
    (n := 128) (post := Spec.TripleDes.ecbPost d AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1024) h (by decide) (by decide) (by decide) (Proof.TripleDes.ecbPostOut_local _ d)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.TripleDes.AArch64
