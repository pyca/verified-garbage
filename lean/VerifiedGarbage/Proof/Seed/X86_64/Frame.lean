module
public import VerifiedGarbage.Proof.Seed.Scratch
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Depth

import VerifiedGarbage.Proof.Seed.X86_64.KeyVerified
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Seed.X86_64.Lit
public import VerifiedGarbage.Impl.Seed.X86_64.ExpandKey
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintSum

/-!
# SEED on x86-64, with its working space on the stack

Key expansion runs its code, proved with the working space as an argument,
in a frame that allocates it and zeroes it after the code
(`Verified.stackScratchWiped`), since it holds the key and the round keys:
1064 bytes, the 1056 of the working space and 8 to keep `rsp` aligned. The
code uses no other stack. ECB does the same around calls of the blocks
functions (`EcbCall.lean`).
-/

@[expose] public section

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64

theorem expandKey_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratchWiped 1064 .rdx 132 Impl.Seed.X86_64.expandKey)
      (Spec.Seed.expandKeyContract X86_64.abi 1064) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Seed.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 132) (post := Proof.Seed.expandKeyPost X86_64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 1064) expandKey_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Seed.expandKeyPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Seed.X86_64
