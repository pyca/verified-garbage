module

public import VerifiedGarbage.Proof.Seed.AArch64.KeyVerified
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs

/-!
# SEED on AArch64, with its working space on the stack

Key expansion runs its code, proved with the working space as an argument,
in a frame that allocates it and zeroes it after the code
(`Verified.stackScratchWiped`), since it holds the key and the round keys:
the 976 bytes of the working space. The code uses no other stack. ECB does
the same around calls of the blocks functions (`EcbCall.lean`).
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64

theorem expandKey_framed :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratchWiped 976 .x2 122 Impl.Seed.AArch64.expandKey)
      (Spec.Seed.expandKeyContract AArch64.abi 976) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Seed.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 122) (post := Proof.Seed.expandKeyPost AArch64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 976) expandKey_verified (by decide) (by decide) (by decide)
    (Proof.Seed.expandKeyPostOut_local _)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Seed.AArch64
