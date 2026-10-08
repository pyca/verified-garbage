import VerifiedGarbage.Proof.Seed.AArch64.KeyVerified
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe

/-!
# SEED on AArch64, with its working space on the stack

Key expansion and ECB run their code, proved with the working space as an
argument, in a frame that allocates it and zeroes it after the code
(`Verified.stackScratchWiped`), since it holds the key, the round keys and
the data: the 976 bytes of the working space. The code uses no other stack.
-/

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

/-- An implementation `c` of ECB in the direction `d`, proved with its
working space as an argument and no stack, in its frame. -/
theorem ecb_framed {c : Prog isa} {d : Spec.Seed.Direction}
    (h : Verified AArch64.target c (Proof.Seed.ecbScratchContract AArch64.abi d 122 0)) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 976 .x3 122 c)
      (Spec.Seed.ecbContract AArch64.abi d 976) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Seed.ecbSig) (nm := "scratch") (e := .u64)
    (n := 122) (post := Spec.Seed.ecbPost d AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 976) h (by decide) (by decide) (by decide) (Proof.Seed.ecbPostOut_local _ d)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem encrypt_framed :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratchWiped 976 .x3 122 Impl.Seed.AArch64.encrypt)
      (Spec.Seed.ecbContract AArch64.abi .encrypt 976) :=
  ecb_framed encrypt_verified

theorem decrypt_framed :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratchWiped 976 .x3 122 Impl.Seed.AArch64.decrypt)
      (Spec.Seed.ecbContract AArch64.abi .decrypt 976) :=
  ecb_framed decrypt_verified

end VG.Proof.Seed.AArch64
