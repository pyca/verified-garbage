import VerifiedGarbage.Proof.Seed.X86_64.KeyVerified
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe

/-!
# SEED on x86-64, with its working space on the stack

Key expansion and ECB run their code, proved with the working space as an
argument, in a frame that allocates it and zeroes it after the code
(`Verified.stackScratchWiped`), since it holds the key, the round keys and
the data: 1064 bytes, the 1056 of the working space and 8 to keep `rsp`
aligned. The code uses no other stack.
-/

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

/-- An implementation `c` of ECB in the direction `d`, proved with its
working space as an argument and no stack, in its frame. -/
theorem ecb_framed {c : Prog isa} {d : Spec.Seed.Direction}
    (h : Verified X86_64.target c (Proof.Seed.ecbScratchContract X86_64.abi d 132 0))
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ 0) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 1064 .rcx 132 c)
      (Spec.Seed.ecbContract X86_64.abi d 1064) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Seed.ecbSig) (nm := "scratch") (e := .u64)
    (n := 132) (post := Spec.Seed.ecbPost d X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1064) h (by decide) (by decide) (by decide) hsp hd (by decide)
    (Proof.Seed.ecbPostOut_local _ d)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem encrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 1064 .rcx 132 Impl.Seed.X86_64.encrypt)
      (Spec.Seed.ecbContract X86_64.abi .encrypt 1064) :=
  ecb_framed encrypt_verified (Code.all_of_allInstrs (by lit_decide)) (by lit_decide)

theorem decrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 1064 .rcx 132 Impl.Seed.X86_64.decrypt)
      (Spec.Seed.ecbContract X86_64.abi .decrypt 1064) :=
  ecb_framed decrypt_verified (Code.all_of_allInstrs (by lit_decide)) (by lit_decide)

end VG.Proof.Seed.X86_64
