import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Verified
import VerifiedGarbage.Proof.TripleDes.Scratch
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe

/-!
# Triple DES key expansion and ECB on AArch64, with their working space on the stack

Key expansion and ECB run their code, proved with the working space as an
argument, in a frame that allocates it and zeroes it after the code
(`Verified.stackScratchWiped`), since it may hold the key schedule and the
data: 512 bytes for key expansion and 1024 for ECB. The code uses no other
stack.
-/

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64

/-- A state satisfying `vg_triple_des_expand_key`'s precondition: a 16-byte
key at `0x1000` and the schedule at `0x2000`. -/
def expandKeyFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 384⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.TripleDes.expandKeyContract AArch64.abi 512).pre s := by
  implies_sat [Spec.TripleDes.expandKeyContract, Spec.TripleDes.expandKeySig,
    Spec.TripleDes.expandKeyPre, Spec.TripleDes.expandKeyPost, Spec.TripleDes.validKey, AArch64.abi,
    AArch64.argRegs] [expandKeyFrameSat] using expandKeyFrameSat

theorem expandKey_framed :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratchWiped 512 .x3 64 Impl.TripleDes.AArch64.Key.expandKey)
      (Spec.TripleDes.expandKeyContract AArch64.abi 512) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.TripleDes.expandKeySig) (nm := "scratch")
    (e := .u64) (n := 64) (pre := Spec.TripleDes.expandKeyPre AArch64.abi.ptrBits)
    (post := Spec.TripleDes.expandKeyPost AArch64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 512) Key.verified (by decide) (by decide) (by decide)
    (Proof.TripleDes.expandKeyPostOut_local _) expandKeyFrameSat_pre

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
