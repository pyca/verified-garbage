import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Verified
import VerifiedGarbage.Proof.TripleDes.Scratch
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe

/-!
# Triple DES key expansion and ECB on x86-64, with their working space on the stack

Key expansion and each implementation of ECB run their code, proved with the
working space as an argument, in a frame that allocates it and zeroes it
after the code (`Verified.stackScratchWiped`), since it may hold the key
schedule and the data: 520 bytes for key expansion (512 of working space)
and 1032 for ECB (1024), with 8 more to keep `rsp` aligned. Key expansion
uses no other stack, and ECB 8 bytes, for its call of the core.
-/

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64

/-- A state satisfying `vg_triple_des_expand_key`'s precondition: a 16-byte
key at `0x1000` and the schedule at `0x2000`. -/
def expandKeyFrameSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 384⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.TripleDes.expandKeyContract X86_64.abi 520).pre s := by
  implies_sat [Spec.TripleDes.expandKeyContract, Spec.TripleDes.expandKeySig,
    Spec.TripleDes.expandKeyPre, Spec.TripleDes.expandKeyPost, Spec.TripleDes.validKey, X86_64.abi,
    X86_64.argRegs] [expandKeyFrameSat] using expandKeyFrameSat

theorem expandKey_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratchWiped 520 .rcx 64 Impl.TripleDes.X86_64.Key.expandKey)
      (Spec.TripleDes.expandKeyContract X86_64.abi 520) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.TripleDes.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 64) (pre := Spec.TripleDes.expandKeyPre X86_64.abi.ptrBits)
    (post := Spec.TripleDes.expandKeyPost X86_64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 520) Key.verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.TripleDes.expandKeyPostOut_local _) expandKeyFrameSat_pre

/-- An implementation `c` of ECB in the direction `d`, proved with its
working space as an argument and 8 bytes of stack, for its call of the core,
in its frame. -/
theorem ecb_framed {c : Prog isa} {d : Spec.TripleDes.Direction}
    (h : Verified X86_64.target c (Proof.TripleDes.ecbScratchContract X86_64.abi d 8))
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ 8) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 1032 .rcx 128 c)
      (Spec.TripleDes.ecbContract X86_64.abi d 1040) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.TripleDes.ecbSig) (nm := "scratch") (e := .u64)
    (n := 128) (post := Spec.TripleDes.ecbPost d X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 1032) h (by decide) (by decide) (by decide) hsp hd (by decide)
    (Proof.TripleDes.ecbPostOut_local _ d)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.TripleDes.X86_64
