module

public import VerifiedGarbage.Spec.Seed.Contract
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Impl.Seed.RISCV64.ExpandKey
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Seed.RISCV64.Verified
import VerifiedGarbage.Proof.Seed.RISCV64.KeyVerified
import VerifiedGarbage.Proof.Seed.Scratch
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Framework.Contract

/-!
# SEED on RISC-V, with its working space on the stack

Key expansion and ECB run their code, proved with the working space as an argument, in a frame
that allocates it and zeroes it after the code
(`Verified.stackScratchWiped`), since it holds the round keys and the data:
the 1032 bytes of the working space's 129 words, in a frame of 1040.
-/

@[expose] public section

namespace VG.Proof.Seed.RISCV64

open VG VG.RISCV64

def expandKeyFrameSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Seed.expandKeyContract abi 1040).pre s := by
  implies_sat [Spec.Seed.expandKeyContract, Spec.Seed.expandKeySig, abi, argRegs]
    [expandKeyFrameSat] using expandKeyFrameSat

/-- Key expansion, with its working space on the stack. -/
theorem expandKey_framed :
    Verified target (Impl.StackScratch.RISCV64.withStackScratchWiped 1040 .a2 129 Impl.Seed.RISCV64.expandKey)
      (Spec.Seed.expandKeyContract abi 1040) :=
  Verified.stackScratchWiped (sig := Spec.Seed.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 129) (post := Proof.Seed.expandKeyPost abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 1040) (words := 129) expandKey_verified (by decide) (by decide) (by decide)
    (Proof.Seed.expandKeyPostOut_local _) expandKeyFrameSat_pre

def ecbFrameSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x3000 | .a2 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩]

theorem ecbFrameSat_pre (d : Spec.Seed.Direction) : ∃ s, (Spec.Seed.ecbContract abi d 1040).pre s := by
  implies_sat [Spec.Seed.ecbContract, Spec.Seed.ecbSig, Spec.Seed.ecbPost, abi, argRegs]
    [ecbFrameSat] using ecbFrameSat

/-- ECB in the direction `d`, with its working space on the stack. -/
theorem ecb_framed (d : Spec.Seed.Direction) :
    Verified target (Impl.StackScratch.RISCV64.withStackScratchWiped 1040 .a3 129 (Impl.Seed.RISCV64.ecb d))
      (Spec.Seed.ecbContract abi d 1040) :=
  Verified.stackScratchWiped (sig := Spec.Seed.ecbSig) (nm := "scratch") (e := .u64)
    (n := 129) (post := Spec.Seed.ecbPost d abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1040) (words := 129) (ecb_verified d) (by decide) (by decide) (by decide)
    (Proof.Seed.ecbPostOut_local _ _) (ecbFrameSat_pre _)

end VG.Proof.Seed.RISCV64
