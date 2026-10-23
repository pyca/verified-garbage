module

public import VerifiedGarbage.Spec.Seed.Contract
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Impl.Seed.PPC64LE.ExpandKey
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Seed.PPC64LE.KeyVerified
import VerifiedGarbage.Proof.Seed.PPC64LE.Verified
import VerifiedGarbage.Proof.Seed.Scratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract

/-!
# SEED on PPC64LE, with its working space on the stack

Key expansion and ECB run their code, proved with the working space as an
argument, in a frame that allocates it and zeroes it after the code
(`Verified.stackScratchWiped`), since it holds the key, the round keys and
the data: the 1040 bytes of the working space's 130 words, and 32 bytes of
the frame.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE

def expandKeyFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Seed.expandKeyContract abi 1072).pre s := by
  implies_sat [Spec.Seed.expandKeyContract, Spec.Seed.expandKeySig, abi, argRegs]
    [expandKeyFrameSat] using expandKeyFrameSat

/-- Key expansion, with its working space on the stack. -/
theorem expandKey_framed :
    Verified target (Impl.StackScratch.PPC64LE.withStackScratchWiped 1072 .r5 130 Impl.Seed.PPC64LE.expandKey)
      (Spec.Seed.expandKeyContract abi 1072) :=
  Verified.stackScratchWiped (sig := Spec.Seed.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 130) (post := Proof.Seed.expandKeyPost abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 1072) (words := 130) expandKey_verified (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Seed.expandKeyPost_local _)
    (Proof.Seed.expandKeyPostOut_local _) expandKeyFrameSat_pre

def ecbFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r5 => 1 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩]

theorem ecbFrameSat_pre (d : Spec.Seed.Direction) : ∃ s, (Spec.Seed.ecbContract abi d 1072).pre s := by
  implies_sat [Spec.Seed.ecbContract, Spec.Seed.ecbSig, Spec.Seed.ecbPost, abi, argRegs]
    [ecbFrameSat] using ecbFrameSat

/-- ECB in the direction `d`, with its working space on the stack. -/
theorem ecb_framed (d : Spec.Seed.Direction) :
    Verified target (Impl.StackScratch.PPC64LE.withStackScratchWiped 1072 .r6 130 (Impl.Seed.PPC64LE.ecb d))
      (Spec.Seed.ecbContract abi d 1072) :=
  Verified.stackScratchWiped (sig := Spec.Seed.ecbSig) (nm := "scratch") (e := .u64)
    (n := 130) (post := Spec.Seed.ecbPost d abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1072) (words := 130) (ecb_verified d) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Seed.ecbPost_local _ _)
    (Proof.Seed.ecbPostOut_local _ _) (ecbFrameSat_pre _)

end VG.Proof.Seed.PPC64LE
