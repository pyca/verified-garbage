module

public import VerifiedGarbage.Proof.TripleDes.Scratch
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Triple DES ECB on PPC64LE, with its working space on the stack

ECB runs its code, proved with the working space as an argument, in a frame
that allocates it and zeroes it after the code (`Verified.stackScratchWiped`),
since it may hold the data and the saved registers of the block functions:
1056 bytes, the frame's 32-byte header and the 1024 of working space. The
code uses no other stack: its calls keep the return address in the link
register.
-/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE

/-- A state satisfying the ECB functions' precondition, without the working
space: the schedule at `0x1000` and no blocks at `0x2000`. -/
def ecbFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 0⟩]

theorem ecbFrameSat_pre (d : Spec.TripleDes.Direction) :
    ∃ s, (Spec.TripleDes.ecbContract PPC64LE.abi d 1056).pre s := by
  implies_sat [Spec.TripleDes.ecbContract, Spec.TripleDes.ecbSig, Spec.TripleDes.ecbPost,
    PPC64LE.abi, PPC64LE.argRegs] [ecbFrameSat] using ecbFrameSat

/-- An implementation `c` of ECB in the direction `d`, proved with its
working space as an argument and no stack, in its frame. -/
theorem ecb_framed {c : Prog isa} {d : Spec.TripleDes.Direction}
    (h : Verified PPC64LE.target c (Proof.TripleDes.ecbScratchContract PPC64LE.abi d 0)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 1056 .r6 128 c)
      (Spec.TripleDes.ecbContract PPC64LE.abi d 1056) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.TripleDes.ecbSig) (nm := "scratch") (e := .u64)
    (n := 128) (post := Spec.TripleDes.ecbPost d PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1056) (words := 128) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.ecbPost_local _ d) (Proof.TripleDes.ecbPostOut_local _ d) (ecbFrameSat_pre d)

end VG.Proof.TripleDes.PPC64LE
