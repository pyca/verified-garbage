import VerifiedGarbage.Proof.Sha3.X86.Shared
import VerifiedGarbage.Proof.Sha3.Scratch
import VerifiedGarbage.Proof.Framework.X86.StackScratch

/-!
# The SHA-3 sponge on x86, with its working space on the stack

`absorb`, `pad` and `squeeze` run their code, proved with the working space
as an argument (`Shared.lean`), in a frame that allocates it and copies the
arguments passed on the stack (`Verified.stackScratch`): the return address,
the copied argument slots (five for `absorb` and `squeeze`, four for `pad`)
and the 640 bytes of working space. The copies are read only where the pre-
and postconditions read the buffers (`Proof/Sha3/Scratch.lean`).
-/

namespace VG.Proof.Sha3.X86.Frame

open VG VG.X86

/-- A state satisfying `vg_keccak_absorb`'s precondition, without the
working space. -/
def absorbSat : State :=
  { Stream.Absorb.sat with wr := [⟨0x1000, 200⟩, ⟨0x4004, 20⟩] }

theorem absorbSat_pre : ∃ s, (Spec.Sha3.absorbContract X86.abi 680).pre s := by
  implies_sat [Spec.Sha3.absorbContract, Spec.Sha3.absorbSig, Spec.Sha3.absorbPre,
    Spec.Sha3.absorbPost, Spec.Sha3.rates, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [absorbSat, Stream.Absorb.sat, Stream.Absorb.satMem, X86.arg, X86.argAddr, Mem.readW,
      Mem.read] using absorbSat

theorem absorb_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 668 5 Impl.Sha3.X86.Stream.absorb)
      (Spec.Sha3.absorbContract X86.abi 680) :=
  X86.Verified.stackScratch (sig := Spec.Sha3.absorbSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.absorbPre X86.abi.ptrBits) (post := Spec.Sha3.absorbPost X86.abi.ptrBits)
    (wa := true) (stack := 12) (bytes := 668) Shared.absorb (by decide) (by lit_decide)
    (by lit_decide) (absorbPre_local _) (absorbPost_local _) absorbSat_pre

/-- A state satisfying `vg_keccak_pad`'s precondition, without the working
space. -/
def padSat : State := { Stream.Pad.sat with wr := [⟨0x1000, 200⟩, ⟨0x4004, 16⟩] }

theorem padSat_pre : ∃ s, (Spec.Sha3.padContract X86.abi 676).pre s := by
  implies_sat [Spec.Sha3.padContract, Spec.Sha3.padSig, Spec.Sha3.padPre, Spec.Sha3.padPost,
    Spec.Sha3.rates, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [padSat, Stream.Pad.sat, Stream.Pad.satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using padSat

theorem pad_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 664 4 Impl.Sha3.X86.Stream.pad)
      (Spec.Sha3.padContract X86.abi 676) :=
  X86.Verified.stackScratch (sig := Spec.Sha3.padSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.padPre X86.abi.ptrBits) (post := Spec.Sha3.padPost X86.abi.ptrBits)
    (wa := true) (stack := 12) (bytes := 664) Shared.pad (by decide) (by lit_decide)
    (by lit_decide) (padPre_local _) (padPost_local _) padSat_pre

/-- A state satisfying `vg_keccak_squeeze`'s precondition, without the
working space. -/
def squeezeSat : State :=
  { Stream.Squeeze.sat with wr := [⟨0x1000, 200⟩, ⟨0x2000, 0⟩, ⟨0x4004, 20⟩] }

theorem squeezeSat_pre : ∃ s, (Spec.Sha3.squeezeContract X86.abi 680).pre s := by
  implies_sat [Spec.Sha3.squeezeContract, Spec.Sha3.squeezeSig, Spec.Sha3.squeezePre,
    Spec.Sha3.squeezePost, Spec.Sha3.rates, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [squeezeSat, Stream.Squeeze.sat, Stream.Squeeze.satMem, X86.arg, X86.argAddr, Mem.readW,
      Mem.read] using squeezeSat

theorem squeeze_framed :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratch 668 5 Impl.Sha3.X86.Stream.squeeze)
      (Spec.Sha3.squeezeContract X86.abi 680) :=
  X86.Verified.stackScratch (sig := Spec.Sha3.squeezeSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.squeezePre X86.abi.ptrBits) (post := Spec.Sha3.squeezePost X86.abi.ptrBits)
    (wa := true) (stack := 12) (bytes := 668) Shared.squeeze (by decide) (by lit_decide)
    (by lit_decide) (squeezePre_local _) (squeezePost_local _) squeezeSat_pre

end VG.Proof.Sha3.X86.Frame
