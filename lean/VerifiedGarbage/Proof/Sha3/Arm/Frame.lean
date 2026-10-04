import VerifiedGarbage.Proof.Sha3.Arm.Shared
import VerifiedGarbage.Proof.Sha3.Scratch
import VerifiedGarbage.Proof.Framework.Arm.StackScratch

/-!
# The SHA-3 sponge on ARMv7, with its working space on the stack

`absorb`, `pad` and `squeeze` run their code, proved with the working space
as an argument (`Shared.lean`), in a frame of 656 bytes that allocates it
(`Verified.stackScratch`): the copies of the other arguments passed on the
stack (`absorb`'s `len`, `squeeze`'s `outlen`, none for `pad`), the buffer's
address, the saved `lr` and the 640 bytes of working space. The copies are
read only where the pre- and postconditions read the buffers
(`Proof/Sha3/Scratch.lean`).
-/

namespace VG.Proof.Sha3.Arm.Frame

open VG VG.Arm

/-- A state satisfying `vg_keccak_absorb`'s precondition, without the
working space. -/
def absorbSat : State :=
  { Stream.Absorb.sat with rd := [⟨0, 0⟩, ⟨0x4000, 4⟩], wr := [⟨0x1000, 200⟩] }

theorem absorbSat_pre : ∃ s, (Spec.Sha3.absorbContract Arm.abi 656).pre s := by
  implies_sat [Spec.Sha3.absorbContract, Spec.Sha3.absorbSig, Spec.Sha3.absorbPre,
    Spec.Sha3.absorbPost, Spec.Sha3.rates, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr]
    [absorbSat, Stream.Absorb.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using absorbSat

theorem absorb_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 656 1 Impl.Sha3.Arm.Stream.absorb)
      (Spec.Sha3.absorbContract Arm.abi 656) :=
  Arm.Verified.stackScratch (sig := Spec.Sha3.absorbSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.absorbPre Arm.abi.ptrBits) (post := Spec.Sha3.absorbPost Arm.abi.ptrBits)
    (wa := true) (stack := 0) (m := 1) Shared.absorb (by decide) (by decide) (by decide)
    (by decide) (absorbPre_local _) (absorbPost_local _) absorbSat_pre

/-- A state satisfying `vg_keccak_pad`'s precondition, without the working
space. -/
def padSat : State := { Stream.Pad.sat with rd := [], wr := [⟨0x1000, 200⟩] }

theorem padSat_pre : ∃ s, (Spec.Sha3.padContract Arm.abi 656).pre s := by
  implies_sat [Spec.Sha3.padContract, Spec.Sha3.padSig, Spec.Sha3.padPre, Spec.Sha3.padPost,
    Spec.Sha3.rates, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [padSat, Stream.Pad.sat] using padSat

theorem pad_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 656 0 Impl.Sha3.Arm.Stream.pad)
      (Spec.Sha3.padContract Arm.abi 656) :=
  Arm.Verified.stackScratch (sig := Spec.Sha3.padSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.padPre Arm.abi.ptrBits) (post := Spec.Sha3.padPost Arm.abi.ptrBits)
    (wa := true) (stack := 0) (m := 0) Shared.pad (by decide) (by decide) (by decide)
    (by decide) (padPre_local _) (padPost_local _) padSat_pre

/-- A state satisfying `vg_keccak_squeeze`'s precondition, without the
working space. -/
def squeezeSat : State :=
  { Stream.Squeeze.sat with rd := [⟨0x4000, 4⟩], wr := [⟨0x1000, 200⟩, ⟨0x2000, 0⟩] }

theorem squeezeSat_pre : ∃ s, (Spec.Sha3.squeezeContract Arm.abi 656).pre s := by
  implies_sat [Spec.Sha3.squeezeContract, Spec.Sha3.squeezeSig, Spec.Sha3.squeezePre,
    Spec.Sha3.squeezePost, Spec.Sha3.rates, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr]
    [squeezeSat, Stream.Squeeze.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using squeezeSat

theorem squeeze_framed :
    Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratch 656 1 Impl.Sha3.Arm.Stream.squeeze)
      (Spec.Sha3.squeezeContract Arm.abi 656) :=
  Arm.Verified.stackScratch (sig := Spec.Sha3.squeezeSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.squeezePre Arm.abi.ptrBits) (post := Spec.Sha3.squeezePost Arm.abi.ptrBits)
    (wa := true) (stack := 0) (m := 1) Shared.squeeze (by decide) (by decide) (by decide)
    (by decide) (squeezePre_local _) (squeezePost_local _) squeezeSat_pre

end VG.Proof.Sha3.Arm.Frame
