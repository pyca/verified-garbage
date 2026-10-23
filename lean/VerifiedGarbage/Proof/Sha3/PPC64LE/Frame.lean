module

import VerifiedGarbage.Proof.Sha3.Scratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Verified
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
import VerifiedGarbage.Proof.Framework.Contract

/-!
# The SHA-3 sponge on PPC64LE, with its working space on the stack

`absorb`, `pad` and `squeeze` run their code, proved with the working space
as an argument (`Stream/Verified.lean`), in a frame of 672 bytes that
allocates it (`Verified.stackScratch`): the frame's 32-byte header and the
640 bytes of working space. Below it, their own frame saving the link
register takes 48 bytes more.
-/

@[expose] public section

namespace VG.Proof.Sha3.PPC64LE.Frame

open VG VG.PPC64LE

/-- A state satisfying `vg_keccak_absorb`'s precondition, without the
working space. -/
def absorbSat : State := { Stream.absorbSat with wr := [⟨0x1000, 200⟩] }

theorem absorbSat_pre : ∃ s, (Spec.Sha3.absorbContract PPC64LE.abi (48 + 672)).pre s := by
  implies_sat [Spec.Sha3.absorbContract, Spec.Sha3.absorbSig, Spec.Sha3.absorbPre,
    Spec.Sha3.absorbPost, Spec.Sha3.rates, PPC64LE.abi, PPC64LE.argRegs]
    [absorbSat, Stream.absorbSat] using absorbSat

theorem absorb_framed : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch 672 .r8 Impl.Sha3.PPC64LE.Stream.absorb)
    (Spec.Sha3.absorbContract PPC64LE.abi (48 + 672)) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Sha3.absorbSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.absorbPre PPC64LE.abi.ptrBits) (post := Spec.Sha3.absorbPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 48) (bytes := 672) Stream.absorb_verified (by decide) (by decide)
    (absorbPre_local _) (absorbPost_local _) absorbSat_pre

/-- A state satisfying `vg_keccak_pad`'s precondition, without the working
space. -/
def padSat : State := { Stream.padSat with wr := [⟨0x1000, 200⟩] }

theorem padSat_pre : ∃ s, (Spec.Sha3.padContract PPC64LE.abi (48 + 672)).pre s := by
  implies_sat [Spec.Sha3.padContract, Spec.Sha3.padSig, Spec.Sha3.padPre, Spec.Sha3.padPost,
    Spec.Sha3.rates, PPC64LE.abi, PPC64LE.argRegs] [padSat, Stream.padSat] using padSat

theorem pad_framed : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch 672 .r7 Impl.Sha3.PPC64LE.Stream.pad)
    (Spec.Sha3.padContract PPC64LE.abi (48 + 672)) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Sha3.padSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.padPre PPC64LE.abi.ptrBits) (post := Spec.Sha3.padPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 48) (bytes := 672) Stream.pad_verified (by decide) (by decide)
    (padPre_local _) (padPost_local _) padSat_pre

/-- A state satisfying `vg_keccak_squeeze`'s precondition, without the
working space. -/
def squeezeSat : State := { Stream.squeezeSat with wr := [⟨0x1000, 200⟩, ⟨0x2000, 0⟩] }

theorem squeezeSat_pre : ∃ s, (Spec.Sha3.squeezeContract PPC64LE.abi (48 + 672)).pre s := by
  implies_sat [Spec.Sha3.squeezeContract, Spec.Sha3.squeezeSig, Spec.Sha3.squeezePre,
    Spec.Sha3.squeezePost, Spec.Sha3.rates, PPC64LE.abi, PPC64LE.argRegs]
    [squeezeSat, Stream.squeezeSat] using squeezeSat

theorem squeeze_framed : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch 672 .r8 Impl.Sha3.PPC64LE.Stream.squeeze)
    (Spec.Sha3.squeezeContract PPC64LE.abi (48 + 672)) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Sha3.squeezeSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.squeezePre PPC64LE.abi.ptrBits)
    (post := Spec.Sha3.squeezePost PPC64LE.abi.ptrBits) (wa := true) (stack := 48) (bytes := 672)
    Stream.squeeze_verified (by decide) (by decide) (squeezePre_local _) (squeezePost_local _)
    squeezeSat_pre

end VG.Proof.Sha3.PPC64LE.Frame
