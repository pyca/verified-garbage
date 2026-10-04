import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Squeeze
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/-!
# The SHA-3 sponge on x86-64, with its working space on the stack

`absorb`, `pad` and `squeeze` run their code, proved with the working space
as an argument (`Stream/`), in a frame of 648 bytes that allocates it
(`Verified.stackScratch`): the 640 bytes of working space, and 8 more to
keep `rsp` aligned. Their call of the permutation uses 8 bytes below it, as
before.
-/

namespace VG.Proof.Sha3.X86_64.Frame

open VG VG.X86_64

/-- A state satisfying `vg_keccak_absorb`'s precondition, without the
working space. -/
def absorbSat : State := { Stream.Absorb.sat with wr := [⟨0x1000, 200⟩] }

theorem absorbSat_pre : ∃ s, (Spec.Sha3.absorbContract X86_64.abi 656).pre s := by
  implies_sat [Spec.Sha3.absorbContract, Spec.Sha3.absorbSig, Spec.Sha3.absorbPre,
    Spec.Sha3.absorbPost, Spec.Sha3.rates, X86_64.abi, X86_64.argRegs]
    [absorbSat, Stream.Absorb.sat] using absorbSat

theorem absorb_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 648 .r9 Impl.Sha3.X86_64.Stream.absorb)
      (Spec.Sha3.absorbContract X86_64.abi 656) :=
  X86_64.Verified.stackScratch (sig := Spec.Sha3.absorbSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.absorbPre X86_64.abi.ptrBits)
    (post := Spec.Sha3.absorbPost X86_64.abi.ptrBits) (wa := true) (stack := 8) (bytes := 648)
    Stream.Absorb.absorb_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) absorbSat_pre

/-- A state satisfying `vg_keccak_pad`'s precondition, without the working
space. -/
def padSat : State := { Stream.Pad.sat with wr := [⟨0x1000, 200⟩] }

theorem padSat_pre : ∃ s, (Spec.Sha3.padContract X86_64.abi 656).pre s := by
  implies_sat [Spec.Sha3.padContract, Spec.Sha3.padSig, Spec.Sha3.padPre, Spec.Sha3.padPost,
    Spec.Sha3.rates, X86_64.abi, X86_64.argRegs] [padSat, Stream.Pad.sat] using padSat

theorem pad_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 648 .r8 Impl.Sha3.X86_64.Stream.pad)
      (Spec.Sha3.padContract X86_64.abi 656) :=
  X86_64.Verified.stackScratch (sig := Spec.Sha3.padSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.padPre X86_64.abi.ptrBits) (post := Spec.Sha3.padPost X86_64.abi.ptrBits)
    (wa := true) (stack := 8) (bytes := 648) Stream.Pad.pad_verified (by decide) (by decide)
    (by decide) (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) padSat_pre

/-- A state satisfying `vg_keccak_squeeze`'s precondition, without the
working space. -/
def squeezeSat : State := { Stream.Squeeze.sat with wr := [⟨0x1000, 200⟩, ⟨0x2000, 16⟩] }

theorem squeezeSat_pre : ∃ s, (Spec.Sha3.squeezeContract X86_64.abi 656).pre s := by
  implies_sat [Spec.Sha3.squeezeContract, Spec.Sha3.squeezeSig, Spec.Sha3.squeezePre,
    Spec.Sha3.squeezePost, Spec.Sha3.rates, X86_64.abi, X86_64.argRegs]
    [squeezeSat, Stream.Squeeze.sat] using squeezeSat

theorem squeeze_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 648 .r9 Impl.Sha3.X86_64.Stream.squeeze)
      (Spec.Sha3.squeezeContract X86_64.abi 656) :=
  X86_64.Verified.stackScratch (sig := Spec.Sha3.squeezeSig) (nm := "scratch") (e := .u64)
    (n := 80) (pre := Spec.Sha3.squeezePre X86_64.abi.ptrBits)
    (post := Spec.Sha3.squeezePost X86_64.abi.ptrBits) (wa := true) (stack := 8) (bytes := 648)
    Stream.Squeeze.squeeze_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) squeezeSat_pre

end VG.Proof.Sha3.X86_64.Frame
