import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch

/-!
# The SHA-3 sponge on AArch64, with its working space on the stack

`absorb`, `pad` and `squeeze`, with any implementation of the permutation,
run their code, proved with the working space as an argument (`Stream/`), in
a frame of 640 bytes that allocates it (`Verified.stackScratch`).
-/

namespace VG.Proof.Sha3.AArch64.Frame

open VG VG.AArch64

/-- A state satisfying `vg_keccak_absorb`'s precondition, without the
working space: the state at `0x1000`, rate 72 and no data at `0x2000`. -/
def absorbSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 72 | .x3 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 200⟩]

theorem absorbSat_pre : ∃ s, (Spec.Sha3.absorbContract AArch64.abi 656).pre s := by
  implies_sat [Spec.Sha3.absorbContract, Spec.Sha3.absorbSig, Spec.Sha3.absorbPre,
    Spec.Sha3.absorbPost, Spec.Sha3.rates, AArch64.abi, AArch64.argRegs] [absorbSat]
    using absorbSat

theorem absorb_framed (v : Permutation) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch 640 .x5
        (Impl.Sha3.AArch64.Stream.absorbWith v.callee))
      (Spec.Sha3.absorbContract AArch64.abi 656) :=
  AArch64.Verified.stackScratch (sig := Spec.Sha3.absorbSig) (nm := "scratch") (e := .u64)
    (n := 80) (pre := Spec.Sha3.absorbPre AArch64.abi.ptrBits)
    (post := Spec.Sha3.absorbPost AArch64.abi.ptrBits) (wa := true) (stack := 16) (bytes := 640)
    (Stream.Absorb.absorb_verified v) (by decide) (by decide) absorbSat_pre

/-- A state satisfying `vg_keccak_pad`'s precondition, without the working
space: the state at `0x1000` and rate 136. -/
def padSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 136 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩]

theorem padSat_pre : ∃ s, (Spec.Sha3.padContract AArch64.abi 656).pre s := by
  implies_sat [Spec.Sha3.padContract, Spec.Sha3.padSig, Spec.Sha3.padPre, Spec.Sha3.padPost,
    Spec.Sha3.rates, AArch64.abi, AArch64.argRegs] [padSat] using padSat

theorem pad_framed (v : Permutation) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch 640 .x4
        (Impl.Sha3.AArch64.Stream.padWith v.callee))
      (Spec.Sha3.padContract AArch64.abi 656) :=
  AArch64.Verified.stackScratch (sig := Spec.Sha3.padSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.padPre AArch64.abi.ptrBits) (post := Spec.Sha3.padPost AArch64.abi.ptrBits)
    (wa := true) (stack := 16) (bytes := 640) (Stream.Pad.pad_verified v) (by decide) (by decide)
    padSat_pre

/-- A state satisfying `vg_keccak_squeeze`'s precondition, without the
working space: the state at `0x1000`, rate 72 and no output at `0x2000`. -/
def squeezeSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 72 | .x3 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 0⟩]

theorem squeezeSat_pre : ∃ s, (Spec.Sha3.squeezeContract AArch64.abi 656).pre s := by
  implies_sat [Spec.Sha3.squeezeContract, Spec.Sha3.squeezeSig, Spec.Sha3.squeezePre,
    Spec.Sha3.squeezePost, Spec.Sha3.rates, AArch64.abi, AArch64.argRegs] [squeezeSat]
    using squeezeSat

theorem squeeze_framed (v : Permutation) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch 640 .x5
        (Impl.Sha3.AArch64.Stream.squeezeWith v.callee))
      (Spec.Sha3.squeezeContract AArch64.abi 656) :=
  AArch64.Verified.stackScratch (sig := Spec.Sha3.squeezeSig) (nm := "scratch") (e := .u64)
    (n := 80) (pre := Spec.Sha3.squeezePre AArch64.abi.ptrBits)
    (post := Spec.Sha3.squeezePost AArch64.abi.ptrBits) (wa := true) (stack := 16) (bytes := 640)
    (Stream.Squeeze.squeeze_verified v) (by decide) (by decide) squeezeSat_pre

end VG.Proof.Sha3.AArch64.Frame
