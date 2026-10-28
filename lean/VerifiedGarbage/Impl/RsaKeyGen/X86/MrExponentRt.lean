module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Exponent
public import VerifiedGarbage.Impl.MillerRabin.X86.Ops

/-! # Miller–Rabin's exponent prepared at the run-time width

The same exponent and marker as `Exponent.code w (slot w 5) (slot w 0)
(slot w 27)`, read through the prepared header's pointers and width: the
marker from the first nonzero pair of array 5, then array 0 copied into
array 27 and halved there in place, once and then where the marker asks.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.MrExponentRt
open VG VG.X86 VG.Impl.Mont.X86
open VG.Impl.MillerRabin.X86 (ptr copy aExponent)

/-- The next pair at `ebp` into `ebx:esi` if those are still zero; `edi`
counts the pairs. -/
def pairStep : List Instr :=
  [.mov .eax (.mem (at_ .ebp 0)), .mov .ecx (.mem (at_ .ebp 4))] ++ LowPair.choose ++
    [.alu .add .ebp (.imm 8), .alu .sub .edi (.imm 1)]

/-- `ebp` at array 5 and `edi` its `w` pairs, the workspace pointer saved
below them. -/
def scanSetup : List Instr :=
  [.mov .ebx (.imm 0), .mov .esi (.imm 0)] ++ ptr .ebp 5 ++
    [.mov .edx (.mem (sc 48)), .store (at_ .esp 0) .edi, .mov .edi (.reg .edx)]

/-- `ebx:esi`, the first nonzero pair of array 5. -/
def scan : Prog isa :=
  .frame (.alloc 20)
    (.seq (.block scanSetup) (.seq (.loop (.block pairStep) .ne) (.block [.mov .edi (.mem (at_ .esp 0))])))
    (.free 20)

/-- The marker, `x & -x` of the pair, at header byte 136. -/
def marker : Prog isa := .seq scan (.block (LowBit.code ++ Exponent.saveMarker))

/-- Array 0 into array 27, the word above each zeroed, and the mask `ecx`
of a halving. -/
def copyTops : Prog isa :=
  .seq (copy aExponent 0) (.block [.mov .eax (.imm 0), .store (at_ .ebx 0) .eax, .store (at_ .ebp 0) .eax,
    .mov .ecx (.imm (BitVec.allOnes 32))])

/-- One word of a pass: the word at `ebp` halved, with the next word's low
bit, where the mask `ecx` is all ones. -/
def halfStep : List Instr := HalfPass.step 0 0 ++ [.alu .add .ebp (.imm 4), .alu .sub .esi (.imm 1)]

/-- Array 27 halved in place where the mask `ecx` is all ones; `ebp` ends on
the word above it. -/
def half : Prog isa := .seq (.block (ptr .ebp aExponent ++ VG.Impl.MillerRabin.X86.words)) (.loop (.block halfStep) .ne)

def halfIf (j : Nat) : Prog isa := .seq (.block (SigMask.code Exponent.markerOffset j)) half

/-- The marker above the exponent, at `ebp`. -/
def finish : List Instr :=
  [.mov .eax (.mem (sc Exponent.markerOffset)), .mov .edx (.mem (sc (Exponent.markerOffset + 4))),
    .store (at_ .ebp 0) .eax, .store (at_ .ebp 4) .edx]

def code : Prog isa :=
  .seq marker (.seq copyTops (.seq half (.seq (halfIf 1) (.seq (halfIf 2) (.seq (halfIf 3) (.block finish))))))

end VG.Impl.RsaKeyGen.X86.MrExponentRt
