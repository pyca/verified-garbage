module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessRt
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Impl.Rsa.X86.KeyWs

/-! # R² and the constants at the run-time width

`PreparedR2.code w` and `Constants.code w` for the width at header byte 48,
every array through its header pointer. R² starts at the candidate's top
bit, `2^(64 w − 1)` in array 6, doubled `w + 1` times modulo the candidate
(array 0) to `2^w R`, then squared six times. A doubling sums into array 2
with its carry above it, subtracts the candidate into array 6 and selects
the sum where it was below the candidate. Its loops take `edi` for a pointer
or a count, so the doublings run in a frame that keeps the workspace pointer.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.PrepareRt
open VG VG.X86 VG.Impl.Mont.X86
open VG.Impl.MillerRabin.X86 (ptr mulY copy)
open VG.Impl.RsaKeyGen.X86.WitnessRt (draw)

/-- `ebp` at array 6, `ecx` its octets and `eax` zero. -/
def zeroArgs : List Instr := ptr .ebp 6 ++ draw ++ [.mov .ecx (.reg .edx), .mov .eax (.imm 0)]

def zeroLoop : Prog isa :=
  .loop (.block [.store (at_ .ebp 0) .eax, .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 4)]) .ne

/-- Array 6 zeroed. -/
def zero : Prog isa := .seq (.block zeroArgs) zeroLoop

/-- Array 6's top bit set. -/
def top : List Instr :=
  ptr .ebp 6 ++ draw ++ [.alu .add .ebp (.reg .edx), .alu .sub .ebp (.imm 4),
    .mov .eax (.imm 0x80000000), .store (at_ .ebp 0) .eax]

/-- `2^(64 w − 1)` in array 6. -/
def seed : Prog isa := .seq zero (.block top)

/-- `ebx` at array 6, `ebp` at array 2, `edx` their octets and no carry. -/
def doubleArgs : List Instr := ptr .ebx 6 ++ ptr .ebp 2 ++ draw ++ [.mov .ecx (.imm 0)]

/-- `[ebp] := 2 [ebx]`, `edx` octets, the carry a mask in `ecx`
(`PublicRt.double`'s). -/
def doubleLoop : Prog isa :=
  .loop (.block [.mov .eax (.mem (at_ .ebx 0)), .alu .add .ecx (.reg .ecx),
    .alu .adc .eax (.reg .eax), .store (at_ .ebp 0) .eax, .alu .sbb .ecx (.reg .ecx),
    .alu .add .ebx (.imm 4), .alu .add .ebp (.imm 4), .alu .sub .edx (.imm 4)]) .ne

/-- The carry, a word above the sum. -/
def carry : List Instr := [.mov .eax (.imm 0), .alu .sub .eax (.reg .ecx), .store (at_ .ebp 0) .eax]

/-- `ebp` at the sum (array 2), `ebx` at the candidate, `edi` at array 6. -/
def reduceArgs : List Instr :=
  ptr .ebp 2 ++ ptr .ebx 0 ++ ptr .eax 6 ++ draw ++ [.mov .edi (.reg .eax), .mov .ecx (.imm 0)]

/-- `[edi] := [ebp] − [ebx]`, the borrow a mask in `ecx` (`PublicRt.reduce`'s). -/
def reduceLoop : Prog isa :=
  .loop (.block [.mov .eax (.mem (at_ .ebp 0)), .alu .add .ecx (.reg .ecx),
    .alu .sbb .eax (.mem (at_ .ebx 0)), .store (at_ .edi 0) .eax, .alu .sbb .ecx (.reg .ecx),
    .alu .add .ebp (.imm 4), .alu .add .ebx (.imm 4), .alu .add .edi (.imm 4),
    .alu .sub .edx (.imm 4)]) .ne

/-- `ecx` all ones when the sum with its carry is below the candidate. -/
def below : List Instr :=
  [.mov .eax (.mem (at_ .ebp 0)), .alu .add .ecx (.reg .ecx), .alu .sbb .eax (.imm 0),
    .alu .sbb .eax (.reg .eax), .mov .ecx (.reg .eax), .mov .edi (.mem (at_ .esp 0))]

/-- `ebp` at the sum, `ebx` at array 6, `edi` their octets. -/
def selectArgs : List Instr := ptr .ebp 2 ++ ptr .ebx 6 ++ draw ++ [.mov .edi (.reg .edx)]

/-- `[ebx] := [ebp]` where `ecx` is all ones (`PublicRt.select`'s). -/
def selectLoop : Prog isa :=
  .loop (.block [.mov .eax (.mem (at_ .ebx 0)), .mov .edx (.mem (at_ .ebp 0)),
    .alu .xor .edx (.reg .eax), .alu .and .edx (.reg .ecx), .alu .xor .eax (.reg .edx),
    .store (at_ .ebx 0) .eax, .alu .add .ebp (.imm 4), .alu .add .ebx (.imm 4),
    .alu .sub .edi (.imm 4)]) .ne

/-- The workspace pointer back, and one doubling fewer left. -/
def next : List Instr := [.mov .edi (.mem (at_ .esp 0)), .alu .sub .esi (.imm 1)]

/-- `2 [6]` in array 2, its carry above it. -/
def sum : Prog isa := .seq (.block doubleArgs) (.seq doubleLoop (.block carry))

/-- The sum less the candidate in array 6. -/
def reduce : Prog isa := .seq (.block reduceArgs) reduceLoop

/-- The sum in array 6 where it was below the candidate, and the next doubling. -/
def select : Prog isa := .seq (.block selectArgs) (.seq selectLoop (.block next))

/-- Array 6 doubled modulo the candidate. -/
def double : Prog isa := .seq sum (.seq reduce (.seq (.block below) select))

/-- The workspace pointer saved, and `w + 1` doublings to do. -/
def doublesArgs : List Instr :=
  [.store (at_ .esp 0) .edi, .mov .esi (.mem (sc 48)), .alu .add .esi (.imm 1)]

/-- `2^w R` in array 6. -/
def doubles : Prog isa :=
  .frame (.alloc 20) (.seq (.block doublesArgs) (.loop double .ne)) (.free 20)

/-- `PreparedR2.code w`: R² in array 4. -/
def r2 (montName : String) (montCode : Prog isa) : Prog isa :=
  .seq (.seq seed (.seq doubles (VG.Impl.Rsa.X86.Keys.seqs (List.replicate 6 (mulY montName montCode 6)))))
    (copy 4 6)

/-- One in array 6. -/
def one : Prog isa := .seq zero (.block (ptr .ebp 6 ++ [.mov .eax (.imm 1), .store (at_ .ebp 0) .eax]))

/-- `edi` at array 10, `ebp` at the candidate, `ebx` at array 9. -/
def subtractArgs : List Instr :=
  [.store (at_ .esp 0) .edi] ++ ptr .ebp 0 ++ ptr .ebx 9 ++ ptr .eax 10 ++ draw ++
    [.mov .edi (.reg .eax), .mov .ecx (.imm 0)]

/-- `[10] := [0] − [9]`, in a frame that keeps the workspace pointer. -/
def subtract : Prog isa :=
  .frame (.alloc 20) (.seq (.block subtractArgs) (.seq reduceLoop (.block [.mov .edi (.mem (at_ .esp 0))])))
    (.free 20)

/-- `Constants.code w`: `R mod c` in array 9 and `c − R mod c` in array 10. -/
def constants (montName : String) (montCode : Prog isa) : Prog isa :=
  .seq one (.seq (mulY montName montCode 4) (.seq (copy 9 6) subtract))

end VG.Impl.RsaKeyGen.X86.PrepareRt
