module
public import VerifiedGarbage.Impl.Mont.X86.Words
import VerifiedGarbage.Impl.Mont.X86.Power

public import VerifiedGarbage.Impl.Mont.X86.Power

/-! # Secret-exponent operations on 32-bit x86 -/

@[expose] public section
namespace VG.Impl.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86

/-- Shift one little-endian word down by a bit, bringing in the next word's
low bit. The final word instead brings in zero. -/
def shiftWord (out : Nat) (last : Bool) : List Instr :=
  [.mov .eax (if last then .imm 0 else .mem (sc (out + 4))),
   .alu .and .eax (.imm 1), .shift .ror .eax 1,
   .mov .edx (.mem (sc out)), .shift .shr .edx 1,
   .alu .add .edx (.reg .eax), .store (sc out) .edx]

/-- Ascending traversal preserves each next word until its low bit is read. -/
def shiftExponent : Nat → Nat → List Instr
  | 0, _ => []
  | n + 1, out => shiftWord out (n == 0) ++ shiftExponent n (out + 4)

/-- The `k` words at `out` (`2 ≤ k`) shifted down by a bit, as
`shiftExponent`: words `0` to `k - 2` in a loop, each bringing in the next
word's low bit, then the top word, bringing in zero. -/
def shiftDown (k out : Nat) : Prog isa :=
  .seq (wordLoop (k - 1) [.mov .eax (.mem (at_ .ebp (out + 4))), .alu .and .eax (.imm 1),
    .shift .ror .eax 1, .mov .edx (.mem (at_ .ebp out)), .shift .shr .edx 1,
    .alu .add .edx (.reg .eax), .store (at_ .ebp out) .edx])
    (.block (shiftWord (out + 4 * (k - 1)) true))

/-- The low exponent bit as an all-zero or all-one mask in the workspace. -/
def exponentMask (exp mask : Nat) : List Instr :=
  [.mov .ecx (.mem (sc exp)), .alu .and .ecx (.imm 1),
   .mov .eax (.imm 0), .alu .sub .eax (.reg .ecx), .store (sc mask) .eax]

/-- Conditional product selection, using a saved secret mask. -/
def selectProduct (M : Mod) (out product mask : Nat) : Prog isa :=
  .seq (.block [.mov .ecx (.mem (sc mask))]) (selectsW (words M) out product out)

end VG.Impl.Mont.X86.Dynamic
