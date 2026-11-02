module

public import VerifiedGarbage.Impl.Mont.X86.MulRt
public import VerifiedGarbage.TCB.Code

/-! # Compact prepared Montgomery multiplication for x86 key generation

The multiplication uses the same paired-word rows as `vg_rsa_mont_mul_at`.
Its prepared workspace follows `Proof.Rsa.Mont`: arrays 2 and 3 contain the
product, and subtraction writes the result array directly after every input
has been consumed. Saving registers on the stack leaves room for the full
product in those two arrays and avoids copying the operands to another
workspace on every Miller–Rabin square.
-/

@[expose] public section
namespace VG.Impl.Mont.X86.Compact
open VG VG.X86 VG.Impl.Mont.X86

/-- Four saved registers precede cdecl's return address and arguments. -/
def arg (i : Nat) : MemOp := at_ .esp (20 + 4 * i)

/-- The multiplier is Rt's slot 20; the product starts immediately after it. -/
def accOff : Nat := 24

/-- The low word of the prepared array pointer for array j. -/
def arrayPtr (r : Reg) (j : Nat) : List Instr :=
  [.mov r (.mem (arg 0)), .mov r (.mem (at_ r (64 + 8 * j)))]

/-- The low word of the prepared array pointer selected by argument i.
The header pointers are 64-bit words; 32-bit address-space fit makes their
high words zero. -/
def operandPtr (r : Reg) (i : Nat) (t : Reg) : List Instr :=
  [.mov r (.mem (arg 0)), .mov t (.mem (arg i)), .alu .add t (.reg t),
    .alu .add t (.reg t), .alu .add t (.reg t), .alu .add r (.reg t),
    .mov r (.mem (at_ r 64))]

/-- r = 8 w, doubled k more times; t is temporary. -/
def lenTimes (r t : Reg) (k : Nat) : List Instr :=
  [.mov t (.mem (arg 0)), .mov r (.mem (at_ t 48))] ++
    List.replicate (3 + k) (.alu .add r (.reg r))

def scratchPtr : List Instr := arrayPtr .edi 2

def accPtr : List Instr := [.mov .ebp (.reg .edi), .alu .add .ebp (.imm (BitVec.ofNat 32 accOff))]

def zeroAcc : Prog isa :=
  .seq (.block (accPtr ++ lenTimes .esi .eax 1 ++ [.alu .add .esi (.imm 4), .mov .eax (.imm 0)]))
    (.loop (.block [.store (at_ .ebp 0) .eax, .alu .add .ebp (.imm 4), .alu .sub .esi (.imm 4)]) .ne)

def carryUp : List Instr := Rt.carryWords ++ lenTimes .eax .edx 0 ++ [.alu .sub .ebp (.reg .eax)]

/-- A row with the prepared pointer code selecting its multiplicand. -/
def mulRow (ptr : List Instr) : Prog isa :=
  .seq (.block ([.mov .ebx (.imm 0)] ++ ptr ++ lenTimes .esi .eax 0))
    (.seq (.loop (.block Rt.pairStep) .ne) (.block carryUp))

def loadA : List Instr := operandPtr .ecx 3 .edx ++
  [.mov .eax (.reg .ebp), .alu .sub .eax (.reg .edi), .alu .sub .eax (.imm (BitVec.ofNat 32 accOff)),
    .alu .add .eax (.reg .ecx), .mov .eax (.mem (at_ .eax 0)), .store (sc Rt.multOff) .eax]

def redDigit : List Instr :=
  [.mov .edx (.mem (arg 0)), .mov .eax (.mem (at_ .ebp 0)),
    .mov .edx (.mem (at_ .edx 56)), .mul .edx, .store (sc Rt.multOff) .eax]

def rowEnd : List Instr :=
  [.alu .add .ebp (.imm 4)] ++ lenTimes .eax .edx 0 ++
    [.alu .add .eax (.reg .edi), .alu .add .eax (.imm (BitVec.ofNat 32 accOff)), .alu .cmp .ebp (.reg .eax)]

def row : Prog isa :=
  .seq (.block loadA) <| .seq (mulRow (operandPtr .ecx 4 .edx)) <|
  .seq (.block redDigit) <| .seq (mulRow (arrayPtr .ecx 0)) (.block rowEnd)

def rows : Prog isa := .seq (.block accPtr) (.loop row .ne)

/-- The high product minus M goes directly into the result. No operand is
read afterward, so this also supports a result aliasing either operand. -/
def subM : Prog isa :=
  .seq (.block (arrayPtr .esi 0 ++ operandPtr .ebx 2 .edx ++ lenTimes .edi .eax 0 ++ [.mov .ecx (.imm 0)]))
    (.seq (.loop (.block ([.mov .eax (.mem (at_ .ebp 0))] ++ Rt.restore ++
      [.alu .sbb .eax (.mem (at_ .esi 0)), .store (at_ .ebx 0) .eax, .alu .sbb .ecx (.reg .ecx),
        .alu .add .ebp (.imm 4), .alu .add .esi (.imm 4), .alu .add .ebx (.imm 4),
        .alu .sub .edi (.imm 4)])) .ne) (.block scratchPtr))

/-- Select the subtraction when the high product with its carry is at least M. -/
def select : Prog isa :=
  .seq (.block (lenTimes .eax .edx 0 ++ [.alu .sub .ebp (.reg .eax)] ++
    operandPtr .esi 2 .edx ++ lenTimes .edi .eax 0))
    (.loop (.block [.mov .eax (.mem (at_ .ebp 0)), .mov .edx (.mem (at_ .esi 0)),
      .alu .xor .edx (.reg .eax), .alu .and .edx (.reg .ecx), .alu .xor .eax (.reg .edx),
      .store (at_ .esi 0) .eax, .alu .add .ebp (.imm 4), .alu .add .esi (.imm 4),
      .alu .sub .edi (.imm 4)]) .ne)

/-- Restore the other saved registers from the frame before its final pop. -/
def restoreRegs : List Instr :=
  [.mov .edi (.mem (at_ .esp 0)), .mov .esi (.mem (at_ .esp 4)), .mov .ebp (.mem (at_ .esp 8))]

/-- Arithmetic inside the register-saving frame. -/
def core : Prog isa :=
  .seq (.block scratchPtr) <| .seq zeroAcc <| .seq rows <| .seq subM <|
    .seq (.block Rt.mask) select

def body : Prog isa :=
  .frame (.push [.ebx, .ebp, .esi, .edi])
    (.seq core (.block restoreRegs)) (.pop .ebx 4)

end VG.Impl.Mont.X86.Compact
