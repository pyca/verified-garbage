module

public import VerifiedGarbage.Impl.Rsa.X86.Div
public import VerifiedGarbage.Impl.Mont.X86.Exponent

/-! # Fixed-offset arrays and scalar slots for i686 RSA key operations

EDI holds the workspace base. Each array has `n` native words plus two
extra words. EBX holds a carry or borrow bit; ESI is reserved for the
outer iteration count. Array selections use masks derived from scalar
slots, so their addresses never depend on the selected value.
-/

@[expose] public section
namespace VG.Impl.Rsa.X86.Keys
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | [c] => c
  | c :: cs => .seq c (seqs cs)

def hdr : Nat := 160
def stride (n : Nat) : Nat := 4 * (n + 2)
def slot (n j : Nat) : Nat := hdr + j * stride n

def sOdd : Nat := 100
def sB : Nat := 104
def sC : Nat := 108
def sT : Nat := 112

def sub3 (n o a b : Nat) : Prog isa :=
  .seq (chainW .sbb n (slot n o) (slot n a) (slot n b))
    (.block [.mov .ebx (.reg .ecx), .alu .and .ebx (.imm 1)])

def sel (n o a b sl : Nat) : Prog isa :=
  .seq (.block [.mov .ecx (.imm 0), .alu .sub .ecx (.mem (sc sl))])
    (selectsW n (slot n a) (slot n b) (slot n o))

def copy (n o a : Nat) : Prog isa := Div.copyWords n (slot n a) (slot n o)

def half (n j : Nat) : Prog isa :=
  .block ([.store (sc (slot n j + 4 * n)) .ebx] ++ Dynamic.shiftExponent (n + 1) (slot n j))

def bitOf (n sl j : Nat) : List Instr :=
  [.mov .eax (.mem (sc (slot n j))), .alu .and .eax (.imm 1), .store (sc sl) .eax]

def andS (d a b : Nat) : List Instr :=
  [.mov .eax (.mem (sc a)), .alu .and .eax (.mem (sc b)), .store (sc d) .eax]

def setOne (n j : Nat) : List Instr := [.mov .eax (.imm 1), .store (sc (slot n j)) .eax]

def orOne (n j : Nat) : List Instr :=
  [.mov .eax (.mem (sc (slot n j))), .alu .or .eax (.imm 1), .store (sc (slot n j)) .eax]

def clrLow (n j : Nat) : List Instr :=
  [.mov .eax (.mem (sc (slot n j))), .alu .or .eax (.imm 1), .alu .xor .eax (.imm 1),
    .store (sc (slot n j)) .eax]

def eqS (n d a b t : Nat) : Prog isa :=
  .seq (sub3 n t a b) (.seq (.block [.store (sc sT) .ebx]) (.seq (sub3 n t b a)
    (.block [.alu .or .ebx (.mem (sc sT)), .alu .xor .ebx (.imm 1), .store (sc d) .ebx])))
end VG.Impl.Rsa.X86.Keys
