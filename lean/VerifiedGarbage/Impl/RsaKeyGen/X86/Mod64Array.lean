module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Word

/-! # Reduce a candidate-sized native array by the public exponent

The caller owns a 20-byte frame at ESP. Its first two words hold the
descending source pointer and the remaining word count. Each word's bits
execute as a fixed sequence; only the public array count controls a loop.
The workspace and exponent are read-only.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Mod64
open VG VG.X86

def stack (d : Nat) : MemOp := ⟨.esp, d⟩

def zeroRemainder : List Instr := [.mov .ecx (.imm 0), .mov .ebx (.imm 0)]

def loadWord : List Instr := [.mov .eax (.mem (stack 0)), .mov .esi (.mem ⟨.eax, 0⟩)]

def previousWord : List Instr :=
  [.mov .eax (.mem (stack 0)), .alu .sub .eax (.imm 4), .store (stack 0) .eax]

def countDown : List Instr :=
  [.mov .eax (.mem (stack 4)), .alu .sub .eax (.imm 1), .store (stack 4) .eax, .alu .cmp .eax (.imm 0)]

def advance : List Instr := previousWord ++ countDown

def arrayStep (exponent : Nat) : Prog isa :=
  .seq (.block loadWord) (.seq (.block (word exponent)) (.block advance))

end VG.Impl.RsaKeyGen.X86.Mod64
