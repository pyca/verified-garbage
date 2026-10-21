module

public import VerifiedGarbage.Impl.Mont.X86

/-! # Retain the eleven cdecl arguments in the candidate header before nested calls -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.CandidateArgs
open VG VG.X86 VG.Impl.Mont.X86

def arg (i : Nat) : MemOp := at_ .esp (20 + 4 * i)

def copy (i : Nat) : List Instr := [.mov .eax (.mem (arg i)), .store (sc (4 * i)) .eax]

def copies : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (copies n) (.block (copy n))

/-- The shared round uses header bytes 8 and 12 for comparisons. Keep the
used-output pointer from argument 2 additionally at byte 44. -/
def saveUsed : List Instr := [.mov .eax (.mem (sc 8)), .store (sc 44) .eax]

def code : Prog isa := .seq (copies 11) (.block saveUsed)

def enter : Prog isa := .seq (.block [.mov .edi (.mem (arg 9))]) code

end VG.Impl.RsaKeyGen.X86.CandidateArgs
