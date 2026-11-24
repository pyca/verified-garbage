module

public import VerifiedGarbage.Impl.Aes.X86.Linear

/-!
# Instructions, entry and exit of functions in general registers, on x86 (32-bit)

Short forms of instructions, and the prologue and epilogue of the functions
whose scratch buffer, at `edi`, holds a bitsliced state and the S-box's
spill slots in `[0, 256)` (`Linear.lean`, `Sbox.lean`) and the saved
registers in `[256, 272)`: AES's key expansion (`ExpandKey.lean`), and other
ciphers' kernels.
-/

@[expose] public section

namespace VG.Impl.Aes.X86

open VG.X86

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- Argument `i` on entry (cdecl). -/
def argOp (i : Nat) : MemOp := at_ .esp (4 + 4 * i)

def movI (d : Reg) (v : BitVec 32) : Instr := .mov d (.imm v)
def addI (d : Reg) (v : BitVec 32) : Instr := .alu .add d (.imm v)
def subI (d : Reg) (v : BitVec 32) : Instr := .alu .sub d (.imm v)
def addR (d s : Reg) : Instr := .alu .add d (.reg s)
def subR (d s : Reg) : Instr := .alu .sub d (.reg s)

/-- The callee-saved registers, and their offsets in the scratch buffer. -/
def savedRegs : List (Reg × Nat) := [(.ebx, 256), (.esi, 260), (.edi, 264), (.ebp, 268)]

/-- Load the scratch pointer (argument `k`) into `edi`, saving the registers. -/
def saveRegs (k : Nat) : List Instr :=
  ([.mov .eax (.mem (argOp k))] : List Instr) ++ savedRegs.map (fun (r, d) => .store (at_ .eax d) r) ++
    [movR .edi .eax]

/-- Restore the registers (`edi`, the base, last). -/
def restoreRegs : List Instr :=
  [.mov .ebx (.mem (at_ .edi 256)), .mov .esi (.mem (at_ .edi 260)), .mov .ebp (.mem (at_ .edi 268)),
   .mov .edi (.mem (at_ .edi 264))]

/-- `d := 2ᵏ d`. -/
def dbl (d : Reg) (k : Nat) : List Instr := (List.range k).map fun _ => addR d d

end VG.Impl.Aes.X86
