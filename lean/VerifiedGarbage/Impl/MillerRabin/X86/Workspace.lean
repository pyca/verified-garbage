module

public import VerifiedGarbage.Impl.Mont.X86.MulRt
public import VerifiedGarbage.Impl.Bignum.X86.CopyBytes
public import VerifiedGarbage.Impl.Rsa.X86.KeyRt
public import VerifiedGarbage.Spec.MillerRabin

/-! # The shared compact Miller–Rabin workspace on i686

Numbers retain the shared representation of `w` 64-bit limbs, but loads
and Montgomery arithmetic operate on 32-bit words. Buffer transfers use
the existing byte-copy routine. The existing offset-based Montgomery
callable supplies every product.

Its temporary range starts 32 bytes before array 2 and ends 24 bytes
before array 5. The protected tail of array 1 and the low words of array 4
are saved on entry and restored on exit. Thus this adapter needs neither
another multiplication implementation nor a different public contract.
-/

@[expose] public section
namespace VG.Impl.MillerRabin.X86
open VG VG.X86 VG.Impl.Mont.X86

def sp (d : Nat) : MemOp := at_ .esp d

/-- Outgoing arguments, saved registers and two protected workspace ranges. -/
def frameBytes : Nat := 1132
def savedRegisters : List (Reg × Nat) := [(.ebx, 36), (.esi, 40), (.edi, 44), (.ebp, 48)]
def savedLength : Nat := 52
def tableCursor : Nat := 60
def savedTail : Nat := 64
def savedArray : Nat := 96

/-- The low half of the shared public limb-count word. -/
def width (r : Reg) : List Instr :=
  [.mov r (.mem (sc 48)), .alu .add r (.reg r), .alu .add r (.reg r), .alu .add r (.reg r)]

/-- Array `j`'s offset, with `t` its public stride. -/
def arrayOffset (r : Reg) (j : Nat) (t : Reg) : List Instr :=
  width t ++ [.alu .add t (.imm 16), .mov r (.imm 256)] ++
    List.replicate j (.alu .add r (.reg t))

def arrayPointer (r : Reg) (j : Nat) (t : Reg) : List Instr :=
  arrayOffset r j t ++ [.alu .add r (.reg .edi)]

def copy (o a : Nat) : Prog isa :=
  .seq (.block (arrayPointer .esi a .edx ++ arrayPointer .ebx o .edx ++ width .ecx))
    VG.Impl.Bignum.X86.copyBytes

def stackPointer (r : Reg) (d : Nat) : List Instr :=
  [.mov r (.reg .esp), .alu .add r (.imm (BitVec.ofNat 32 d))]

/-- The scratch offset is `arrAt w 2 - 32 = 256 + 16 w`. -/
def scratchOffset (r : Reg) : List Instr :=
  width r ++ [.alu .add r (.reg r), .alu .add r (.imm 256)]

def scratchPointer (r : Reg) : List Instr :=
  scratchOffset r ++ [.alu .add r (.reg .edi)]

/-- Save the 32 bytes borrowed from the end of array 1. -/
def saveTail : Prog isa :=
  .seq (.block (scratchPointer .esi ++ stackPointer .ebx savedTail ++ [.mov .ecx (.imm 32)]))
    VG.Impl.Bignum.X86.copyBytes

/-- Save the array-4 prefix the multiplication may overwrite. -/
def saveArray : Prog isa :=
  .seq (.block (arrayPointer .esi 4 .edx ++ stackPointer .ebx savedArray ++ width .ecx))
    VG.Impl.Bignum.X86.copyBytes

def saveProtected : Prog isa := .seq saveTail saveArray

def restoreTail : Prog isa :=
  .seq (.block (scratchPointer .ebx ++ stackPointer .esi savedTail ++ [.mov .ecx (.imm 32)]))
    VG.Impl.Bignum.X86.copyBytes

def restoreArray : Prog isa :=
  .seq (.block (arrayPointer .ebx 4 .edx ++ stackPointer .esi savedArray ++ width .ecx))
    VG.Impl.Bignum.X86.copyBytes

def restoreProtected : Prog isa := .seq restoreTail restoreArray

/-- cdecl arguments of the existing, fully reduced Montgomery product. -/
def productArgs (o a b : Nat) : List Instr :=
  [.store (sp 0) .edi, .mov .eax (.mem (sp (36 + savedLength))), .store (sp 4) .eax,
   .mov .eax (.mem (sc 48)), .store (sp 8) .eax,
   .mov .eax (.imm 256), .store (sp 12) .eax,
   .mov .eax (.imm 56), .store (sp 16) .eax] ++
  scratchOffset .eax ++ [.store (sp 20) .eax] ++
  arrayOffset .eax o .edx ++ [.store (sp 24) .eax] ++
  arrayOffset .eax a .edx ++ [.store (sp 28) .eax] ++
  arrayOffset .eax b .edx ++ [.store (sp 32) .eax]

def product (o a b : Nat) : Prog isa :=
  .frame (.alloc 36)
    (.seq (.block (productArgs o a b))
      (.call Spec.Rsa.MontMul.mulApi.name VG.Impl.Mont.X86.Rt.body))
    (.free 36)

/-- Comparisons are bits in the two halves of header word 23. -/
def equal (dst a b : Nat) : Prog isa :=
  .seq (.block (arrayPointer .ebp a .edx ++ arrayPointer .ebx b .edx ++ width .edx ++
      [.mov .ecx (.imm 0)]))
    (.seq VG.Impl.Rsa.X86.KeyRt.eqLoop
      (.block [.mov .eax (.imm 0), .alu .sub .eax (.reg .ecx), .alu .or .eax (.reg .ecx),
        .shift .shr .eax 31, .alu .xor .eax (.imm 1), .store (sc dst) .eax]))

/-- A public-address, masked selection over one full number. -/
def select (o a : Nat) : Prog isa :=
  .seq (.block (arrayPointer .ebp a .edx ++ arrayPointer .ebx o .edx ++ width .edx ++
      [.mov .ecx (.reg .esi), .mov .esi (.reg .edi), .mov .edi (.reg .edx)]))
    (.seq VG.Impl.Bignum.X86.CrtRt.selectLoop
      (.block [.mov .edi (.reg .esi)]))

end VG.Impl.MillerRabin.X86
