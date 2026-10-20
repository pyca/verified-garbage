module

public import VerifiedGarbage.Impl.Mont.X86.Words

/-! # Fixed-schedule long division for i686 RSA key operations

Arrays contain native 32-bit words at fixed offsets from EDI. The quotient
has `n` words; remainder, divisor, and temporary have `n + 1`. The divisor's
extra word is zero. ESI counts the public `32 * n` iterations. EBX carries
one bit between the shifts and the quotient update.
-/

@[expose] public section
namespace VG.Impl.Rsa.X86.Div
open VG VG.X86 VG.Impl.Mont.X86
open VG.Impl.Mont.X86.Dynamic

def copyWords (n src dst : Nat) : Prog isa :=
  .seq (.block [.mov .ecx (.imm 0)]) (selectsW n src src dst)

/-- Shift left through a separate temporary. Optionally save the top bit in EBX. -/
def shift (n dst tmp : Nat) (saveCarry : Bool) : Prog isa :=
  .seq (chainW .adc n tmp dst dst)
    (.seq (.block (if saveCarry then [.mov .ebx (.reg .ecx), .alu .and .ebx (.imm 1)] else []))
      (copyWords n tmp dst))

/-- Insert EBX's bit into the even low word of the shifted array. -/
def insertBit (dst : Nat) : List Instr :=
  [.mov .eax (.mem (sc dst)), .alu .add .eax (.reg .ebx), .store (sc dst) .eax]

def selectMask : List Instr :=
  [.mov .ebx (.reg .ecx), .alu .xor .ebx (.imm (-1)), .alu .and .ebx (.imm 1),
    .alu .xor .ecx (.imm (-1))]

def reduce (n rem divisor tmp : Nat) : Prog isa :=
  .seq (chainW .sbb (n + 1) tmp rem divisor)
    (.seq (.block selectMask) (selectsW (n + 1) rem tmp rem))

def shiftArrays (n quotient rem tmp : Nat) : Prog isa :=
  .seq (shift n quotient tmp true)
    (.seq (shift (n + 1) rem tmp false) (.block (insertBit rem)))

def step (n quotient rem divisor tmp : Nat) : Prog isa :=
  .seq (shiftArrays n quotient rem tmp)
    (.seq (reduce n rem divisor tmp)
      (.block (insertBit quotient ++ [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)])))

/-- Division runs to completion even for a zero divisor, with the same schedule. -/
def code (n quotient rem divisor tmp : Nat) : Prog isa :=
  .seq (.seq (zerosW rem (n + 1))
    (.block [.mov .esi (.imm (BitVec.ofNat 32 (32 * n)))]))
    (.loop (step n quotient rem divisor tmp) .ne)
end VG.Impl.Rsa.X86.Div
