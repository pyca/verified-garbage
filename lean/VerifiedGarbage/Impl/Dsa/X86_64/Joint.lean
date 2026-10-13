module

public import VerifiedGarbage.Impl.Dsa.X86_64.Arithmetic
public import VerifiedGarbage.Impl.Dsa.Layout

/-! # Joint two-bit exponentiation for DSA verification

A sixteen-entry table contains g^i y^j R for i,j < 4. Each window
squares the accumulator twice and multiplies by a constant-time selection.
The workspace and selected Montgomery backend are shared with RSA.
-/

@[expose] public section

namespace VG.Impl.Dsa.X86_64.Joint
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64

/-- Both exponent pointers are public. -/
def sExp2 : Nat := Crt.sRem

/-- The two bytes are packed into sV. Their next two-bit digits form
one four-bit table index; shifting by two advances both digits. -/
def windowIndex : List Instr := [
  .mov .rax (.mem (hdr Crt.sV)), .mov .rdx (.reg .rax), .mov .rcx (.reg .rax),
  .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .store (hdr Crt.sV) .rax,
  .shift .shr .rdx 14, .alu .and .rdx (.imm 3),
  .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx),
  .shift .shr .rcx 6, .alu .and .rcx (.imm 3),
  .alu .add .rdx (.reg .rcx), .store (hdr Crt.sNib) .rdx]

def window (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  mul aY aY aY, mul aY aY aY, .block windowIndex,
  seqs Crt.tabSelect, mul aY aY Crt.aT,
  .block [.mov .rax (.mem (hdr Crt.sBit)), .alu .sub .rax (.imm 1), .store (hdr Crt.sBit) .rax]]

def bytePointers : List Instr := [
  .mov .rcx (.mem (hdr Crt.sI)), .mov .rax (.mem (hdr Crt.sExp)),
  .mov .rsi (.mem (hdr sExp2))]

def byteValues : List Instr := [
  .movzx8 .rdx { base := .rax, index := some .rcx }, .shift .shl .rdx 8,
  .movzx8 .rax { base := .rsi, index := some .rcx },
  .alu .add .rax (.reg .rdx), .store (hdr Crt.sV) .rax, .mov32 .rax (.imm 4), .store (hdr Crt.sBit) .rax]

def byteHead : List Instr := bytePointers ++ byteValues

def bytes (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .loop (seqs [.block byteHead, .loop (window mul) .ne,
    .block [.mov .rax (.mem (hdr Crt.sI)), .alu .add .rax (.imm 1), .store (hdr Crt.sI) .rax,
      .alu .cmp .rax (.mem (hdr Crt.sExpLen))]]) .ne

/-- Store the current g^i y^j entry, advance, and prepare the next entry.
The row/column choice is resolved while constructing the instruction list. -/
def advance (mul : Nat → Nat → Nat → Prog isa) (j : Nat) : Prog isa :=
  if j % 4 = 3 then .seq (mul aX aX aR2) (seqs (Crt.copyArr aY aX))
  else mul aY aY aXm

def buildStep (mul : Nat → Nat → Nat → Prog isa) (j : Nat) : Prog isa :=
  .seq (.seq (seqs (Crt.toEnt aY)) Crt.nextEnt) (advance mul j)

def buildSteps (mul : Nat → Nat → Nat → Prog isa) : Nat → Nat → Prog isa
  | _, 0 => .block []
  | j, count + 1 => .seq (buildStep mul j) (buildSteps mul (j + 1) count)

/-- Inputs: gR in aR2, yR in aXm, R in aX/aY/aOne. The ordinary
one is restored after the table and accumulator have been initialized. -/
def tableInit : List Instr := [.mov .rax (.mem (hdr (sArr aOne))), .mov .rdx (.mem (hdr sW)), .alu .add .rdx (.imm 2),
    .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx),
    .alu .add .rax (.reg .rdx), .store (hdr Crt.sTab) .rax, .store (hdr Crt.sEnt) .rax]

def build (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block tableInit,
  buildSteps mul 0 16, seqs (Crt.copyArr aY aOne), Arithmetic.small aOne 1]

/-- Encode both ordinary bases before reusing R²'s array for gR. -/
def encode (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  mul aY aR2 aOne, mul aX aX aR2, mul aXm aXm aR2,
  seqs (Crt.copyArr aR2 aX), seqs (Crt.copyArr aOne aY), seqs (Crt.copyArr aX aY)]

/-- Verification's two scalar buffers have the same public byte length. -/
def expInit : List Instr := [
  .mov .rax (.mem (hdr Crt.sLink)),
  .mov .rcx (.mem { base := .rax, disp := VG.Impl.Dsa.Layout.Field.qLen.offset }),
  .mov .rdx (.reg .rax),
  .alu .add .rdx (.imm (BitVec.ofNat 32 VG.Impl.Dsa.Layout.u)), .store (hdr Crt.sExp) .rdx,
  .mov .rdx (.reg .rax), .alu .add .rdx (.imm (BitVec.ofNat 32 VG.Impl.Dsa.Layout.v)),
  .store (hdr sExp2) .rdx,
  .store (hdr Crt.sExpLen) .rcx, .mov32 .rdx (.imm 0), .store (hdr Crt.sI) .rdx]

/-- Load and encode both bases, then construct the joint table. -/
def prepare (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  Arithmetic.constants mul,
  Arithmetic.load aX VG.Impl.Dsa.Layout.arg VG.Impl.Dsa.Layout.argLen,
  Arithmetic.load aXm VG.Impl.Dsa.Layout.arg2 VG.Impl.Dsa.Layout.arg2Len,
  encode mul, build mul]

/-- Consume the two scalar buffers and decode the result. -/
def run (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  seqs [.block expInit, bytes mul, mul aY aY aOne]

/-- Two bases in the parent call header, and verification's u/v scalars. -/
def power (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (prepare mul) (run mul)

end VG.Impl.Dsa.X86_64.Joint
