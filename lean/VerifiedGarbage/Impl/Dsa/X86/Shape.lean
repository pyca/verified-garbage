module

public import VerifiedGarbage.Impl.Dsa.X86.Width
public import VerifiedGarbage.Impl.Dsa.X86.Core

/-! # Public DSA domain shape checks before arithmetic initialization

Recognize supported actual p/q bit lengths, even when their byte buffers
have leading zero padding. Only public values control the digest-prefix
selection and the caller's early rejection of invalid domain shapes.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86.Shape
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

/-- Six temporary masks occupy the reserved context header. -/
def saveWidth (n bits offset : Nat) : Prog isa :=
  .seq (optionalWidth n (slot n 0) (slot n 8) bits) (.block [.store (sc offset) .edx])

def threeWidths (n a b c output : Nat) : Prog isa :=
  .seq (saveWidth n a output) (.seq (saveWidth n b (output + 4)) (saveWidth n c (output + 8)))

def loadWidths (len : Nat) (modulus : VG.Impl.Dsa.Layout.Field) (a b c output : Nat) : Prog isa :=
  let n := (len + 7) / 8
  .seq (Core.load n len (slot n 0) (.input modulus)) (threeWidths n a b c output)

def saveParity (n : Nat) : List Instr :=
  [.mov .eax (.mem (sc (slot n 0))), .store (sc 56) .eax]

def combine : List Instr :=
  [.mov .eax (.mem (sc 32)), .alu .and .eax (.mem (sc 44)),
    .mov .ebx (.mem (sc 48)), .alu .or .ebx (.mem (sc 44)), .alu .or .ebx (.mem (sc 52)), .alu .and .ebx (.mem (sc 36)),
    .alu .or .eax (.reg .ebx), .mov .ebx (.mem (sc 40)), .alu .and .ebx (.mem (sc 52)),
    .alu .or .eax (.reg .ebx), .alu .and .eax (.mem (sc 56)),
    .store (sc (Layout.field .mask)) .eax]

/-- The input oddness bits are combined into an all-ones/zero mask. -/
def parity (qN : Nat) : List Instr :=
  [.mov .edx (.mem (sc (slot qN 0))), .alu .and .edx (.mem (sc 56)),
    .alu .and .edx (.imm 1), .mov .eax (.imm 0), .alu .sub .eax (.reg .edx),
    .store (sc 56) .eax]

/-- Select the actual subgroup byte width and clamp the digest length.
The three width masks are mutually exclusive. -/
def prefixWidth : List Instr := [
  .mov .eax (.mem (sc 44)), .alu .and .eax (.imm 20),
  .mov .edx (.mem (sc 48)), .alu .and .edx (.imm 28), .alu .or .edx (.reg .eax),
  .mov .eax (.mem (sc 52)), .alu .and .eax (.imm 32), .alu .or .edx (.reg .eax)]

def digestClamp : List Instr := [
  .mov .eax (.mem (sc (Layout.field .digestLen))),
  .alu .cmp .eax (.reg .edx), .alu .sbb .ebx (.reg .ebx),
  .alu .xor .eax (.reg .edx), .alu .and .eax (.reg .ebx), .alu .xor .edx (.reg .eax),
  .store (sc (Layout.field .digestPrefixLen)) .edx]

def digestPrefix : Prog isa := .block (prefixWidth ++ digestClamp)

def inspectP (pLen : Nat) : Prog isa :=
  .seq (loadWidths pLen .p 1024 2048 3072 32) (.block (saveParity ((pLen + 7) / 8)))

def inspectQ (qLen : Nat) : Prog isa :=
  .seq (loadWidths qLen .q 160 224 256 44) (.block (parity ((qLen + 7) / 8) ++ combine))

def check (pLen qLen : Nat) : Prog isa := Core.sequence [
  inspectP pLen, inspectQ qLen, digestPrefix,
  .block [.mov .eax (.mem (sc (Layout.field .mask))), .alu .cmp .eax (.imm 0)]]

end VG.Impl.Dsa.X86.Shape
