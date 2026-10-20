module

public import VerifiedGarbage.Impl.Dsa.Arm.Core

/-! # Public DSA domain shape checks before arithmetic initialization

Recognize supported actual p/q bit lengths, even when their byte buffers
have leading zero padding. Only public values control the digest-prefix
selection and the caller's early rejection of invalid domain shapes.
-/

@[expose] public section
namespace VG.Impl.Dsa.Arm.Shape
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic

/-- Six width masks occupy the header's words 8–28. -/
def saveWidth (n bits offset : Nat) : Prog isa :=
  .seq (optionalWidth n (modS n) (expS n) bits) (.block [.str .r2 .r12 offset])

def threeWidths (n a b c output : Nat) : Prog isa :=
  .seq (saveWidth n a output) (.seq (saveWidth n b (output + 4)) (saveWidth n c (output + 8)))

def loadWidths (len : Nat) (modulus : VG.Impl.Dsa.Layout.Field) (a b c output : Nat) : Prog isa :=
  let n := (len + 7) / 8
  .seq (Core.load n len (modS n) (.input modulus)) (threeWidths n a b c output)

/-- p's low word, for its parity. -/
def saveParity (n : Nat) : List Instr :=
  ptr .r10 (modS n) ++ [.ldr .r4 .r10 0, .str .r4 .r12 32]

/-- The masks of the supported (p, q) pairs, combined with the parities. -/
def combine : List Instr :=
  [.ldr .r4 .r12 8, .ldr .r5 .r12 20, .dp .and .r4 .r4 (.reg .r5),
    .ldr .r5 .r12 24, .ldr .r7 .r12 28, .dp .orr .r5 .r5 (.reg .r7),
    .ldr .r7 .r12 20, .dp .orr .r5 .r5 (.reg .r7), .ldr .r7 .r12 12,
    .dp .and .r5 .r5 (.reg .r7), .dp .orr .r4 .r4 (.reg .r5),
    .ldr .r5 .r12 16, .ldr .r7 .r12 28, .dp .and .r5 .r5 (.reg .r7), .dp .orr .r4 .r4 (.reg .r5),
    .ldr .r5 .r12 32, .dp .and .r4 .r4 (.reg .r5), .str .r4 .r12 (Layout.field .mask)]

/-- The parities of p and q, as an all-ones/zero mask at `[32]`. -/
def parity (qN : Nat) : List Instr :=
  ptr .r10 (modS qN) ++ [.ldr .r2 .r10 0, .ldr .r4 .r12 32, .dp .and .r2 .r2 (.reg .r4),
    .dp .and .r2 .r2 (.imm 1), .mov .r4 (.imm 0), .dp .sub .r4 .r4 (.reg .r2), .str .r4 .r12 32]

/-- The actual subgroup byte width, from the three exclusive q masks. -/
def prefixWidth : List Instr := [
  .ldr .r4 .r12 20, .dp .and .r4 .r4 (.imm 20),
  .ldr .r2 .r12 24, .dp .and .r2 .r2 (.imm 28), .dp .orr .r2 .r2 (.reg .r4),
  .ldr .r4 .r12 28, .dp .and .r4 .r4 (.imm 32), .dp .orr .r2 .r2 (.reg .r4)]

/-- The digest length clamped to that width, `min(len, width)`: the borrow
of the word `len - width`, as a mask, selects `len`. -/
def digestClamp : List Instr := [
  .ldr .r7 .r12 (Layout.field .digestLen), mask16, .mov .r3 (.imm 1), .mov .r5 (.reg .r2)] ++
  borrowDigit 0 ++ borrowDigit 1 ++ [
  .dp .sub .r3 .r3 (.imm 1),
  .dp .eor .r7 .r7 (.reg .r2), .dp .and .r7 .r7 (.reg .r3), .dp .eor .r2 .r2 (.reg .r7),
  .str .r2 .r12 (Layout.field .digestPrefixLen)]

def digestPrefix : Prog isa := .block (prefixWidth ++ digestClamp)

def inspectP (pLen : Nat) : Prog isa :=
  .seq (loadWidths pLen .p 1024 2048 3072 8) (.block (saveParity ((pLen + 7) / 8)))

def inspectQ (qLen : Nat) : Prog isa :=
  .seq (loadWidths qLen .q 160 224 256 20) (.block (parity ((qLen + 7) / 8) ++ combine))

def check (pLen qLen : Nat) : Prog isa := Core.sequence [
  inspectP pLen, inspectQ qLen, digestPrefix,
  .block [.ldr .r4 .r12 (Layout.field .mask), .cmp .r4 (.imm 0)]]

end VG.Impl.Dsa.Arm.Shape
