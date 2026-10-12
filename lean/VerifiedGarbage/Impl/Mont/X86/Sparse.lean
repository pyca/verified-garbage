module

public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Impl.Mont.Mod

/-! # In-place word chains for sparse x86 Montgomery reduction -/

@[expose] public section

namespace VG.Impl.Mont.X86
open VG.X86

/-- P-256's field modulus. -/
def p256Prime : Nat := 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1

/-- The existing friendly-reduction certificate encodes `(p + 1) / 2^64`. -/
def p256RedWords : List MWord := [.pow2 32, .zero, .gen 0xffffffff00000001, .zero]

/-- Enable the sparse reducer only for P-256's eight 32-bit words. -/
def p256RedChoice (n m : Nat) : Red :=
  if n = 4 ∧ m = p256Prime then .friendly p256RedWords else .general

def p256RedEnabled (M : Mod) : Bool :=
  M.n == 4 && M.red == .friendly p256RedWords && M.minv.setWidth 32 == (1 : BitVec 32)

/-- Add or subtract `ecx` in the first word, propagating carry or borrow
through the remaining words. The window base is `ebp`. -/
def sparseStep (acc j : Nat) (op : AluOp) (first : Bool) : List Instr :=
  [.mov .eax (.mem { base := .ebp, disp := acc + 4 * j }),
   .alu op .eax (if first then .reg .ecx else .imm 0),
   .store { base := .ebp, disp := acc + 4 * j } .eax]

def sparseChain (acc : Nat) (op op' : AluOp) (k : Nat) : List Instr :=
  (List.range k).flatMap fun j => sparseStep acc j (if j = 0 then op else op') (j == 0)

/-- Add `ecx` at the selected word positions in one carry chain. -/
def multiChain (acc : Nat) (useQ : Nat → Bool) (k : Nat) : List Instr :=
  (List.range k).flatMap fun j => sparseStep acc j (if j = 0 then .add else .adc) (useQ j)

/-- The positive terms at words 3, 6 and 8, relative to word 3. -/
def positiveMask (j : Nat) : Bool := j == 0 || j == 3 || j == 5

/-- `T + q p`, where `q` is the low word of `T` and
`p = 2^256 - 2^224 + 2^192 + 2^96 - 1`. The subtraction of `q`
clears the low word; all other terms are sparse carry chains. -/
def p256Red (acc : Nat) : List Instr :=
  ([.mov .eax (.imm 0), .store { base := .ebp, disp := acc } .eax] : List Instr) ++
  multiChain (acc + 12) positiveMask 7 ++
  sparseChain (acc + 28) .sub .sbb 3

end VG.Impl.Mont.X86
