module

public import VerifiedGarbage.Impl.Mont.Arm

/-! Packed 32-bit Montgomery arithmetic, using baseline half-word products.
All row accesses have fixed offsets, so r12 remains the workspace base and
r10/r11 remain available to curve callers. -/

@[expose] public section
namespace VG.Impl.Mont.Arm.Packed
open VG VG.Arm VG.Impl.Mont.Arm

/-- Scalar halves in r2/r0; r7 is the input word. r6:r5 is the product.
The cross products overwrite the consumed input halves. -/
def head : List Instr :=
  [.mov .r8 (.shifted .r7 .lsr 16), .mov .r7 (.shifted .r7 .lsl 16),
   .mov .r7 (.shifted .r7 .lsr 16),
   .mul .r5 .r2 .r7, .mul .r6 .r0 .r8, .mul .r7 .r0 .r7]

def cross (r : Reg) : List Instr :=
  [.adds .r5 .r5 (.shifted r .lsl 16), .adc .r6 .r6 (.shifted r .lsr 16)]

def product : List Instr :=
  head ++ cross .r7 ++ [.mul .r8 .r2 .r8] ++ cross .r8

def addWord (r : Reg) : List Instr :=
  [.adds .r5 .r5 (.reg r), .adc .r6 .r6 (.imm 0)]

def split : List Instr :=
  [.mov .r0 (.shifted .r2 .lsr 16), .mov .r2 (.shifted .r2 .lsl 16),
    .mov .r2 (.shifted .r2 .lsr 16)]

def step (acc : Nat) (rb : Reg) (src j : Nat) : List Instr :=
  [.ldr .r7 rb (src + 4 * j)] ++ product ++
    [.ldr .r7 .r12 (acc + 4 * j)] ++ addWord .r7 ++ addWord .r3 ++
    [.str .r5 .r12 (acc + 4 * j), .mov .r3 (.reg .r6)]

def carry (acc n : Nat) : List Instr :=
  [.ldr .r5 .r12 (acc + 4 * n), .ldr .r6 .r12 (acc + 4 * n + 4)] ++
  addWord .r3 ++ [.str .r5 .r12 (acc + 4 * n), .str .r6 .r12 (acc + 4 * n + 4)]

def row (acc : Nat) (rb : Reg) (src n : Nat) : List Instr :=
  split ++ [.mov .r3 (.imm 0)] ++ (List.range n).flatMap (step acc rb src) ++ carry acc n

def shift (acc n : Nat) : List Instr :=
  (List.range (n + 1)).flatMap (fun j =>
    [.ldr .r5 .r12 (acc + 4 * j + 4), .str .r5 .r12 (acc + 4 * j)]) ++
  [.mov .r5 (.imm 0), .str .r5 .r12 (acc + 4 * (n + 1))]

def round (M : Mod) (acc : Nat) : List Instr :=
  [.ldr .r2 .r1 0] ++ row acc .r4 0 (2 * M.n) ++
  [.ldr .r2 .r12 acc, .movw .r7 (BitVec.ofNat 16 M.minv.toNat),
    .movt .r7 (BitVec.ofNat 16 (M.minv.toNat >>> 16)), .mul .r2 .r2 .r7] ++
  row acc .r12 M.mo (2 * M.n) ++ shift acc (2 * M.n) ++
  [.dp .add .r1 .r1 (.imm 4), .subs .r9 .r9 (.imm 1)]

/-- Convert packed words to half-word digits for the existing reducer. -/
def expand (acc dst n : Nat) : List Instr :=
  [.movw .r6 0xffff] ++ (List.range n).flatMap fun j =>
    digitAt .r12 acc j ++ [.str .r7 .r12 (dst + 4 * j)]

def mulR (M : Mod) (acc : Nat) : Prog isa :=
  .seq (.block (zeros acc (2 * M.n + 2) ++ [.mov .r9 (.imm (BitVec.ofNat 32 (2 * M.n)))])) <|
  .seq (.loop (.block (round M acc)) .ne) <|
  .block (expand acc (acc + 8 * M.n + 8) (4 * M.n + 1) ++
    csub M (acc + 8 * M.n + 8) .lr 0)

end VG.Impl.Mont.Arm.Packed
