module

public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Spec.X448
public import VerifiedGarbage.Impl.X25519.X86

/-!
# X448: x86 (32-bit) implementation

Field elements are fourteen 32-bit words, any number below `2^448`. The field
arithmetic is the functions `vg_gf448_r32_mul`, `vg_gf448_r32_sqr`, `vg_gf448_r32_add`,
`vg_gf448_r32_sub` and `vg_gf448_r32_mul_a24` (`Proof/X448/X86/FnVerified.lean`),
which X448 and Ed448 call rather than inlining it; reduction uses
`2^448 = 2^224 + 1` modulo the field prime. Sums, differences and the
reductions are carry chains (`adc`, `sbb`), and the product is by product
scanning (X25519's columns, `Impl/X25519/X86.lean`).

Arguments use cdecl: output, scalar, point, and working space are at
`[esp + 4]` through `[esp + 16]`. The stack pointer moves only for the calls
of the field functions, whose arguments take the 20 bytes below the return
address. `edi` holds the working space and `esi` the ladder or squaring
counter.
-/

@[expose] public section

namespace VG.Impl.X448.X86

open VG.X86

def at_ (r : Reg) (d : Nat) : MemOp := { base := r, disp := d }
def sc (d : Nat) : MemOp := at_ .edi d
def ld (r : Reg) (d : Nat) : Instr := .mov r (.mem (sc d))
def st (r : Reg) (d : Nat) : Instr := .store (sc d) r

/-- Slots reserve 128 bytes, of which 56 hold an element's words. -/
def slot (n : Nat) : Nat := 64 + 128 * n
def X1 : Nat := slot 0
def X2 : Nat := slot 1
def Z2 : Nat := slot 2
def X3 : Nat := slot 3
def Z3 : Nat := slot 4
def A : Nat := slot 5
def B : Nat := slot 6
def C : Nat := slot 7
def D : Nat := slot 8
def AA : Nat := slot 9
def BB : Nat := slot 10
def E : Nat := slot 11
def DA : Nat := slot 12
def CB : Nat := slot 13
def T0 : Nat := slot 14
def T1 : Nat := slot 15
def T2 : Nat := slot 16
def T3 : Nat := slot 17
def T4 : Nat := slot 18
def T5 : Nat := slot 19
def T6 : Nat := slot 20
def T7 : Nat := slot 21
def SWAP : Nat := 32
def BITS : Nat := 3072
def ACC : Nat := 3584
def TMP : Nat := 3840

/-- Copy the fourteen words. -/
def copy (o a : Nat) : List Instr :=
  (List.range 14).flatMap fun i => [ld .eax (a + 4 * i), st .eax (o + 4 * i)]

/-- Carry the sum in `eax` and the incoming carry in `ebx`. -/
def carryStep (rb : Reg) (o : Nat) : List Instr :=
  [.alu .add .ebx (.reg .eax), .mov .edx (.reg .ebx), .alu .and .edx (.imm 65535),
    .store (at_ rb o) .edx, .shift .shr .ebx 16]

def carryPass (rb : Reg) (o : Nat) (src : Nat → List Instr) : List Instr :=
  (List.range 28).flatMap fun i => src i ++ carryStep rb (o + 4 * i)

/-- One product of a multiplication row, `a_i b_j` with `b_j` at `mb j`, added
to the previous rows. -/
def rowSrcWith (mb : Nat → MemOp) (j : Nat) : List Instr :=
  [.mov .eax (.mem (mb j)), .mul .ecx, .alu .add .eax (.mem (at_ .ebp (ACC + 4 * j)))]

/-- A row's last carry, the row pointer advanced, and its comparison with the end. -/
def rowEnd : List Instr :=
  [.store (at_ .ebp (ACC + 112)) .ebx, .alu .add .ebp (.imm 4),
    .mov .edx (.reg .edi), .alu .add .edx (.imm 112), .alu .cmp .ebp (.reg .edx)]

/-- A multiplication row: `ldA` loads `a_i` into `ecx`, `mb j` addresses `b_j`. -/
def rowWith (ldA : List Instr) (mb : Nat → MemOp) : List Instr :=
  ldA ++ [.mov .ebx (.imm 0)] ++ carryPass .ebp ACC (rowSrcWith mb) ++ rowEnd

def row (a b : Nat) : List Instr := rowWith [.mov .ecx (.mem (at_ .ebp a))] (fun j => sc (b + 4 * j))

def zeroAcc : List Instr :=
  [.mov .eax (.imm 0)] ++ (List.range 28).flatMap fun i => [st .eax (ACC + 4 * i)]

def mulPre : List Instr := zeroAcc ++ [.mov .ebp (.reg .edi)]

/-! ## The field functions

`vg_gf448_r32_{mul,sqr,add,sub,mul_a24}(ws, o, a[, b])` (`Proof/X448/X86/FnVerified.lean`),
cdecl: the arguments at `[esp + 4]` to `[esp + 16]`. Each loads `ws` into
`edi` and saves the callee-saved registers in the last 16 bytes of its own
working space (`SAVE`), points `esi`, `ebx` and `ebp` at its operands and its
result, and restores the registers. They use no stack, and every address is
`ws` plus a constant or an offset. -/

/-- Where the field functions save the callee-saved registers. -/
def SAVE : Nat := 4080

/-- Argument `i` of a field function. -/
def argOp (i : Nat) : MemOp := at_ .esp (4 + 4 * i)

/-- `edi = ws`, and `ebx`, `esi`, `edi` and `ebp` saved at `SAVE`, through `eax`. -/
def fnEntry : List Instr :=
  [.mov .eax (.mem (argOp 0)), .store (at_ .eax SAVE) .ebx, .store (at_ .eax (SAVE + 4)) .esi,
    .store (at_ .eax (SAVE + 8)) .edi, .store (at_ .eax (SAVE + 12)) .ebp, .mov .edi (.reg .eax)]

/-- The registers restored, `edi` last. -/
def fnExit : List Instr :=
  [.mov .ebx (.mem (sc SAVE)), .mov .esi (.mem (sc (SAVE + 4))), .mov .ebp (.mem (sc (SAVE + 12))),
    .mov .edi (.mem (sc (SAVE + 8)))]

/-- `r = ws + ` argument `i`. -/
def argPtr (r : Reg) (i : Nat) : List Instr := [.mov r (.mem (argOp i)), .alu .add r (.reg .edi)]

/-! ### Carry chains -/

/-- The word at `x`, `op` (`adc` or `sbb`) `src` with the carry, to `y`. -/
def chainStep (op : AluOp) (y x : MemOp) (src : Src) : List Instr :=
  [.mov .eax (.mem x), .alu op .eax src, .store y .eax]

/-- `n` words at `y` = those at `x`, `op` the operands `src k`, with the carry from each word to
the next. -/
def chain (op : AluOp) (y x : Nat → MemOp) (src : Nat → Src) (n : Nat) : List Instr :=
  (List.range n).flatMap fun k => chainStep op (y k) (x k) (src k)

/-- Word `k` of the element at `r`. -/
def wordAt (r : Reg) (k : Nat) : MemOp := at_ r (4 * k)

/-- The operands of a fold: `ecx` into words 0 and 7, and the carry on. -/
def foldSrc (k : Nat) : Src := if k = 0 ∨ k = 7 then .reg .ecx else .imm 0

/-- `ecx` = 1 if the carry flag is set, else 0; the carry flag cleared. -/
def carry1 : List Instr := [.alu .sbb .ecx (.reg .ecx), .alu .and .ecx (.imm 1)]

/-- The carry (or borrow) `ecx` of 448 bits, below `2^32 - 1`, folded into the element at `ebp`, as
`2^448 = 2^224 + 1`; then a carry out of that, which leaves the high seven words so small (or so
large, for a borrow) that folding it does not carry out of word 7. The carry flag is clear. -/
def foldChain (op : AluOp) : List Instr :=
  chain op (wordAt .ebp) (wordAt .ebp) foldSrc 14 ++ carry1 ++ chain op (wordAt .ebp) (wordAt .ebp) foldSrc 8

/-- The carry flag cleared (and `ecx`). -/
def clearCarry : List Instr := [.alu .xor .ecx (.reg .ecx)]

/-- The element at `ebp` = that at `esi` `op` that at `ebx`. -/
def addSub (op : AluOp) : List Instr :=
  clearCarry ++ chain op (wordAt .ebp) (wordAt .esi) (fun k => .mem (wordAt .ebx k)) 14 ++ carry1 ++ foldChain op

/-! ### The product

`vg_gf448_r32_mul` copies its operands (`PA`, `PB`), multiplies them by
product scanning into 28 words (`PROD`) and folds those by the prime into the
result, by carry chains. All of these are in the functions' own working
space, at constant offsets of `edi`. -/

/-- The operands' words and the product's. -/
def PA : Nat := ACC
def PB : Nat := ACC + 56
def PROD : Nat := ACC + 112

/-- The element at `esi` to `[edi + o]`. -/
def operand (o : Nat) : List Instr :=
  (List.range 14).flatMap fun k => [.mov .eax (.mem (wordAt .esi k)), st .eax (o + 4 * k)]

/-- The products `a_i b_j` of column `k`: `i + j = k`. -/
def prodTerms (k : Nat) : List Impl.X25519.X86.Term :=
  ((List.range 14).filter fun i => i ≤ k && k - i < 14).map fun i => .mulM (PA + 4 * i) (PB + 4 * (k - i))

/-- The terms of column `k` of the square of the words at `PA`: the products
`a_i a_j` with `i < j` and `i + j = k`, doubled, and `a_{k/2}²` for an even `k`. -/
def sqrTerms (k : Nat) : List Impl.X25519.X86.Term :=
  ((List.range 14).filter fun i => 2 * i < k && k - i < 14).map
      (fun i => .mulM2 (PA + 4 * i) (PA + 4 * (k - i))) ++
    if k % 2 = 0 ∧ k / 2 < 14 then [.mulM (PA + 4 * (k / 2)) (PA + 4 * (k / 2))] else []

/-- Word `k` of the product. -/
def pw (k : Nat) : MemOp := sc (PROD + 4 * k)

/-- The carry flag added to `ecx`, and cleared. -/
def carryUp : List Instr := [.alu .adc .ecx (.imm 0)]

/-- The product `p0 + p1 φ + p2 φ² + p3 φ³` (of seven words each, `φ = 2^224`, `φ² = φ + 1`) into
the element at `ebp`: `(p0, p1) + (p2, p3) + (p3, p3) + (0, p2)`, and the carries, at most 3,
folded. -/
def reduce : List Instr :=
  clearCarry ++ chain .adc (wordAt .ebp) pw (fun k => .mem (pw (14 + k))) 14 ++ carryUp ++
    chain .adc (wordAt .ebp) (wordAt .ebp) (fun k => .mem (pw (21 + k % 7))) 14 ++ carryUp ++
    chain .adc (fun k => wordAt .ebp (7 + k)) (fun k => wordAt .ebp (7 + k)) (fun k => .mem (pw (14 + k))) 7 ++
    carryUp ++ foldChain .adc

/-- The 28 columns `ts` of a product into `PROD`, reduced into the element at argument 1. -/
def prodWords (ts : Nat → List Impl.X25519.X86.Term) : List Instr :=
  Impl.X25519.X86.zeroAcc ++ Impl.X25519.X86.cols PROD 28 ts ++ argPtr .ebp 1 ++ reduce

/-- `vg_gf448_r32_mul`. -/
def mulFn : Prog isa :=
  .block (fnEntry ++ argPtr .esi 2 ++ operand PA ++ argPtr .esi 3 ++ operand PB ++ prodWords prodTerms ++ fnExit)

/-- `vg_gf448_r32_sqr(ws, o, a)`: as `vg_gf448_r32_mul` of `a` and `a`, with the
columns of a square: 105 multiplications rather than 196. -/
def sqrFn : Prog isa :=
  .block (fnEntry ++ argPtr .esi 2 ++ operand PA ++ prodWords sqrTerms ++ fnExit)

/-- Word `k` of `39081` (in `ebx`) times the element at `esi`, and the carry word `ecx`, to the
element at `ebp`. -/
def a24Step (k : Nat) : List Instr :=
  [.mov .eax (.mem (wordAt .esi k)), .mul .ebx, .alu .add .eax (.reg .ecx), .alu .adc .edx (.imm 0),
    .store (wordAt .ebp k) .eax, .mov .ecx (.reg .edx)]

/-- The element at `ebp` = `39081` times that at `esi`. -/
def mulA24 : List Instr :=
  [.mov .ebx (.imm 39081), .mov .ecx (.imm 0)] ++ (List.range 14).flatMap a24Step ++
    [.alu .test .ecx (.reg .ecx)] ++ foldChain .adc

/-- The pointers of a binary function: `esi` and `ebx` at its operands, `ebp` at its result. -/
def argPtrs : List Instr := argPtr .esi 2 ++ argPtr .ebx 3 ++ argPtr .ebp 1

/-- `vg_gf448_r32_add`. -/
def addFn : Prog isa := .block (fnEntry ++ argPtrs ++ addSub .adc ++ fnExit)

/-- `vg_gf448_r32_sub`. -/
def subFn : Prog isa := .block (fnEntry ++ argPtrs ++ addSub .sbb ++ fnExit)

/-- `vg_gf448_r32_mul_a24`. -/
def mulA24Fn : Prog isa := .block (fnEntry ++ argPtr .esi 2 ++ argPtr .ebp 1 ++ mulA24 ++ fnExit)

/-! ## Calls of the field functions

The offsets in `eax`, `ecx` and `edx`, and `ws = edi`, pushed as the
arguments: the call changes `eax`, `ecx`, `edx`, the flags, the result, the
function's own working space and the 20 bytes below `esp`. -/

def call3 (name : String) (body : Prog isa) (o a b : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.imm (BitVec.ofNat 32 o)), .mov .ecx (.imm (BitVec.ofNat 32 a)),
      .mov .edx (.imm (BitVec.ofNat 32 b))])
    (.frame (.push [.edx, .ecx, .eax, .edi]) (.call name body) (.pop .eax 4))

def call2 (name : String) (body : Prog isa) (o a : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.imm (BitVec.ofNat 32 o)), .mov .ecx (.imm (BitVec.ofNat 32 a))])
    (.frame (.push [.ecx, .eax, .edi]) (.call name body) (.pop .eax 3))

def sqrCall (o a : Nat) : Prog isa := call2 "vg_gf448_r32_sqr" sqrFn o a

/-- A product is a call of `vg_gf448_r32_mul`, and a square of `vg_gf448_r32_sqr`. -/
def mulCall (o a b : Nat) : Prog isa :=
  if a = b then sqrCall o a else call3 "vg_gf448_r32_mul" mulFn o a b
def addCall (o a b : Nat) : Prog isa := call3 "vg_gf448_r32_add" addFn o a b
def subCall (o a b : Nat) : Prog isa := call3 "vg_gf448_r32_sub" subFn o a b
def a24Call (o a : Nat) : Prog isa := call2 "vg_gf448_r32_mul_a24" mulA24Fn o a

/-- Swap under the mask in `ebx`. -/
def cswap (x y : Nat) : List Instr :=
  (List.range 14).flatMap fun i =>
    [ld .eax (x + 4 * i), ld .ecx (y + 4 * i), .mov .edx (.reg .eax), .alu .xor .edx (.reg .ecx),
      .alu .and .edx (.reg .ebx), .alu .xor .eax (.reg .edx), .alu .xor .ecx (.reg .edx),
      st .eax (x + 4 * i), st .ecx (y + 4 * i)]

inductive Op
  | mul (o a b : Nat)
  | mulSmall (o a : Nat)
  | add (o a b : Nat)
  | sub (o a b : Nat)
  | copy (o a : Nat)
  deriving DecidableEq, Repr

def Op.code : Op → Prog isa
  | .mul o a b => mulCall o a b
  | .mulSmall o a => a24Call o a
  | .add o a b => addCall o a b
  | .sub o a b => subCall o a b
  | .copy o a => .block (X86.copy o a)

def ops : List Op → Prog isa
  | [] => .block []
  | o :: os => .seq o.code (ops os)

def stepOps : List Op :=
  [.add A X2 Z2, .mul AA A A, .sub B X2 Z2, .mul BB B B, .sub E AA BB,
    .add C X3 Z3, .sub D X3 Z3, .mul DA D A, .mul CB C B,
    .add X3 DA CB, .mul X3 X3 X3, .sub Z3 DA CB, .mul Z3 Z3 Z3, .mul Z3 X1 Z3,
    .mul X2 AA BB, .mulSmall Z2 E, .add Z2 AA Z2, .mul Z2 E Z2]

def stepHead : List Instr :=
  [.alu .sub .esi (.imm 1), .mov .ebp (.reg .edi), .alu .add .ebp (.reg .esi),
    .movzx8 .eax (at_ .ebp BITS), ld .ecx SWAP, .alu .xor .ecx (.reg .eax), st .eax SWAP,
    .mov .ebx (.imm 0), .alu .sub .ebx (.reg .ecx)] ++ cswap X2 X3 ++ cswap Z2 Z3

def stepBody : Prog isa := .seq (.block stepHead) (ops stepOps)
def step : Prog isa := .seq stepBody (.block [.alu .cmp .esi (.imm 0)])
def ladder : Prog isa := .seq (.block [.mov .esi (.imm 448)]) (.loop step .ne)

def lastSwap : List Instr :=
  [ld .ecx SWAP, .mov .ebx (.imm 0), .alu .sub .ebx (.reg .ecx)] ++ cswap X2 X3 ++ cswap Z2 Z3

/-- Square `n` times in place, for positive `n`. -/
def sqn (o n : Nat) : Prog isa :=
  .seq (.block [.mov .esi (.imm (BitVec.ofNat 32 n))])
    (.loop (.seq (mulCall o o o) (.block [.alu .sub .esi (.imm 1)])) .ne)

def invert : Prog isa :=
  .seq (ops [.copy T0 Z2]) <| .seq (sqn T0 1) <| .seq (ops [.mul T0 T0 Z2, .copy T1 T0]) <|
  .seq (sqn T1 2) <| .seq (ops [.mul T1 T1 T0, .copy T2 T1]) <|
  .seq (sqn T2 4) <| .seq (ops [.mul T2 T2 T1, .copy T3 T2]) <|
  .seq (sqn T3 8) <| .seq (ops [.mul T3 T3 T2, .copy T4 T3]) <|
  .seq (sqn T4 16) <| .seq (ops [.mul T4 T4 T3, .copy T5 T4]) <|
  .seq (sqn T5 32) <| .seq (ops [.mul T5 T5 T4, .copy T6 T5]) <|
  .seq (sqn T6 64) <| .seq (ops [.mul T6 T6 T5]) <|
  .seq (sqn T6 64) <| .seq (ops [.mul T6 T6 T5]) <|
  .seq (sqn T6 16) <| .seq (ops [.mul T6 T6 T3]) <|
  .seq (sqn T6 8) <| .seq (ops [.mul T6 T6 T2]) <|
  .seq (sqn T6 4) <| .seq (ops [.mul T6 T6 T1]) <|
  .seq (sqn T6 2) <| .seq (ops [.mul T6 T6 T0, .copy T7 T6]) <|
  .seq (sqn T7 1) <| .seq (ops [.mul T7 T7 Z2]) <|
  .seq (sqn T7 225) <| .seq (sqn T6 2) <| ops [.mul T6 T6 Z2, .mul T7 T7 T6]

/-- Word `k` of the point at `esi` to `X1` and `X3`. -/
def decodeWord (k : Nat) : List Instr :=
  [.mov .eax (.mem (wordAt .esi k)), st .eax (X1 + 4 * k), st .eax (X3 + 4 * k)]

/-- Bit `j` of the byte in `eax` to `[ebp + o + j]`. -/
def bitP (o j : Nat) : List Instr :=
  [.mov .edx (.reg .eax)] ++ (if j = 0 then [] else [.shift .shr .edx j]) ++
    [.alu .and .edx (.imm 1), .store8 (at_ .ebp (o + j)) .dl]

/-- One byte: the byte at `esi` expanded into the bytes at `ebp + o`, …, `ebp + o + 7`; then
`esi`, `ebp` and the count `ecx` moved on (ZF set at 0). -/
def bitsBody (o : Nat) : List Instr :=
  [.movzx8 .eax (at_ .esi 0)] ++ (List.range 8).flatMap (bitP o) ++
    [.alu .add .esi (.imm 1), .alu .add .ebp (.imm 8), .alu .sub .ecx (.imm 1)]

/-- The `n` bytes at `esi` expanded into their bits in the working space: byte `o + 8 i + j` is
bit `j` of byte `i`, through `ebp = edi + 8 i`, counted by `ecx`. -/
def bitsLoop (o n : Nat) : Prog isa :=
  .seq (.block [.mov .ebp (.reg .edi), .mov .ecx (.imm (BitVec.ofNat 32 n))])
    (.loop (.block (bitsBody o)) .ne)

/-- RFC 7748's clamp of the expanded bits: bits 0 and 1 cleared, bit 447 set. -/
def clamp : List Instr :=
  [.mov .edx (.imm 0), .store8 (sc BITS) .dl, .store8 (sc (BITS + 1)) .dl,
    .mov .edx (.imm 1), .store8 (sc (BITS + 447)) .dl]

/-- Expand the scalar's bytes, then apply the RFC 7748 clamp. -/
def bits : Prog isa :=
  .seq (.block [.mov .esi (.mem (at_ .esp 8))]) (.seq (bitsLoop BITS 56) (.block clamp))

def initSlots : List Instr :=
  [.alu .xor .eax (.reg .eax)] ++
  (List.range 64).map (fun i => st .eax (X2 + 4 * i)) ++
  (List.range 576).map (fun i => st .eax (Z3 + 4 * i)) ++
  [st .eax SWAP, .mov .eax (.imm 1), st .eax X2, st .eax Z3]

/-- Save through `eax` before replacing the working-space register. -/
def save : List Instr :=
  [.mov .eax (.mem (at_ .esp 16)), .store (at_ .eax 0) .ebx, .store (at_ .eax 4) .esi,
    .store (at_ .eax 8) .edi, .store (at_ .eax 12) .ebp, .mov .edi (.reg .eax)]

def setup : List Instr := save ++ [.mov .esi (.mem (at_ .esp 12))] ++
  (List.range 14).flatMap decodeWord ++ initSlots

/-- The element at `X2` reduced fully, in place: `x + 1 + 2^224` (at `TMP`) if it carries out of
448 bits, which it does exactly when `x` is not below the prime, and `x` if not. -/
def freeze : List Instr :=
  clearCarry ++ chain .adc (fun k => sc (TMP + 4 * k)) (fun k => sc (X2 + 4 * k))
      (fun k => .imm (if k = 0 ∨ k = 7 then 1 else 0)) 14 ++
    [.alu .sbb .ecx (.reg .ecx)] ++
  (List.range 14).flatMap fun i =>
    [ld .eax (X2 + 4 * i), ld .edx (TMP + 4 * i), .alu .xor .edx (.reg .eax),
      .alu .and .edx (.reg .ecx), .alu .xor .eax (.reg .edx), st .eax (X2 + 4 * i)]

/-- Word `k` of slot 1 to the output at `esi`. -/
def packWord (k : Nat) : List Instr := [ld .eax (X2 + 4 * k), .store (wordAt .esi k) .eax]

/-- Restore `edi` last, reading every saved register through `eax`. -/
def restore : List Instr :=
  [.mov .eax (.reg .edi), .mov .ebx (.mem (at_ .eax 0)), .mov .esi (.mem (at_ .eax 4)),
    .mov .ebp (.mem (at_ .eax 12)), .mov .edi (.mem (at_ .eax 8))]

def finish : Prog isa :=
  .seq (mulCall X2 X2 T7) (.block (freeze ++ [.mov .esi (.mem (at_ .esp 4))] ++
    (List.range 14).flatMap packWord ++ restore))

def x448 : Prog isa :=
  .seq (.block setup) <| .seq bits <| .seq ladder <| .seq (.block lastSwap) <| .seq invert finish

end VG.Impl.X448.X86
