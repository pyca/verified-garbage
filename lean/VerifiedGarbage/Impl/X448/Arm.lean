module

public import VerifiedGarbage.TCB.Arm.Isa

/-!
# X448: ARMv7 implementation

Field elements are twenty-eight 16-bit limbs in 32-bit words. Each
multiplication row propagates carries so that every multiply and addition
fits in a word. Reduction uses `2^448 = 2^224 + 1` modulo the field prime.
Only baseline instructions are used, including the low-word `mul`.

`r0` holds the working space, `r8` the output pointer, `r10` the link
register, `r11` the ladder or squaring counter, and `r6` the limb mask.
Registers `r4` through `r11` are saved in the working space and restored
before returning. Multiplications, additions, subtractions and the
multiplication by `a24` are calls of the functions `vg_gf448_r16_*` below,
which keep `r0`, `r8`, `r10` and `r11`.
-/

@[expose] public section

namespace VG.Impl.X448.Arm

open VG.Arm

def ld (r : Reg) (d : Nat) : Instr := .ldr r .r0 d
def st (r : Reg) (d : Nat) : Instr := .str r .r0 d

/-- Slots reserve 128 bytes, of which 112 hold the limbs. -/
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

/-- Copy the twenty-eight limbs. -/
def copy (o a : Nat) : List Instr :=
  (List.range 28).flatMap fun i => [ld .r3 (a + 4 * i), st .r3 (o + 4 * i)]

/-- Carry the sum in `r3` and the incoming carry in `r5`. -/
def carryStepT (t rb : Reg) (o : Nat) : List Instr :=
  [.dp .add .r3 .r3 (.reg .r5), .dp .and t .r3 (.reg .r6), .str t rb o,
    .mov .r5 (.shifted .r3 .lsr 16)]

abbrev carryStep (rb : Reg) (o : Nat) : List Instr := carryStepT .r4 rb o

/-- Carry twenty-eight sums supplied by `src`, through `t`. -/
def carryPassT (t rb : Reg) (o : Nat) (src : Nat → List Instr) : List Instr :=
  (List.range 28).flatMap fun i => src i ++ carryStepT t rb (o + 4 * i)

/-- Carry twenty-eight sums supplied by `src`. -/
abbrev carryPass (rb : Reg) (o : Nat) (src : Nat → List Instr) : List Instr := carryPassT .r4 rb o src

/-- Carry the twenty-eight limbs at `a` into those at `o` from `rb`. -/
def passR (rb : Reg) (o a : Nat) : List Instr :=
  [.mov .r5 (.imm 0)] ++ carryPass rb o (fun i => [ld .r3 (a + 4 * i)])

def pass (o a : Nat) : List Instr := passR .r0 o a

/-- Fold the carry into limbs 0 and 14. -/
def fold : List Instr :=
  [0, 14].flatMap fun i => [ld .r3 (TMP + 4 * i), .dp .add .r3 .r3 (.reg .r5), st .r3 (TMP + 4 * i)]

/-- The coefficients at `TMP` normalized into the result, at `r9`. -/
def normalize : List Instr := pass TMP TMP ++ fold ++ pass TMP TMP ++ fold ++ passR .r9 0 TMP

/-- One word of a multiplication row. -/
def rowStep (b j : Nat) : List Instr :=
  [ld .r2 (b + 4 * j), .mul .r2 .r1 .r2, .ldr .r3 .r7 (ACC + 4 * j),
    .dp .add .r3 .r3 (.reg .r2)] ++ carryStep .r7 (ACC + 4 * j)

def row (a b : Nat) : List Instr :=
  [.ldr .r1 .r7 a, .mov .r5 (.imm 0)] ++ (List.range 28).flatMap (rowStep b) ++
  [.str .r5 .r7 (ACC + 112), .dp .add .r7 .r7 (.imm 4), .subs .r9 .r9 (.imm 1)]

/-- One word of a multiplication row of the field functions, for the second
operand at `r12`, in the row `q` (0 or 1) words above `r7`; the carry goes
through `r2`, so that `r4` can count. -/
def rowStepF (q j : Nat) : List Instr :=
  [.ldr .r2 .r12 (4 * j), .mul .r2 .r1 .r2, .ldr .r3 .r7 (ACC + 4 * q + 4 * j),
    .dp .add .r3 .r3 (.reg .r2)] ++ carryStepT .r2 .r7 (ACC + 4 * q + 4 * j)

/-- The row of the limb of the first operand `q` words above `lr`, into the
accumulator `q` words above `r7`. -/
def rowHalfF (q : Nat) : List Instr :=
  [.ldr .r1 .lr (4 * q), .mov .r5 (.imm 0)] ++ (List.range 28).flatMap (rowStepF q) ++
    [.str .r5 .r7 (ACC + 4 * q + 112)]

/-- Two rows; then `r7` and `lr` move up two words, and `r4` counts the pairs
of rows down. -/
def rowF : List Instr :=
  rowHalfF 0 ++ rowHalfF 1 ++
    [.dp .add .r7 .r7 (.imm 8), .dp .add .lr .lr (.imm 8), .subs .r4 .r4 (.imm 1)]

def reduceCol (k : Nat) : List Instr :=
  [ld .r3 (ACC + 4 * k), ld .r2 (ACC + 4 * (k + 28)), .dp .add .r3 .r3 (.reg .r2)] ++
  (if k < 14 then [ld .r2 (ACC + 4 * (k + 42)), .dp .add .r3 .r3 (.reg .r2)]
   else [ld .r2 (ACC + 4 * (k + 14)), .dp .add .r3 .r3 (.reg .r2),
     ld .r2 (ACC + 4 * (k + 28)), .dp .add .r3 .r3 (.reg .r2)]) ++ [st .r3 (TMP + 4 * k)]

/-- Initialize the first half of the product; each row writes the next carry word. -/
def zeroAcc : List Instr :=
  [.mov .r3 (.imm 0)] ++ (List.range 28).flatMap fun i => [st .r3 (ACC + 4 * i)]

def mulPre : List Instr := zeroAcc ++ [.mov .r7 (.reg .r0), .mov .r9 (.imm 28)]

def mulPreF : List Instr := zeroAcc ++ [.mov .r7 (.reg .r0), .mov .r4 (.imm 14)]

/-- `[r9] = [lr] [r12]` (`lr` moves past the first operand). -/
def mul : Prog isa :=
  .seq (.block mulPreF) <|
  .seq (.loop (.block rowF) .ne) <|
    .block ((List.range 28).flatMap reduceCol ++ normalize)

/-- The low word of limb `i` of twice the prime; its high bit is added separately. -/
def subK (i : Nat) : BitVec 16 := if i = 14 then 0xfffc else 0xfffe

/-- `[r9] = [lr] + [r12]`. -/
def add : List Instr :=
  (List.range 28).flatMap (fun i =>
    [.ldr .r3 .lr (4 * i), .ldr .r2 .r12 (4 * i), .dp .add .r3 .r3 (.reg .r2),
      st .r3 (TMP + 4 * i)]) ++ normalize

/-- `[r9] = [lr] - [r12]`, as `[lr] + 2p - [r12]`. -/
def sub : List Instr :=
  (List.range 28).flatMap (fun i =>
    [.ldr .r3 .lr (4 * i), .movw .r2 (subK i), .dp .add .r2 .r2 (.imm 65536),
      .dp .add .r3 .r3 (.reg .r2), .ldr .r2 .r12 (4 * i), .dp .sub .r3 .r3 (.reg .r2),
      st .r3 (TMP + 4 * i)]) ++ normalize

/-- `[r9] = 39081 [lr]`. -/
def mulSmall : List Instr :=
  [.movw .r5 39081] ++ (List.range 28).flatMap (fun i =>
    [.ldr .r3 .lr (4 * i), .mul .r3 .r3 .r5, st .r3 (TMP + 4 * i)]) ++ normalize

/-! ## The field functions

`vg_gf448_r16_{mul,add,sub,mul_a24}(ws = r0, o = r1, a = r2, b = r3)`
(`Spec/X448/Field16.lean`): the registers they change and must restore are
saved at `SAVE` (in their own working space, from `ACC`), `r6` takes the
limb mask, and `r9`, `lr` and `r12` point to `[o]`, `[a]` and `[b]`. They
never write `r0`, `r8`, `r10` or `r11`, so that a caller keeps its working
space and the values a constant-time analysis must know to be public there
across a call; a call changes `r1`–`r3`, `r12` and `lr`, and the registers
it restores. -/

/-- Where the functions save the registers they restore. -/
def SAVE : Nat := 3968

def fnSaved : List Reg := [.r4, .r5, .r6, .r7, .r9, .lr]

def saveFn : List Instr := (List.range 6).map fun i => st (fnSaved[i]!) (SAVE + 4 * i)

def restoreFn : List Instr := (List.range 6).map fun i => ld (fnSaved[i]!) (SAVE + 4 * i)

/-- The registers saved, the mask, and the pointers to `[o]`, `[a]` and (if
`hasB`) `[b]`. -/
def entryFn (hasB : Bool) : List Instr :=
  saveFn ++ [.movw .r6 65535, .dp .add .r9 .r0 (.reg .r1), .dp .add .lr .r0 (.reg .r2)] ++
    (if hasB then [.dp .add .r12 .r0 (.reg .r3)] else [])

def fn (hasB : Bool) (op : Prog isa) : Prog isa :=
  .seq (.block (entryFn hasB)) <| .seq op (.block restoreFn)

def mulFn : Prog isa := fn true mul
def addFn : Prog isa := fn true (.block add)
def subFn : Prog isa := fn true (.block sub)
def mulA24Fn : Prog isa := fn false (.block mulSmall)

/-- A call of the function `f`, whose code is `body`, with the offsets as arguments. -/
def callFn (f : String) (body : Prog isa) (o a b : Nat) : Prog isa :=
  .seq (.block [.movw .r1 (BitVec.ofNat 16 o), .movw .r2 (BitVec.ofNat 16 a),
    .movw .r3 (BitVec.ofNat 16 b)]) (.call f body)

def mulA24Call (o a : Nat) : Prog isa :=
  .seq (.block [.movw .r1 (BitVec.ofNat 16 o), .movw .r2 (BitVec.ofNat 16 a)])
    (.call "vg_gf448_r16_mul_a24" mulA24Fn)

/-- Swap under the mask in `r5`. -/
def cswap (x y : Nat) : List Instr :=
  (List.range 28).flatMap fun i =>
    [ld .r3 (x + 4 * i), ld .r2 (y + 4 * i), .dp .eor .r4 .r3 (.reg .r2),
      .dp .and .r4 .r4 (.reg .r5), .dp .eor .r3 .r3 (.reg .r4),
      .dp .eor .r2 .r2 (.reg .r4), st .r3 (x + 4 * i), st .r2 (y + 4 * i)]

inductive Op
  | mul (o a b : Nat)
  | mulSmall (o a : Nat)
  | add (o a b : Nat)
  | sub (o a b : Nat)
  | copy (o a : Nat)
  deriving DecidableEq, Repr

def Op.code : Op → Prog isa
  | .mul o a b => callFn "vg_gf448_r16_mul" mulFn o a b
  | .mulSmall o a => mulA24Call o a
  | .add o a b => callFn "vg_gf448_r16_add" addFn o a b
  | .sub o a b => callFn "vg_gf448_r16_sub" subFn o a b
  | .copy o a => .block (Arm.copy o a)

def ops : List Op → Prog isa
  | [] => .block []
  | o :: os => .seq o.code (ops os)

def stepOps : List Op :=
  [.add A X2 Z2, .mul AA A A, .sub B X2 Z2, .mul BB B B, .sub E AA BB,
    .add C X3 Z3, .sub D X3 Z3, .mul DA D A, .mul CB C B,
    .add X3 DA CB, .mul X3 X3 X3, .sub Z3 DA CB, .mul Z3 Z3 Z3, .mul Z3 X1 Z3,
    .mul X2 AA BB, .mulSmall Z2 E, .add Z2 AA Z2, .mul Z2 E Z2]

def stepHead : List Instr :=
  [.dp .sub .r11 .r11 (.imm 1), .dp .add .r7 .r0 (.reg .r11), .ldrb .r3 .r7 BITS,
    ld .r2 SWAP, .dp .eor .r2 .r2 (.reg .r3), st .r3 SWAP,
    .mov .r5 (.imm 0), .dp .sub .r5 .r5 (.reg .r2)] ++ cswap X2 X3 ++ cswap Z2 Z3

def stepBody : Prog isa := .seq (.block stepHead) (ops stepOps)

def step : Prog isa := .seq stepBody (.block [.cmp .r11 (.imm 0)])

def ladder : Prog isa := .seq (.block [.movw .r11 448]) (.loop step .ne)

def lastSwap : List Instr :=
  [ld .r2 SWAP, .mov .r5 (.imm 0), .dp .sub .r5 .r5 (.reg .r2)] ++ cswap X2 X3 ++ cswap Z2 Z3

/-- Square `n` times in place, for positive `n`. -/
def sqn (o n : Nat) : Prog isa :=
  .seq (.block [.movw .r11 (BitVec.ofNat 16 n)])
    (.loop (.seq (Op.code (.mul o o o)) (.block [.subs .r11 .r11 (.imm 1)])) .ne)

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

/-- Two byte loads decode a limb without requiring input alignment. -/
def decodeLimb (i : Nat) : List Instr :=
  [.ldrb .r3 .r2 (2 * i), .ldrb .r4 .r2 (2 * i + 1),
    .dp .add .r3 .r3 (.shifted .r4 .lsl 8), st .r3 (X1 + 4 * i), st .r3 (X3 + 4 * i)]

/-- Expand one scalar byte into eight individual bits. -/
def bitsBody : List Instr :=
  [.dp .add .r7 .r1 (.reg .r11), .ldrb .r3 .r7 0,
    .dp .add .r7 .r0 (.shifted .r11 .lsl 3)] ++
  (List.range 8).flatMap (fun j =>
    [.mov .r2 (if j = 0 then .reg .r3 else .shifted .r3 .lsr j),
      .dp .and .r2 .r2 (.imm 1), .strb .r2 .r7 (BITS + j)]) ++
  [.dp .add .r11 .r11 (.imm 1), .cmp .r11 (.imm 56)]

def bits : Prog isa :=
  .seq (.block [.mov .r11 (.imm 0)]) <|
  .seq (.loop (.block bitsBody) .ne) <|
    .block [.mov .r3 (.imm 0), .strb .r3 .r0 BITS, .strb .r3 .r0 (BITS + 1),
      .mov .r3 (.imm 1), .strb .r3 .r0 (BITS + 447)]

/-- Initialize the other slots, retaining the decoded coordinate. -/
def initSlots : List Instr :=
  [.mov .r3 (.imm 0)] ++
  (List.range 64).map (fun i => st .r3 (X2 + 4 * i)) ++
  (List.range 576).map (fun i => st .r3 (Z3 + 4 * i)) ++
  [st .r3 SWAP, .mov .r3 (.imm 1), st .r3 X2, st .r3 Z3]

def saved : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

def setup : List Instr :=
  (List.range 8).map (fun i => .str (saved[i]!) .r3 (4 * i)) ++
  [.mov .r8 (.reg .r0), .mov .r10 (.reg .lr), .mov .r0 (.reg .r3), .movw .r6 65535] ++
  (List.range 28).flatMap decodeLimb ++ initSlots

/-- Add `1 + 2^224`, then select the carried result when the carry is one. -/
def freeze : List Instr :=
  copy TMP X2 ++ [0, 14].flatMap (fun i =>
    [ld .r3 (TMP + 4 * i), .dp .add .r3 .r3 (.imm 1), st .r3 (TMP + 4 * i)]) ++ pass TMP TMP ++
  [.mov .r4 (.imm 0), .dp .sub .r4 .r4 (.reg .r5)] ++
  (List.range 28).flatMap fun i =>
    [ld .r3 (X2 + 4 * i), ld .r2 (TMP + 4 * i), .dp .eor .r2 .r2 (.reg .r3),
      .dp .and .r2 .r2 (.reg .r4), .dp .eor .r3 .r3 (.reg .r2), st .r3 (X2 + 4 * i)]

def packLimb (i : Nat) : List Instr :=
  [ld .r3 (X2 + 4 * i), .strb .r3 .r8 (2 * i), .mov .r3 (.shifted .r3 .lsr 8),
    .strb .r3 .r8 (2 * i + 1)]

def finish : Prog isa :=
  .seq (Op.code (.mul X2 X2 T7)) (.block (freeze ++ (List.range 28).flatMap packLimb ++
    .mov .lr (.reg .r10) :: (List.range 8).map fun i => ld (saved[i]!) (4 * i)))

def x448 : Prog isa :=
  .seq (.block setup) <| .seq bits <| .seq ladder <| .seq (.block lastSwap) <| .seq invert finish

end VG.Impl.X448.Arm
