module

public import VerifiedGarbage.Impl.X25519.Arm

/-!
# X25519: 32-bit ARM implementation with `umaal`

`vg_x25519_umaal(out = r0, scalar = r1, point = r2, scratch = r3)`, for CPUs
with `umaal` (`hi:lo := n m + hi + lo`, which cannot overflow).

A field element is eight 32-bit words `x0 + 2³² x1 + … + 2²²⁴ x7` at a constant
offset of the working space, whose base is in `r0` once the arguments are
read: any number below `2²⁵⁶` stands for its residue modulo `p = 2²⁵⁵ - 19`.
Products and the sums `b + 121665 a` are folded at bit 255, so they are below
`2²⁵⁵ + 2³²`, at most `2p`; only the result is reduced fully. Every register
but `r0` is working space of the arithmetic, so the ladder keeps its counter,
the last bit of the scalar and `out` in memory:

* `[0, 36)`: the saved `r4`–`r11` and `lr`; `OUT`, `CNT` and `SWAP`;
* `x1, x2, z2, x3, z3`, the ladder's temporaries and the inversion's result,
  32 bytes each (`X1`, …), and the low half of a product (`ACC`);
* the bits of the scalar (`BITS` of the baseline, which `bits` writes: byte
  `t` is bit `t` of the clamped scalar).

The arithmetic, in which every carry is the high word of an `umaal`:

* `mul`: the product row by row. The eight live words of the accumulator
  and the row's carry are the nine registers `rg`, each row using them one
  further on (`rg (i + 1 + j)` is word `i + j` in row `i`, and `rg i` its
  carry), so that a product `a_i b_j` is a load of `b_j` and one `umaal`;
  a row stores its low word in `ACC`. Then `lo + 38 hi` (`2²⁵⁶ ≡ 38`), a
  word and a carry `c` more, and the fold at bit 255 (`fold19`): with
  `q = 2c + bit 255`, bit 255 cleared and `19 q` added (`2²⁵⁵ ≡ 19`);
* `add`, for operands at most `2p`: the sum, then `38` times its carry;
* `sub`, for a subtrahend at most `2p`: `a + ¬b + 1`, whose carry is 0 if it
  borrowed, and then `2²⁵⁶ - 38` more (`fixup`: the words of the mask, the
  lowest less 37);
* `addA24`: `b + 121665 a` in one chain, then `fold19`;
* `cswap`: the baseline's, over eight words;
* `freeze`: the full reduction of a number below `2p`: `y = x + 19`, and
  `y - 2²⁵⁵` if bit 255 of `y` is set, `x = y - 19` if not (`fixup` again,
  adding `2²⁵⁶ - 19`).

The ladder follows RFC 7748 §5, over the bits of the scalar from 254 down to
0. The inversion `z2^(p-2)` is square-and-multiply over the bits of `p - 2`
from 254 down to 0: every bit but 4 and 2 is 1.

The only branches are on the counter, and every address is a pointer plus a
constant or the counter, so only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.X25519.Arm.Words

open VG.Arm

/-! ## The layout of the working space -/

def OUT : Nat := 40
def CNT : Nat := 44
def SWAP : Nat := 48
def X1 : Nat := 64
def X2 : Nat := 96
def Z2 : Nat := 128
def X3 : Nat := 160
def Z3 : Nat := 192
def A : Nat := 224
def B : Nat := 256
def C : Nat := 288
def D : Nat := 320
def AA : Nat := 352
def BB : Nat := 384
def E : Nat := 416
def DA : Nat := 448
def CB : Nat := 480
def R : Nat := 512
def ACC : Nat := 544

/-! ## Registers -/

/-- The nine registers of a product, in rotation. -/
def rg (i : Nat) : Reg :=
  match i % 9 with
  | 0 => .r3 | 1 => .r4 | 2 => .r5 | 3 => .r6 | 4 => .r7 | 5 => .r8 | 6 => .r9 | 7 => .r10 | _ => .r11

/-- The registers of the words of a sum. -/
def xr : Nat → Reg
  | 0 => .r4 | 1 => .r5 | 2 => .r6 | 3 => .r7 | 4 => .r8 | 5 => .r9 | 6 => .r10 | _ => .r11

/-- The registers `X` as the element at `o`. -/
def stores (o : Nat) (X : Nat → Reg) : List Instr := (List.range 8).flatMap fun k => [.str (X k) .r0 (o + 4 * k)]

/-! ## Field arithmetic -/

/-- The number `X + 2²⁵⁶ c` folded at bit 255: `q = 2c + bit 255`, bit 255
cleared, and `19 q` added. -/
def fold19 (X : Nat → Reg) (c : Reg) : List Instr :=
  ([.mov .r12 (.shifted (X 7) .lsr 31), .dp .add .r12 .r12 (.shifted c .lsl 1),
    .dp .bic (X 7) (X 7) (.imm 0x80000000), .dp .add .lr .r12 (.shifted .r12 .lsl 1),
    .dp .add .r12 .lr (.shifted .r12 .lsl 4), .mov .lr (.imm 0)] : List Instr) ++
  (List.range 8).flatMap fun k => [.umaal (X k) .r12 .lr .lr]

/-- Row `i` of a product: the accumulator plus `a_i · b`, and its low word
into `ACC`. -/
def mulRow (a b i : Nat) : List Instr :=
  ([.ldr .r1 .r0 (a + 4 * i), .mov (rg i) (.imm 0)] : List Instr) ++
  (List.range 8).flatMap (fun j => [.ldr .r2 .r0 (b + 4 * j), .umaal (rg (i + 1 + j)) (rg i) .r1 .r2]) ++
  ([.str (rg (i + 1)) .r0 (ACC + 4 * i)] : List Instr)

/-- `lo + 38 hi`: word `k` in `rg (k + 8)`, and the carry in `r1`. -/
def mulFold : List Instr :=
  ([.mov .r1 (.imm 0), .mov .r2 (.imm 38)] : List Instr) ++
  (List.range 8).flatMap fun k => [.ldr (rg (k + 8)) .r0 (ACC + 4 * k), .umaal (rg (k + 8)) .r1 .r2 (rg k)]

/-- `[o] = [a] · [b]` (`o` may be `a` or `b`). -/
def mul (o a b : Nat) : List Instr :=
  (List.range 8).flatMap (fun j => [.mov (rg (j + 1)) (.imm 0)]) ++ (List.range 8).flatMap (mulRow a b) ++
    mulFold ++ fold19 (fun k => rg (k + 8)) .r1 ++ stores o fun k => rg (k + 8)

/-- `[o] = [a] + [b]`. -/
def add (o a b : Nat) : List Instr :=
  ([.mov .r1 (.imm 0), .mov .r2 (.imm 1)] : List Instr) ++
  (List.range 8).flatMap (fun k =>
    [.ldr (xr k) .r0 (a + 4 * k), .ldr .r3 .r0 (b + 4 * k), .umaal (xr k) .r1 .r2 .r3]) ++
  ([.mov .r3 (.imm 38), .mul .r1 .r1 .r3, .mov .r3 (.imm 0)] : List Instr) ++
  (List.range 8).flatMap (fun k => [.umaal (xr k) .r1 .r3 .r3]) ++ stores o xr

/-- `2²⁵⁶ - (K + 1)` added to `xr` if `r1` is 0, and nothing if it is 1
(`r2` = 1). -/
def fixup (K : BitVec 32) : List Instr :=
  ([.dp .sub .r1 .r1 (.imm 1), .dp .bic .r3 .r1 (.imm K), .mov .r12 (.imm 0)] : List Instr) ++
  (List.range 8).flatMap fun k => [.umaal (xr k) .r12 .r2 (if k = 0 then .r3 else .r1)]

/-- `[o] = [a] - [b]`. -/
def sub (o a b : Nat) : List Instr :=
  ([.mov .r1 (.imm 1), .mov .r2 (.imm 1)] : List Instr) ++
  (List.range 8).flatMap (fun k =>
    [.ldr (xr k) .r0 (a + 4 * k), .ldr .r3 .r0 (b + 4 * k), .mvn .r3 (.reg .r3), .umaal (xr k) .r1 .r2 .r3]) ++
  fixup 37 ++ stores o xr

/-- `[o] = [b] + 121665 [a]`, with `121665 = 0x1db41`. -/
def addA24 (o b a : Nat) : List Instr :=
  ([.movw .r2 0xdb41, .movt .r2 1, .mov .r1 (.imm 0)] : List Instr) ++
  (List.range 8).flatMap (fun k =>
    [.ldr (xr k) .r0 (b + 4 * k), .ldr .r3 .r0 (a + 4 * k), .umaal (xr k) .r1 .r2 .r3]) ++
  fold19 xr .r1 ++ stores o xr

/-- Swaps `[x]` and `[y]` if the mask `r9` is all ones (and not if it is
zero). -/
def cswap (x y : Nat) : List Instr := (List.range 8).flatMap (cswapStep x y)

/-! ## The ladder -/

/-- The start of an iteration of the ladder, for the bit `t = CNT - 1`: `k_t`
from `BITS`, the swaps by the mask `-(swap ^ k_t)`, and `swap = k_t`. -/
def stepHead : List Instr :=
  ([.ldr .r1 .r0 CNT, .dp .sub .r1 .r1 (.imm 1), .str .r1 .r0 CNT, .dp .add .r2 .r0 (.reg .r1),
    .ldrb .r2 .r2 BITS, .ldr .r3 .r0 SWAP, .str .r2 .r0 SWAP, .dp .eor .r2 .r2 (.reg .r3),
    .mov .r9 (.imm 0), .dp .sub .r9 .r9 (.reg .r2)] : List Instr) ++ cswap X2 X3 ++ cswap Z2 Z3

/-- One iteration of the ladder: `stepHead`, then the formulas of RFC 7748 §5. -/
def step : Prog isa :=
  .seq (.block stepHead) <|
  .seq (.block (add A X2 Z2)) <| .seq (.block (mul AA A A)) <| .seq (.block (sub B X2 Z2)) <|
  .seq (.block (mul BB B B)) <| .seq (.block (sub E AA BB)) <| .seq (.block (add C X3 Z3)) <|
  .seq (.block (sub D X3 Z3)) <| .seq (.block (mul DA D A)) <| .seq (.block (mul CB C B)) <|
  .seq (.block (add X3 DA CB)) <| .seq (.block (mul X3 X3 X3)) <| .seq (.block (sub Z3 DA CB)) <|
  .seq (.block (mul Z3 Z3 Z3)) <| .seq (.block (mul Z3 X1 Z3)) <| .seq (.block (mul X2 AA BB)) <|
  .seq (.block (addA24 Z2 AA E)) <| .seq (.block (mul Z2 E Z2)) (.block [.ldr .r1 .r0 CNT, .cmp .r1 (.imm 0)])

/-- The 255 iterations, for `t` from 254 down to 0, with `swap = 0`. -/
def ladder : Prog isa :=
  .seq (.block [.mov .r1 (.imm 255), .str .r1 .r0 CNT, .mov .r1 (.imm 0), .str .r1 .r0 SWAP]) (.loop step .ne)

/-- The swap after the loop. -/
def lastSwap : List Instr :=
  ([.ldr .r2 .r0 SWAP, .mov .r9 (.imm 0), .dp .sub .r9 .r9 (.reg .r2)] : List Instr) ++ cswap X2 X3 ++
    cswap Z2 Z3

/-! ## Inversion

`[R] = [Z2]^(p-2)`, square-and-multiply over the bits of `p - 2` from 254
down to 0 (`t = CNT - 1`): `R = R²`, then `R = R · Z2` unless `t` is 4 or 2. -/

/-- `[R] = 1`. -/
def one : List Instr :=
  ([.mov .r1 (.imm 1), .mov .r2 (.imm 0), .str .r1 .r0 R] : List Instr) ++ storeN .r2 (R + 4) 7

def invStep : Prog isa :=
  .seq (.block [.ldr .r1 .r0 CNT, .dp .sub .r1 .r1 (.imm 1), .str .r1 .r0 CNT]) <|
  .seq (.block (mul R R R)) <| .seq (.block [.ldr .r1 .r0 CNT, .cmp .r1 (.imm 4)]) <|
  .seq (.ite .eq (.block [])
      (.seq (.block [.cmp .r1 (.imm 2)]) (.ite .eq (.block []) (.block (mul R R Z2)))))
    (.block [.ldr .r1 .r0 CNT, .cmp .r1 (.imm 0)])

def invert : Prog isa :=
  .seq (.block (one ++ ([.mov .r1 (.imm 255), .str .r1 .r0 CNT] : List Instr))) (.loop invStep .ne)

/-! ## Encoding and decoding -/

/-- The callee-saved registers, saved at `4i` of the working space. -/
def savedReg : Nat → Reg
  | 0 => .r4 | 1 => .r5 | 2 => .r6 | 3 => .r7 | 4 => .r8 | 5 => .r9 | 6 => .r10 | 7 => .r11 | _ => .lr

/-- Saves the registers (with the working space in `r3`), then `out` into
`r12` and the working space into `r0`. -/
def setup : List Instr :=
  (List.range 9).flatMap (fun i => [.str (savedReg i) .r3 (4 * i)]) ++
  ([.mov .r12 (.reg .r0), .mov .r0 (.reg .r3)] : List Instr)

/-- Word `k` of `u` (bytes `4k` to `4k + 3` at `r2`, the top bit masked) into
`xr k`. -/
def decodeStep (k : Nat) : List Instr :=
  ([.ldrb (xr k) .r2 (4 * k), .ldrb .r3 .r2 (4 * k + 1), .dp .add (xr k) (xr k) (.shifted .r3 .lsl 8),
    .ldrb .r3 .r2 (4 * k + 2), .dp .add (xr k) (xr k) (.shifted .r3 .lsl 16),
    .ldrb .r3 .r2 (4 * k + 3)] : List Instr) ++
    (if k = 7 then ([.dp .and .r3 .r3 (.imm 127)] : List Instr) else []) ++
    ([.dp .add (xr k) (xr k) (.shifted .r3 .lsl 24)] : List Instr)

/-- `out` into `OUT`, the u-coordinate into `X1` and `X3`, and `x2 = 1`,
`z3 = 1` and `z2 = 0`. -/
def init : List Instr :=
  .str .r12 .r0 OUT :: (List.range 8).flatMap decodeStep ++ stores X1 xr ++ stores X3 xr ++
    (List.range 8).flatMap (fun k => [.mov (xr k) (.imm (if k = 0 then 1 else 0))]) ++ stores X2 xr ++
    stores Z3 xr ++ ([.mov (xr 0) (.imm 0)] : List Instr) ++ stores Z2 xr

/-- The number in `xr`, below `2p`, reduced fully. -/
def freeze : List Instr :=
  ([.mov .r12 (.imm 19), .mov .r3 (.imm 0)] : List Instr) ++
  (List.range 8).flatMap (fun k => [.umaal (xr k) .r12 .r3 .r3]) ++
  ([.mov .r1 (.shifted (xr 7) .lsr 31), .mov .r2 (.imm 1)] : List Instr) ++ fixup 18 ++
  ([.dp .bic (xr 7) (xr 7) (.imm 0x80000000)] : List Instr)

/-- Word `k` of the result, `xr k`, as bytes `4k` to `4k + 3` of `out` (`r1`). -/
def outStep (k : Nat) : List Instr :=
  [.strb (xr k) .r1 (4 * k), .mov .r2 (.shifted (xr k) .lsr 8), .strb .r2 .r1 (4 * k + 1),
    .mov .r2 (.shifted (xr k) .lsr 16), .strb .r2 .r1 (4 * k + 2), .mov .r2 (.shifted (xr k) .lsr 24),
    .strb .r2 .r1 (4 * k + 3)]

/-- `[X2]` reduced fully, into `out`. -/
def output : List Instr :=
  (List.range 8).flatMap (fun k => [.ldr (xr k) .r0 (X2 + 4 * k)]) ++ freeze ++
  ([.ldr .r1 .r0 OUT] : List Instr) ++ (List.range 8).flatMap outStep

def restore : List Instr := (List.range 9).flatMap fun i => [.ldr (savedReg i) .r0 (4 * i)]

/-- `vg_x25519_umaal`. -/
def x25519Umaal : Prog isa :=
  .seq (.block setup) <| .seq bits <| .seq (.block init) <| .seq ladder <| .seq (.block lastSwap) <|
    .seq invert (.block (mul X2 X2 R ++ output ++ restore))

/-! ## `vg_x25519_base_umaal`

`vg_x25519_base_umaal(out = r0, scalar = r1, scratch = r2)`: `X25519(k, 9)` by
`vg_x25519_umaal` on the base point's u-coordinate, for CPUs with `umaal`, on
which the ladder with packed words is faster than the comb over 16-bit limbs
(`Impl/X25519/Arm/Base.lean`).

`scratch` is 8192 bytes, of which `vg_x25519_umaal` takes the first 4096.
The u-coordinate 9 is written at byte `BP` = 4096, eight words, and `r4` and
`lr` are saved after it (the call overwrites `lr`, and `r4`, which the callee
preserves, keeps the address across the call), so that it needs no stack.
Only the pointers can affect timing. -/

/-- The byte of `scratch` where the base point's u-coordinate is written. -/
def BP : Nat := 4096

/-- `r3 := scratch + BP`, `r4` and `lr` saved after the point there, `r4` set
to it, the u-coordinate 9 written, and the arguments of `vg_x25519_umaal`:
the point in `r2` and the working space in `r3`. -/
def baseSetup : List Instr :=
  [.dp .add .r3 .r2 (.imm 4096), .str .r4 .r3 36, .str .lr .r3 32, .mov .r4 (.reg .r3),
   .mov .r12 (.imm 9), .str .r12 .r3 0, .mov .r12 (.imm 0), .str .r12 .r3 4, .str .r12 .r3 8,
   .str .r12 .r3 12, .str .r12 .r3 16, .str .r12 .r3 20, .str .r12 .r3 24, .str .r12 .r3 28,
   .mov .r12 (.reg .r2), .mov .r2 (.reg .r3), .mov .r3 (.reg .r12)]

/-- `lr` and `r4` restored. -/
def baseFinish : List Instr := [.ldr .lr .r4 32, .ldr .r4 .r4 36]

def x25519BaseUmaal : Prog isa :=
  .seq (.block baseSetup) (.seq (.call "vg_x25519_umaal" x25519Umaal) (.block baseFinish))

end VG.Impl.X25519.Arm.Words
