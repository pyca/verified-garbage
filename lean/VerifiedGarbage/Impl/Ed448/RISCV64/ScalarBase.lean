module

public import VerifiedGarbage.Impl.X448.RISCV64.R64
public import VerifiedGarbage.Spec.Ed448
public import VerifiedGarbage.Impl.Ed448.Comb

/-!
# Ed448 on RISC-V: base-point multiplication

`vg_ed448_scalar_base(out = a0, scalar = a1, scratch = a2)`: the encoding of
`[s]B` for the 456-bit little-endian scalar `s`, without pruning.

X448's field code on this target does the arithmetic: field elements are
seven 64-bit words (the same 56 bytes as fourteen 32-bit limbs) in the
56-byte slots of the working space, and the operations are `mul`, `add`,
`sub` and `invert` of `Impl/X448/RISCV64/R64.lean` (with `mul` and `mulhu`,
in the registers `t0`, `t3`–`t6`, `a1`, `a2`, `a4`–`a7`) and `freeze` of
`Impl/X448/RISCV64.lean`. Points are the specification's projective
coordinates `(X : Y : Z)`. The working space, rounded up to a multiple of 8
(`align`), is in `a3`, as in X448; the constants' words are built with `lui`
and `addiw`.

The multiplication is x86-64's four-column comb (`combLoop`, below): `R`
starts as the neutral point `(0 : 1 : 1)` (`combInit`), and each of 114 rows
doubles it and adds the affine table entry of four bits of the scalar, 114
apart. The table's sixteen entries (`Impl/Ed448/Comb.lean`) are built once
at `CTAB`, past the field slots (`tabBuild`), and every row reads all of them
(`combSelect`). The scalar's bits are expanded into bytes at X448's `BITS`
(byte `t` is bit `t`), as X448 expands its scalar. Finally `R` is encoded
(§5.2.2): `Z` inverted (X448's `invert`, `Z` being in its slot `Z2`),
`x = X/Z` fully reduced into `out` for its low bit, then `y = Y/Z`, and the
bit as the top bit of the 57th byte.

The slots `P`, `T`, the addition's temporaries and `sel` serve verification's
equation (`VerifyEquation.lean`), whose loop runs RFC 8032's addition
(`addition`) of `R` and `P`.

The function uses only caller-saved registers and no stack. The only branches are on the
loop counters, and every address is a pointer plus a constant or a counter,
so only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.Ed448.RISCV64

open VG.RISCV64 VG.Impl.Words.RISCV64
open VG.Impl.X448.RISCV64 (freeze bitsBody BITS R X2 Z2 align)
open VG.Impl.X448.RISCV64.R64 (mul add sub cswap invert)

/-! ## The slots -/

def RX : Nat := X2
def RY : Nat := 0
def RZ : Nat := Z2
def PX : Nat := 168
def PY : Nat := 224
def PZ : Nat := 280
def DK : Nat := 336
def TX : Nat := 392
def TY : Nat := 448
def TZ : Nat := 504
/-- The addition's temporaries (`B` and `E` are in `TY` and `TZ`, `H`'s
second factor and `AF` in `TX`, `AG` in `TY`, which they leave in time). -/
def TA : Nat := 560
def TC : Nat := 616
def TD : Nat := 672
def TF : Nat := 728
def TG : Nat := 784
def TH : Nat := R
/-! ## Constants -/

/-- Word `k` of `v`, as `lui` and `addiw` build it (sign-extended) and `sw`
stores its low 32 bits. -/
def constLimb (o v k : Nat) : List Instr :=
  li32 .a4 (BitVec.ofNat 32 (v / 2 ^ (32 * k))) ++ [.store .w .a4 .a3 (o + 4 * k)]

/-- The element `v` into the slot at `o`. -/
def constField (o v : Nat) : List Instr := (List.range 14).flatMap (constLimb o v)

/-! ## The bits of the scalar -/

/-- `BITS[8i + j] = bit j of scalar[i]`, for the 57 bytes at `a1`. -/
def baseBits : Prog isa :=
  .seq (.block [.addi .a6 .a3 0, .li .t0 57]) (.loop (.block bitsBody) (.nonzero .t0))

/-! ## The selection and the addition of verification's equation -/

/-- Limb `k` of `[q]`, or of `[r]` if the mask `t0` is all ones, into limb
`k` of `[o]`. -/
def selStep (o q r k : Nat) : List Instr :=
  [.load .w .a2 .a3 (q + 4 * k), .load .w .a4 .a3 (r + 4 * k), .logic .xor .a4 .a4 .a2,
    .logic .and .a4 .a4 .t0, .logic .xor .a2 .a2 .a4, .store .w .a2 .a3 (o + 4 * k)]

def sel (o q r : Nat) : List Instr := (List.range 14).flatMap (selStep o q r)

/-- `T = R + P` (RFC 8032 §5.2.4's addition, in its order): `A = Z₁Z₂`,
`B = A²`, `C = X₁X₂`, `D = Y₁Y₂`, `E = dCD`, `F = B - E`, `G = B + E`,
`H = (X₁ + Y₁)(X₂ + Y₂)`, `X₃ = AF(H - C - D)`, `Y₃ = AG(D - C)`,
`Z₃ = FG`. -/
def addition : Prog isa :=
  .seq (mul TA RZ PZ) <| .seq (mul TY TA TA) <| .seq (mul TC RX PX) <| .seq (mul TD RY PY) <|
  .seq (mul TZ DK TC) <| .seq (mul TZ TZ TD) <| .seq (.block (sub TF TY TZ)) <|
  .seq (.block (add TG TY TZ)) <| .seq (.block (add TH RX RY)) <| .seq (.block (add TX PX PY)) <|
  .seq (mul TH TH TX) <| .seq (mul TX TA TF) <| .seq (.block (sub TH TH TC)) <|
  .seq (.block (sub TH TH TD)) <| .seq (mul TX TX TH) <| .seq (mul TY TA TG) <|
  .seq (.block (sub TH TD TC)) <| .seq (mul TY TY TH) (mul TZ TF TG)

/-! ## The encoding -/

/-- `1/Z` into `R`; `x = X/Z` fully reduced into `out`, and its low bit as
bit 7 of `t1`; `y = Y/Z` fully reduced into `out`, and the bit as the top
bit of its 57th byte. -/
def baseEncode : Prog isa :=
  .seq invert <| .seq (mul X2 RX R) <|
  .seq (.block (freeze ++ [.load .b .t1 .a0 0, .li .a6 1, .logic .and .t1 .t1 .a6, .shift .sll .d .t1 .t1 7])) <|
  .seq (mul X2 RY R) (.block (freeze ++ [.store .b .t1 .a0 56]))

/-! ## The four-column comb

The base-point multiplication proper (`scalarBase`): the comb of x86-64
(`Impl/Ed448/Comb.lean`'s table of the sixteen affine points
`[i₀ + 2¹¹⁴ i₁ + 2²²⁸ i₂ + 2³⁴² i₃] B`), 114 rows from the top, each a
doubling of `R` (`dblOps`, RFC 8032 §5.2.4's doubling), the table entry of
the row's four bits selected by a full masked scan (`combSelect`) into
`(SX : SY : 1)`, and its addition to `R` in place (`addOps`, the addition with
`Z₂ = 1`). The table is built once at `CTAB`, past the field slots, from
literals (`tabBuild`, with `a3` moved there for its stores). -/

/-- The selected entry `(x, y)`. -/
def SX : Nat := 168
def SY : Nat := 224

/-- The point operations' temporaries. -/
def U0 : Nat := 280
def U1 : Nat := 392
def U2 : Nat := 448
def U3 : Nat := 504
def U4 : Nat := 560
def U5 : Nat := 616
def U6 : Nat := 672
def U7 : Nat := 728
def U8 : Nat := 784

/-- The table, at `a3 + CTAB`: entry `i`'s `x` at `112 i`, its `y` at `112 i + 56`. -/
def CTAB : Nat := 2048

/-- A field operation of `R64`. -/
inductive COp where
  | mul (o x y : Nat)
  | add (o x y : Nat)
  | sub (o x y : Nat)

def COp.code : COp → Prog isa
  | .mul o x y => Impl.X448.RISCV64.R64.mul o x y
  | .add o x y => .block (Impl.X448.RISCV64.R64.add o x y)
  | .sub o x y => .block (Impl.X448.RISCV64.R64.sub o x y)

/-- The operations in order. -/
def opsProg : List COp → Prog isa
  | [] => .block []
  | op :: ops => .seq op.code (opsProg ops)

/-- `R = 2R` (RFC 8032 §5.2.4): `B = (X + Y)²`, `C = X²`, `D = Y²`,
`E = C + D`, `H = Z²`, `J = E - 2H`, `X = (B - E) J`, `Y = E (C - D)`,
`Z = E J`. -/
def dblOps : List COp :=
  [.add U0 RX RY, .mul U0 U0 U0, .mul U1 RX RX, .mul U2 RY RY, .add U3 U1 U2, .mul U4 RZ RZ,
    .add U5 U4 U4, .sub U5 U3 U5, .sub U6 U0 U3, .mul RX U6 U5, .sub U7 U1 U2, .mul RY U3 U7,
    .mul RZ U3 U5]

/-- `R = R + (SX : SY : 1)` (RFC 8032 §5.2.4's addition with `A = Z₁`):
`B = Z₁²`, `C = X₁x`, `D = Y₁y`, `E = dCD`, `F = B - E`, `G = B + E`,
`H = (X₁ + Y₁)(x + y)`, `X₃ = Z₁F(H - C - D)`, `Y₃ = Z₁G(D - C)`,
`Z₃ = FG`, each coordinate of `R` written once its last use is past. -/
def addOps : List COp :=
  [.mul U1 RZ RZ, .mul U2 RX SX, .mul U3 RY SY, .mul U4 DK U2, .mul U4 U4 U3, .sub U5 U1 U4,
    .add U6 U1 U4, .add U7 RX RY, .add U8 SX SY, .mul U7 U7 U8, .mul U8 RZ U5, .sub U7 U7 U2,
    .sub U7 U7 U3, .mul RX U8 U7, .mul U8 RZ U6, .sub U7 U3 U2, .mul RY U8 U7, .mul RZ U5 U6]

/-- The table at `a3 + CTAB`, `a3` moved there and back. -/
def tabBuild : List Instr :=
  [.addi .a3 .a3 2047, .addi .a3 .a3 1] ++
    (List.range 16).flatMap (fun i =>
      constField (112 * i) (Comb.entry i).1.val ++ constField (112 * i + 56) (Comb.entry i).2.val) ++
    [.addi .a3 .a3 (-2048)]

/-- `R = (0 : 1 : 1)` and `d`. -/
def combInit : List Instr :=
  constField RX Spec.Ed448.identity.X.val ++ constField RY Spec.Ed448.identity.Y.val ++
    constField RZ Spec.Ed448.identity.Z.val ++ constField DK Spec.Ed448.d.val

/-- The row's index into `a5`: bits `t`, `t + 114`, `t + 228` and `t + 342`
of the scalar (`t = t1`), as `i₀ + 2 i₁ + 4 i₂ + 8 i₃`. -/
def combDigit : List Instr :=
  [.add .a1 .a3 .t1, .load .b .a5 .a1 (BITS + 342), .load .b .a4 .a1 (BITS + 228),
    .add .a5 .a5 .a5, .add .a5 .a5 .a4, .load .b .a4 .a1 (BITS + 114), .add .a5 .a5 .a5,
    .add .a5 .a5 .a4, .load .b .a4 .a1 BITS, .add .a5 .a5 .a5, .add .a5 .a5 .a4]

/-- Doubleword `k` of entry `i` (in `t2 = a3 + CTAB`) into doubleword `k` of
`(SX, SY)` if the mask `t0` is all ones. -/
def selWord (i k : Nat) : List Instr :=
  [.load .d .a2 .a3 (SX + 8 * k), .load .d .a4 .t2 (112 * i + 8 * k), .logic .and .a4 .a4 .t0,
    .logic .or .a2 .a2 .a4, .store .d .a2 .a3 (SX + 8 * k)]

/-- Entry `i`, under the mask `t0 = -(a5 = i)`. -/
def selEntry (i : Nat) : List Instr :=
  [.logicImm .xor .a2 .a5 i, .li .a6 1, .sltu .a2 .a2 .a6, .li .t0 0, .sub .t0 .t0 .a2] ++
    (List.range 14).flatMap (selWord i)

/-- `(SX, SY)` zeroed, then every entry scanned. -/
def combSelect : List Instr :=
  .li .a2 0 :: (List.range 14).flatMap (fun k => [.store .d .a2 .a3 (SX + 8 * k)]) ++
    [.addi .t2 .a3 2047, .addi .t2 .t2 1] ++ (List.range 16).flatMap selEntry

/-- One row, `t = t1 - 1`. -/
def combStep : Prog isa :=
  .seq (.block [.addi .t1 .t1 (-1)]) <| .seq (opsProg dblOps) <|
    .seq (.block (combDigit ++ combSelect)) (opsProg addOps)

/-- The 114 rows, from 113 down to 0. -/
def combLoop : Prog isa := .seq (.block [.li .t1 114]) (.loop combStep (.nonzero .t1))

/-- `vg_ed448_scalar_base(out = a0, scalar = a1, scratch = a2)`. -/
def scalarBase : Prog isa :=
  .seq (.block ([.addi .a3 .a2 0] ++ align ++ combInit ++ tabBuild)) <| .seq baseBits <|
    .seq combLoop baseEncode

end VG.Impl.Ed448.RISCV64
