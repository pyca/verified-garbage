module

public import VerifiedGarbage.Impl.X448.RISCV64.R64
public import VerifiedGarbage.Spec.Ed448

/-!
# Ed448 on RISC-V: base-point multiplication

`vg_ed448_scalar_base(out = a0, scalar = a1, scratch = a2)`: the encoding of
`[s]B` for the 456-bit little-endian scalar `s`, without pruning.

The PPC64LE code (`Impl/Ed448/PPC64LE/ScalarBase.lean`), register for
register as X448's port is. X448's field code on this target does the
arithmetic: field elements are seven 64-bit words (the same 56 bytes as
fourteen 32-bit limbs) in the 56-byte slots of the working space, and the
operations are `mul`, `add`, `sub`, `cswap` and `invert` of
`Impl/X448/RISCV64/R64.lean` (with `mul` and `mulhu`, in the registers
`t0`, `t3`–`t6`, `a1`, `a2`, `a4`–`a7`) and `freeze` of
`Impl/X448/RISCV64.lean`. Points are the specification's projective
coordinates `(X : Y : Z)`. The working space, rounded up to a multiple of 8
(`align`), is in `a3`, as in X448; the constants' words are built with `lui`
and `addiw`.

As on PPC64LE, every bit takes two iterations of the same code, the
addition of RFC 8032 §5.2.4 (`pointAdd`) of `R` and `P`: `P` is `R` in the
first (a doubling, as the specification's `pointMul` doubles) and the base
point `Q` in the second, selected with a mask of the iteration's parity, and
the sum `T` replaces `R` with a mask: always in the first, and when the bit
is set in the second. The scalar's bits are expanded into bytes at X448's
`BITS` (byte `t` is bit `t`), as X448 expands its scalar.

The slots below X448's `ACC` hold `R`, `P`, `d`, `T` and the addition's
temporaries; `Q` is above `BITS`, read only by the selection. `R` is the
neutral point `(0 : 1 : 1)` at first. Finally `R` is encoded (§5.2.2): `Z`
inverted (X448's `invert`, `Z` being in its slot `Z2`), `x = X/Z` fully
reduced into `out` for its low bit, then `y = Y/Z`, and the bit as the top
bit of the 57th byte.

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
/-- The base point, above `BITS`. -/
def QX : Nat := 1520
def QY : Nat := 1576
def QZ : Nat := 1632

/-! ## Constants -/

/-- Word `k` of `v`, as `lui` and `addiw` build it (sign-extended) and `sw`
stores its low 32 bits. -/
def constLimb (o v k : Nat) : List Instr :=
  li32 .a4 (BitVec.ofNat 32 (v / 2 ^ (32 * k))) ++ [.store .w .a4 .a3 (o + 4 * k)]

/-- The element `v` into the slot at `o`. -/
def constField (o v : Nat) : List Instr := (List.range 14).flatMap (constLimb o v)

/-- `R = (0 : 1 : 1)`, `Q` the base point and `d`. -/
def initSlots : List Instr :=
  constField RX Spec.Ed448.identity.X.val ++ constField RY Spec.Ed448.identity.Y.val ++
    constField RZ Spec.Ed448.identity.Z.val ++ constField QX Spec.Ed448.basePoint.X.val ++
    constField QY Spec.Ed448.basePoint.Y.val ++ constField QZ Spec.Ed448.basePoint.Z.val ++
    constField DK Spec.Ed448.d.val

/-! ## The bits of the scalar -/

/-- `BITS[8i + j] = bit j of scalar[i]`, for the 57 bytes at `a1`. -/
def baseBits : Prog isa :=
  .seq (.block [.addi .a6 .a3 0, .li .t0 57]) (.loop (.block bitsBody) (.nonzero .t0))

/-! ## The loop -/

/-- Limb `k` of `[q]`, or of `[r]` if the mask `t0` is all ones, into limb
`k` of `[o]`. -/
def selStep (o q r k : Nat) : List Instr :=
  [.load .w .a2 .a3 (q + 4 * k), .load .w .a4 .a3 (r + 4 * k), .logic .xor .a4 .a4 .a2,
    .logic .and .a4 .a4 .t0, .logic .xor .a2 .a2 .a4, .store .w .a2 .a3 (o + 4 * k)]

def sel (o q r : Nat) : List Instr := (List.range 14).flatMap (selStep o q r)

/-- `P = R` if bit 0 of `t1` (the parity, into `t2`) is set, else `Q`. -/
def baseSelect : List Instr :=
  [.shift .sll .d .a1 .t1 63, .shift .srl .d .a1 .a1 63, .addi .t2 .a1 0, .li .t0 0, .sub .t0 .t0 .a1] ++
    sel PX QX RX ++ sel PY QY RY ++ sel PZ QZ RZ

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

/-- `T` swapped into `R` under the mask of the parity or bit `t1 >> 1` (from
`BITS`). -/
def baseSwap : List Instr :=
  [.shift .srl .d .a1 .t1 1, .add .a1 .a3 .a1, .load .b .a1 .a1 BITS, .logic .or .a1 .a1 .t2, .li .t0 0,
    .sub .t0 .t0 .a1] ++ cswap RX TX ++ cswap RY TY ++ cswap RZ TZ

/-- One iteration, `h = t1 - 1`: `R + R` if `h` is odd, `R + Q` if even, into
`R` if `h` is odd or bit `h >> 1` of the scalar set. -/
def baseStep : Prog isa :=
  .seq (.block ([.addi .t1 .t1 (-1)] ++ baseSelect)) <| .seq addition (.block baseSwap)

/-- Two iterations for each of the 456 bits, from 455 down to 0. -/
def baseLoop : Prog isa := .seq (.block [.li .t1 912]) (.loop baseStep (.nonzero .t1))

/-! ## The encoding -/

/-- `1/Z` into `R`; `x = X/Z` fully reduced into `out`, and its low bit as
bit 7 of `t1`; `y = Y/Z` fully reduced into `out`, and the bit as the top
bit of its 57th byte. -/
def baseEncode : Prog isa :=
  .seq invert <| .seq (mul X2 RX R) <|
  .seq (.block (freeze ++ [.load .b .t1 .a0 0, .li .a6 1, .logic .and .t1 .t1 .a6, .shift .sll .d .t1 .t1 7])) <|
  .seq (mul X2 RY R) (.block (freeze ++ [.store .b .t1 .a0 56]))

/-- `vg_ed448_scalar_base(out = a0, scalar = a1, scratch = a2)`. -/
def scalarBase : Prog isa :=
  .seq (.block ([.addi .a3 .a2 0] ++ align ++ initSlots)) <| .seq baseBits <| .seq baseLoop baseEncode

end VG.Impl.Ed448.RISCV64
