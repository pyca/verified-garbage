module

public import VerifiedGarbage.Impl.X25519.AArch64.Word
public import VerifiedGarbage.Impl.X25519.AArch64.Neon
public import VerifiedGarbage.Impl.AArch64Weave
public import VerifiedGarbage.Impl.Ed25519.AArch64.Divstep

/-!
# X25519 on AArch64: the ladder's products `DA` and `CB` in AdvSIMD

`Word.lean`'s ladder, but for where each iteration computes `DA = D·A` and
`CB = C·B`: in AdvSIMD (`Neon.prod2`), as radix-2²⁵·⁵ limbs, interleaved with
the scalar operations that do not need them (`AA`, `BB`, `E`, `X₂ = AA·BB` and
`Z₂ = E·(AA + a24·E)`), so that the vector and the integer units run at once.
The scalar code then adds the limbs up into `X₃ = DA + CB` and `Z₃ = DA - CB`
(`recombine`), exactly, before squaring them.

The function saves `v8`–`v15` (which the products use) at `VSAVE`, and writes
the products' constants at `Neon.CONST` before the ladder.
-/

@[expose] public section

namespace VG.Impl.X25519.AArch64.Hybrid

open VG.AArch64 VG.Impl.Ed25519.AArch64

/-- `[x0 + off]` into `t`. -/
abbrev ld (t : Reg) (off : Nat) : Instr := VG.Impl.Ed25519.AArch64.ld t off
/-- `t` into `[x0 + off]`. -/
abbrev st (t : Reg) (off : Nat) : Instr := VG.Impl.Ed25519.AArch64.st t off
open VG.Impl.X25519.AArch64.Neon (CONST M26 M25 C19 V)
open VG.Impl.AArch64Weave (weave)

/-- The limbs of `DA` (lane 0) and `CB` (lane 1). -/
def LBUF : Nat := 944
/-- Where `v8`–`v15` are saved. -/
def VSAVE : Nat := 1152

/-- `4p` in radix 2²⁵·⁵: limb `k`, added to the limbs of `DA - CB`. -/
def bias (k : Nat) : Nat := if k = 0 then 2 ^ 28 - 76 else if k % 2 = 0 then 2 ^ 28 - 4 else 2 ^ 27 - 4

/-- The register holding `bias k` (`x9`, `x16` or `x17`). -/
def biasReg (k : Nat) : Reg := if k = 0 then .x9 else if k % 2 = 0 then .x16 else .x17

/-- Put limb `k`, in `x12`, at bit `limbOff k` of one of two accumulators: the
limbs of even index in `x4`–`x7`, those of odd index in `x2`, `x3`, `x8`,
`x21`, `x15`. Limbs of the same parity are 51 bits apart and below 2²⁹, so
they never overlap: each word is written by its first limb and added to
without a carry by the next. -/
def put : Nat → List Instr
  | 0 => [mov .x4 .x12]
  | 1 => [.lsl .x .x2 .x12 26]
  | 2 => [.lsl .x .x14 .x12 51, .add .x .x4 .x4 .x14, .lsr .x .x5 .x12 13]
  | 3 => [.lsl .x .x3 .x12 13]
  | 4 => [.lsl .x .x14 .x12 38, .add .x .x5 .x5 .x14, .lsr .x .x6 .x12 26]
  | 5 => [mov .x8 .x12]
  | 6 => [.lsl .x .x14 .x12 25, .add .x .x6 .x6 .x14]
  | 7 => [.lsl .x .x14 .x12 51, .add .x .x8 .x8 .x14, .lsr .x .x21 .x12 13]
  | 8 => [.lsl .x .x7 .x12 12]
  | _ => [.lsl .x .x14 .x12 38, .add .x .x21 .x21 .x14, .lsr .x .x15 .x12 26]

/-- Limb `k` of `DA + CB` (or of `DA + 4p - CB`, if `sub`) into `x12`, and into its accumulator. -/
def limbSum (sub : Bool) (k : Nat) : List Instr :=
  [ld .x12 (LBUF + 16 * k), ld .x13 (LBUF + 16 * k + 8)] ++
  (if sub then [.add .x .x12 .x12 (biasReg k), .sub .x .x12 .x12 .x13] else [.add .x .x12 .x12 .x13]) ++
  put k

/-- The two accumulators' sum into `x4`–`x7` and `x20`. -/
def combine : List Instr :=
  [.adds .x .x4 .x4 .x2, .adcs .x .x5 .x5 .x3, .adcs .x .x6 .x6 .x8, .adcs .x .x7 .x7 .x21,
    .adcs .x .x20 .x15 .x10]

/-- `[o] := DA + CB` (or `DA - CB`, if `sub`), from the limbs at `LBUF`. -/
def recombine (sub : Bool) (o : Nat) : List Instr :=
  [.movz .w .x10 0 0, .movz .w .x11 38 0] ++
  (if sub then
    [.movz .w .x9 0xffb4 0, .movk .w .x9 0x0fff 1, .movz .w .x16 0xfffc 0, .movk .w .x16 0x0fff 1,
      .movz .w .x17 0xfffc 0, .movk .w .x17 0x07ff 1]
   else []) ++
  (List.range 10).flatMap (limbSum sub) ++ combine ++ fold ++ store4 o

/-- The scalar half of the products' phase: `AA`, `BB`, `E`, `X₂ = AA·BB`, `Z₂ = E·(AA + a24·E)`. -/
def scalarA : List Instr :=
  fieldCode [.sqr 9 5, .sqr 10 6, .sub 11 9 10, .mul 1 9 10] ++
  VG.Impl.X25519.AArch64.mulA24 (offset 2) (offset 11) ++ fieldCode [.add 2 9 2, .mul 2 11 2]

/-- `DA` and `CB` in AdvSIMD. -/
def vectorA : List Instr := Neon.prod2 LBUF (offset 8) (offset 5) (offset 7) (offset 6)

/-- `X₃ = (DA + CB)²` and `Z₃ = X₁ (DA - CB)²`, the latter's square going straight
from its reduction to the product. -/
def tail : List Instr := fieldCode [.sqr 3 3] ++ fieldSqrMul (offset 4) (offset 0) (offset 4)

/-- The field operations of an iteration. -/
def stepFields : List Instr :=
  fieldCode [.add 5 1 2, .sub 6 1 2, .add 7 3 4, .sub 8 3 4] ++ weave scalarA vectorA ++
  recombine false (offset 3) ++ recombine true (offset 4) ++ tail

def step : List Instr := Word.stepHead ++ stepFields

def ladder : Prog isa :=
  .seq (.block [.movz .x .x19 255 0]) (.loop (.block step) (.nonzero .x .x19))

/-- The products' constants at `CONST`, with `x2` as a temporary. -/
def consts : List Instr :=
  [.movz .x .x2 0xffff 0, .movk .x .x2 0x03ff 1, st .x2 M26, st .x2 (M26 + 8),
    .movz .x .x2 0xffff 0, .movk .x .x2 0x01ff 1, st .x2 M25, st .x2 (M25 + 8),
    .movz .x .x2 19 0, .movk .x .x2 19 2, st .x2 C19, st .x2 (C19 + 8)]

def vsave : List Instr := (List.range 8).map fun k => .strq (V (8 + k)) .x0 (VSAVE + 16 * k)
def vrestore : List Instr := (List.range 8).map fun k => .ldrq (V (8 + k)) .x0 (VSAVE + 16 * k)

def setup : List Instr := Word.setup ++ vsave ++ consts

def finish : List Instr := vrestore ++ Word.finish

def x25519 : Prog isa :=
  .seq (.block setup) <| .seq ladder <| .seq (.block Word.lastSwap) <|
  .seq VG.Impl.Ed25519.AArch64.Divstep.invert (.block finish)

end VG.Impl.X25519.AArch64.Hybrid
