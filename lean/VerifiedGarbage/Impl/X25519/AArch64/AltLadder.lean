module

public import VerifiedGarbage.Impl.X25519.AArch64.AltOps
public import VerifiedGarbage.Impl.X25519.AArch64.Word
public import VerifiedGarbage.Impl.Ed25519.AArch64.Divstep

/-!
# X25519 on AArch64: s2n-bignum's `_alt` ladder

The ladder of `curve25519_x25519_byte_alt` (see `AltOps`), its iteration
operation for operation, with its order and its sharing of slots: the sums and
differences of both points, the product `DA` of the addition, then the bit,
the point to double chosen by `mux_4` (no swap of the points), and the rest of
the addition and the doubling. Slots 1–4 hold `(X₂, Z₂)` and `(X₃, Z₃)` of
RFC 7748's ladder, below `2·p`; slot 0 holds `X₁`. As in s2n-bignum, the
iterations for the bits clamping sets (254) and clears (2, 1, 0) are
specialized (`first`, `tail`); the function shares `Word`'s setup, inversion
and output.
-/

@[expose] public section

namespace VG.Impl.X25519.AArch64.AltLadder

open VG.AArch64 VG.Impl.Ed25519.AArch64
open VG.Impl.X25519.AArch64.Alt

/-- The bit of the scalar for this iteration, which it stores as the new swap,
and `Z` set if it equals the old one (so that the point at `xn` is doubled). -/
def bitFlags : List Instr :=
  [.subImm .x .x19 .x19 1, .add .x .x8 .x0 .x19, .ldrb .x2 .x8 Word.BITS,
    Word.ld .x3 Word.SWAP, Word.st .x2 Word.SWAP, .subs .x .x3 .x3 .x2]

/-- `[o] := 121666·[a] + [b]` (`cmadd_4`), with `x1` (the output pointer)
kept in `x20` meanwhile. -/
def cmaddA24 (o a b : Nat) : List Instr :=
  [VG.Impl.Ed25519.AArch64.mov .x20 .x1, .movz .x .x1 0xdb42 0, .movk .x .x1 1 1] ++
  cmadd4 o a b ++ [VG.Impl.Ed25519.AArch64.mov .x1 .x20]

/-- One iteration. Slots: 0 `X₁`; 1 `xn` (and `s`); 2 `zn` (and `dn`, `e`);
3 `xm` (and `dnsm`, `spro`); 4 `zm` (and `sm`, `dpro`); 5 `sn`; 6 `dm`;
7 `dmsn` (and `p`); 8 `d`. -/
def body : List Instr :=
  [.movz .x .x17 0 0] ++
  subTwice4 (offset 6) (offset 3) (offset 4) ++ addTwice4 (offset 5) (offset 1) (offset 2) ++
  subTwice4 (offset 2) (offset 1) (offset 2) ++ addTwice4 (offset 4) (offset 3) (offset 4) ++
  mul4 (offset 7) (offset 5) (offset 6) ++
  bitFlags ++
  mux4 (offset 8) (offset 6) (offset 2) ++ mux4 (offset 1) (offset 4) (offset 5) ++
  mul4 (offset 3) (offset 4) (offset 2) ++ sqr4 (offset 8) (offset 8) ++
  subTwice4 (offset 4) (offset 7) (offset 3) ++ sqr4 (offset 1) (offset 1) ++
  addTwice4 (offset 3) (offset 7) (offset 3) ++ sqr4 (offset 4) (offset 4) ++
  subTwice4 (offset 7) (offset 1) (offset 8) ++ sqr4 (offset 3) (offset 3) ++
  cmaddA24 (offset 2) (offset 7) (offset 8) ++
  mul4 (offset 1) (offset 1) (offset 8) ++ mul4 (offset 4) (offset 4) (offset 0) ++
  mul4 (offset 2) (offset 7) (offset 2)

/-- An iteration, ending with `x16 = x19 - 3`, zero after the one for bit 3. -/
def step : List Instr := body ++ [.subImm .x .x16 .x19 3]

/-- `[o] := 4·[a] + [b]` (`cmadd_4`), with `x1` kept in `x20` meanwhile. -/
def cmadd4x (o a b : Nat) : List Instr :=
  [VG.Impl.Ed25519.AArch64.mov .x20 .x1, .movz .x .x1 4 0] ++
  cmadd4 o a b ++ [VG.Impl.Ed25519.AArch64.mov .x1 .x20]

/-- The iteration for bit 254, which clamping sets: from `(X₂, Z₂) = (1, 0)`
and `(X₃, Z₃) = (X₁, 1)`, the swap makes `(X₁, 1)` the point doubled, and the
sum of the points is `(4·X₁², 4·X₁)`. As s2n-bignum's start, a doubling of
`(X₁, 1)`, but with RFC 7748's `(X₃, Z₃)`. -/
def first : List Instr :=
  [.movz .x .x17 0 0] ++
  subTwice4 (offset 8) (offset 3) (offset 4) ++ addTwice4 (offset 1) (offset 3) (offset 4) ++
  cmadd4x (offset 4) (offset 0) (offset 2) ++
  sqr4 (offset 8) (offset 8) ++ sqr4 (offset 1) (offset 1) ++
  mul4 (offset 3) (offset 0) (offset 4) ++
  subTwice4 (offset 7) (offset 1) (offset 8) ++ cmaddA24 (offset 2) (offset 7) (offset 8) ++
  mul4 (offset 1) (offset 1) (offset 8) ++ mul4 (offset 2) (offset 7) (offset 2) ++
  [.movz .x .x2 1 0, Word.st .x2 Word.SWAP]

/-- Doubling `(xn, zn)` in slots 1 and 2. -/
def dbl : List Instr :=
  subTwice4 (offset 8) (offset 1) (offset 2) ++ addTwice4 (offset 1) (offset 1) (offset 2) ++
  sqr4 (offset 8) (offset 8) ++ sqr4 (offset 1) (offset 1) ++
  subTwice4 (offset 7) (offset 1) (offset 8) ++ cmaddA24 (offset 2) (offset 7) (offset 8) ++
  mul4 (offset 1) (offset 1) (offset 8) ++ mul4 (offset 2) (offset 7) (offset 2)

/-- The iterations for bits 2, 1 and 0, which clamping clears: the point the
swap chooses (`mux_4` into slots 1 and 2), doubled three times, as in
s2n-bignum. -/
def tail : List Instr :=
  [.movz .x .x17 0 0, Word.ld .x3 Word.SWAP, .movz .x .x2 0 0, .subs .x .x3 .x3 .x2] ++
  mux4 (offset 1) (offset 3) (offset 1) ++ mux4 (offset 2) (offset 4) (offset 2) ++
  dbl ++ dbl ++ dbl

/-- The iterations for bits 253 down to 3. -/
def ladder : Prog isa :=
  .seq (.block [.movz .x .x19 254 0]) (.loop (.block step) (.nonzero .x .x16))

def x25519 : Prog isa :=
  .seq (.block Word.setup) <| .seq (.block first) <| .seq ladder <| .seq (.block tail) <|
  .seq VG.Impl.Ed25519.AArch64.Divstep.invert (.block Word.finish)

end VG.Impl.X25519.AArch64.AltLadder
