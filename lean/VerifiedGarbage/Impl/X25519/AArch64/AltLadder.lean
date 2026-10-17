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
RFC 7748's ladder, below `2·p`; slot 0 holds `X₁`. Unlike s2n-bignum, all 255
iterations run from bit 254 down (the clamped bits included), as in `Word`,
whose setup, last swap, inversion and output the function shares.
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
def step : List Instr :=
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

def ladder : Prog isa :=
  .seq (.block [.movz .x .x19 255 0]) (.loop (.block step) (.nonzero .x .x19))

def x25519 : Prog isa :=
  .seq (.block Word.setup) <| .seq ladder <| .seq (.block Word.lastSwap) <|
  .seq VG.Impl.Ed25519.AArch64.Divstep.invert (.block Word.finish)

end VG.Impl.X25519.AArch64.AltLadder
