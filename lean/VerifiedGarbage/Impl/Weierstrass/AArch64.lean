module

public import VerifiedGarbage.Impl.Mont.AArch64
public import VerifiedGarbage.Impl.Mont.AArch64.P256Square
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Mont
public import VerifiedGarbage.Impl.Weierstrass.Slots

/-!
# Short Weierstrass curves on AArch64: points and scalar multiplication

Code for any curve `y² = x³ + ax + b` over a prime field of `n` 64-bit
words, with the Montgomery arithmetic of `Impl/Mont/AArch64.lean`. Field
elements are in Montgomery form (`x R mod p`, `R = 2^(64 n)`) in slots of
the working space, whose base is in `x0`; a point is three slots, projective
coordinates `(X : Y : Z)`.

* `fprog`: field operations on slots (`FOp`, `Impl/Weierstrass/Slots.lean`),
  such as the complete addition `rcb`, one after the other.
* `ladder`: `[k]G` by double-and-add from the top bit, 256 times (or as many
  bits as the table has): `D = R + R`, `S = D + G` and `R = D` or `S` by a
  mask of the bit, so every iteration does the same.
* powers are by chains of the exponent (`AArch64/Chain.lean`).
* `bits`: the bits of a little-endian number in a slot, one byte each.

The loops count down in `x19`. The only branches are on it, and every
address is `x0` plus a constant, or plus the counter: nothing but `x0` may
affect timing.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.AArch64

open VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass

/-- The code of a field operation. -/
def opCode (M : Mod) : FOp → List Instr
  | .mul o a b => if a == b && P256Square.supported M then
      P256Square.square M o a else Mont.AArch64.mul M o a b
  | .add o a b => Mont.AArch64.add M o a b
  | .sub o a b => Mont.AArch64.sub M o a b

/-- A straight-line sequence of field operations. -/
def fprog (M : Mod) (ops : List FOp) : List Instr := ops.flatMap (opCode M)

/-- `[o] = [a] [b] R⁻¹ mod m` by a call of the function `f`, whose code is
`Mont.mulFn n m`, on the working space at `x0`: `x30`, which the call
changes, is kept in `v29`, which the function does not write, and the
offsets are the arguments (below `2¹⁶`). -/
def mulCall (f : String) (n m o a b : Nat) : Prog isa :=
  .seq (.block [.vop (.ins .d2 .v29 0 .x30), .movz .x .x1 (BitVec.ofNat 16 o) 0,
      .movz .x .x2 (BitVec.ofNat 16 a) 0, .movz .x .x3 (BitVec.ofNat 16 b) 0]) <|
    .seq (.call f (Mont.mulFn n m)) (.block [.umov .x .x30 .v29 0])

/-- The code of a field operation: a call for a product modulo a modulus
whose products are functions (`Mont.callOf`), else `opCode`. -/
def opProg (M : Mod) (op : FOp) : Prog isa :=
  match op, Mont.callOf M with
  | .mul o a b, some (f, m) => mulCall f M.n m o a b
  | op, _ => .block (opCode M op)

/-- Programs one after the other. -/
def progs : List (Prog isa) → Prog isa
  | [] => .block []
  | [p] => p
  | p :: ps => .seq p (progs ps)

/-- Straight-line code as a sequence of blocks (the same instructions as their
concatenation; the kernel handles many short blocks better than one long one). -/
def blocks : List (List Instr) → Prog isa
  | [] => .block []
  | [b] => .block b
  | b :: bs => .seq (.block b) (blocks bs)

/-- `fprog`, a block per operation, or a call for a product. -/
def fprogB (M : Mod) (ops : List FOp) : Prog isa := progs (ops.map (opProg M))

/-- `[o] = [a]` if the mask `x3` is zero, `[b]` if it is all ones, `n`
words, through `x1` and `x2`. -/
def sel : Nat → Nat → Nat → Nat → List Instr
  | 0, _, _, _ => []
  | k + 1, o, a, b => [ld .x1 a, ld .x2 b, .logic .eor .x .x2 .x2 .x1, .logic .and .x .x2 .x2 .x3,
      .logic .eor .x .x1 .x1 .x2, st .x1 o] ++ sel k (o + 8) (a + 8) (b + 8)

/-- `o = a` or `b`, a point, by the mask `x3`. -/
def selPt (n : Nat) (o a b : Pt) : List Instr :=
  sel n o.x a.x b.x ++ sel n o.y a.y b.y ++ sel n o.z a.z b.z

/-- `[o] = [a]`, `n` words, through `x1`. -/
def copy : Nat → Nat → Nat → List Instr
  | 0, _, _ => []
  | k + 1, o, a => [ld .x1 a, st .x1 o] ++ copy k (o + 8) (a + 8)

/-- The mask `x3 = -[x0 + x19 + d]` of the bit of iteration `x19`, through
`x1`, `x7` and `x16`. -/
def bitMask (d : Nat) : List Instr :=
  [.movz .x .x7 0 0, .add .x .x16 .x0 .x19, .ldrb .x1 .x16 d, .sub .x .x3 .x7 .x1]

/-- `x19 -= 1`. -/
def decCounter : Instr := .subImm .x .x19 .x19 1

/-- One iteration of the ladder, for the bit `t = x19 - 1`: `D = R + R`,
`T = D + G`, then `R = T` if bit `t` is set, else `D`. -/
def ladderBody (L : LadderCfg) : Prog isa :=
  .seq (.block [decCounter]) <| .seq (fprogB L.M (rcb L.S L.R L.R L.D)) <|
    .seq (fprogB L.M (rcb L.S L.D L.G L.T)) <|
    .block (bitMask L.bits ++ selPt L.M.n L.R L.D L.T)

/-- The ladder over the bits `nbits - 1` down to 0, from `R` as set up by the
caller (the point at infinity). -/
def ladder (L : LadderCfg) : Prog isa :=
  .seq (.block [.movz .x .x19 (BitVec.ofNat 16 L.nbits) 0]) (.loop (ladderBody L) (.nonzero .x .x19))

/-- `x2` all ones iff `x1 = 0` (below 1), with `x7 = 0`, through `x5` and `x16`. -/
def isZeroMask : List Instr := [.movz .x .x5 1 0, .subs .x .x16 .x1 .x5, .sbc .x .x2 .x7 .x7]

/-- `x2` all ones iff the `n`-word number at `a` is zero: the `orr` of its words
in `x1`, through `x2`. -/
def zeroMask (n a : Nat) : List Instr :=
  [zero7, ld .x1 a] ++ ((List.range (n - 1)).flatMap fun j =>
    [ld .x2 (a + 8 * (j + 1)), .logic .orr .x .x1 .x1 .x2]) ++ isZeroMask

/-- Byte `j` of the table at `dst` for byte `x19` of the number: bit `j` of
`x1` (with `x5 = 1`), stored at `x17 + dst + j`, where `x17 = x0 + 8 x19`. -/
def bitJ (dst j : Nat) : List Instr :=
  (if j = 0 then [.logic .and .x .x2 .x1 .x5] else [.lsr .x .x2 .x1 j, .logic .and .x .x2 .x2 .x5]) ++
    [.strb .x2 .x17 (dst + j)]

/-- The table at `dst` of the bits of the `nbytes`-byte little-endian number at
`src`: byte `8i + j` is bit `j` of byte `i` (so byte `t` is bit `t`), from
the top byte down. -/
def bits (src dst nbytes : Nat) : Prog isa :=
  .seq (.block [.movz .x .x19 (BitVec.ofNat 16 nbytes) 0, .movz .x .x5 1 0]) (.loop (.block (
    [decCounter, .add .x .x16 .x0 .x19, .ldrb .x1 .x16 src, .lsl .x .x17 .x19 3,
      .add .x .x17 .x0 .x17] ++
    (List.range 8).flatMap (bitJ dst))) (.nonzero .x .x19))

/-! ## Numbers as bytes -/

/-- `[x0 + o] = ` the `len`-byte big-endian number at `[src]`, `n` words
(`8 (n - 1) ≤ len ≤ 8 n`, `8 ≤ len`), through `x5` (and `x17`): word `j` the
byte reversal of the eight bytes at `src + len - 8 (j + 1)` (through
`x17 = ` that address unless `len` is a multiple of 8, as `ldr` needs), and a
top word of fewer bytes `t` the first eight bytes' reversal shifted right by
`8 (8 - t)`. -/
def loadBytes (len n o : Nat) (src : Reg) : List Instr :=
  (List.range n).flatMap fun j =>
    if 8 * (j + 1) ≤ len then
      if len % 8 = 0 then [.ldr .x .x5 src (len - 8 * (j + 1)), .rev .x5 .x5, st .x5 (o + 8 * j)]
      else [.addImm .x .x17 src (len - 8 * (j + 1)), .ldr .x .x5 .x17 0, .rev .x5 .x5, st .x5 (o + 8 * j)]
    else if len ≤ 8 * j then const64 .x5 0 ++ [st .x5 (o + 8 * j)]
    else [.ldr .x .x5 src 0, .rev .x5 .x5, .lsr .x .x5 .x5 (8 * (8 * (j + 1) - len)), st .x5 (o + 8 * j)]

/-- `[x0 + o] = [x0 + o] >> sh`, `n` words (`0 < sh < 64`), through `x1` and
`x2`: word `j` is bits `sh … sh + 63` of words `j + 1` and `j` (`extr`), the
top word shifted right. -/
def shrWords (n o sh : Nat) : List Instr :=
  (List.range n).flatMap fun j =>
    [ld .x1 (o + 8 * j)] ++
    (if j + 1 < n then [ld .x2 (o + 8 * (j + 1)), .extr .x .x1 .x2 .x1 sh] else [.lsr .x .x1 .x1 sh]) ++
    [st .x1 (o + 8 * j)]

/-- `[dst + d] = ` the `n`-word number at `[x0 + a]` masked with `x3`, in
`len` bytes big-endian (`8 (n - 1) ≤ len ≤ 8 n`), through `x1`, `x2` (and
`x17`): its whole words byte-reversed to `dst + d + len - 8 (j + 1)`
(through `x17 = ` that address unless `d + len` is a multiple of 8), and a
top word of fewer bytes a byte at a time. -/
def storeBytes (len n : Nat) (dst : Reg) (d a : Nat) : List Instr :=
  (List.range n).flatMap fun j =>
    if 8 * (j + 1) ≤ len then
      [ld .x1 (a + 8 * j), .logic .and .x .x1 .x1 .x3, .rev .x1 .x1] ++
      (if (d + len) % 8 = 0 then [.str .x .x1 dst (d + (len - 8 * (j + 1)))]
      else [.addImm .x .x17 dst (d + (len - 8 * (j + 1))), .str .x .x1 .x17 0])
    else
      [ld .x1 (a + 8 * j), .logic .and .x .x1 .x1 .x3] ++
      (List.range (len - 8 * j)).flatMap fun i =>
        if len - 8 * j - 1 - i = 0 then [.strb .x1 dst (d + i)]
        else [.lsr .x .x2 .x1 (8 * (len - 8 * j - 1 - i)), .strb .x2 dst (d + i)]

/-- `[x0 + o] = x`, `n` words, through `x1`. -/
def setConst (n : Nat) (o x : Nat) : List Instr :=
  (List.range n).flatMap fun j => const64 .x1 (BitVec.ofNat 64 (x >>> (64 * j))) ++ [st .x1 (o + 8 * j)]

end VG.Impl.Weierstrass.AArch64
