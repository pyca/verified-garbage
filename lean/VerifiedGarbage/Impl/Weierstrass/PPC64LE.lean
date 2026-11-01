module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.Call

/-!
# Short Weierstrass curves on PPC64LE: points, scalar multiplication, powers

Code for any curve `y² = x³ + ax + b` over a prime field of `n` 64-bit
words, whose Montgomery arithmetic is calls of the functions of a modulus
(`Proof/Weierstrass/MontContract.lean`, `Impl/Weierstrass/PPC64LE/Mont.lean`), which
use the `64 n` bytes of the working space below byte 4096 for themselves.
Field elements are in Montgomery form (`x R mod p`, `R = 2^(64 n)`) in slots
of the working space, whose base is in `r3`, which the functions keep; a
point is three slots, projective coordinates `(X : Y : Z)`. As on 32-bit ARM
(`Impl/Weierstrass/Arm.lean`):

* `fprog`: field operations on slots (`FOp`, `Impl/Weierstrass/Slots.lean`),
  such as the complete addition `rcb`, one after the other.
* `ladder`: `[k]G` by double-and-add from the top bit, 256 times (or as many
  bits as the table has): `D = R + R`, `S = D + G` and `R = D` or `S` by a
  mask of the bit (in `r10`), so every iteration does the same.
* `pow`: `x^e` by square-and-multiply over the bits of a public exponent,
  also always multiplying and selecting by a mask, so that one loop serves
  every exponent.
* `bits`: the bits of a little-endian number in a slot, one byte each.
* `loadBytes`, `shrWords`, `storeBytes`: numbers to and from big-endian
  bytes (`ldbrx`, `stdbrx`).

The loops count down in `r31`, which the functions called keep (the caller
saves it). The only branches are on it, and every address is `r3` plus a
constant, or plus the counter: nothing but `r3` may affect timing.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.PPC64LE

open VG.PPC64LE VG.Impl.Weierstrass

/-- The working space's base. -/
abbrev wb : Reg := .r3

/-- `d = s` (`mr d, s`, the extended mnemonic of `or d, s, s`). -/
def mov (d s : Reg) : Instr := .logic .or d s s

/-- `[o] = [a]` if the mask `r10` is zero, `[b]` if it is all ones, `k`
64-bit words, through `r4` and `r5`. -/
def sel : Nat → Nat → Nat → Nat → List Instr
  | 0, _, _, _ => []
  | k + 1, o, a, b => [.load .d .r4 wb a, .load .d .r5 wb b, .logic .xor .r5 .r5 .r4, .logic .and .r5 .r5 .r10,
      .logic .xor .r4 .r4 .r5, .store .d .r4 wb o] ++ sel k (o + 8) (a + 8) (b + 8)

/-- `o = a` or `b`, a point of `n`-word coordinates, by the mask `r10`. -/
def selPt (n : Nat) (o a b : Pt) : List Instr :=
  sel n o.x a.x b.x ++ sel n o.y a.y b.y ++ sel n o.z a.z b.z

/-- `[o] = [a]`, `k` 64-bit words, through `r4`. -/
def copy : Nat → Nat → Nat → List Instr
  | 0, _, _ => []
  | k + 1, o, a => [.load .d .r4 wb a, .store .d .r4 wb o] ++ copy k (o + 8) (a + 8)

/-- The mask `r10 = -[r3 + r31 + d]` of the bit of iteration `r31`,
through `r4` and `r5`. -/
def bitMask (d : Nat) : List Instr := [.add .r4 wb .r31, .lbz .r4 .r4 d, .li .r5 0, .sub .r10 .r5 .r4]

/-- `r31 -= 1`. -/
def decCounter : Instr := .subi .r31 .r31 1

/-- The loops' condition: `r31` is not zero. -/
abbrev more : Cond := .nonzero .d .r31

/-- One iteration of the ladder, for the bit `t = r31 - 1`: `D = R + R`,
`T = D + G`, then `R = T` if bit `t` is set, else `D`, modulo `S`. -/
def ladderBody (L : LadderCfg) (S : Impl.Weierstrass.Mont.Modulus) : Prog isa :=
  .seq (.block [decCounter]) <| .seq (fprog S (rcb L.S L.R L.R L.D)) <|
    .seq (fprog S (rcb L.S L.D L.G L.T)) <|
    .block (bitMask L.bits ++ selPt L.M.n L.R L.D L.T)

/-- The ladder over the bits `nbits - 1` down to 0, from `R` as set up by the
caller (the point at infinity). -/
def ladder (L : LadderCfg) (S : Impl.Weierstrass.Mont.Modulus) : Prog isa :=
  .seq (.block [.li .r31 L.nbits]) (.loop (ladderBody L S) more)

/-- One iteration: `acc = acc²`, `tmp = acc · base`, and `acc = tmp` if the
exponent's bit `r31 - 1` is set, modulo `S`. -/
def powBody (P : PowCfg) (S : Impl.Weierstrass.Mont.Modulus) : Prog isa :=
  .seq (.block [decCounter]) <| .seq (mulCall S P.acc P.acc P.acc) <|
  .seq (mulCall S P.tmp P.acc P.base) <|
    .block (bitMask P.bits ++ sel P.M.n P.acc P.acc P.tmp)

/-- `[acc] = [base]^e` (in Montgomery form), from the top bit of `e`. -/
def pow (P : PowCfg) (S : Impl.Weierstrass.Mont.Modulus) : Prog isa :=
  .seq (.block (copy P.M.n P.acc P.one ++ [.li .r31 P.nbits])) (.loop (powBody P S) more)

/-- Byte `j` of the table for byte `r31` of the number: bit `j` of `r4`,
stored at `[r5 + dst + j]`, where `r5 = r3 + 8 r31` (`r7 = 1`), through
`r6`. -/
def bitJ (dst j : Nat) : List Instr :=
  (if j = 0 then [.logic .and .r6 .r4 .r7] else [.lsr .d .r6 .r4 j, .logic .and .r6 .r6 .r7]) ++
    [.stb .r6 .r5 (dst + j)]

/-- The table at `dst` of the bits of the `nbytes`-byte little-endian number at
`src`: byte `8i + j` is bit `j` of byte `i` (so byte `t` is bit `t`), from
the top byte down. -/
def bits (src dst nbytes : Nat) : Prog isa :=
  .seq (.block [.li .r31 nbytes]) (.loop (.block (
    [decCounter, .add .r4 wb .r31, .lbz .r4 .r4 src, .lsl .r5 .r31 3, .add .r5 wb .r5, .li .r7 1] ++
    (List.range 8).flatMap (bitJ dst))) more)

/-! ## Numbers as bytes -/

/-- `[r3 + o] = ` the `len`-byte big-endian number at `[src]`, in `n`
64-bit words (`8 ≤ len ≤ 8 n`), through `r8` and `r9`: word `j` is the
big-endian doubleword at `src + len - 8 (j + 1)` (`ldbrx`), a word of fewer
bytes `t` the first eight bytes shifted right by `8 (8 - t)` bits, and the
words past `len` zero. -/
def loadBytes (len n o : Nat) (src : Reg) : List Instr :=
  (List.range n).flatMap fun j =>
    if 8 * (j + 1) ≤ len then
      [.li .r9 (len - 8 * (j + 1)), .loadRev .d .r8 src .r9, .store .d .r8 wb (o + 8 * j)]
    else if 8 * j < len then
      [.li .r9 0, .loadRev .d .r8 src .r9, .lsr .d .r8 .r8 (8 * (8 * (j + 1) - len)),
        .store .d .r8 wb (o + 8 * j)]
    else [.li .r8 0, .store .d .r8 wb (o + 8 * j)]

/-- `[r3 + o] = [r3 + o] >> sh`, `n` 64-bit words (`0 < sh < 64`), through
`r4` and `r8`: word `j` is word `j` shifted right, or'd with word `j + 1`
shifted left by `64 - sh`. -/
def shrWords (n o sh : Nat) : List Instr :=
  (List.range n).flatMap fun j =>
    ([.load .d .r4 wb (o + 8 * j), .lsr .d .r4 .r4 sh] : List Instr) ++
    ((if j + 1 < n then
      [.load .d .r8 wb (o + 8 * (j + 1)), .lsl .r8 .r8 (64 - sh), .logic .or .r4 .r4 .r8]
    else []) : List Instr) ++
    ([.store .d .r4 wb (o + 8 * j)] : List Instr)

/-- `[dst + d] = ` the `n`-word number at `[r3 + a]` masked with `r10`, in
`len` bytes big-endian (`len ≤ 8 n`, the number below `2^(8 len)`), through
`r4`–`r6`: its whole 64-bit words byte-reversed to `dst + d + len - 8 (j +
1)` (`stdbrx`), a word of fewer bytes a byte at a time, and nothing of the
words past `len`. -/
def storeBytes (len n : Nat) (dst : Reg) (d a : Nat) : List Instr :=
  (List.range n).flatMap fun j =>
    if 8 * (j + 1) ≤ len then
      [.load .d .r4 wb (a + 8 * j), .logic .and .r4 .r4 .r10, .li .r6 (d + (len - 8 * (j + 1))),
        .storeRev .d .r4 dst .r6]
    else if 8 * j < len then
      [.load .d .r4 wb (a + 8 * j), .logic .and .r4 .r4 .r10] ++
      (List.range (len - 8 * j)).flatMap fun i =>
        if len - 8 * j - 1 - i = 0 then [.stb .r4 dst (d + i)]
        else [.lsr .d .r5 .r4 (8 * (len - 8 * j - 1 - i)), .stb .r5 dst (d + i)]
    else []

end VG.Impl.Weierstrass.PPC64LE
