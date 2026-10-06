import VerifiedGarbage.Impl.Mont.Arm
import VerifiedGarbage.Impl.Weierstrass.Slots

/-!
# Short Weierstrass curves on 32-bit ARM: points, scalar multiplication, powers

Code for any curve `y² = x³ + ax + b` over a prime field of `n` 64-bit
words (`2n` 32-bit words), with the Montgomery arithmetic of
`Impl/Mont/Arm.lean`, whose operations use an accumulator of
`4 (8n + 2)` bytes at `wk` in the working space. Field elements are in
Montgomery form (`x R mod p`, `R = 2^(64 n)`) in slots of the working space,
whose base is in `r12`; a point is three slots, projective coordinates
`(X : Y : Z)`. As on x86 (`Impl/Weierstrass/X86.lean`):

* `fprog`: field operations on slots (`FOp`, `Impl/Weierstrass/Slots.lean`),
  such as the complete addition `rcb`, one after the other.
* `ladder`: `[k]G` by double-and-add from the top bit, 256 times (or as many
  bits as the table has): `D = R + R`, `S = D + G` and `R = D` or `S` by a
  mask of the bit (in `r10`), so every iteration does the same.
* `pow`: `x^e` by square-and-multiply over the bits of a public exponent,
  also always multiplying and selecting by a mask, so that one loop serves
  every exponent.
* `bits`: the bits of a little-endian number in a slot, one byte each.

The loops count down in `r11`, which the arithmetic does not use. The only
branches are on it and on the multiplications' counter `r9`, and every
address is `r12` plus a constant, or plus a counter: nothing but `r12` may
affect timing.
-/

namespace VG.Impl.Weierstrass.Arm

open VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Weierstrass

/-- The code of a field operation, with the accumulator at `wk`. -/
def opCode (M : Mod) (wk : Nat) : FOp → Prog isa
  | .mul o a b => Mont.Arm.mul M wk o a b
  | .add o a b => .block (Mont.Arm.add M wk o a b)
  | .sub o a b => .block (Mont.Arm.sub M wk o a b)

/-- Programs one after the other. -/
def progs : List (Prog isa) → Prog isa
  | [] => .block []
  | [p] => p
  | p :: ps => .seq p (progs ps)

/-- A straight-line sequence of field operations. -/
def fprog (M : Mod) (wk : Nat) (ops : List FOp) : Prog isa := progs (ops.map (opCode M wk))

/-- `[o] = [a]` if the mask `r10` is zero, `[b]` if it is all ones, `k`
32-bit words, through `r4` and `r5`. -/
def sel : Nat → Nat → Nat → Nat → List Instr
  | 0, _, _, _ => []
  | k + 1, o, a, b => [.ldr .r4 wb a, .ldr .r5 wb b, .dp .eor .r5 .r5 (.reg .r4), .dp .and .r5 .r5 (.reg .r10),
      .dp .eor .r4 .r4 (.reg .r5), .str .r4 wb o] ++ sel k (o + 4) (a + 4) (b + 4)

/-- `o = a` or `b`, a point of `n`-word coordinates, by the mask `r10`. -/
def selPt (n : Nat) (o a b : Pt) : List Instr :=
  sel (2 * n) o.x a.x b.x ++ sel (2 * n) o.y a.y b.y ++ sel (2 * n) o.z a.z b.z

/-- `[o] = [a]`, `k` 32-bit words, through `r4`. -/
def copy : Nat → Nat → Nat → List Instr
  | 0, _, _ => []
  | k + 1, o, a => [.ldr .r4 wb a, .str .r4 wb o] ++ copy k (o + 4) (a + 4)

/-- `r += 4096` if the offset `d` is past what a load or store reaches
(`d ≥ 4096`), which then takes `d - 4096`. -/
def far (r : Reg) (d : Nat) : List Instr := if d < 4096 then [] else [.dp .add r r (.imm 4096)]

/-- The mask `r10 = -[r12 + r11 + d]` of the bit of iteration `r11`,
through `r4` and `r5`. -/
def bitMask (d : Nat) : List Instr :=
  [.dp .add .r4 wb (.reg .r11)] ++ far .r4 d ++ [.ldrb .r4 .r4 (d % 4096), .mov .r5 (.imm 0),
    .dp .sub .r10 .r5 (.reg .r4)]

/-- `r11 -= 1`. -/
def decCounter : Instr := .dp .sub .r11 .r11 (.imm 1)

/-- `Z` for the loop: whether `r11` is zero. -/
def testCounter : Instr := .cmp .r11 (.imm 0)

/-- One iteration of the ladder, for the bit `t = r11 - 1`: `D = R + R`,
`T = D + G`, then `R = T` if bit `t` is set, else `D`. -/
def ladderBody (L : LadderCfg) (wk : Nat) : Prog isa :=
  .seq (.block [decCounter]) <| .seq (fprog L.M wk (rcb L.S L.R L.R L.D)) <|
    .seq (fprog L.M wk (rcb L.S L.D L.G L.T)) <|
    .block (bitMask L.bits ++ selPt L.M.n L.R L.D L.T ++ [testCounter])

/-- The ladder over the bits `nbits - 1` down to 0, from `R` as set up by the
caller (the point at infinity). -/
def ladder (L : LadderCfg) (wk : Nat) : Prog isa :=
  .seq (.block [.mov .r11 (.imm (BitVec.ofNat 32 L.nbits))]) (.loop (ladderBody L wk) .ne)

/-- One iteration: `acc = acc²`, `tmp = acc · base`, and `acc = tmp` if the
exponent's bit `r11 - 1` is set. -/
def powBody (P : PowCfg) (wk : Nat) : Prog isa :=
  .seq (.block [decCounter]) <| .seq (Mont.Arm.mul P.M wk P.acc P.acc P.acc) <|
  .seq (Mont.Arm.mul P.M wk P.tmp P.acc P.base) <|
    .block (bitMask P.bits ++ sel (2 * P.M.n) P.acc P.acc P.tmp ++ [testCounter])

/-- `[acc] = [base]^e` (in Montgomery form), from the top bit of `e`. -/
def pow (P : PowCfg) (wk : Nat) : Prog isa :=
  .seq (.block (copy (2 * P.M.n) P.acc P.one ++ [.mov .r11 (.imm (BitVec.ofNat 32 P.nbits))]))
    (.loop (powBody P wk) .ne)

/-- Byte `j` of the table for byte `r11` of the number: bit `j` of `r4`,
stored at `[r5 + dst + j]`, where `r5 = r12 + 8 r11`, through `r7`. -/
def bitJ (dst j : Nat) : List Instr :=
  (if j = 0 then [.dp .and .r7 .r4 (.imm 1)] else [.mov .r7 (.shifted .r4 .lsr j), .dp .and .r7 .r7 (.imm 1)]) ++
    [.strb .r7 .r5 (dst % 4096 + j)]

/-- The table at `dst` of the bits of the `nbytes`-byte little-endian number at
`src`: byte `8i + j` is bit `j` of byte `i` (so byte `t` is bit `t`), from
the top byte down (`r5` past 4096 more if the table is: `far`). -/
def bits (src dst nbytes : Nat) : Prog isa :=
  .seq (.block [.mov .r11 (.imm (BitVec.ofNat 32 nbytes))]) (.loop (.block (
    [decCounter, .dp .add .r4 wb (.reg .r11), .ldrb .r4 .r4 src, .dp .add .r5 wb (.shifted .r11 .lsl 3)] ++
    far .r5 dst ++ (List.range 8).flatMap (bitJ dst) ++ [testCounter])) .ne)

/-! ## Numbers as bytes -/

/-- `[r12 + o] = ` the `len`-byte big-endian number at `[src]`, in the `2 n`
32-bit words of `n` 64-bit ones (`4 ≤ len ≤ 8 n`), through `r4`: word `j`
is the byte reversal of the word at `src + len - 4 (j + 1)`, a word of fewer
bytes `t` the first four bytes' reversal shifted right by `8 (4 - t)` bits,
and the words past `len` zero. -/
def loadBytes (len n o : Nat) (src : Reg) : List Instr :=
  (List.range (2 * n)).flatMap fun j =>
    if 4 * (j + 1) ≤ len then
      [.ldr .r4 src (len - 4 * (j + 1)), .rev .r4 .r4, .str .r4 wb (o + 4 * j)]
    else if 4 * j < len then
      [.ldr .r4 src 0, .rev .r4 .r4, .mov .r4 (.shifted .r4 .lsr (8 * (4 * (j + 1) - len))),
        .str .r4 wb (o + 4 * j)]
    else [.mov .r4 (.imm 0), .str .r4 wb (o + 4 * j)]

/-- `[r12 + o] = [r12 + o] >> sh`, the `2 n` 32-bit words of `n` 64-bit
ones (`0 < sh < 32`), through `r4` and `r5`: word `j` is word `j` shifted
right, or'd with word `j + 1` shifted left by `32 - sh`. -/
def shrWords (n o sh : Nat) : List Instr :=
  (List.range (2 * n)).flatMap fun j =>
    [.ldr .r4 wb (o + 4 * j), .mov .r4 (.shifted .r4 .lsr sh)] ++
    (if j + 1 < 2 * n then
      [.ldr .r5 wb (o + 4 * (j + 1)), .dp .orr .r4 .r4 (.shifted .r5 .lsl (32 - sh))]
    else []) ++
    [.str .r4 wb (o + 4 * j)]

/-- `[dst + d] = ` the `n`-word number at `[r12 + a]` masked with `r10`, in
`len` bytes big-endian (`len ≤ 8 n`, the number below `2^(8 len)`), through
`r4` and `r5`: its whole 32-bit words byte-reversed to
`dst + d + len - 4 (j + 1)`, a word of fewer bytes a byte at a time, and
nothing of the words past `len`. -/
def storeBytes (len n : Nat) (dst : Reg) (d a : Nat) : List Instr :=
  (List.range (2 * n)).flatMap fun j =>
    if 4 * (j + 1) ≤ len then
      [.ldr .r4 wb (a + 4 * j), .dp .and .r4 .r4 (.reg .r10), .rev .r4 .r4,
        .str .r4 dst (d + (len - 4 * (j + 1)))]
    else if 4 * j < len then
      [.ldr .r4 wb (a + 4 * j), .dp .and .r4 .r4 (.reg .r10)] ++
      (List.range (len - 4 * j)).flatMap fun i =>
        if len - 4 * j - 1 - i = 0 then [.strb .r4 dst (d + i)]
        else [.mov .r5 (.shifted .r4 .lsr (8 * (len - 4 * j - 1 - i))), .strb .r5 dst (d + i)]
    else []

/-- `r4 = x mod 2³²`. -/
def movImm (x : Nat) : List Instr :=
  [.movw .r4 (BitVec.ofNat 16 x), .movt .r4 (BitVec.ofNat 16 (x >>> 16))]

/-- `[r12 + o] = x`, `n` words, through `r4`. -/
def setConst (n : Nat) (o x : Nat) : List Instr :=
  (List.range (2 * n)).flatMap fun j => movImm (x >>> (32 * j)) ++ [.str .r4 wb (o + 4 * j)]

end VG.Impl.Weierstrass.Arm
