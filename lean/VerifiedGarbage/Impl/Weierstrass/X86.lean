import VerifiedGarbage.Impl.Mont.X86
import VerifiedGarbage.Impl.Weierstrass.Slots

/-!
# Short Weierstrass curves on x86 (32-bit): points, scalar multiplication, powers

Code for any curve `y² = x³ + ax + b` over a prime field of `n` 64-bit
words (`2n` 32-bit words), with the Montgomery arithmetic of
`Impl/Mont/X86.lean`, whose multiplications use an accumulator of
`4 (4n + 1)` bytes at `wk` in the working space. Field elements are in
Montgomery form (`x R mod p`, `R = 2^(64 n)`) in slots of the working space,
whose base is in `edi`; a point is three slots, projective coordinates
`(X : Y : Z)`.

* `fprog`: field operations on slots (`FOp`, `Impl/Weierstrass/Slots.lean`),
  such as the complete addition `rcb`, one after the other.
* `ladder`: `[k]G` by double-and-add from the top bit, 256 times (or as many
  bits as the table has): `D = R + R`, `S = D + G` and `R = D` or `S` by a
  mask of the bit, so every iteration does the same.
* `pow`: `x^e` by square-and-multiply over the bits of a public exponent,
  also always multiplying and selecting by a mask, so that one loop serves
  every exponent.
* `bits`: the bits of a little-endian number in a slot, one byte each.

The loops count down in `esi`, which the arithmetic does not use. The only
branches are on it and on the multiplications' counter `ebp`, and every
address is `edi` plus a constant, or plus a counter: nothing but `edi` may
affect timing.
-/

namespace VG.Impl.Weierstrass.X86

open VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass

/-- The code of a field operation, with the accumulator at `wk`. -/
def opCode (M : Mod) (wk : Nat) : FOp → Prog isa
  | .mul o a b => Mont.X86.mul M wk o a b
  | .add o a b => .block (Mont.X86.add M wk o a b)
  | .sub o a b => .block (Mont.X86.sub M wk o a b)

/-- Programs one after the other. -/
def progs : List (Prog isa) → Prog isa
  | [] => .block []
  | [p] => p
  | p :: ps => .seq p (progs ps)

/-- A straight-line sequence of field operations. -/
def fprog (M : Mod) (wk : Nat) (ops : List FOp) : Prog isa := progs (ops.map (opCode M wk))

/-- `[o] = [a]` if the mask `ecx` is zero, `[b]` if it is all ones, `k`
32-bit words, through `eax` and `edx`. -/
def sel : Nat → Nat → Nat → Nat → List Instr
  | 0, _, _, _ => []
  | k + 1, o, a, b => [.mov .eax (.mem (sc a)), .mov .edx (.mem (sc b)), .alu .xor .edx (.reg .eax),
      .alu .and .edx (.reg .ecx), .alu .xor .eax (.reg .edx), .store (sc o) .eax] ++
      sel k (o + 4) (a + 4) (b + 4)

/-- `o = a` or `b`, a point of `n`-word coordinates, by the mask `ecx`. -/
def selPt (n : Nat) (o a b : Pt) : List Instr :=
  sel (2 * n) o.x a.x b.x ++ sel (2 * n) o.y a.y b.y ++ sel (2 * n) o.z a.z b.z

/-- `[o] = [a]`, `k` 32-bit words, through `eax`. -/
def copy : Nat → Nat → Nat → List Instr
  | 0, _, _ => []
  | k + 1, o, a => [.mov .eax (.mem (sc a)), .store (sc o) .eax] ++ copy k (o + 4) (a + 4)

/-- The mask `ecx = -[edi + esi + d]` of the bit of iteration `esi`, through
`eax`. -/
def bitMask (d : Nat) : List Instr :=
  [.mov .eax (.reg .edi), .alu .add .eax (.reg .esi), .movzx8 .eax (at_ .eax d), .mov .ecx (.imm 0),
    .alu .sub .ecx (.reg .eax)]

/-- `esi -= 1`. -/
def decCounter : Instr := .alu .sub .esi (.imm 1)

/-- `ZF` for the loop: whether `esi` is zero. -/
def testCounter : Instr := .alu .test .esi (.reg .esi)

/-- One iteration of the ladder, for the bit `t = esi - 1`: `D = R + R`,
`T = D + G`, then `R = T` if bit `t` is set, else `D`. -/
def ladderBody (L : LadderCfg) (wk : Nat) : Prog isa :=
  .seq (.block [decCounter]) <| .seq (fprog L.M wk (rcb L.S L.R L.R L.D)) <|
    .seq (fprog L.M wk (rcb L.S L.D L.G L.T)) <|
    .block (bitMask L.bits ++ selPt L.M.n L.R L.D L.T ++ [testCounter])

/-- The ladder over the bits `nbits - 1` down to 0, from `R` as set up by the
caller (the point at infinity). -/
def ladder (L : LadderCfg) (wk : Nat) : Prog isa :=
  .seq (.block [.mov .esi (.imm (BitVec.ofNat 32 L.nbits))]) (.loop (ladderBody L wk) .ne)

/-- One iteration: `acc = acc²`, `tmp = acc · base`, and `acc = tmp` if the
exponent's bit `esi - 1` is set. -/
def powBody (P : PowCfg) (wk : Nat) : Prog isa :=
  .seq (.block [decCounter]) <| .seq (Mont.X86.mul P.M wk P.acc P.acc P.acc) <|
  .seq (Mont.X86.mul P.M wk P.tmp P.acc P.base) <|
    .block (bitMask P.bits ++ sel (2 * P.M.n) P.acc P.acc P.tmp ++ [testCounter])

/-- `[acc] = [base]^e` (in Montgomery form), from the top bit of `e`. -/
def pow (P : PowCfg) (wk : Nat) : Prog isa :=
  .seq (.block (copy (2 * P.M.n) P.acc P.one ++ [.mov .esi (.imm (BitVec.ofNat 32 P.nbits))]))
    (.loop (powBody P wk) .ne)

/-- Byte `j` of the table for byte `esi` of the number: bit `j` of `eax`,
stored at `[ebx + dst + j]`, where `ebx = edi + 8 esi`, through `edx`. -/
def bitJ (dst j : Nat) : List Instr :=
  [.mov .edx (.reg .eax)] ++ (if j = 0 then [] else [.shift .shr .edx j]) ++
    [.alu .and .edx (.imm 1), .store8 (at_ .ebx (dst + j)) .dl]

/-- The table at `dst` of the bits of the `nbytes`-byte little-endian number at
`src`: byte `8i + j` is bit `j` of byte `i` (so byte `t` is bit `t`), from
the top byte down. -/
def bits (src dst nbytes : Nat) : Prog isa :=
  .seq (.block [.mov .esi (.imm (BitVec.ofNat 32 nbytes))]) (.loop (.block (
    [decCounter, .mov .eax (.reg .edi), .alu .add .eax (.reg .esi), .movzx8 .eax (at_ .eax src),
      .mov .ebx (.reg .esi), .alu .add .ebx (.reg .ebx), .alu .add .ebx (.reg .ebx),
      .alu .add .ebx (.reg .ebx), .alu .add .ebx (.reg .edi)] ++
    (List.range 8).flatMap (bitJ dst) ++ [testCounter])) .ne)

/-! ## Numbers as bytes -/

/-- `[edi + o] = ` the `n`-word (`2n` 32-bit words) big-endian number at
`[src]`, little-endian, through `eax`. -/
def loadBE (n : Nat) (o : Nat) (src : Reg) : List Instr :=
  (List.range (2 * n)).flatMap fun j =>
    [.mov .eax (.mem (at_ src (4 * (2 * n - 1 - j)))), .bswap .eax, .store (sc (o + 4 * j)) .eax]

/-- `[dst + d] = ` the `n`-word number at `[edi + a]`, big-endian, masked with
`ecx`, through `eax`. -/
def storeBE (n : Nat) (dst : Reg) (d a : Nat) : List Instr :=
  (List.range (2 * n)).flatMap fun j =>
    [.mov .eax (.mem (sc (a + 4 * j))), .alu .and .eax (.reg .ecx), .bswap .eax,
      .store (at_ dst (d + 4 * (2 * n - 1 - j))) .eax]

/-- `[edi + o] = x`, `n` words, through `eax`. -/
def setConst (n : Nat) (o x : Nat) : List Instr :=
  (List.range (2 * n)).flatMap fun j =>
    [.mov .eax (.imm (BitVec.ofNat 32 (x >>> (32 * j)))), .store (sc (o + 4 * j)) .eax]

end VG.Impl.Weierstrass.X86
