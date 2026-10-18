module

public import VerifiedGarbage.Impl.Rsa.X86_64.Crt

/-!
# RSA with the CRT private key on x86-64, with AVX512_IFMA, for any size

`vg_rsa_private_crt_ifma`: `vg_rsa_private_crt_adx`'s code, but for a
modulus of `2 W` words and primes of `W` words each, whose two
exponentiations (modulo `p` and modulo `q`) run at once, in radix `2⁵²`,
with AVX512_IFMA's `vpmadd52luq` and `vpmadd52huq`, with numbers of `4 R`
limbs in `R` 256-bit registers each (`Lay`): `R = 5`, `W = 16` for
2048-bit keys, `R = 8`, `W = 24` for 3072-bit keys, `R = 10`, `W = 32` for
4096-bit keys. The two accumulators take `2 R`
registers, with the two broadcast limbs, the two `u`, a zero and a
temporary: `2 R + 6` of the thirty-two, named through `VReg` and the
`EVEX.256` instructions of `TCB/X86_64/Evex.lean`, which reach
`ymm16`–`ymm31`.

* A number below `2^(208 R)` is `4 R` limbs below `2⁵²`, limb `j` in
  quadword `j / R` of the 32-byte vector `j % R` (`32 R` bytes): the stride
  layout.
* `amm`: two almost-Montgomery multiplications at once, `a b 2^(-52 S)`
  modulo `p` and modulo `q`, in `S ≤ 4 R` steps (30 of the 32 limbs for
  3072-bit keys, whose primes need no more): for each limb `b_i`
  of the second operand, the low halves of `a b_i` into the accumulator and
  the high halves of those that stay in their lane, `u = acc₀ k₀ mod 2⁵²`,
  the low halves of `u m`, the carry of limb 0 into limb 1 (`vpsrlq` and
  `vmovq`, which keeps the low quadword), the accumulator shifted down a
  limb (a change of the registers' roles and `valignq` of the register of
  limb 0 with the zero register, which moves its lanes down one and the
  zero in), and the high halves of `u m` and of the rest of `a b_i`.
* The bases and 1 in Montgomery form (`R_I = 2^(52 S)`) from those of
  `vg_rsa_private_crt` (`R_X = 2^(64 W)`) by a multiplication by
  `2^(104 S - 64 W) mod X` (`R_X` doubled `104 S - 128 W` times); a table
  of the `2^w` powers; `w` squares and a multiplication by the masked
  selection of an entry per window of `w` bits (4 for 2048-bit keys, 5
  otherwise), the exponents padded with zero bytes at the top to whole
  groups of `w` bytes and recoded into digits of `w` bits, a byte each,
  from the first digit with a bit of the exponent; then a multiplication
  by 1, which leaves the result out of Montgomery form, reduced in 64-bit
  words.
-/

@[expose] public section

namespace VG.Impl.Rsa.X86_64.CrtIfma

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
  VG.Impl.Rsa.X86_64.Crt

/-- The offset of the modulus in a prime's region. -/
def oM : Nat := 0

/-- The sizes: `R` registers per number, primes of `W` words, `S` steps
of a multiplication (`S ≤ 4 R`): the Montgomery radix is `2^(52 S)`;
windows of `w` bits; and `nl` lanes, numbers multiplied side by side, each
in its own region `D` bytes after the previous one (the two primes). -/
structure Lay where
  R : Nat
  W : Nat
  S : Nat
  w : Nat
  nl : Nat
  deriving DecidableEq, Repr

namespace Lay

variable (l : Lay)

/-- The limbs of a number. -/
def L : Nat := 4 * l.R
/-- The bytes of a number. -/
def NB : Nat := 32 * l.R
/-- The bytes of the exponent, a prime's. -/
def E : Nat := 8 * l.W
/-- The entries of the table. -/
def T : Nat := 2 ^ l.w
/-- The bytes of the padded exponent: `E` and the fewest zero bytes before
it that make it a whole number of groups of `w` bytes. -/
def P : Nat := l.E + (l.w - l.E % l.w) % l.w
/-- The digits of `w` bits of the padded exponent, 8 per group. -/
def ND : Nat := 8 * (l.P / l.w)
/-- The first digit with a bit of the exponent (those before are zero). -/
def k0 : Nat := 8 * (l.P - l.E) / l.w
/-- The bytes of the padded exponent and of its digits (none with windows of
4 bits, whose digits are the exponent's nibbles), each a whole number of 32
bytes. -/
def XE : Nat := (l.P + 31) / 32 * 32 + (if l.w = 4 then 0 else (l.ND + 31) / 32 * 32)

/-! In a prime's region: the modulus, `k₀` in each quadword, `Y`, the base
`X`, the selected entry, the table, the padded exponent, its digits (a byte
each), `2^(104 S - 64 W) mod X`, the digit being read, the last multiplier. -/
def oK0 : Nat := l.NB
def oY : Nat := l.NB + 32
def oX : Nat := l.oY + l.NB
def oS : Nat := l.oX + l.NB
def oTab : Nat := l.oS + l.NB
def oE : Nat := l.oTab + l.T * l.NB
def oD : Nat := l.oE + (l.P + 31) / 32 * 32
def oK1 : Nat := l.oE + l.XE
def oV : Nat := l.oK1 + l.NB
/-- The last multiplier: 1 for `q`, `R mod p` for `p`. -/
def oFin : Nat := l.oV + 32
/-- `q`'s region from `p`'s. -/
def D : Nat := l.oFin + l.NB
/-- The caller's MXCSR (its bits 15:0) and `0x1FBF`, after both regions. -/
def oMx : Nat := 2 * l.D
/-- The size of the area. -/
def areaBytes : Nat := 2 * l.D + 8

/-- The doublings of `R_X mod X` that make `2^(104 S - 64 W) mod X`. -/
def dbls : Nat := 104 * l.S - 128 * l.W

/-- The quadword of limb `j` in the stride layout. -/
def off (j : Nat) : Nat := 32 * (j % l.R) + 8 * (j / l.R)

end Lay

/-- 2048-bit keys: primes of 16 words, numbers of 20 limbs, windows of 4
bits. -/
def lay2048 : Lay := ⟨5, 16, 20, 4, 2⟩
/-- 3072-bit keys: primes of 24 words, numbers of 32 limbs, of which 30
hold the primes' 1536 bits and a multiplication's 30 steps, windows of 5
bits. -/
def lay3072 : Lay := ⟨8, 24, 30, 5, 2⟩
/-- 4096-bit keys: primes of 32 words, numbers of 40 limbs, windows of 5
bits. -/
def lay4096 : Lay := ⟨10, 32, 40, 5, 2⟩

/-- In the prime workspaces: the base of the IFMA area, and a counter. -/
def sIfma : Nat := sFn 13
def sCtr : Nat := sFn 14

def at_ (r : Reg) (d : Nat) : MemOp := { base := r, disp := d }

def mask52 : BitVec 64 := BitVec.ofNat 64 (2 ^ 52 - 1)

/-! ## Registers -/

/-- Vector register `n` (of 32). -/
def vreg (n : Nat) : VReg :=
  match n with
  | 0 => .lo .xmm0 | 1 => .lo .xmm1 | 2 => .lo .xmm2 | 3 => .lo .xmm3
  | 4 => .lo .xmm4 | 5 => .lo .xmm5 | 6 => .lo .xmm6 | 7 => .lo .xmm7
  | 8 => .lo .xmm8 | 9 => .lo .xmm9 | 10 => .lo .xmm10 | 11 => .lo .xmm11
  | 12 => .lo .xmm12 | 13 => .lo .xmm13 | 14 => .lo .xmm14 | 15 => .lo .xmm15
  | 16 => .hi .xmm16 | 17 => .hi .xmm17 | 18 => .hi .xmm18 | 19 => .hi .xmm19
  | 20 => .hi .xmm20 | 21 => .hi .xmm21 | 22 => .hi .xmm22 | 23 => .hi .xmm23
  | 24 => .hi .xmm24 | 25 => .hi .xmm25 | 26 => .hi .xmm26 | 27 => .hi .xmm27
  | 28 => .hi .xmm28 | 29 => .hi .xmm29 | 30 => .hi .xmm30 | _ => .hi .xmm31

variable (l : Lay)

/-- The register of limb role `k` of lane `p` at step `i` of a block; then
each lane's `b` and `u`, the zero register and a temporary. -/
def acc (p k i : Nat) : VReg := vreg (l.R * p + (k + i) % l.R)
def bReg (p : Nat) : VReg := vreg (l.nl * l.R + p)
def uReg (p : Nat) : VReg := vreg (l.nl * l.R + l.nl + p)
def zReg : VReg := vreg (l.nl * l.R + 2 * l.nl)
def tReg : VReg := vreg (l.nl * l.R + 2 * l.nl + 1)

/-! ## The multiplication -/

/-- Step `i` of a block, for each lane (`p` then `q`) in turn at each stage:
`r8` the first operand, `r9` the second plus 8 per block, `r10` the region
(the modulus and `k₀`). Ordered so that the chain through `u` and the
shift starts first: the low halves into roles 0 and 1, `u`, what role 1
needs before the shift, the shift, then the rest limb by limb. -/
def ammStep (i : Nat) : List Instr :=
  let ps := List.range l.nl
  let D := l.D
  let loA (p k : Nat) : Instr := .evMadd52Load false (acc l p k i) (bReg l p) (at_ .r8 (D * p + 32 * k))
  let hiA (p k : Nat) : Instr := .evMadd52Load true (acc l p (k + 1) i) (bReg l p) (at_ .r8 (D * p + 32 * k))
  let loM (p k : Nat) : Instr := .evMadd52Load false (acc l p k i) (uReg l p) (at_ .r10 (D * p + oM + 32 * k))
  let hiM (p k : Nat) : Instr := .evMadd52Load true (acc l p k (i + 1)) (uReg l p) (at_ .r10 (D * p + oM + 32 * k))
  ps.flatMap (fun p => [.mov .rax (.mem (at_ .r9 (D * p + 32 * i))), .eop (.vmovq (bReg l p) .rax),
    .eop (.vpbroadcastq (bReg l p) (bReg l p))]) ++
  ps.flatMap (fun p => [loA p 0, loA p 1]) ++
  ps.flatMap (fun p => [.eop (.bin .vpxorq (tReg l) (tReg l) (tReg l)),
    .evMadd52Load false (tReg l) (acc l p 0 i) (at_ .r10 (D * p + l.oK0)),
    .eop (.vpbroadcastq (uReg l p) (tReg l))]) ++
  ps.flatMap (fun p => [hiA p 0, loM p 0, loM p 1]) ++
  ps.flatMap (fun p => [.eop (.shift .vpsrlq (tReg l) (acc l p 0 i) 52), .eop (.vmovqx (tReg l) (tReg l)),
    .eop (.bin .vpaddq (acc l p 1 i) (acc l p 1 i) (tReg l)),
    .eop (.valignq (acc l p 0 i) (zReg l) (acc l p 0 i) 1)]) ++
  ps.flatMap (fun p => [hiM p 0]) ++
  ps.flatMap (fun p => (List.range (l.R - 2)).flatMap fun j =>
    [loA p (j + 2), hiA p (j + 1), loM p (j + 2), hiM p (j + 1)]) ++
  ps.flatMap (fun p => [hiA p (l.R - 1), hiM p (l.R - 1)])

/-- A block: `R` steps, then the next block's limbs of the second operand
and the count of blocks. -/
def ammBlock : List Instr :=
  (List.range l.R).flatMap (ammStep l) ++ ([.alu .add .r9 (.imm 8), .alu .sub .rcx (.imm 1)] : List Instr)

/-- Lane `p`'s carry (`rdx`, then `rsi`) and its temporary (`rax`, then `rcx`). -/
def cReg (p : Nat) : Reg := if p = 0 then .rdx else .rsi
def cTmp (p : Nat) : Reg := if p = 0 then .rax else .rcx

/-- Limb `j` of lane `p`'s carry chain. -/
def carryStep (j p : Nat) : List Instr :=
  [.alu .add (cReg p) (.mem (at_ .r11 (l.D * p + l.off j))), .mov (cTmp p) (.reg (cReg p)),
    .alu .and (cTmp p) (.reg .r12), .store (at_ .r11 (l.D * p + l.off j)) (cTmp p), .shift .shr (cReg p) 52]

/-- The accumulators' limbs, carried in order into limbs below `2⁵²`, at
`r11` (and `r11 + D`), the lanes' chains interleaved (carries in `rdx` and
`rsi`); `r12` holds `2⁵² - 1`. -/
def carryOut : List Instr :=
  (List.range l.nl).map (fun p => .mov32 (cReg p) (.imm 0)) ++
    (List.range l.L).flatMap fun j => (List.range l.nl).flatMap (carryStep l j)

/-! ### The multiplication with a look-ahead of `u`

`ammCoreU`: `ammCore` with its `S` steps unrolled and the next step's `u`
computed from limb 1 of the accumulator alone, before the rest of the row,
so that the chain from one `u` to the next is a multiplication, the carry,
the additions into limb 1, the multiplication by `k₀` and the broadcast,
and the row's other products run beside it. The limbs of the second
operand and the `u`s alternate between two registers of each lane (`par`,
the step's parity), so no step copies one. -/

/-- Lane `p`'s registers after the roles: the limb of the second operand and
`u` of a step of parity `par`, a temporary, the two products of `u` for limb
1, and the next `lo(a₀ b)`; then the zero register. -/
def ubReg (p par : Nat) : VReg := vreg (l.nl * l.R + 8 * p + par)
def uuReg (p par : Nat) : VReg := vreg (l.nl * l.R + 8 * p + 2 + par)
def utReg (p : Nat) : VReg := vreg (l.nl * l.R + 8 * p + 4)
def um1Reg (p : Nat) : VReg := vreg (l.nl * l.R + 8 * p + 5)
def um2Reg (p : Nat) : VReg := vreg (l.nl * l.R + 8 * p + 6)
def upnReg (p : Nat) : VReg := vreg (l.nl * l.R + 8 * p + 7)
def uzReg : VReg := vreg (l.nl * l.R + 8 * l.nl)

/-- Step `i` of lane `p`: `b_i` in `ubReg p (i % 2)`, `u_i` in
`uuReg p (i % 2)`, and role 0 already holding `lo(a₀ b_i)`; it leaves
`b_(i+1)`, `u_(i+1)` and role 0's `lo(a₀ b_(i+1))` for the next, unless `i`
is the last step. -/
def ammStepU (p i : Nat) : List Instr :=
  let D := l.D
  let par := i % 2
  let nxt := (i + 1) % 2
  let B := ubReg l p par
  let U := uuReg l p par
  let z (r : VReg) : Instr := .eop (.bin .vpxorq r r r)
  let loA (k : Nat) : Instr := .evMadd52Load false (acc l p k i) B (at_ .r8 (D * p + 32 * k))
  let hiA (k : Nat) : Instr := .evMadd52Load true (acc l p (k + 1) i) B (at_ .r8 (D * p + 32 * k))
  let loM (k : Nat) : Instr := .evMadd52Load false (acc l p k i) U (at_ .r10 (D * p + oM + 32 * k))
  let hiM (k : Nat) : Instr := .evMadd52Load true (acc l p k (i + 1)) U (at_ .r10 (D * p + oM + 32 * k))
  let last := l.S ≤ i + 1
  [loM 0, z (um1Reg l p), .evMadd52Load false (um1Reg l p) U (at_ .r10 (D * p + oM + 32)),
    z (um2Reg l p), .evMadd52Load true (um2Reg l p) U (at_ .r10 (D * p + oM)),
    loA 1, hiA 0] ++
  (if last then [] else
    [.mov .rax (.mem (at_ .r9 (D * p + l.off (i + 1)))), .eop (.vmovq (ubReg l p nxt) .rax),
      .eop (.vpbroadcastq (ubReg l p nxt) (ubReg l p nxt)), z (upnReg l p),
      .evMadd52Load false (upnReg l p) (ubReg l p nxt) (at_ .r8 (D * p)),
      .eop (.bin .vpaddq (acc l p 1 i) (acc l p 1 i) (upnReg l p))]) ++
  [.eop (.bin .vpaddq (acc l p 1 i) (acc l p 1 i) (um1Reg l p)),
    .eop (.bin .vpaddq (acc l p 1 i) (acc l p 1 i) (um2Reg l p)),
    .eop (.shift .vpsrlq (utReg l p) (acc l p 0 i) 52), .eop (.vmovqx (utReg l p) (utReg l p)),
    .eop (.bin .vpaddq (acc l p 1 i) (acc l p 1 i) (utReg l p))] ++
  (if last then [] else
    [z (utReg l p), .evMadd52Load false (utReg l p) (acc l p 1 i) (at_ .r10 (D * p + l.oK0)),
      .eop (.vpbroadcastq (uuReg l p nxt) (utReg l p))]) ++
  [.eop (.valignq (acc l p 0 i) (uzReg l) (acc l p 0 i) 1)] ++
  (List.range (l.R - 2)).flatMap (fun j => [loA (j + 2), hiA (j + 1), loM (j + 2), hiM (j + 1)]) ++
  [hiA (l.R - 1), hiM (l.R - 1)]

/-- The start: `b₀`, role 0's `lo(a₀ b₀)` and `u₀` from it. -/
def ammStartU (p : Nat) : List Instr :=
  [.mov .rax (.mem (at_ .r9 (l.D * p))), .eop (.vmovq (ubReg l p 0) .rax),
    .eop (.vpbroadcastq (ubReg l p 0) (ubReg l p 0)),
    .evMadd52Load false (acc l p 0 0) (ubReg l p 0) (at_ .r8 (l.D * p)),
    .eop (.bin .vpxorq (utReg l p) (utReg l p) (utReg l p)),
    .evMadd52Load false (utReg l p) (acc l p 0 0) (at_ .r10 (l.D * p + l.oK0)),
    .eop (.vpbroadcastq (uuReg l p 0) (utReg l p))]

/-- `ammCore` with the look-ahead, its `S` steps unrolled. -/
def ammCoreU : Prog isa :=
  .block (([.mov .r10 (.reg .rbx)] : List Instr) ++
    (List.range (l.nl * l.R)).map (fun r => .eop (.bin .vpxorq (vreg r) (vreg r) (vreg r))) ++
    [.eop (.bin .vpxorq (uzReg l) (uzReg l) (uzReg l))] ++
    (List.range l.nl).flatMap (ammStartU l) ++
    (List.range l.S).flatMap (fun i => (List.range l.nl).flatMap fun p => ammStepU l p i) ++
    ((List.range l.nl).flatMap fun p => (List.range l.R).map fun k =>
      .evStore (at_ .r11 (l.D * p + 32 * k)) (acc l p k (l.S % l.R))) ++
    ([.movImm64 .r12 mask52] : List Instr) ++ carryOut l)

/-- `[r11] := [r8] [r9] 2^(-52 S)` modulo each prime, almost (`rbx` the
area): `S / R` blocks, then the first `S % R` steps of another, which leave
role `k` in the register of `k + S % R`. -/
def ammCore : Prog isa :=
  .seq (.block (([.mov .r10 (.reg .rbx), .mov32 .rcx (.imm (BitVec.ofNat 32 (l.S / l.R)))] : List Instr) ++
      (List.range (l.nl * l.R + 2 * l.nl + 1)).map fun r => .eop (.bin .vpxorq (vreg r) (vreg r) (vreg r))))
    (.seq (.loop (.block (ammBlock l)) .ne)
      (.block ((List.range (l.S % l.R)).flatMap (ammStep l) ++ ((List.range l.nl).flatMap fun p => (List.range l.R).map fun k =>
          .evStore (at_ .r11 (l.D * p + 32 * k)) (acc l p k (l.S % l.R))) ++
        ([.movImm64 .r12 mask52] : List Instr) ++ carryOut l)))

/-- The multiplication of a layout: with the look-ahead for 2048 bits. -/
def ammMul : Prog isa := if l = lay2048 then ammCoreU l else ammCore l

/-- `[o] := [a] [b] 2^(-52 S)`, the offsets in `p`'s region. -/
def amm (o a b : Nat) : Prog isa :=
  .seq (.block [.mov .r8 (.reg .rbx), .alu .add .r8 (.imm (BitVec.ofNat 32 a)), .mov .r9 (.reg .rbx),
      .alu .add .r9 (.imm (BitVec.ofNat 32 b)), .mov .r11 (.reg .rbx), .alu .add .r11 (.imm (BitVec.ofNat 32 o))])
    (ammMul l)

/-! ## Moving numbers between the layouts -/

/-- `r` shifted left by `t` (`0 < t < 64`), through `rbp`: rotated, its low
`t` bits cleared. -/
def shl (r : Reg) (t : Nat) : List Instr :=
  [.shift .ror r (64 - t), .movImm64 .rbp (BitVec.ofNat 64 (2 ^ 64 - 2 ^ t)), .alu .and r (.reg .rbp)]

/-- The `W` words at `rsi` into the limbs at `r11` (`r12` holds `2⁵² - 1`). -/
def to52 : List Instr :=
  (List.range l.L).flatMap fun j =>
    let b := 52 * j
    let w := b / 64
    let s := b % 64
    if l.W ≤ w then [.mov32 .rax (.imm 0), .store (at_ .r11 (l.off j)) .rax] else
    ([.mov .rax (.mem (at_ .rsi (8 * w)))] : List Instr) ++
    (if s = 0 then [] else [.shift .shr .rax s]) ++
    (if 12 < s ∧ w + 1 < l.W then
      ([.mov .rcx (.mem (at_ .rsi (8 * (w + 1))))] : List Instr) ++ shl .rcx (64 - s) ++
        ([.alu .or .rax (.reg .rcx)] : List Instr)
    else []) ++
    ([.alu .and .rax (.reg .r12), .store (at_ .r11 (l.off j)) .rax] : List Instr)

/-- The limbs below `2⁵²` at `r11` into `W + 1` words at `r8`. -/
def to64 : List Instr :=
  (List.range (l.W + 1)).flatMap fun w =>
    let lo := 64 * w
    let js := (List.range l.L).filter fun j => 52 * j < lo + 64 ∧ lo < 52 * j + 52
    (.mov32 .rax (.imm 0) :: js.flatMap fun j =>
      ([.mov .rcx (.mem (at_ .r11 (l.off j)))] : List Instr) ++
      (if lo ≤ 52 * j then (if 52 * j = lo then [] else shl .rcx (52 * j - lo))
        else [.shift .shr .rcx (lo - 52 * j)]) ++
      ([.alu .or .rax (.reg .rcx)] : List Instr)) ++
    ([.store (at_ .r8 (8 * w)) .rax] : List Instr)

/-! ## Before the vector code, in a prime's workspace (`rdi`) -/

/-- `aT := 2^dbls [aY] mod X` (`[aY] = R_X mod X`, so `aT = 2^(104 S - 64 W) mod X`). -/
def k1 : List (Prog isa) :=
  copyArr aT aY ++ [.block [.mov32 .rcx (.imm (BitVec.ofNat 32 l.dbls))], doubles aN aAcc aTmp aT sCtr]

/-- `to52`'s arguments for array `j` and the limbs at offset `o` of region
`p`: the array, the limbs, and `2⁵² - 1`. -/
def arrPtrs (p j o : Nat) : List Instr :=
  [.mov .rsi (.mem (hdr (sArr j))), .mov .r11 (.mem (hdr sIfma)),
    .alu .add .r11 (.imm (BitVec.ofNat 32 (l.D * p + o))), .movImm64 .r12 mask52]

/-- Array `j` into the limbs at offset `o` of the region at `r11`'s base
`rbx + p D`. -/
def arr52 (p j o : Nat) : List Instr := arrPtrs l p j o ++ to52 l

/-- The arrays every region takes, with their offsets: the modulus,
`2^dbls R_X mod X`, `x R_X`, `R_X`, and `R_X` again as the last multiplier
(`q`'s then 1, `finOne`). -/
def arrs : List (Nat × Nat) := [(aN, oM), (aT, l.oK1), (aXc, l.oX), (aY, l.oY), (aY, l.oFin)]

/-- `to52`'s arguments for the entry of `ps` that `r8` counts down to
(`ps.length` for the first). -/
def arrSel (p : Nat) : List (Nat × Nat) → Prog isa
  | [] => .block []
  | [(j, o)] => .block (arrPtrs l p j o)
  | (j, o) :: ps => .seq (.block [.alu .cmp .r8 (.imm (BitVec.ofNat 32 (ps.length + 1)))])
      (.ite .e (.block (arrPtrs l p j o)) (arrSel p ps))

/-- `arrs` into region `p`, by one `to52` in a loop. -/
def arrLoop (p : Nat) : Prog isa :=
  .seq (.block [.mov32 .r8 (.imm 5)])
    (.loop (.seq (arrSel l p (arrs l)) (.block (to52 l ++ ([.alu .sub .r8 (.imm 1)] : List Instr)))) .ne)

/-- `k₀` (the low 52 bits of the inverse) in each quadword of `oK0`, `r11`
the region (`r12` holds `2⁵² - 1`). -/
def k0St (p : Nat) : List Instr :=
  ([.mov .r11 (.mem (hdr sIfma)), .alu .add .r11 (.imm (BitVec.ofNat 32 (l.D * p))),
    .mov .rax (.mem (hdr sMinv)), .alu .and .rax (.reg .r12)] : List Instr) ++
  (List.range 4).map (fun i => .store (at_ .r11 (l.oK0 + 8 * i)) .rax)

/-- Zeros where the padded exponent goes. -/
def eZero : List Instr :=
  .mov32 .rax (.imm 0) :: (List.range ((l.P + 7) / 8)).map (fun i => .store (at_ .r11 (l.oE + 8 * i)) .rax)

/-- `q`'s last multiplier, 1 (`rax` is 0). -/
def finOne : List Instr :=
  (List.range l.L).map (fun j => .store (at_ .r11 (l.oFin + l.off j)) .rax) ++
    ([.mov32 .rax (.imm 1), .store (at_ .r11 l.oFin) .rax] : List Instr)

/-- The exponent's bytes (pointer and length in `n`'s slots `slotPtr`,
`slotLen`) at the end of the `P` at `oE`. -/
def eCopy (slotPtr slotLen : Nat) : List (Prog isa) :=
  [.block [.mov .rax (.mem (hdr sLink)), .mov .rsi (.mem (ws .rax slotPtr)), .mov .rcx (.mem (ws .rax slotLen)),
      .alu .add .r11 (.imm (BitVec.ofNat 32 (l.oE + l.P))), .alu .sub .r11 (.reg .rcx)],
    .loop (.block [.movzx8 .rax (at0 .rsi), .store8 (at0 .r11) .rax, .alu .add .rsi (.imm 1),
      .alu .add .r11 (.imm 1), .alu .sub .rcx (.imm 1)]) .ne]

/-- A group of `w` bytes of the padded exponent at `r8` (most significant
first) into its 8 digits of `w` bits at `r9`, a byte each; then the next
group. -/
def recodeBody : List Instr :=
  ([.mov32 .rax (.imm 0)] : List Instr) ++
  (List.range l.w).flatMap (fun j => [.shift .shl .rax 8, .movzx8 .rdx (at_ .r8 j), .alu .or .rax (.reg .rdx)]) ++
  (List.range 8).flatMap (fun t => [.mov .rdx (.reg .rax)] ++
    (if t = 7 then [] else [.shift .shr .rdx (l.w * (7 - t))]) ++
    [.alu .and .rdx (.imm (BitVec.ofNat 32 (l.T - 1))), .store8 (at_ .r9 t) .rdx]) ++
  ([.alu .add .r8 (.imm (BitVec.ofNat 32 l.w)), .alu .add .r9 (.imm 8), .alu .sub .rcx (.imm 1)] : List Instr)

/-- The padded exponent of region `p` into its `ND` digits at `oD`. -/
def recode (p : Nat) : List (Prog isa) :=
  [.block [.mov .r8 (.mem (hdr sIfma)), .alu .add .r8 (.imm (BitVec.ofNat 32 (l.D * p + l.oE))),
      .mov .r9 (.mem (hdr sIfma)), .alu .add .r9 (.imm (BitVec.ofNat 32 (l.D * p + l.oD))),
      .mov32 .rcx (.imm (BitVec.ofNat 32 (l.P / l.w)))],
    .loop (.block (recodeBody l)) .ne]

/-- A prime's region (`p` 0 or 1): the modulus, `2^(104 S - 64 W) mod X`,
`x R_X` as `X`, `R_X` as `Y`, the last multiplier, `k₀`, the padded
exponent and, with windows of more than 4 bits, its digits. -/
def region (p slotPtr slotLen : Nat) : List (Prog isa) :=
  k1 l ++ [arrLoop l p] ++
    [.block (k0St l p), .block (eZero l)] ++
    (if p = 0 then [] else [.block (finOne l)]) ++ eCopy l slotPtr slotLen ++ (if l.w = 4 then [] else recode l p)

/-! ## The vector code (`rbx` the area) -/

/-- `[S] := T_v` for each prime, `v` the digit at `oV`:
for each entry `j`, OR'ed in under the mask of `j = v` (one `vpternlogq`
per register), in registers `0`–`R - 1`, with the mask in `R` and a
temporary in `R + 1`. -/
def select (p : Nat) : List (Prog isa) :=
  [.block (([.mov .r8 (.reg .rbx), .alu .add .r8 (.imm (BitVec.ofNat 32 (l.D * p + l.oTab))),
      .mov .rdx (.mem (at_ .rbx (l.D * p + l.oV))), .mov32 .rcx (.imm 0)] : List Instr) ++ (List.range l.R).map fun k => .eop (.bin .vpxorq (vreg k) (vreg k) (vreg k))),
    .loop (.block (([.mov .rax (.reg .rcx), .alu .xor .rax (.reg .rdx), .alu .cmp .rax (.imm 1),
        .alu .sbb .rax (.reg .rax), .eop (.vmovq (vreg l.R) .rax), .eop (.vpbroadcastq (vreg l.R) (vreg l.R))] : List Instr) ++
      ((List.range l.R).flatMap fun k => [.evLoad (vreg (l.R + 1)) (at_ .r8 (32 * k)),
        .eop (.vpternlogq (vreg k) (vreg (l.R + 1)) (vreg l.R) 0xF8)]) ++
      ([.alu .add .r8 (.imm (BitVec.ofNat 32 l.NB)), .alu .add .rcx (.imm 1),
        .alu .cmp .rcx (.imm (BitVec.ofNat 32 l.T))] : List Instr))) .ne,
    .block ((List.range l.R).map fun k => .evStore (at_ .rbx (l.D * p + l.oS + 32 * k)) (vreg k))]

/-- `[o] := [a]` (a number) in both regions. -/
def copyN (o a : Nat) : List Instr :=
  (List.range 2).flatMap fun p => (List.range l.R).flatMap fun k =>
    [.evLoad (vreg 0) (at_ .rbx (l.D * p + a + 32 * k)), .evStore (at_ .rbx (l.D * p + o + 32 * k)) (vreg 0)]

/-- The operands of entry `i < 2` (`r13 = oTab + NB i`) of `convTab`: `Y`
or `X` (`oY + NB i`), in place, times `[oK1]`. -/
def convSetup : List Instr :=
  [.mov .r8 (.reg .rbx), .alu .add .r8 (.reg .r13), .alu .sub .r8 (.imm (BitVec.ofNat 32 (l.oTab - l.oY))),
   .mov .r9 (.reg .rbx), .alu .add .r9 (.imm (BitVec.ofNat 32 l.oK1)), .mov .r11 (.reg .r8)]

/-- The operands of entry `i ≥ 2` (`r13 = oTab + NB i`): `T_(i-1)`, `X`, `T_i`. -/
def tabSetup : List Instr :=
  [.mov .r8 (.reg .rbx), .alu .add .r8 (.reg .r13), .alu .sub .r8 (.imm (BitVec.ofNat 32 l.NB)),
   .mov .r9 (.reg .rbx), .alu .add .r9 (.imm (BitVec.ofNat 32 l.oX)), .mov .r11 (.reg .rbx),
   .alu .add .r11 (.reg .r13)]

/-- Entry `i` of `convTab` (`r13 = oTab + NB i`), one multiplication: below
2, `Y` or `X` into Montgomery form; after `X`, the table's first entries
`T_0 = Y` and `T_1 = X`; from 2, `T_i = T_(i-1) X 2^(-52 S)`. Then `r13`
to the next entry, `ZF` after the last. -/
def convTabBody : Prog isa :=
  .seq (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 (l.oTab + 2 * l.NB)))])
    (.seq (.ite .b (.block (convSetup l)) (.block (tabSetup l)))
      (.seq (ammMul l)
        (.seq (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 (l.oTab + l.NB)))])
          (.seq (.ite .e (.block (copyN l l.oTab l.oY ++ copyN l (l.oTab + l.NB) l.oX)) (.block []))
            (.block [.alu .add .r13 (.imm (BitVec.ofNat 32 l.NB)),
              .alu .cmp .r13 (.imm (BitVec.ofNat 32 (l.oTab + l.T * l.NB)))])))))

/-- `Y` and `X` into Montgomery form (times `[oK1] 2^(-52 S)`), and the
table `T_0 = Y`, `T_1 = X`, `T_i = T_(i-1) X 2^(-52 S)`, in one loop. -/
def convTab : List (Prog isa) :=
  [.block [.mov32 .r13 (.imm (BitVec.ofNat 32 l.oTab))], .loop (convTabBody l) .ne]

/-- The operands of a window's multiplication: `[oY] := [oY] [b]`. -/
def winSetup (b : Nat) : List Instr :=
  [.mov .r8 (.reg .rbx), .alu .add .r8 (.imm (BitVec.ofNat 32 l.oY)), .mov .r9 (.reg .rbx),
   .alu .add .r9 (.imm (BitVec.ofNat 32 b)), .mov .r11 (.reg .rbx),
   .alu .add .r11 (.imm (BitVec.ofNat 32 l.oY))]

/-- A nibble of `r` by the mask in `rdx` (all ones for the high nibble,
zero for the low), through `rcx`: `lo ^ ((hi ^ lo) & mask)`. -/
def nibSel (r : Reg) : List Instr :=
  [.mov .rcx (.reg r), .shift .shr .rcx 4, .alu .and r (.imm 15), .alu .xor .rcx (.reg r),
    .alu .and .rcx (.reg .rdx), .alu .xor r (.reg .rcx)]

/-- Digit `r13` of each prime into its `V`: with windows of 4 bits, a nibble
of byte `r13 / 2` of the padded exponent (the high one for an even digit);
otherwise the digit's byte at `oD`. -/
def digLoad : List Instr :=
  if l.w = 4 then
    ([.mov .r8 (.reg .r13), .shift .shr .r8 1, .mov .rdx (.reg .r13), .alu .and .rdx (.imm 1),
      .alu .sub .rdx (.imm 1),
      .movzx8 .rax { base := .rbx, index := some .r8, disp := ((l.oE : Nat) : Int) },
      .movzx8 .rsi { base := .rbx, index := some .r8, disp := ((l.D + l.oE : Nat) : Int) }] : List Instr) ++
    nibSel .rax ++ ([.store (at_ .rbx l.oV) .rax] : List Instr) ++
    nibSel .rsi ++ ([.store (at_ .rbx (l.D + l.oV)) .rsi] : List Instr)
  else
    (List.range 2).flatMap fun p =>
      [.movzx8 .rax { base := .rbx, index := some .r13, disp := ((l.D * p + l.oD : Nat) : Int) },
        .store (at_ .rbx (l.D * p + l.oV)) .rax]

/-- A window: `Y := Y^(2^w) T_v 2^(-52 S)` for each prime, `v` its digit
`r13` (`digLoad`, into `oV`). `S := T_v` first, then one loop of `w + 1`
multiplications (`r15` counting them down): `w` squarings of `Y`, then
`Y S`. After the last digit (`r13 = ND`), instead `S := Fin` and the one
multiplication `Y S`. -/
def window : List (Prog isa) :=
  [.seq (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 l.ND))])
      (.ite .e (.block (copyN l l.oS l.oFin ++ [.mov32 .r15 (.imm 1)]))
        (seqs ([.block (digLoad l)] ++ select l 0 ++ select l 1 ++
          [.block [.mov32 .r15 (.imm (BitVec.ofNat 32 (l.w + 1)))]]))),
    .loop (.seq (.block [.alu .cmp .r15 (.imm 1)])
      (.seq (.ite .e (.block (winSetup l l.oS)) (.block (winSetup l l.oY)))
        (.seq (ammMul l) (.block [.alu .sub .r15 (.imm 1)])))) .ne]

/-- The exponentiations, a digit of each exponent (`r13`, from the first
that holds a bit of it, `k0`) at a time, and after the last,
`Y := Y Fin 2^(-52 S)` (`window`). -/
def expLoop : List (Prog isa) :=
  convTab l ++ [.block [.mov32 .r13 (.imm (BitVec.ofNat 32 l.k0))],
    .loop (seqs (window l ++ [.block [.alu .add .r13 (.imm 1), .alu .cmp .r13 (.imm (BitVec.ofNat 32 (l.ND + 1)))]])) .ne]

/-- Intel's MXCSR prologue and epilogue around `c` (see "MCDT" in
`TCB/X86_64/Isa.lean`), the slots at `oMx`. -/
def withMxcsr (c : Prog isa) : Prog isa :=
  .seq (.block [.stmxcsr (at_ .rbx l.oMx), .mov32 .r11 (.mem (at_ .rbx l.oMx)), .alu32 .and .r11 (.imm 0xFFFF),
      .store32 (at_ .rbx l.oMx) .r11])
    (.seq (.seq (.block [.mov32 .rax (.imm 0x1FBF), .store32 (at_ .rbx (l.oMx + 4)) .rax,
        .ldmxcsr (at_ .rbx (l.oMx + 4)), .lfence]) (.seq c (.block [.lfence])))
      (.block [.ldmxcsr (at_ .rbx l.oMx), .vop .vzeroupper]))

/-- The vector code: the exponentiations (`Y` and `X` into Montgomery form
with the table), the results multiplied by `oFin`. -/
def vec : Prog isa :=
  withMxcsr l (seqs (expLoop l))

/-- In a prime's workspace: the result into `aY`, reduced below `X`. -/
def result (p : Nat) : List (Prog isa) :=
  [.block (([.mov .r11 (.mem (hdr sIfma)), .alu .add .r11 (.imm (BitVec.ofNat 32 (l.D * p + l.oY))),
      .mov .r8 (.mem (hdr (sArr aAcc)))] : List Instr) ++ to64 l ++
      ([.mov .rbx (.mem (hdr (sArr aY))), .mov .r10 (.mem (hdr (sArr aN))), .mov .r12 (.mem (hdr sW)),
        .mov .rsi (.mem (hdr (sArr aTmp)))] : List Instr)),
    subMod, selectAcc]

/-! ## The phases -/

/-- A prime's bases, in its workspace (`rdi := [sl]`), from `n`'s `R_n² mod
n` and `c R_n mod n` (`R_n = R_X²`, as `n` has twice the prime's words):
`aY := R_X² mod X` (`redc`, which multiplies by `R_X⁻²`), `aXc := c mod X`,
then `aXc := c R_X mod X` (through `aT`) and `aY := R_X mod X`. -/
def prep (mul : Nat → Nat → Nat → Prog isa) (sl : Nat) (pc : Bool := false) (off : List Instr := []) :
    List (Prog isa) :=
  [.block [.mov .rdi (.mem (hdr sl))]] ++ redc mul aR2 ++ copyArr aY aXc ++ redc mul aXm ++ [mul aT aY aXc] ++
    copyArr aXc aT ++ (if pc then loadPre aY off else [mul aY aY aOne]) ++ [.block [leave]]

/-- `q`'s and `p`'s bases (`x R_X mod X` in `aXc`, `R_X mod X` in `aY`, with
`pc` from `pre`). -/
def pre (mul : Nat → Nat → Nat → Prog isa) (pc : Bool := false) : List (Prog isa) :=
  prep mul sWsQ pc offQ ++ prep mul sWsP pc offP

/-- The IFMA area after `q`'s workspace, its base into both prime
workspaces; the regions; the vector code; the results. -/
def ifma : List (Prog isa) :=
  [.block (([.mov .rdx (.mem (hdr sWsQ))] : List Instr) ++ wsEndT ++ ([.mov .rdx (.mem (hdr sWsP)), .store (ws .rdx sIfma) .rax,
      .mov .rdx (.mem (hdr sWsQ)), .store (ws .rdx sIfma) .rax, enterP] : List Instr))] ++
  region l 0 sDp sPlen ++ [.block [leave, enterQ]] ++ region l 1 sDq sQlen ++
  [.block [.mov .rbx (.mem (hdr sIfma))], vec l] ++
  result l 1 ++ [.block [leave, enterP]] ++ result l 0 ++ [.block [leave]]

/-- `p`'s phase after its exponentiation: `aXc := R_p² mod p` as in `prep`,
`m_q` (`q`'s `aY`, of as many words) into `aChunk` and `aXc := m_q R_p mod
p` (through `aChunk`); then `h = (m_p - m_q) qInv mod p` into `aY`, as
`pPhase` computes it. -/
def post (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  [.block [enterP]] ++ redc mul aR2 ++
  [.block [.mov .rax (.mem (hdr sLink)), .mov .rax (.mem (ws .rax sWsQ)), .mov .rsi (.mem (ws .rax (sArr aY))),
      .mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aChunk)))],
    copyWords, mul aChunk aChunk aXc] ++ copyArr aXc aChunk ++
  subModArr aT aY aXc ++ loadArr aChunk sQinv sPlen ++ maskArr aChunk ++ [mul aY aT aChunk, .block [leave]]

/-- Whether `n` has `2 W` words and `p` and `q` `W` (`(len + 7) / 8` of
their lengths in bytes): ZF. -/
def sizes : List Instr :=
  [.mov .rax (.mem (hdr sW)), .alu .xor .rax (.imm (BitVec.ofNat 32 (2 * l.W))), .mov .rdx (.mem (hdr sPlen)),
    .alu .add .rdx (.imm 7), .shift .shr .rdx 3, .alu .xor .rdx (.imm (BitVec.ofNat 32 l.W)),
    .alu .or .rax (.reg .rdx), .mov .rdx (.mem (hdr sQlen)),
    .alu .add .rdx (.imm 7), .shift .shr .rdx 3, .alu .xor .rdx (.imm (BitVec.ofNat 32 l.W)),
    .alu .or .rax (.reg .rdx)]


end VG.Impl.Rsa.X86_64.CrtIfma

namespace VG.Impl.Rsa.X86_64.CrtIfma
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
  VG.Impl.Rsa.X86_64.Crt

/-- ZF: whether the key has the sizes of one of the layouts. -/
def anySizes : Prog isa :=
  .seq (.block (sizes lay2048)) (.ite .e (.block [])
    (.seq (.block (sizes lay3072)) (.ite .e (.block []) (.block (sizes lay4096)))))

/-- The vector code of the layout whose sizes the key has (one of them, by
`anySizes`). -/
def ifmaAny : Prog isa :=
  .seq (.block (sizes lay2048)) (.ite .e (seqs (ifma lay2048))
    (.seq (.block (sizes lay3072)) (.ite .e (seqs (ifma lay3072)) (seqs (ifma lay4096)))))

/-- The IFMA computation for 2048-, 3072- and 4096-bit keys, the CRT one
otherwise: `pre` and `post` do not depend on the layout, so only the vector
code is chosen by it. -/
def main (mul : Nat → Nat → Nat → Prog isa) (pc : Bool := false) : Prog isa :=
  seqs (nSetup mul pc ++ primesSetup ++ checks ++
    [.seq anySizes (.ite .e (seqs (pre mul pc ++ [ifmaAny] ++ post mul))
      (seqs (qPhase mul (Crt.expLoop mul tabSelect) pc ++ pPhase mul (Crt.expLoop mul tabSelect) pc)))] ++
    finish)

/-- `vg_rsa_private_crt_ifma`; with `pc`, `vg_rsa_private_crt_precomputed_ifma`. -/
def code (mul : Nat → Nat → Nat → Prog isa) (pc : Bool := false) : Prog isa :=
  .seq (.block (Crt.entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] : List Instr) ++ invalid))
    (.ite .ne fail (main mul pc))

end VG.Impl.Rsa.X86_64.CrtIfma
