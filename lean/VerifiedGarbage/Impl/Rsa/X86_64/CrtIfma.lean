import VerifiedGarbage.Impl.Rsa.X86_64.Crt

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
* `amm`: two almost-Montgomery multiplications at once, `a b 2^(-208 R)`
  modulo `p` and modulo `q`: for each limb `b_i`
  of the second operand, the low halves of `a b_i` into the accumulator and
  the high halves of those that stay in their lane, `u = acc₀ k₀ mod 2⁵²`,
  the low halves of `u m`, the carry of limb 0 into limb 1 (`vpsrlq` and
  `vmovq`, which keeps the low quadword), the accumulator shifted down a
  limb (a change of the registers' roles and `valignq` of the register of
  limb 0 with the zero register, which moves its lanes down one and the
  zero in), and the high halves of `u m` and of the rest of `a b_i`.
* The bases and 1 in Montgomery form (`R_I = 2^(208 R)`) from those of
  `vg_rsa_private_crt` (`R_X = 2^(64 W)`) by a multiplication by
  `2^(416 R - 64 W) mod X` (`R_X` doubled `416 R - 128 W` times); a table
  of the 16 powers; four squares and a multiplication by the masked
  selection of an entry per window of 4 bits, with the exponents padded with
  zero bytes at the top to `8 W` bytes; then a multiplication by 1, which
  leaves the result out of Montgomery form, reduced in 64-bit words.
-/

namespace VG.Impl.Rsa.X86_64.CrtIfma

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
  VG.Impl.Rsa.X86_64.Crt

/-- The offset of the modulus in a prime's region. -/
def oM : Nat := 0

/-- The sizes: `R` registers per number, primes of `W` words. -/
structure Lay where
  R : Nat
  W : Nat
  deriving DecidableEq, Repr

namespace Lay

variable (l : Lay)

/-- The limbs of a number. -/
def L : Nat := 4 * l.R
/-- The bytes of a number. -/
def NB : Nat := 32 * l.R
/-- The bytes of the padded exponent. -/
def E : Nat := 8 * l.W

/-! In a prime's region: the modulus, `k₀` in each quadword, `Y`, the base
`X`, the selected entry, the table, the padded exponent, `2^(416 R - 64 W)
mod X`, the bytes of the exponent being read, the last multiplier. -/
def oK0 : Nat := l.NB
def oY : Nat := l.NB + 32
def oX : Nat := l.oY + l.NB
def oS : Nat := l.oX + l.NB
def oTab : Nat := l.oS + l.NB
def oE : Nat := l.oTab + 16 * l.NB
def oK1 : Nat := l.oE + l.E
def oV : Nat := l.oK1 + l.NB
/-- The last multiplier: 1 for `q`, `R mod p` for `p`. -/
def oFin : Nat := l.oV + 32
/-- `q`'s region from `p`'s. -/
def D : Nat := l.oFin + l.NB
/-- The caller's MXCSR (its bits 15:0) and `0x1FBF`, after both regions. -/
def oMx : Nat := 2 * l.D
/-- The size of the area. -/
def areaBytes : Nat := 2 * l.D + 8

/-- The doublings of `R_X mod X` that make `2^(416 R - 64 W) mod X`. -/
def dbls : Nat := 416 * l.R - 128 * l.W

/-- The quadword of limb `j` in the stride layout. -/
def off (j : Nat) : Nat := 32 * (j % l.R) + 8 * (j / l.R)

end Lay

/-- 2048-bit keys: primes of 16 words, numbers of 20 limbs. -/
def lay2048 : Lay := ⟨5, 16⟩
/-- 3072-bit keys: primes of 24 words, numbers of 32 limbs. -/
def lay3072 : Lay := ⟨8, 24⟩
/-- 4096-bit keys: primes of 32 words, numbers of 40 limbs. -/
def lay4096 : Lay := ⟨10, 32⟩

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

/-- The register of limb role `k` of prime `p` at step `i` of a block. -/
def acc (p k i : Nat) : VReg := vreg (l.R * p + (k + i) % l.R)
def bReg (p : Nat) : VReg := vreg (2 * l.R + p)
def uReg (p : Nat) : VReg := vreg (2 * l.R + 2 + p)
def zReg : VReg := vreg (2 * l.R + 4)
def tReg : VReg := vreg (2 * l.R + 5)

/-! ## The multiplication -/

/-- Step `i` of a block, for `p` (0) and `q` (1) in turn at each stage:
`r8` the first operand, `r9` the second plus 8 per block, `r10` the region
(the modulus and `k₀`). Ordered so that the chain through `u` and the
shift starts first: the low halves into roles 0 and 1, `u`, what role 1
needs before the shift, the shift, then the rest limb by limb. -/
def ammStep (i : Nat) : List Instr :=
  let ps := [0, 1]
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

/-- The accumulators' limbs, carried in order into limbs below `2⁵²`, at
`r11` and `r11 + D`, the two chains interleaved (carries in `rdx` and
`rsi`); `r12` holds `2⁵² - 1`. -/
def carryOut : List Instr :=
  ([.mov32 .rdx (.imm 0), .mov32 .rsi (.imm 0)] : List Instr) ++ (List.range l.L).flatMap fun j =>
    [.alu .add .rdx (.mem (at_ .r11 (l.off j))), .mov .rax (.reg .rdx), .alu .and .rax (.reg .r12),
     .store (at_ .r11 (l.off j)) .rax, .shift .shr .rdx 52,
     .alu .add .rsi (.mem (at_ .r11 (l.D + l.off j))), .mov .rcx (.reg .rsi), .alu .and .rcx (.reg .r12),
     .store (at_ .r11 (l.D + l.off j)) .rcx, .shift .shr .rsi 52]

/-- `[r11] := [r8] [r9] 2^(-208 R)` modulo each prime, almost (`rbx` the area). -/
def ammCore : Prog isa :=
  .seq (.block (([.mov .r10 (.reg .rbx), .mov32 .rcx (.imm 4)] : List Instr) ++
      (List.range (2 * l.R + 5)).map fun r => .eop (.bin .vpxorq (vreg r) (vreg r) (vreg r))))
    (.seq (.loop (.block (ammBlock l)) .ne)
      (.block (((List.range 2).flatMap fun p => (List.range l.R).map fun k =>
          .evStore (at_ .r11 (l.D * p + 32 * k)) (acc l p k 0)) ++
        ([.movImm64 .r12 mask52] : List Instr) ++ carryOut l)))

/-- `[o] := [a] [b] 2^(-208 R)`, the offsets in `p`'s region. -/
def amm (o a b : Nat) : Prog isa :=
  .seq (.block [.mov .r8 (.reg .rbx), .alu .add .r8 (.imm (BitVec.ofNat 32 a)), .mov .r9 (.reg .rbx),
      .alu .add .r9 (.imm (BitVec.ofNat 32 b)), .mov .r11 (.reg .rbx), .alu .add .r11 (.imm (BitVec.ofNat 32 o))])
    (ammCore l)

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

/-- `aT := 2^dbls [aY] mod X` (`[aY] = R_X mod X`, so `aT = 2^(416 R - 64 W) mod X`). -/
def k1 : List (Prog isa) :=
  copyArr aT aY ++ [.block [.mov32 .rcx (.imm (BitVec.ofNat 32 l.dbls))], doubles aN aAcc aTmp aT sCtr]

/-- Array `j` into the limbs at offset `o` of the region at `r11`'s base
`rbx + p D`. -/
def arr52 (p j o : Nat) : List Instr :=
  ([.mov .rsi (.mem (hdr (sArr j))), .mov .r11 (.mem (hdr sIfma)),
    .alu .add .r11 (.imm (BitVec.ofNat 32 (l.D * p + o))), .movImm64 .r12 mask52] : List Instr) ++ to52 l

/-- `k₀` (the low 52 bits of the inverse) in each quadword of `oK0`, `r11`
the region (`r12` holds `2⁵² - 1`). -/
def k0St (p : Nat) : List Instr :=
  ([.mov .r11 (.mem (hdr sIfma)), .alu .add .r11 (.imm (BitVec.ofNat 32 (l.D * p))),
    .mov .rax (.mem (hdr sMinv)), .alu .and .rax (.reg .r12)] : List Instr) ++
  (List.range 4).map (fun i => .store (at_ .r11 (l.oK0 + 8 * i)) .rax)

/-- Zeros where the exponent goes. -/
def eZero : List Instr :=
  .mov32 .rax (.imm 0) :: (List.range l.W).map (fun i => .store (at_ .r11 (l.oE + 8 * i)) .rax)

/-- `q`'s last multiplier, 1 (`rax` is 0). -/
def finOne : List Instr :=
  (List.range l.L).map (fun j => .store (at_ .r11 (l.oFin + l.off j)) .rax) ++
    ([.mov32 .rax (.imm 1), .store (at_ .r11 l.oFin) .rax] : List Instr)

/-- The exponent's bytes (pointer and length in `n`'s slots `slotPtr`,
`slotLen`) at the end of the `E` at `oE`. -/
def eCopy (slotPtr slotLen : Nat) : List (Prog isa) :=
  [.block [.mov .rax (.mem (hdr sLink)), .mov .rsi (.mem (ws .rax slotPtr)), .mov .rcx (.mem (ws .rax slotLen)),
      .alu .add .r11 (.imm (BitVec.ofNat 32 (l.oE + l.E))), .alu .sub .r11 (.reg .rcx)],
    .loop (.block [.movzx8 .rax (at0 .rsi), .store8 (at0 .r11) .rax, .alu .add .rsi (.imm 1),
      .alu .add .r11 (.imm 1), .alu .sub .rcx (.imm 1)]) .ne]

/-- A prime's region (`p` 0 or 1): the modulus, `2^(416 R - 64 W) mod X`,
`x R_X` as `X`, `R_X` as `Y`, the last multiplier, `k₀`, the padded
exponent. -/
def region (p slotPtr slotLen : Nat) : List (Prog isa) :=
  k1 l ++ [.block (arr52 l p aN oM), .block (arr52 l p aT l.oK1), .block (arr52 l p aXc l.oX),
      .block (arr52 l p aY l.oY)] ++
    (if p = 0 then [.block (arr52 l p aY l.oFin)] else []) ++ [.block (k0St l p), .block (eZero l)] ++
    (if p = 0 then [] else [.block (finOne l)]) ++ eCopy l slotPtr slotLen

/-! ## The vector code (`rbx` the area) -/

/-- `[S] := T_v` for each prime, `v` the top 4 bits of the quadword at `oV`:
for each entry `j`, OR'ed in under the mask of `j = v`, in registers
`0`–`R - 1`, with the mask in `R` and a temporary in `R + 1`. -/
def select (p : Nat) : List (Prog isa) :=
  [.block (([.mov .r8 (.reg .rbx), .alu .add .r8 (.imm (BitVec.ofNat 32 (l.D * p + l.oTab))),
      .mov .rdx (.mem (at_ .rbx (l.D * p + l.oV))), .shift .shr .rdx 60,
      .mov32 .rcx (.imm 0)] : List Instr) ++ (List.range l.R).map fun k => .eop (.bin .vpxorq (vreg k) (vreg k) (vreg k))),
    .loop (.block (([.mov .rax (.reg .rcx), .alu .xor .rax (.reg .rdx), .alu .cmp .rax (.imm 1),
        .alu .sbb .rax (.reg .rax), .eop (.vmovq (vreg l.R) .rax), .eop (.vpbroadcastq (vreg l.R) (vreg l.R))] : List Instr) ++
      ((List.range l.R).flatMap fun k => [.evLoad (vreg (l.R + 1)) (at_ .r8 (32 * k)),
        .eop (.bin .vpandq (vreg (l.R + 1)) (vreg (l.R + 1)) (vreg l.R)),
        .eop (.bin .vporq (vreg k) (vreg k) (vreg (l.R + 1)))]) ++
      ([.alu .add .r8 (.imm (BitVec.ofNat 32 l.NB)), .alu .add .rcx (.imm 1), .alu .cmp .rcx (.imm 16)] : List Instr))) .ne,
    .block ((List.range l.R).map fun k => .evStore (at_ .rbx (l.D * p + l.oS + 32 * k)) (vreg k))]

/-- `[o] := [a]` (a number) in both regions. -/
def copyN (o a : Nat) : List Instr :=
  (List.range 2).flatMap fun p => (List.range l.R).flatMap fun k =>
    [.evLoad (vreg 0) (at_ .rbx (l.D * p + a + 32 * k)), .evStore (at_ .rbx (l.D * p + o + 32 * k)) (vreg 0)]

/-- The table: `T_0 = Y`, `T_1 = X`, `T_i = T_(i-1) X 2^(-208 R)` (`r13` the
offset of `T_i`). -/
def tabBuild : List (Prog isa) :=
  [.block (copyN l l.oTab l.oY ++ copyN l (l.oTab + l.NB) l.oX ++
      ([.mov32 .r13 (.imm (BitVec.ofNat 32 (l.oTab + 2 * l.NB)))] : List Instr)),
    .loop (.seq (.block [.mov .r8 (.reg .rbx), .alu .add .r8 (.reg .r13), .alu .sub .r8 (.imm (BitVec.ofNat 32 l.NB)),
        .mov .r9 (.reg .rbx), .alu .add .r9 (.imm (BitVec.ofNat 32 l.oX)), .mov .r11 (.reg .rbx),
        .alu .add .r11 (.reg .r13)])
      (.seq (ammCore l) (.block [.alu .add .r13 (.imm (BitVec.ofNat 32 l.NB)),
        .alu .cmp .r13 (.imm (BitVec.ofNat 32 (l.oTab + 16 * l.NB)))]))) .ne]

/-- A window: `Y := Y¹⁶ T_v 2^(-208 R)` for each prime, `v` the top 4 bits
of its byte at `oV`, which moves up 4 bits. -/
def window : List (Prog isa) :=
  [.block [.mov32 .r15 (.imm 4)],
    .loop (.seq (amm l l.oY l.oY l.oY) (.block [.alu .sub .r15 (.imm 1)])) .ne] ++
  select l 0 ++ select l 1 ++
  [.block ((List.range 2).flatMap fun p => [.mov .rax (.mem (at_ .rbx (l.D * p + l.oV))), .shift .ror .rax 60,
      .store (at_ .rbx (l.D * p + l.oV)) .rax]),
    amm l l.oY l.oY l.oS]

/-- The exponentiations, a byte of each exponent (`r13`) at a time. -/
def expLoop : List (Prog isa) :=
  tabBuild l ++ [.block [.mov32 .r13 (.imm 0)],
    .loop (seqs ([.block ((List.range 2).flatMap fun p =>
        [.movzx8 .rax { base := .rbx, index := some .r13, disp := ((l.D * p + l.oE : Nat) : Int) },
          .shift .ror .rax 8, .store (at_ .rbx (l.D * p + l.oV)) .rax]), .block [.mov32 .r14 (.imm 2)],
      .loop (seqs (window l ++ [.block [.alu .sub .r14 (.imm 1)]])) .ne,
      .block [.alu .add .r13 (.imm 1), .alu .cmp .r13 (.imm (BitVec.ofNat 32 l.E))]])) .ne]

/-- Intel's MXCSR prologue and epilogue around `c` (see "MCDT" in
`TCB/X86_64/Isa.lean`), the slots at `oMx`. -/
def withMxcsr (c : Prog isa) : Prog isa :=
  .seq (.block [.stmxcsr (at_ .rbx l.oMx), .mov32 .r11 (.mem (at_ .rbx l.oMx)), .alu32 .and .r11 (.imm 0xFFFF),
      .store32 (at_ .rbx l.oMx) .r11])
    (.seq (.seq (.block [.mov32 .rax (.imm 0x1FBF), .store32 (at_ .rbx (l.oMx + 4)) .rax,
        .ldmxcsr (at_ .rbx (l.oMx + 4)), .lfence]) (.seq c (.block [.lfence])))
      (.block [.ldmxcsr (at_ .rbx l.oMx), .vop .vzeroupper]))

/-- The vector code: `X` and `Y` into Montgomery form, the
exponentiations, and the results multiplied by `oFin`. -/
def vec : Prog isa :=
  withMxcsr l (seqs ([amm l l.oX l.oX l.oK1, amm l l.oY l.oY l.oK1] ++ expLoop l ++ [amm l l.oY l.oY l.oFin]))

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
def prep (mul : Nat → Nat → Nat → Prog isa) (sl : Nat) : List (Prog isa) :=
  [.block [.mov .rdi (.mem (hdr sl))]] ++ redc mul aR2 ++ copyArr aY aXc ++ redc mul aXm ++ [mul aT aY aXc] ++
    copyArr aXc aT ++ [mul aY aY aOne, .block [leave]]

/-- `q`'s and `p`'s bases (`x R_X mod X` in `aXc`, `R_X mod X` in `aY`). -/
def pre (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  prep mul sWsQ ++ prep mul sWsP

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
def main (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  seqs (nSetup mul ++ primesSetup ++ checks ++
    [.seq anySizes (.ite .e (seqs (pre mul ++ [ifmaAny] ++ post mul)) (seqs (qPhase mul ++ pPhase mul)))] ++
    finish)

/-- `vg_rsa_private_crt_ifma`. -/
def code (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block (Crt.entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] : List Instr) ++ invalid))
    (.ite .ne fail (main mul))

end VG.Impl.Rsa.X86_64.CrtIfma
