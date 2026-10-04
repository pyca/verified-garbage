import VerifiedGarbage.Impl.Rsa.X86_64.Crt

/-!
# RSA with the CRT private key on x86-64, with AVX512_IFMA

`vg_rsa_private_crt_ifma`: `vg_rsa_private_crt_adx`'s code, but for a
modulus of 32 words and primes of 16 words each, whose two exponentiations
(modulo `p` and modulo `q`) run at once, in radix `2⁵²`, with AVX512_IFMA's
`vpmadd52luq` and `vpmadd52huq` on `ymm` registers.

* A number below `2¹⁰⁴⁰` is twenty limbs below `2⁵²`, limb `j` in quadword
  `j / 5` of the 32-byte vector `j % 5` (160 bytes): the stride layout.
* `amm`: two almost-Montgomery multiplications at once, `a b 2⁻¹⁰⁴⁰` modulo
  `p` and modulo `q` (below `2 p` and `2 q` for inputs below them), each in
  five registers. For each limb `b_i` of the second operand: the low halves
  of `a b_i` into the accumulator; `u = acc₀ k₀ mod 2⁵²` (`k₀ = -m⁻¹ mod
  2⁵²`); the low halves of `u m`; the carry of limb 0 into limb 1; the
  accumulator shifted down a limb, which in the stride layout is a change
  of the registers' roles and a lane shift of the register of limb 0; and
  the high halves of `a b_i` and `u m`. Five limbs make a block, after
  which the roles are back where they started. The result is carried
  limb by limb into twenty limbs below `2⁵²`.
* The two exponentiations: the bases and 1 in Montgomery form (`R = 2¹⁰⁴⁰`)
  from those of `vg_rsa_private_crt` (`R = 2¹⁰²⁴`) by a multiplication by
  `2¹⁰⁵⁶ mod X`, a table of the 16 powers, and four squares and a
  multiplication by the masked selection of an entry per window of 4 bits,
  with the exponents padded with zero bytes at the top to 128 bytes; then a
  multiplication by 1, which leaves the result out of Montgomery form,
  below `X + 1`, reduced in 64-bit words.

The IFMA area follows `q`'s workspace: `p`'s region, then `q`'s at `D`,
then the MXCSR slots. Its base stays in `rbx` while the vector code runs,
and in slot `sIfma` of the prime workspaces otherwise.
-/

namespace VG.Impl.Rsa.X86_64.CrtIfma

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
  VG.Impl.Rsa.X86_64.Crt

/-! ## Layout -/

/-- In a prime's region: the modulus, `k₀` in each quadword, `Y`, the base
`X`, the selected entry, the table, the padded exponent, `2¹⁰⁵⁶ mod X`,
the bytes of the exponent being read, the last multiplier. -/
def oM : Nat := 0
def oK0 : Nat := 160
def oY : Nat := 192
def oX : Nat := 352
def oS : Nat := 512
def oTab : Nat := 672
def oE : Nat := 3232
def oK1 : Nat := 3360
def oV : Nat := 3520
/-- The last multiplier: 1 for `q`, `R mod p` for `p`. -/
def oFin : Nat := 3552
/-- `q`'s region from `p`'s. -/
def D : Nat := 3712
/-- The caller's MXCSR (its bits 15:0) and `0x1FBF`, after both regions. -/
def oMx : Nat := 2 * D
/-- The size of the area. -/
def areaBytes : Nat := 2 * D + 8

/-- In the prime workspaces: the base of the IFMA area, and a counter. -/
def sIfma : Nat := sFn 13
def sCtr : Nat := sFn 14

/-- The quadword of limb `j` in the stride layout. -/
def off (j : Nat) : Nat := 32 * (j % 5) + 8 * (j / 5)

def at_ (r : Reg) (d : Nat) : MemOp := { base := r, disp := d }

def mask52 : BitVec 64 := BitVec.ofNat 64 (2 ^ 52 - 1)

/-! ## The multiplication -/

def xr : Nat → XReg
  | 0 => .xmm0 | 1 => .xmm1 | 2 => .xmm2 | 3 => .xmm3 | 4 => .xmm4
  | 5 => .xmm5 | 6 => .xmm6 | 7 => .xmm7 | 8 => .xmm8 | 9 => .xmm9
  | 10 => .xmm10 | 11 => .xmm11 | 12 => .xmm12 | 13 => .xmm13 | 14 => .xmm14 | _ => .xmm15

/-- The register of limb role `k` of prime `p` at step `i` of a block. -/
def acc (p k i : Nat) : XReg := xr (5 * p + (k + i) % 5)
def bReg (p : Nat) : XReg := xr (10 + p)
def uReg (p : Nat) : XReg := xr (12 + p)
def zReg : XReg := .xmm14
def tReg : XReg := .xmm15

/-- Step `i` (0–4) of a block, for `p` (0) and `q` (1) in turn at each
stage: `r8` the first operand, `r9` the second plus 8 per block, `r10` the
region (the modulus and `k₀`). -/
def ammStep (i : Nat) : List Instr :=
  let ps := [0, 1]
  ps.flatMap (fun p => [.mov .rax (.mem (at_ .r9 (D * p + 32 * i))), .vop (.vmovq (bReg p) .rax),
    .vop (.vpbroadcastq .l256 (bReg p) (bReg p))]) ++
  ps.flatMap (fun p => (List.range 5).map fun k =>
    .vpmadd52Load false (acc p k i) (bReg p) (at_ .r8 (D * p + 32 * k))) ++
  ps.flatMap (fun p => [.vop (.vbin .vpxor .l256 tReg tReg tReg),
    .vpmadd52Load false tReg (acc p 0 i) (at_ .r10 (D * p + oK0)),
    .vop (.vpbroadcastq .l256 (uReg p) tReg)]) ++
  ps.flatMap (fun p => (List.range 5).map fun k =>
    .vpmadd52Load false (acc p k i) (uReg p) (at_ .r10 (D * p + oM + 32 * k))) ++
  ps.flatMap (fun p => [.vop (.vshift .psrlq .l256 tReg (acc p 0 i) 52),
    .vop (.vpblendd .l256 tReg zReg tReg 0x03), .vop (.vbin .vpaddq .l256 (acc p 1 i) (acc p 1 i) tReg),
    .vop (.vpermq (acc p 0 i) (acc p 0 i) 0x39),
    .vop (.vpblendd .l256 (acc p 0 i) (acc p 0 i) zReg 0xC0)]) ++
  ps.flatMap (fun p => (List.range 5).flatMap fun k =>
    [.vpmadd52Load true (acc p k (i + 1)) (bReg p) (at_ .r8 (D * p + 32 * k)),
     .vpmadd52Load true (acc p k (i + 1)) (uReg p) (at_ .r10 (D * p + oM + 32 * k))])

/-- A block: five steps, then the next block's limbs of the second operand
and the count of blocks. -/
def ammBlock : List Instr :=
  (List.range 5).flatMap ammStep ++ [.alu .add .r9 (.imm 8), .alu .sub .rcx (.imm 1)]

/-- The accumulators' twenty limbs, carried in order into limbs below `2⁵²`,
at `r11` and `r11 + D`, the two chains interleaved (carries in `rdx` and
`rsi`); `r12` holds `2⁵² - 1`. -/
def carryOut : List Instr :=
  [.mov32 .rdx (.imm 0), .mov32 .rsi (.imm 0)] ++ (List.range 20).flatMap fun j =>
    [.alu .add .rdx (.mem (at_ .r11 (off j))), .mov .rax (.reg .rdx), .alu .and .rax (.reg .r12),
     .store (at_ .r11 (off j)) .rax, .shift .shr .rdx 52,
     .alu .add .rsi (.mem (at_ .r11 (D + off j))), .mov .rcx (.reg .rsi), .alu .and .rcx (.reg .r12),
     .store (at_ .r11 (D + off j)) .rcx, .shift .shr .rsi 52]

/-- `[r11] := [r8] [r9] 2⁻¹⁰⁴⁰` modulo each prime, almost (`rbx` the area). -/
def ammCore : Prog isa :=
  .seq (.block ([.mov .r10 (.reg .rbx), .mov32 .rcx (.imm 4)] ++
      (List.range 15).map fun r => .vop (.vbin .vpxor .l256 (xr r) (xr r) (xr r))))
    (.seq (.loop (.block ammBlock) .ne)
      (.block (((List.range 2).flatMap fun p => (List.range 5).map fun k =>
          .vmovdquStore .l256 (at_ .r11 (D * p + 32 * k)) (acc p k 0)) ++
        [.movImm64 .r12 mask52] ++ carryOut)))

/-- `[o] := [a] [b] 2⁻¹⁰⁴⁰`, the offsets in `p`'s region. -/
def amm (o a b : Nat) : Prog isa :=
  .seq (.block [.mov .r8 (.reg .rbx), .alu .add .r8 (.imm (BitVec.ofNat 32 a)), .mov .r9 (.reg .rbx),
      .alu .add .r9 (.imm (BitVec.ofNat 32 b)), .mov .r11 (.reg .rbx), .alu .add .r11 (.imm (BitVec.ofNat 32 o))])
    ammCore

/-! ## Moving numbers between the layouts -/

/-- `r` shifted left by `t` (`0 < t < 64`), through `rbp`: rotated, its low
`t` bits cleared. -/
def shl (r : Reg) (t : Nat) : List Instr :=
  [.shift .ror r (64 - t), .movImm64 .rbp (BitVec.ofNat 64 (2 ^ 64 - 2 ^ t)), .alu .and r (.reg .rbp)]

/-- The sixteen words at `rsi` into twenty limbs at `r11` (`r12` holds
`2⁵² - 1`). -/
def to52 : List Instr :=
  (List.range 20).flatMap fun j =>
    let b := 52 * j
    let w := b / 64
    let s := b % 64
    ([.mov .rax (.mem (at_ .rsi (8 * w)))] : List Instr) ++
    (if s = 0 then [] else [.shift .shr .rax s]) ++
    (if 12 < s ∧ w + 1 < 16 then
      ([.mov .rcx (.mem (at_ .rsi (8 * (w + 1))))] : List Instr) ++ shl .rcx (64 - s) ++
        ([.alu .or .rax (.reg .rcx)] : List Instr)
    else []) ++
    ([.alu .and .rax (.reg .r12), .store (at_ .r11 (off j)) .rax] : List Instr)

/-- Twenty limbs below `2⁵²` at `r11` into seventeen words at `r8`. -/
def to64 : List Instr :=
  (List.range 17).flatMap fun w =>
    let lo := 64 * w
    let js := (List.range 20).filter fun j => 52 * j < lo + 64 ∧ lo < 52 * j + 52
    (.mov32 .rax (.imm 0) :: js.flatMap fun j =>
      ([.mov .rcx (.mem (at_ .r11 (off j)))] : List Instr) ++
      (if lo ≤ 52 * j then (if 52 * j = lo then [] else shl .rcx (52 * j - lo))
        else [.shift .shr .rcx (lo - 52 * j)]) ++
      ([.alu .or .rax (.reg .rcx)] : List Instr)) ++
    [.store (at_ .r8 (8 * w)) .rax]

/-! ## Before the vector code, in a prime's workspace (`rdi`) -/

/-- `aT := 2³² [aY] mod X` (`[aY] = R mod X`, so `aT = 2¹⁰⁵⁶ mod X`). -/
def k1 : List (Prog isa) :=
  copyArr aT aY ++ [.block [.mov32 .rcx (.imm 32)], doubles aN aAcc aTmp aT sCtr]

/-- Array `j` into the limbs at offset `o` of the region at `r11`'s base
`rbx + p D`. -/
def arr52 (p j o : Nat) : List Instr :=
  [.mov .rsi (.mem (hdr (sArr j))), .mov .r11 (.mem (hdr sIfma)),
    .alu .add .r11 (.imm (BitVec.ofNat 32 (D * p + o))), .movImm64 .r12 mask52] ++ to52

/-- A prime's region (`p` 0 or 1): the modulus, `k₀`, `2¹⁰⁵⁶ mod X`, `x R`
as `X`, `R` as `Y` (both still with `R = 2¹⁰²⁴`), the last multiplier, the padded exponent
(pointer and length in `n`'s slots `slotPtr`, `slotLen`). -/
def region (p slotPtr slotLen : Nat) : List (Prog isa) :=
  k1 ++ [.block (arr52 p aN oM ++ arr52 p aT oK1 ++ arr52 p aXc oX ++ arr52 p aY oY ++
    (if p = 0 then arr52 p aY oFin else []) ++
    [.mov .r11 (.mem (hdr sIfma)), .alu .add .r11 (.imm (BitVec.ofNat 32 (D * p))),
      .mov .rax (.mem (hdr sMinv)), .alu .and .rax (.reg .r12)] ++
    (List.range 4).map (fun l => .store (at_ .r11 (oK0 + 8 * l)) .rax) ++
    [.mov32 .rax (.imm 0)] ++ (List.range 16).map (fun l => .store (at_ .r11 (oE + 8 * l)) .rax) ++
    (if p = 0 then [] else (List.range 20).map (fun j => .store (at_ .r11 (oFin + off j)) .rax) ++
      [.mov32 .rax (.imm 1), .store (at_ .r11 oFin) .rax]) ++
    [
      .mov .rax (.mem (hdr sLink)), .mov .rsi (.mem (ws .rax slotPtr)), .mov .rcx (.mem (ws .rax slotLen)),
      .alu .add .r11 (.imm (BitVec.ofNat 32 (oE + 128))), .alu .sub .r11 (.reg .rcx)]),
    .loop (.block [.movzx8 .rax (at0 .rsi), .store8 (at0 .r11) .rax, .alu .add .rsi (.imm 1),
      .alu .add .r11 (.imm 1), .alu .sub .rcx (.imm 1)]) .ne]

/-! ## The vector code (`rbx` the area) -/

/-- `[S] := T_v` for each prime, `v` the top 4 bits of the quadword at `oV`:
for each entry `j`, OR'ed in under the mask of `j = v`. -/
def select (p : Nat) : List (Prog isa) :=
  [.block ([.mov .r8 (.reg .rbx), .alu .add .r8 (.imm (BitVec.ofNat 32 (D * p + oTab))),
      .mov .rdx (.mem (at_ .rbx (D * p + oV))), .shift .shr .rdx 60,
      .mov32 .rcx (.imm 0)] ++ (List.range 5).map fun k => .vop (.vbin .vpxor .l256 (xr k) (xr k) (xr k))),
    .loop (.block ([.mov .rax (.reg .rcx), .alu .xor .rax (.reg .rdx), .alu .cmp .rax (.imm 1),
        .alu .sbb .rax (.reg .rax), .vop (.vmovq .xmm5 .rax), .vop (.vpbroadcastq .l256 .xmm5 .xmm5)] ++
      ((List.range 5).flatMap fun k => [.vmovdquLoad .l256 .xmm6 (at_ .r8 (32 * k)),
        .vop (.vbin .vpand .l256 .xmm6 .xmm6 .xmm5), .vop (.vbin .vpor .l256 (xr k) (xr k) .xmm6)]) ++
      [.alu .add .r8 (.imm 160), .alu .add .rcx (.imm 1), .alu .cmp .rcx (.imm 16)])) .ne,
    .block ((List.range 5).map fun k => .vmovdquStore .l256 (at_ .rbx (D * p + oS + 32 * k)) (xr k))]

/-- `[o] := [a]` (160 bytes) in both regions. -/
def copy160 (o a : Nat) : List Instr :=
  (List.range 2).flatMap fun p => (List.range 5).flatMap fun k =>
    [.vmovdquLoad .l256 .xmm0 (at_ .rbx (D * p + a + 32 * k)), .vmovdquStore .l256 (at_ .rbx (D * p + o + 32 * k)) .xmm0]

/-- The table: `T_0 = Y`, `T_1 = X`, `T_i = T_(i-1) X 2⁻¹⁰⁴⁰` (`r13` the
offset of `T_i`). -/
def tabBuild : List (Prog isa) :=
  [.block (copy160 oTab oY ++ copy160 (oTab + 160) oX ++ [.mov32 .r13 (.imm (BitVec.ofNat 32 (oTab + 320)))]),
    .loop (.seq (.block [.mov .r8 (.reg .rbx), .alu .add .r8 (.reg .r13), .alu .sub .r8 (.imm 160),
        .mov .r9 (.reg .rbx), .alu .add .r9 (.imm (BitVec.ofNat 32 oX)), .mov .r11 (.reg .rbx),
        .alu .add .r11 (.reg .r13)])
      (.seq ammCore (.block [.alu .add .r13 (.imm 160), .alu .cmp .r13 (.imm (BitVec.ofNat 32 (oTab + 2560)))]))) .ne]

/-- A window: `Y := Y¹⁶ T_v 2⁻¹⁰⁴⁰` for each prime, `v` the top 4 bits of
its byte at `oV`, which moves up 4 bits. -/
def window : List (Prog isa) :=
  [.block [.mov32 .r15 (.imm 4)],
    .loop (.seq (amm oY oY oY) (.block [.alu .sub .r15 (.imm 1)])) .ne] ++
  select 0 ++ select 1 ++
  [.block ((List.range 2).flatMap fun p => [.mov .rax (.mem (at_ .rbx (D * p + oV))), .shift .ror .rax 60,
      .store (at_ .rbx (D * p + oV)) .rax]),
    amm oY oY oS]

/-- The exponentiations, a byte of each exponent (`r13`) at a time. -/
def expLoop : List (Prog isa) :=
  tabBuild ++ [.block [.mov32 .r13 (.imm 0)],
    .loop (seqs ([.block ((List.range 2).flatMap fun p =>
        [.movzx8 .rax { base := .rbx, index := some .r13, disp := ((D * p + oE : Nat) : Int) },
          .shift .ror .rax 8, .store (at_ .rbx (D * p + oV)) .rax]), .block [.mov32 .r14 (.imm 2)],
      .loop (seqs (window ++ [.block [.alu .sub .r14 (.imm 1)]])) .ne,
      .block [.alu .add .r13 (.imm 1), .alu .cmp .r13 (.imm 128)]])) .ne]

/-- Intel's MXCSR prologue and epilogue around `c` (see "MCDT" in
`TCB/X86_64/Isa.lean`), the slots at `oMx`. -/
def withMxcsr (c : Prog isa) : Prog isa :=
  .seq (.block [.stmxcsr (at_ .rbx oMx), .mov32 .r11 (.mem (at_ .rbx oMx)), .alu32 .and .r11 (.imm 0xFFFF),
      .store32 (at_ .rbx oMx) .r11])
    (.seq (.seq (.block [.mov32 .rax (.imm 0x1FBF), .store32 (at_ .rbx (oMx + 4)) .rax,
        .ldmxcsr (at_ .rbx (oMx + 4)), .lfence]) (.seq c (.block [.lfence])))
      (.block [.ldmxcsr (at_ .rbx oMx), .vop .vzeroupper]))

/-- The vector code: `X` and `Y` into Montgomery form, the
exponentiations, and the results multiplied by `oFin`: `m_q` (below `q +
1`) and `m_p R_p mod p` (below `2 p`). -/
def vec : Prog isa :=
  withMxcsr (seqs ([amm oX oX oK1, amm oY oY oK1] ++ expLoop ++ [amm oY oY oFin]))

/-- In a prime's workspace: the result into `aY`, reduced below `X`. -/
def result (p : Nat) : List (Prog isa) :=
  [.block ([.mov .r11 (.mem (hdr sIfma)), .alu .add .r11 (.imm (BitVec.ofNat 32 (D * p + oY))),
      .mov .r8 (.mem (hdr (sArr aAcc)))] ++ to64 ++
      [.mov .rbx (.mem (hdr (sArr aY))), .mov .r10 (.mem (hdr (sArr aN))), .mov .r12 (.mem (hdr sW)),
        .mov .rsi (.mem (hdr (sArr aTmp)))]),
    subMod, selectAcc]

/-! ## The phases -/

/-- `q`'s and `p`'s bases (`x R_X mod X` in `aXc`, `R_X mod X` in `aY`).
Both primes have 16 words, so `G = 2^E mod n` is the same for both: it is
computed once, kept in `n`'s `aX` (for `p`'s, and for after the
exponentiations). -/
def pre (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  gPow mul sWsQ ++ copyArr aX aY ++ [.block [enterQ]] ++ redc mul aY ++ copyArr aY aXc ++
    [.block [leave], mul aY aXm aY, .block [enterQ]] ++ redc mul aY ++ [.block [leave]] ++
  copyArr aY aX ++ [.block [enterP]] ++ redc mul aY ++ copyArr aY aXc ++
    [.block [leave], mul aY aXm aY, .block [enterP]] ++ redc mul aY ++ [.block [leave]]

/-- The IFMA area after `q`'s workspace, its base into both prime
workspaces; the regions; the vector code; the results. -/
def ifma : List (Prog isa) :=
  [.block ([.mov .rdx (.mem (hdr sWsQ))] ++ wsEndT ++ [.mov .rdx (.mem (hdr sWsP)), .store (ws .rdx sIfma) .rax,
      .mov .rdx (.mem (hdr sWsQ)), .store (ws .rdx sIfma) .rax, enterP])] ++
  region 0 sDp sPlen ++ [.block [leave, enterQ]] ++ region 1 sDq sQlen ++
  [.block [.mov .rbx (.mem (hdr sIfma))], vec] ++
  result 1 ++ [.block [leave, enterP]] ++ result 0 ++ [.block [leave]]

/-- `p`'s phase after its exponentiation, as `pPhase`: `m_q R_p`, `h`. -/
def post (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  copyArr aY aX ++ [zeroArr aX,
    .block [.mov .rax (.mem (hdr sWsQ)), .mov .rsi (.mem (ws .rax (sArr aY))), .mov .r12 (.mem (ws .rax sW)),
      .mov .rbx (.mem (hdr (sArr aX)))],
    copyWords, mul aX aX aR2, mul aX aX aY, .block [enterP]] ++ redc mul aX ++
  subModArr aT aY aXc ++ loadArr aChunk sQinv sPlen ++ maskArr aChunk ++ [mul aY aT aChunk, .block [leave]]

/-- Whether `n` has 32 words and `p` and `q` 16: ZF. -/
def sizes : List Instr :=
  [.mov .rax (.mem (hdr sW)), .alu .xor .rax (.imm 32), .mov .rdx (.mem (hdr sWsP)), .mov .rdx (.mem (ws .rdx sW)),
    .alu .xor .rdx (.imm 16), .alu .or .rax (.reg .rdx), .mov .rdx (.mem (hdr sWsQ)), .mov .rdx (.mem (ws .rdx sW)),
    .alu .xor .rdx (.imm 16), .alu .or .rax (.reg .rdx)]

def main (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  seqs (nSetup mul ++ primesSetup ++ checks ++ [.block sizes,
    .ite .e (seqs (pre mul ++ ifma ++ post mul)) (seqs (qPhase mul ++ pPhase mul))] ++ finish)

/-- `vg_rsa_private_crt_ifma`. -/
def code (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block (Crt.entry ++ [.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] ++ invalid))
    (.ite .ne fail (main mul))

end VG.Impl.Rsa.X86_64.CrtIfma
