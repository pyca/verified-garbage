module

public import VerifiedGarbage.Impl.Rsa.X86_64.CrtIfma
public import VerifiedGarbage.Impl.Rsa.X86_64.Folded

/-!
# `vg_rsa_public_precomputed_checked` with AVX512_IFMA on x86-64: the layouts

The multiplication of `CrtIfma` with one lane, a modulus of `W` words in
numbers of `4 R` limbs of 52 bits, `S = 4 R` steps (the Montgomery radix
`2^(52 S)`, above `4 n`): 2048-, 3072- and 4096-bit moduli. A window width
does not apply (`w` is unused).
-/

@[expose] public section

namespace VG.Impl.Rsa.X86_64.PubIfma

open VG VG.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64.CrtIfma

/-- 2048-bit moduli: 32 words, numbers of 40 limbs. -/
def pay2048 : Lay := ⟨10, 32, 40, 4, 1⟩
/-- 3072-bit moduli: 48 words, numbers of 60 limbs. -/
def pay3072 : Lay := ⟨15, 48, 60, 4, 1⟩
/-- 4096-bit moduli: 64 words, numbers of 80 limbs. -/
def pay4096 : Lay := ⟨20, 64, 80, 4, 1⟩

/-! ## The area

In the working space, from the accumulator's array (`aAcc`, the base `rbx`):
the modulus' limbs at 0 and `k₀` after them (as `CrtIfma`'s regions), over
the accumulator and the temporary; then the numbers `A` and `B` from `R² mod
m`'s array on (`aXm`'s), and the MXCSR slots after them. -/

variable (l : Lay)

def oA : Nat := 24 * (l.W + 2)
def oB : Nat := oA l + l.NB
def oMx : Nat := oB l + l.NB

/-- `2^kb`, by which `amm(R², R²)` becomes `R'² mod m` (`R = 2^(64 W)`,
`R' = 2^(52 L)`). -/
def kb : Nat := 208 * l.L - 256 * l.W

/-- The offset of array `j` in the workspace (`rdi`), as the header lists it:
the addresses come from `rdi` alone, as the analysis of constant time needs. -/
def arr (j : Nat) : Nat := hdrBytes + j * (8 * (l.W + 2))

/-- `r := rdi + arr j`. -/
def base (r : Reg) (j : Nat) : List Instr := [.mov r (.reg .rdi), .alu .add r (.imm (BitVec.ofNat 32 (arr l j)))]

/-- Array `j` into the limbs at offset `o` (`r12` holds `2⁵² - 1`). -/
def ld52 (j o : Nat) : List Instr :=
  base l .rsi j ++ ([.mov .r11 (.reg .rbx), .alu .add .r11 (.imm (BitVec.ofNat 32 o))] : List Instr) ++ to52 l

/-- The base, the modulus' limbs and `k₀`, and `R² mod m` into `A`. -/
def setup : List Instr :=
  base l .rbx aAcc ++ ([.movImm64 .r12 mask52] : List Instr) ++ ld52 l aN 0 ++
    ([.mov .rax (.mem (hdr sMinv)), .alu .and .rax (.reg .r12)] : List Instr) ++
    (List.range 4).map (fun i => .store (at_ .rbx (l.NB + 8 * i)) .rax) ++ ld52 l aR2 (oA l)

/-- `B := 2^kb` (through `r11 = rbx`): zeros, then its one limb. -/
def pow2 : List Instr :=
  ([.mov .r11 (.reg .rbx), .mov32 .rax (.imm 0)] : List Instr) ++
    (List.range l.L).map (fun j => .store (at_ .r11 (oB l + l.off j)) .rax) ++
    ([.movImm64 .rax (BitVec.ofNat 64 (2 ^ (kb l % 52))), .store (at_ .r11 (oB l + l.off (kb l / 52))) .rax] :
      List Instr)

/-- Intel's MXCSR prologue and epilogue around `c` (see "MCDT" in
`TCB/X86_64/Isa.lean`), the slots at `oMx`. -/
def withMx (c : Prog isa) : Prog isa :=
  .seq (.block [.stmxcsr (at_ .rbx (oMx l)), .mov32 .r11 (.mem (at_ .rbx (oMx l))), .alu32 .and .r11 (.imm 0xFFFF),
      .store32 (at_ .rbx (oMx l)) .r11])
    (.seq (.seq (.block [.mov32 .rax (.imm 0x1FBF), .store32 (at_ .rbx (oMx l + 4)) .rax,
        .ldmxcsr (at_ .rbx (oMx l + 4)), .lfence]) (.seq c (.block [.lfence])))
      (.block [.ldmxcsr (at_ .rbx (oMx l)), .vop .vzeroupper]))

/-- `ammCore`'s operands: `[o] := [a] [b]`, the offsets from `rbx`. -/
def setOps (o a b : Nat) : List Instr :=
  [.mov .r8 (.reg .rbx), .alu .add .r8 (.imm (BitVec.ofNat 32 a)), .mov .r9 (.reg .rbx),
    .alu .add .r9 (.imm (BitVec.ofNat 32 b)), .mov .r11 (.reg .rbx), .alu .add .r11 (.imm (BitVec.ofNat 32 o))]

/-- Multiplication `r13`'s operands, and what it needs before: 0, `A := A A`
(`R⁴ / R'`); 1, `B := 2^kb` and `A := A B` (`R'²`); 2, `B := x` and
`A := B A` (`x R'`); 3 to 18, `A := A A`; 19, `A := A B` (`x^65537`). -/
def sel : Prog isa :=
  .seq (.block [.alu .cmp .r13 (.imm 1)]) (.ite .e (.block (pow2 l ++ setOps (oA l) (oA l) (oB l)))
    (.seq (.block [.alu .cmp .r13 (.imm 2)]) (.ite .e (.block (ld52 l aX (oB l) ++ setOps (oA l) (oB l) (oA l)))
      (.seq (.block [.alu .cmp .r13 (.imm 19)]) (.ite .e (.block (setOps (oA l) (oA l) (oB l)))
        (.block (setOps (oA l) (oA l) (oA l))))))))

/-- The vector code: the twenty multiplications of `sel`, by one `ammMul`
in a loop (`r13` counting them): `A = x^65537`, almost reduced. -/
def vec : Prog isa :=
  withMx l (.seq (.block [.mov32 .r13 (.imm 0)])
    (.loop (seqs [sel l, ammMul l, .block [.alu .add .r13 (.imm 1), .alu .cmp .r13 (.imm 20)]]) .ne))

/-- `A` into words at the accumulator, reduced below `m` into the result. -/
def fin : List (Prog isa) :=
  [.block (([.mov .r11 (.reg .rbx), .alu .add .r11 (.imm (BitVec.ofNat 32 (oA l))), .mov .r8 (.reg .rbx)] :
      List Instr) ++ to64 l ++ base l .rbx aY ++ base l .r10 aN ++
      ([.mov32 .r12 (.imm (BitVec.ofNat 32 l.W))] : List Instr) ++ base l .rsi aTmp),
    subMod, selectAcc]

/-- `x^65537 mod m` into the result, `x` the input. -/
def exp65537 : Prog isa := seqs ([.block (setup l), vec l] ++ fin l)

/-- The ADX code's: `X = x R`, `x^(e-1) R`, then `x^e`. -/
def adxExp (mm : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [mm aXm aX aR2, Folded.exp mm, mm aY aX aY]

/-- `w` (in `rax`) compared with `n`. -/
def cmpW (n : Nat) : Prog isa := .block [.mov .rax (.mem (hdr sW)), .alu .cmp .rax (.imm (BitVec.ofNat 32 n))]

/-- For `e = 65537` and 2048-, 3072- or 4096-bit moduli, `exp65537`;
otherwise the ADX code's. -/
def pubExp (mm : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq Folded.is65537 (.ite .e
    (.seq (cmpW 32) (.ite .e (exp65537 pay2048) (.seq (cmpW 48) (.ite .e (exp65537 pay3072)
      (.seq (cmpW 64) (.ite .e (exp65537 pay4096) (adxExp mm)))))))
    (adxExp mm))

/-- `Folded.rest` with `pubExp`. -/
def rest (mm : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block [.mov .rsi (.mem (hdr sIn)), .mov .rcx (.mem (hdr sK)), .mov .rbx (.mem (hdr (sArr aX)))],
  WordIO.load,
  .block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aX))),
    .mov .r10 (.mem (hdr (sArr aN))), .mov32 .rbp (.imm 0)],
  Compare8.code,
  .block (([.store (hdr sMask) .rbp, .mov .rbx (.mem (at0 .r10))] : List Instr) ++ minv ++
    ([.store (hdr sMinv) .r15, .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)] : List Instr)),
  setWord aOne .rcx,
  pubExp mm,
  .block [.mov .rbx (.mem (hdr (sArr aY))), .mov .rsi (.mem (hdr sOut)), .mov .rcx (.mem (hdr sK)),
    .mov .r15 (.mem (hdr sMask))],
  WordIO.store,
  .block (([.mov .rax (.mem (hdr sMask)), .alu .and .rax (.imm 1)] : List Instr) ++ exit)]

def code (mm : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block Precomputed.entry)
    (.seq (seqs (Precomputed.loadWith Compare8.code)) (.ite .e fail (rest mm)))

/-- `vg_rsa_public_precomputed_checked_ifma`. -/
def checked (mm : Nat → Nat → Nat → Prog isa) : Prog isa :=
  Checked.guarded (code mm)

end VG.Impl.Rsa.X86_64.PubIfma
