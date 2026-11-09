module

public import VerifiedGarbage.Impl.MillerRabin.X86_64.Round
public import VerifiedGarbage.Impl.Rsa.X86_64.PubIfma

/-!
# The shared Miller–Rabin round with AVX512_IFMA on x86-64

`code mul`: for a candidate of 16, 24, 32, 48 or 64 words (`PubIfma`'s
layouts `pay1024`, `pay1536`, `pay2048`, `pay3072`, `pay4096`), the round of `Round.lean` in radix `2⁵²`
with `CrtIfma`'s one-lane multiplication (`ammMul`), whose Montgomery radix
is `R' = 2^(52 S)`; otherwise `round mul`.

The exponent is the prepared `E = (c − 1) / 2^σ` (array `aE`), whose lowest
set bit ends a window of 4 bits and so one of 2 bits: windows of 2 bits
(`Proof/MillerRabin/WindowK.lean`) need a table of four entries, which
with every other number of the radix fits in the round's table arrays
(`aT0` to `aT0 + 15`); the round writes nothing else but its frame. The
area, from array `aT0` rounded up to a cache line (`rbx`, so that no 32-byte
access of the vector code is split): the modulus and `k₀`, `Y`, the
selected entry `S`, the table `T_j = b^j R' mod c` (`j < 4`, so `T_0 = R'
mod c`), `T_0 + c`, `c − T_0` and `c − T_0 + c`, the word of `E` being
scanned, the MXCSR slots and the flag. Every number has limbs below `2⁵²` and is below
`2 c`, so that `y ≡ ±1` is one of two limb-wise equalities with the
constants.

Before the vector code, in limbs: `K = 2^(104 S − 64 w) mod c` and `T_0` by
doublings of `R mod c` (`aR1`), `c − T_0` and the sums; `T_1 = b R mod c`
(`aXm`) times `K` makes `b R'`. The flag is a mask at `oF`, the words of `E` left
in `r15`, the windows left of a word in `r14` and the multiplications left
of a window in `r13`. After the last word, one more pass of three
squarings, each or'ing the flag with `y = −1` under the mask of `σ > j`
(`Round.mrLast`). No branch or address depends on anything but `rdi`, `rsp`
and these counters.
-/

@[expose] public section

namespace VG.Impl.MillerRabin.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
  VG.Impl.Rsa.X86_64.CrtIfma VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Impl.Rsa.X86_64.PubIfma (arr base ld52 setOps)

variable (l : Lay)

/-! ## The area -/

def oY : Nat := l.NB + 32
def oS : Nat := oY l + l.NB
/-- Entry `j` of the table. -/
def oT (j : Nat) : Nat := oS l + l.NB + j * l.NB
/-- `T_0 + c`, `c − T_0` and `c − T_0 + c`. -/
def oP1c : Nat := oT l 4
def oM1 : Nat := oP1c l + l.NB
def oM1c : Nat := oM1 l + l.NB
/-- The word of `E` being scanned. -/
def oV : Nat := oM1c l + l.NB
/-- The caller's MXCSR and `0x1FBF`. -/
def oMx : Nat := oV l + 8
/-- The flag, a mask. -/
def oF : Nat := oMx l + 8

/-- The doublings of `R mod c` that make `T_0 = R' mod c`. -/
def shifts : Nat := 52 * l.S - 64 * l.W

/-! ## Numbers in limbs, before the vector code (`r12` holds `2⁵² − 1`) -/

/-- `[o] := [a] + [b]`, the carries propagated, through `rdx` and `rax`. -/
def addN (o a b : Nat) : List Instr :=
  .mov32 .rdx (.imm 0) :: (List.range l.L).flatMap fun j =>
    [.alu .add .rdx (.mem (at_ .rbx (a + l.off j))), .alu .add .rdx (.mem (at_ .rbx (b + l.off j))),
      .mov .rax (.reg .rdx), .alu .and .rax (.reg .r12), .store (at_ .rbx (o + l.off j)) .rax,
      .shift .shr .rdx 52]

/-- `[o] := [a] − [b] mod 2^(52 L)`, a limb `a_j + (2⁵² − 1) + n − b_j` at a
time (`n` the carry, 1 for no borrow); `rdx` ends 1 if `[a] ≥ [b]`, else 0. -/
def subN (o a b : Nat) : List Instr :=
  .mov32 .rdx (.imm 1) :: (List.range l.L).flatMap fun j =>
    [.mov .rax (.mem (at_ .rbx (a + l.off j))), .alu .add .rax (.reg .r12), .alu .add .rax (.reg .rdx),
      .alu .sub .rax (.mem (at_ .rbx (b + l.off j))), .mov .rdx (.reg .rax), .shift .shr .rdx 52,
      .alu .and .rax (.reg .r12), .store (at_ .rbx (o + l.off j)) .rax]

/-- `[o] := [t]` under the mask `rdx`, limb by limb. -/
def selN (o t : Nat) : List Instr :=
  (List.range l.L).flatMap fun j =>
    [.mov .rax (.mem (at_ .rbx (o + l.off j))), .mov .rcx (.mem (at_ .rbx (t + l.off j))),
      .alu .xor .rcx (.reg .rax), .alu .and .rcx (.reg .rdx), .alu .xor .rax (.reg .rcx),
      .store (at_ .rbx (o + l.off j)) .rax]

/-- `[x] := 2 [x] mod c` (the modulus at 0), through `[tmp] := 2 [x]`. -/
def dbl1 (x tmp : Nat) : List Instr :=
  addN l tmp x x ++ subN l x tmp 0 ++ [.alu .cmp .rdx (.imm 1), .alu .sbb .rdx (.reg .rdx)] ++ selN l x tmp

/-- `[x] := 2^n [x] mod c`, `n ≥ 1` (`r13` counting). -/
def dbls (x tmp n : Nat) : Prog isa :=
  .seq (.block [.mov32 .r13 (.imm (BitVec.ofNat 32 n))])
    (.loop (.block (dbl1 l x tmp ++ [.alu .sub .r13 (.imm 1)])) .ne)

/-- The area's base, array `aT0` rounded up to a multiple of 64 bytes, and
`2⁵² − 1` in `r12`. -/
def area : List Instr :=
  base l .rbx aT0 ++ ([.alu .add .rbx (.imm 63), .alu .and .rbx (.imm (BitVec.ofInt 32 (-64))),
    .movImm64 .r12 mask52] : List Instr)

/-- The numbers of the area before the vector code: the modulus and `k₀`,
`b R mod c` (`aXm`) at `T_1`, `K` at `S`, `T_0`, `c − T_0` and the sums. -/
def setup : List (Prog isa) :=
  [.block (area l ++ ld52 l aN 0 ++
      ([.mov .rax (.mem (hdr sMinv)), .alu .and .rax (.reg .r12)] : List Instr) ++
      (List.range 4).map (fun i => .store (at_ .rbx (l.NB + 8 * i)) .rax) ++ ld52 l aXm (oT l 1) ++
      ld52 l aR1 (oS l) ++ ld52 l aR1 (oT l 0)),
    dbls l (oS l) (oY l) l.dbls, dbls l (oT l 0) (oY l) (shifts l),
    .block (subN l (oM1 l) 0 (oT l 0) ++ addN l (oP1c l) (oT l 0) 0 ++ addN l (oM1c l) (oM1 l) 0)]

/-! ## The vector code (`rbx` the area) -/

/-- The table, by one multiplication in a loop (`r13` counting from 3):
`T_1 := T_1 K`, `T_2 := T_1 T_1`, `T_3 := T_2 T_1`. -/
def table : Prog isa :=
  .seq (.block [.mov32 .r13 (.imm 3)])
    (.loop (.seq (.seq (.block [.alu .cmp .r13 (.imm 3)]) (.ite .e (.block (setOps (oT l 1) (oT l 1) (oS l)))
        (.seq (.block [.alu .cmp .r13 (.imm 2)]) (.ite .e (.block (setOps (oT l 2) (oT l 1) (oT l 1)))
          (.block (setOps (oT l 3) (oT l 2) (oT l 1)))))))
      (.seq (ammMul l) (.block [.alu .sub .r13 (.imm 1)]))) .ne)

/-- `[o] := [a]`, a number, through `vreg 0`. -/
def copyN (o a : Nat) : List Instr :=
  (List.range l.R).flatMap fun k =>
    [.evLoad (vreg 0) (at_ .rbx (a + 32 * k)), .evStore (at_ .rbx (o + 32 * k)) (vreg 0)]

/-- `rcx := −1` if `Y = [k]` limb by limb, else 0 (through `rax`). -/
def eqN (k : Nat) : List Instr :=
  .mov32 .rcx (.imm 0) :: (List.range l.L).flatMap (fun j =>
    [.mov .rax (.mem (at_ .rbx (oY l + l.off j))), .alu .xor .rax (.mem (at_ .rbx (k + l.off j))),
      .alu .or .rcx (.reg .rax)]) ++
  [.alu .cmp .rcx (.imm 1), .alu .sbb .rcx (.reg .rcx)]

/-- `rdx := −1` if `y ≡ −1` (`Y` is `c − T_0` or `c − T_0 + c`), else 0. -/
def isM1 : List Instr :=
  eqN l (oM1 l) ++ [.mov .rdx (.reg .rcx)] ++ eqN l (oM1c l) ++ [.alu .or .rdx (.reg .rcx)]

/-- `rdx := −1` if `y ≡ ±1`, else 0. -/
def isPM1 : List Instr :=
  isM1 l ++ eqN l (oT l 0) ++ [.alu .or .rdx (.reg .rcx)] ++ eqN l (oP1c l) ++ [.alu .or .rdx (.reg .rcx)]

/-- `[S] := T_d`, `d` the window's digit (the top two bits of the word at
`oV`): for each entry `j`, OR'ed in under the mask of `j = d` (one
`vpternlogq` per register), in registers `0`–`R − 1`, with the mask in `R`
and a temporary in `R + 1`. -/
def select : List Instr :=
  ([.mov .rdx (.mem (at_ .rbx (oV l))), .shift .shr .rdx 62] : List Instr) ++
  (List.range l.R).map (fun k => .eop (.bin .vpxorq (vreg k) (vreg k) (vreg k))) ++
  (List.range 4).flatMap (fun j =>
    ([.mov .rax (.reg .rdx), .alu .xor .rax (.imm (BitVec.ofNat 32 j)), .alu .cmp .rax (.imm 1),
      .alu .sbb .rax (.reg .rax), .eop (.vmovq (vreg l.R) .rax), .eop (.vpbroadcastq (vreg l.R) (vreg l.R))] :
        List Instr) ++
    (List.range l.R).flatMap fun k => [.evLoad (vreg (l.R + 1)) (at_ .rbx (oT l j + 32 * k)),
      .eop (.vpternlogq (vreg k) (vreg (l.R + 1)) (vreg l.R) 0xF8)]) ++
  (List.range l.R).map (fun k => .evStore (at_ .rbx (oS l + 32 * k)) (vreg k))

/-- After a window's multiplication by `T_d`: the flag `F := d ≠ 0 ? y ≡ ±1 : F`. -/
def afterMul : List Instr :=
  isPM1 l ++ [.mov .rcx (.mem (at_ .rbx (oF l))), .mov .rax (.mem (at_ .rbx (oV l))), .shift .shr .rax 62,
    .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax), .alu .and .rcx (.reg .rax),
    .alu .xor .rax (.imm (BitVec.ofInt 32 (-1))), .alu .and .rdx (.reg .rax), .alu .or .rcx (.reg .rdx),
    .store (at_ .rbx (oF l)) .rcx]

/-- After a squaring of a window: `F |= y ≡ −1`. -/
def afterSq : List Instr :=
  isM1 l ++ [.mov .rcx (.mem (at_ .rbx (oF l))), .alu .or .rcx (.reg .rdx), .store (at_ .rbx (oF l)) .rcx]

/-- After squaring `j` of the last three: `F |= y ≡ −1` under the mask of
`σ > j` (from the word after `E`'s, as `Round.mrLast`). -/
def afterLast (j : Nat) : List Instr :=
  isM1 l ++ [.movImm64 .rax (sigK j), .alu .and .rax (.mem { base := .rdi, disp := ((arr l aE + 8 * l.W : Nat) : Int) }),
    .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax), .alu .xor .rax (.imm (BitVec.ofInt 32 (-1))),
    .alu .and .rdx (.reg .rax), .mov .rcx (.mem (at_ .rbx (oF l))), .alu .or .rcx (.reg .rdx),
    .store (at_ .rbx (oF l)) .rcx]

/-- ZF iff the pass is the last one, three squarings after the windows (no
words of `E` left). -/
def isLast : List Instr := [.alu .test .r15 (.reg .r15)]

/-- A multiplication of a window (`r13` of them left): `S := T_d` and
`Y := Y S` for the last of a window's three, `Y := Y Y` otherwise; then the
flag. -/
def mult : Prog isa :=
  .seq (.seq (.block isLast) (.ite .e (.block (setOps (oY l) (oY l) (oY l)))
      (.seq (.block [.alu .cmp .r13 (.imm 1)]) (.ite .e (.block (select l ++ setOps (oY l) (oY l) (oS l)))
        (.block (setOps (oY l) (oY l) (oY l)))))))
    (.seq (ammMul l)
      (.seq (.seq (.block isLast) (.ite .e
          (.seq (.block [.alu .cmp .r13 (.imm 3)]) (.ite .e (.block (afterLast l 1))
            (.seq (.block [.alu .cmp .r13 (.imm 2)]) (.ite .e (.block (afterLast l 2)) (.block (afterLast l 3))))))
          (.seq (.block [.alu .cmp .r13 (.imm 1)]) (.ite .e (.block (afterMul l)) (.block (afterSq l))))))
        (.block [.alu .sub .r13 (.imm 1)])))

/-- A window: three multiplications; then the next digit. -/
def window : Prog isa :=
  .seq (.block [.mov32 .r13 (.imm 3)])
    (.seq (.loop (mult l) .ne)
      (.block [.mov .rax (.mem (at_ .rbx (oV l))), .shift .shl .rax 2, .store (at_ .rbx (oV l)) .rax,
        .alu .sub .r14 (.imm 1)]))

/-- A pass over a word of `E`: with `r15` words left, word `r15 − 1` into
`oV` and its 32 windows; with none left, one pass of three squarings. -/
def word : Prog isa :=
  .seq (.seq (.block isLast) (.ite .e (.block [.mov32 .r14 (.imm 1)])
      (.block [.mov .rax (.reg .r15), .alu .sub .rax (.imm 1),
        .mov .rcx (.mem { base := .rdi, index := some .rax, scale := 8, disp := ((arr l aE : Nat) : Int) }),
        .store (at_ .rbx (oV l)) .rcx, .mov32 .r14 (.imm 32)])))
    (.loop (window l) .ne)

/-- The windows: `y := T_0`, the flag clear, `r15 := w`; a pass of `word` for
each word and one more, each taking one off `r15`, to `−1`. -/
def windows : List (Prog isa) :=
  [.block (copyN l (oY l) (oT l 0) ++ ([.mov32 .rax (.imm 0), .store (at_ .rbx (oF l)) .rax,
      .mov32 .r15 (.imm (BitVec.ofNat 32 l.W))] : List Instr)),
    .loop (.seq (word l) (.block [.alu .sub .r15 (.imm 1), .alu .cmp .r15 (.imm (BitVec.ofInt 32 (-1)))])) .ne]

/-- Intel's MXCSR prologue and epilogue around `c` (see "MCDT" in
`TCB/X86_64/Isa.lean`), the caller's MXCSR (its bits 15:0) kept in `rbp`,
which `c` never writes: the shape of a save and restore that the proofs check
(`ctlOk`), as `Ffdh.X86_64.Ifma.withMx`. -/
def withMx (c : Prog isa) : Prog isa :=
  .seq (.seq (.block [.stmxcsr (at_ .rbx (oMx l)), .mov32 .rbp (.mem (at_ .rbx (oMx l))), .alu32 .and .rbp (.imm 0xFFFF)])
      (.seq (.seq (.block [.mov32 .rax (.imm 0x1FBF), .store32 (at_ .rbx (oMx l + 4)) .rax,
          .ldmxcsr (at_ .rbx (oMx l + 4)), .lfence]) (.seq c (.block [.lfence])))
        (.block [.store32 (at_ .rbx (oMx l)) .rbp, .ldmxcsr (at_ .rbx (oMx l))])))
    (.block [.vop .vzeroupper])

/-- The vector code: the table, then the windows. -/
def vec : Prog isa := withMx l (seqs (table l :: windows l))

/-- The passing flag into `rax`, and the callee-saved registers back from
the frame (`rbx` pushed first). -/
def finish : List Instr :=
  [.mov .rax (.mem (at_ .rbx (oF l))), .alu .and .rax (.imm 1),
    .mov .r15 (.mem { base := .rsp, disp := 0 }), .mov .r14 (.mem { base := .rsp, disp := 8 }),
    .mov .r13 (.mem { base := .rsp, disp := 16 }), .mov .r12 (.mem { base := .rsp, disp := 24 }),
    .mov .rbp (.mem { base := .rsp, disp := 32 }), .mov .rbx (.mem { base := .rsp, disp := 40 })]

/-- The round of a layout, in a frame of the six callee-saved registers. -/
def ifma : Prog isa :=
  .frame (.push [.rbx, .rbp, .r12, .r13, .r14, .r15]) (seqs (setup l ++ [vec l, .block (finish l)])) (.pop .r11 6)

end VG.Impl.MillerRabin.X86_64.Ifma

namespace VG.Impl.MillerRabin.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.PubIfma

/-- ZF: whether the candidate has `n` words (`rax` its words). -/
def isW (n : Nat) : List Instr := [.mov .rax (.mem (hdr sW)), .alu .cmp .rax (.imm (BitVec.ofNat 32 n))]

/-- The round of the layout of the candidate's size, `round mul` otherwise. -/
def code (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block (isW 16)) (.ite .e (ifma pay1024)
    (.seq (.block (isW 24)) (.ite .e (ifma pay1536)
      (.seq (.block (isW 32)) (.ite .e (ifma pay2048)
        (.seq (.block (isW 48)) (.ite .e (ifma pay3072)
          (.seq (.block (isW 64)) (.ite .e (ifma pay4096) (round mul))))))))))

end VG.Impl.MillerRabin.X86_64.Ifma
