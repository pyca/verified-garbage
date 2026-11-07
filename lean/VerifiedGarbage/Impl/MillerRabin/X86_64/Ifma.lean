module

public import VerifiedGarbage.Impl.MillerRabin.X86_64.Round
public import VerifiedGarbage.Impl.Rsa.X86_64.PubIfma

/-!
# The shared Miller–Rabin round with AVX512_IFMA on x86-64

`code mul`: for a candidate of 32, 48 or 64 words (`PubIfma`'s layouts
`pay2048`, `pay3072`, `pay4096`), the round of `Round.lean` in radix `2⁵²`
with `CrtIfma`'s one-lane multiplication (`ammMul`), whose Montgomery radix
is `R' = 2^(52 S)`; otherwise `round mul`.

The exponent is the prepared `E = (c − 1) / 2^σ` (array `aE`), whose lowest
set bit ends a window of 4 bits and so one of 2 bits: windows of 2 bits
(`Proof/MillerRabin/WindowK.lean`) need a table of four entries, which
with every other number of the radix fits in the round's table arrays
(`aT0` to `aT0 + 15`), the only arrays it may write but `aAcc`, `aTmp`,
`aXm`, `aY`. The area, from array `aT0` (`rbx`, rounded up to a cache line): the modulus and `k₀`,
`Y`, the selected entry `S`, the table `T_j = b^j R' mod c` (`j < 4`, so
`T_0 = R' mod c`), `T_0 + c`, `c − T_0` and `c − T_0 + c`, and the MXCSR
slots. Every number is below `2 c` with limbs below `2⁵²`, and the
constants are below `2 c` and reduced limb by limb, so that `y ≡ ±1` is
one of two limb-wise equalities.

Before the vector code, in 64-bit words: `K = 2^(104 S − 64 w) mod c` and
`T_0` by doublings of `R mod c` (`aR1`) in `aY`, and `c − T_0` in `aTmp`;
`T_1 = b R mod c` (`aXm`) times `K` makes `b R'`. The flag is in `rbp`, the
word of `E` being scanned in `r15` (its windows from the top), the windows
left of it in `r14` and the multiplications left of a window in `r13`; the
words left in the header's `kWords`. After the last word, one more pass of
three squarings, each or'ing the flag with `y = −1` under the mask of
`σ > j` (`Round.mrLast`).
-/

@[expose] public section

namespace VG.Impl.MillerRabin.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
  VG.Impl.Rsa.X86_64.CrtIfma VG.Impl.RsaKeyGen.X86_64.Candidate

variable (l : Lay)

/-! ## The area -/

/-- The offset of array `j` in the workspace of `W` words. -/
def arr (j : Nat) : Nat := hdrBytes + j * (8 * (l.W + 2))

/-- The area: from array `aT0`. -/
def oArea : Nat := arr l aT0

def oY : Nat := l.NB + 32
def oS : Nat := oY l + l.NB
/-- Entry `j` of the table. -/
def oT (j : Nat) : Nat := oS l + l.NB + j * l.NB
/-- `T_0 + c`, `c − T_0` and `c − T_0 + c`. -/
def oP1c : Nat := oT l 4
def oM1 : Nat := oP1c l + l.NB
def oM1c : Nat := oM1 l + l.NB
/-- The caller's MXCSR and `0x1FBF`. -/
def oMx : Nat := oM1c l + l.NB

/-- The doublings of `R mod c` that make `T_0 = R' mod c`. -/
def shifts : Nat := 52 * l.S - 64 * l.W

/-! ## Before the vector code -/

/-- `r := rdi + arr j`. -/
def base (r : Reg) (j : Nat) : List Instr :=
  [.mov r (.reg .rdi), .alu .add r (.imm (BitVec.ofNat 32 (arr l j)))]

/-- Array `j` into the limbs at offset `o` of the area (`r12` holds `2⁵² − 1`). -/
def ld52 (j o : Nat) : List Instr :=
  base l .rsi j ++ ([.mov .r11 (.reg .rbx), .alu .add .r11 (.imm (BitVec.ofNat 32 o))] : List Instr) ++ to52 l

/-- `[o] := [a] + [b]` limb by limb, the carries propagated (`r12` holds
`2⁵² − 1`), through `rdx` and `rax`. -/
def addN (o a b : Nat) : List Instr :=
  .mov32 .rdx (.imm 0) :: (List.range l.L).flatMap fun j =>
    [.alu .add .rdx (.mem (at_ .rbx (a + l.off j))), .alu .add .rdx (.mem (at_ .rbx (b + l.off j))),
      .mov .rax (.reg .rdx), .alu .and .rax (.reg .r12), .store (at_ .rbx (o + l.off j)) .rax,
      .shift .shr .rdx 52]

/-- `aY := 2^n R mod c`: `R mod c` (`aR1`) copied, doubled `n` times (the
count in `kBits`). -/
def dbl (n : Nat) : List (Prog isa) :=
  [.block (([.mov .r12 (.mem (hdr sW))] : List Instr) ++ base l .rsi aR1 ++ [.mov .rbx (.mem (hdr (sArr aY)))]),
    copyWords, .block [.mov32 .rcx (.imm (BitVec.ofNat 32 n))], doubles aN aAcc aTmp aY kBits]

/-- The area's base, array `aT0` rounded up to a multiple of 64 bytes (a
cache line, so that no 32-byte access of the vector code is split; there is
room for the area at any of the eight offsets), and `2⁵² − 1` in `r12`. -/
def area : List Instr :=
  base l .rbx aT0 ++ ([.alu .add .rbx (.imm 63), .alu .and .rbx (.imm (BitVec.ofInt 32 (-64))),
    .movImm64 .r12 mask52] : List Instr)

/-- The numbers of the area before the vector code: the modulus and `k₀`;
`b R mod c` (`aXm`) at `T_1`, `K` at `S`, `T_0`, `c − T_0`, and the sums. -/
def setup : List (Prog isa) :=
  [.block (area l ++ ld52 l aN 0 ++
      ([.mov .rax (.mem (hdr sMinv)), .alu .and .rax (.reg .r12)] : List Instr) ++
      (List.range 4).map (fun i => .store (at_ .rbx (l.NB + 8 * i)) .rax) ++ ld52 l aXm (oT l 1))] ++
  dbl l l.dbls ++ [.block (area l ++ ld52 l aY (oS l))] ++
  dbl l (shifts l) ++ [.block (area l ++ ld52 l aY (oT l 0))] ++
  [.block (([.mov .r12 (.mem (hdr sW))] : List Instr) ++ base l .r8 aN ++ base l .r10 aY ++ base l .rsi aTmp),
    subMod,
    .block (area l ++ ld52 l aTmp (oM1 l) ++ addN l (oP1c l) (oT l 0) 0 ++ addN l (oM1c l) (oM1 l) 0)]

/-! ## The vector code (`rbx` the area) -/

/-- `[o] := [a] [b] 2^(-52 S)`. -/
def ops (o a b : Nat) : List Instr :=
  [.mov .r8 (.reg .rbx), .alu .add .r8 (.imm (BitVec.ofNat 32 a)), .mov .r9 (.reg .rbx),
    .alu .add .r9 (.imm (BitVec.ofNat 32 b)), .mov .r11 (.reg .rbx), .alu .add .r11 (.imm (BitVec.ofNat 32 o))]

/-- The table, by one multiplication in a loop (`r13` counting from 3):
`T_1 := T_1 K`, `T_2 := T_1 T_1`, `T_3 := T_2 T_1`. -/
def table : Prog isa :=
  .seq (.block [.mov32 .r13 (.imm 3)])
    (.loop (.seq (.seq (.block [.alu .cmp .r13 (.imm 3)]) (.ite .e (.block (ops (oT l 1) (oT l 1) (oS l)))
        (.seq (.block [.alu .cmp .r13 (.imm 2)]) (.ite .e (.block (ops (oT l 2) (oT l 1) (oT l 1)))
          (.block (ops (oT l 3) (oT l 2) (oT l 1)))))))
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

/-- `[S] := T_d`, `d` the window's digit (the top two bits of `r15`): for
each entry `j`, OR'ed in under the mask of `j = d` (one `vpternlogq` per
register), in registers `0`–`R − 1`, with the mask in `R` and a temporary
in `R + 1`. -/
def select : List Instr :=
  ([.mov .rdx (.reg .r15), .shift .shr .rdx 62] : List Instr) ++
  (List.range l.R).map (fun k => .eop (.bin .vpxorq (vreg k) (vreg k) (vreg k))) ++
  (List.range 4).flatMap (fun j =>
    ([.mov .rax (.reg .rdx), .alu .xor .rax (.imm (BitVec.ofNat 32 j)), .alu .cmp .rax (.imm 1),
      .alu .sbb .rax (.reg .rax), .eop (.vmovq (vreg l.R) .rax), .eop (.vpbroadcastq (vreg l.R) (vreg l.R))] :
        List Instr) ++
    (List.range l.R).flatMap fun k => [.evLoad (vreg (l.R + 1)) (at_ .rbx (oT l j + 32 * k)),
      .eop (.vpternlogq (vreg k) (vreg (l.R + 1)) (vreg l.R) 0xF8)]) ++
  (List.range l.R).map (fun k => .evStore (at_ .rbx (oS l + 32 * k)) (vreg k))

/-- After a window's multiplication by `T_d`: the flag `rbp := d ≠ 0 ? y ≡ ±1 : rbp`. -/
def afterMul : List Instr :=
  isPM1 l ++ [.mov .rax (.reg .r15), .shift .shr .rax 62, .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax),
    .alu .and .rbp (.reg .rax), .alu .xor .rax (.imm (BitVec.ofInt 32 (-1))), .alu .and .rdx (.reg .rax),
    .alu .or .rbp (.reg .rdx)]

/-- After a squaring of a window: `rbp |= y ≡ −1`. -/
def afterSq : List Instr := isM1 l ++ [.alu .or .rbp (.reg .rdx)]

/-- After squaring `j` of the last three (`r13 = 4 − j`): `rbp |= y ≡ −1`
under the mask of `σ > j` (from the word after `E`'s, as `Round.mrLast`). -/
def afterLast (j : Nat) : List Instr :=
  isM1 l ++ [.movImm64 .rax (sigK j), .alu .and .rax (.mem { base := .rdi, disp := ((arr l aE + 8 * l.W : Nat) : Int) }),
    .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax), .alu .xor .rax (.imm (BitVec.ofInt 32 (-1))),
    .alu .and .rdx (.reg .rax), .alu .or .rbp (.reg .rdx)]

/-- Whether the pass is the last one, three squarings after the windows:
ZF iff `kWords = 0`. -/
def isLast : List Instr := [.mov .rax (.mem (hdr kWords)), .alu .test .rax (.reg .rax)]

/-- A multiplication of a window (`r13` of them left): `S := T_d` and
`Y := Y S` for the last of a window's three, `Y := Y Y` otherwise; then the
flag. -/
def mult : Prog isa :=
  .seq (.seq (.block isLast) (.ite .e (.block (ops (oY l) (oY l) (oY l)))
      (.seq (.block [.alu .cmp .r13 (.imm 1)]) (.ite .e (.block (select l ++ ops (oY l) (oY l) (oS l)))
        (.block (ops (oY l) (oY l) (oY l)))))))
    (.seq (ammMul l)
      (.seq (.seq (.block isLast) (.ite .e
          (.seq (.block [.alu .cmp .r13 (.imm 3)]) (.ite .e (.block (afterLast l 1))
            (.seq (.block [.alu .cmp .r13 (.imm 2)]) (.ite .e (.block (afterLast l 2)) (.block (afterLast l 3))))))
          (.seq (.block [.alu .cmp .r13 (.imm 1)]) (.ite .e (.block (afterMul l)) (.block (afterSq l))))))
        (.block [.alu .sub .r13 (.imm 1)])))

/-- A window: three multiplications; then the next digit. -/
def window : Prog isa :=
  .seq (.block [.mov32 .r13 (.imm 3)])
    (.seq (.loop (mult l) .ne) (.block [.shift .shl .r15 2, .alu .sub .r14 (.imm 1)]))

/-- A pass over a word of `E`: with `kWords` words left, the next word into
`r15` and its 32 windows; with none left (`kWords = 0`), one pass of three
squarings (`isLast`). -/
def word : Prog isa :=
  .seq (.seq (.block isLast) (.ite .e (.block [.mov32 .r14 (.imm 1)])
      (.block [.mov .rax (.mem (hdr kWords)), .alu .sub .rax (.imm 1),
        .mov .r15 (.mem { base := .rdi, index := some .rax, scale := 8, disp := ((arr l aE : Nat) : Int) }),
        .mov32 .r14 (.imm 32)])))
    (.loop (window l) .ne)

/-- The windows: `y := T_0`, the flag clear, `kWords := w`; a pass of `word`
for each word and one more, each taking one off `kWords`, to `−1`. -/
def windows : List (Prog isa) :=
  [.block (copyN l (oY l) (oT l 0) ++
      ([.mov32 .rbp (.imm 0), .mov32 .rax (.imm (BitVec.ofNat 32 l.W)), .store (hdr kWords) .rax] : List Instr)),
    .loop (.seq (word l) (.block [.mov .rax (.mem (hdr kWords)), .alu .sub .rax (.imm 1),
      .store (hdr kWords) .rax, .alu .cmp .rax (.imm (BitVec.ofInt 32 (-1)))])) .ne]

/-- Intel's MXCSR prologue and epilogue around `c` (see "MCDT" in
`TCB/X86_64/Isa.lean`), the slots at `oMx`: `PubIfma.withMx`'s. -/
def withMx (c : Prog isa) : Prog isa :=
  .seq (.block [.stmxcsr (at_ .rbx (oMx l)), .mov32 .r11 (.mem (at_ .rbx (oMx l))), .alu32 .and .r11 (.imm 0xFFFF),
      .store32 (at_ .rbx (oMx l)) .r11])
    (.seq (.seq (.block [.mov32 .rax (.imm 0x1FBF), .store32 (at_ .rbx (oMx l + 4)) .rax,
        .ldmxcsr (at_ .rbx (oMx l + 4)), .lfence]) (.seq c (.block [.lfence])))
      (.block [.ldmxcsr (at_ .rbx (oMx l)), .vop .vzeroupper]))

/-- The vector code: the table, then the windows. -/
def vec : Prog isa := withMx l (seqs (table l :: windows l))

/-- The passing flag into `rax`, and the callee-saved registers back from
the frame (`rbx` pushed first). -/
def finish : List Instr :=
  [.mov .rax (.reg .rbp), .alu .and .rax (.imm 1),
    .mov .r15 (.mem { base := .rsp, disp := 0 }), .mov .r14 (.mem { base := .rsp, disp := 8 }),
    .mov .r13 (.mem { base := .rsp, disp := 16 }), .mov .r12 (.mem { base := .rsp, disp := 24 }),
    .mov .rbp (.mem { base := .rsp, disp := 32 }), .mov .rbx (.mem { base := .rsp, disp := 40 })]

/-- The round of a layout, in a frame of the six callee-saved registers. -/
def ifma : Prog isa :=
  .frame (.push [.rbx, .rbp, .r12, .r13, .r14, .r15]) (seqs (setup l ++ [vec l, .block (finish)])) (.pop .r11 6)

end VG.Impl.MillerRabin.X86_64.Ifma

namespace VG.Impl.MillerRabin.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.PubIfma

/-- ZF: whether the candidate has `n` words (`rax` its words). -/
def isW (n : Nat) : List Instr := [.mov .rax (.mem (hdr sW)), .alu .cmp .rax (.imm (BitVec.ofNat 32 n))]

/-- The round of the layout of the candidate's size, `round mul` otherwise. -/
def code (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block (isW 32)) (.ite .e (ifma pay2048)
    (.seq (.block (isW 48)) (.ite .e (ifma pay3072)
      (.seq (.block (isW 64)) (.ite .e (ifma pay4096) (round mul))))))

end VG.Impl.MillerRabin.X86_64.Ifma
