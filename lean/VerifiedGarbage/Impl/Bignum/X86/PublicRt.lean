module

public import VerifiedGarbage.Impl.Bignum.X86.PublicFn
public import VerifiedGarbage.Impl.Mont.X86.Sse2
public import VerifiedGarbage.Impl.Bignum.X86.SparseExponent

/-! # Checked public RSA at a width read at run time (i686 cdecl)

`vg_rsa_public_checked` without a copy per width: the modulus's length
`n_len` gives the width `B = 8 ⌈n_len / 8⌉` in bytes of every number, and
every loop runs over `B` bytes through pointers into the working space
(`edi`), counting a register down. The numbers are at `256 + j B` for
`j < 6`: the modulus `M` (0), the input and then the base (1), the result
(2), one (3), `R² mod M` and then the products (4), and from `256 + 5 B`
the range of `vg_rsa_mont_mul_at`, which every multiplication calls. Before
the first call, that range holds each doubling's sum, whose difference with `M` replaces the
number doubled unless the sum is below `M`.

The checks of the modulus and the exponent, the import and export of the
numbers and the exponent's schedule are `PublicFn`'s. Only the public
modulus, exponent and lengths choose branches; the input's acceptance is a
mask, applied to the result.
-/

@[expose] public section
namespace VG.Impl.Bignum.X86.PublicRt
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86.PublicFn

/-- Argument `i`, with `k` words pushed since the entry. -/
def argAt (k i : Nat) : MemOp := at_ .esp (4 + 4 * i + 4 * k)

/-- The header word holding `-M⁻¹ mod 2³²`. -/
def invOff : Nat := 152

/-- The first number's offset in the working space. -/
def numOff : Nat := 256

/-- `r = B`, the bytes of a number, from `n_len`, with `k` words pushed. -/
def widthB (k : Nat) (r : Reg) : List Instr :=
  [.mov r (.mem (argAt k 1)), .alu .add r (.imm 7), .shift .shr r 3, .alu .add r (.reg r),
    .alu .add r (.reg r), .alu .add r (.reg r)]

/-- `r = 256 + j B`, the offset of number `j`, and `t = B`. -/
def offAt (r : Reg) (j : Nat) (t : Reg) : List Instr :=
  widthB 0 t ++ .mov r (.imm (BitVec.ofNat 32 numOff)) :: List.replicate j (.alu .add r (.reg t))

/-- `r = edi + 256 + j B`, a pointer to number `j`, and `t = B`. -/
def slotPtr (r : Reg) (j : Nat) (t : Reg) : List Instr :=
  widthB 0 t ++ [.mov r (.reg .edi), .alu .add r (.imm (BitVec.ofNat 32 numOff))] ++
    List.replicate j (.alu .add r (.reg t))

/-- Number `j` zeroed. -/
def zero (j : Nat) : Prog isa :=
  .seq (.block (slotPtr .ebp j .ecx ++ [.mov .eax (.imm 0)]))
    (.loop (.block [.store (at_ .ebp 0) .eax, .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 4)]) .ne)

/-- Number `j` from the big-endian bytes at argument `p`, as many as argument `l`. -/
def load (j p l : Nat) : Prog isa :=
  .seq (zero j) (.seq (.block (slotPtr .ebx j .ecx ++ [.mov .esi (.mem (argAt 0 p)),
    .mov .ecx (.mem (argAt 0 l)), .alu .add .esi (.reg .ecx), .alu .sub .esi (.imm 1)])) reverseBytes)

/-- Number `j` set to one. -/
def setOne (j : Nat) : Prog isa :=
  .seq (zero j) (.block (slotPtr .eax j .ecx ++ [.mov .ecx (.imm 1), .store (at_ .eax 0) .ecx]))

/-- `ecx` all ones if number `a` is below number `b`, else zero: the borrow
of their difference, which is not stored. -/
def compareAt (a b : Nat) : Prog isa :=
  .seq (.block (slotPtr .esi a .edx ++ slotPtr .ebp b .edx ++ [.mov .ecx (.imm 0)]))
    (.loop (.block [.mov .eax (.mem (at_ .esi 0)), .alu .add .ecx (.reg .ecx),
      .alu .sbb .eax (.mem (at_ .ebp 0)), .alu .sbb .ecx (.reg .ecx), .alu .add .esi (.imm 4),
      .alu .add .ebp (.imm 4), .alu .sub .edx (.imm 4)]) .ne)

/-- `ecx` all ones if the input is below `M`, else zero. -/
def compare : Prog isa := compareAt 1 0

/-- The sum `2 T` (number 4) at `256 + 5 B`, and its carry in the word after it. -/
def double : Prog isa :=
  .seq (.block (slotPtr .ebp 5 .edx ++ slotPtr .ebx 4 .edx ++ [.mov .ecx (.imm 0)]))
    (.seq (.loop (.block [.mov .eax (.mem (at_ .ebx 0)), .alu .add .ecx (.reg .ecx),
      .alu .adc .eax (.reg .eax), .store (at_ .ebp 0) .eax, .alu .sbb .ecx (.reg .ecx),
      .alu .add .ebx (.imm 4), .alu .add .ebp (.imm 4), .alu .sub .edx (.imm 4)]) .ne)
      (.block [.mov .eax (.imm 0), .alu .sub .eax (.reg .ecx), .store (at_ .ebp 0) .eax]))

/-- Number 4 set to the sum minus `M`, and `ecx` all ones if the sum with its
carry is below `M`; `edi` points into number 4, and is set back from argument
`ws`. -/
def reduce (ws : Nat := 8) : Prog isa :=
  .seq (.block (slotPtr .eax 4 .edx ++ slotPtr .ebp 5 .edx ++ slotPtr .ebx 0 .edx ++
      [.mov .edi (.reg .eax), .mov .ecx (.imm 0)]))
    (.seq (.loop (.block [.mov .eax (.mem (at_ .ebp 0)), .alu .add .ecx (.reg .ecx),
      .alu .sbb .eax (.mem (at_ .ebx 0)), .store (at_ .edi 0) .eax, .alu .sbb .ecx (.reg .ecx),
      .alu .add .ebp (.imm 4), .alu .add .ebx (.imm 4), .alu .add .edi (.imm 4),
      .alu .sub .edx (.imm 4)]) .ne)
      (.block [.mov .eax (.mem (at_ .ebp 0)), .alu .add .ecx (.reg .ecx), .alu .sbb .eax (.imm 0),
        .alu .sbb .eax (.reg .eax), .mov .ecx (.reg .eax), .mov .edi (.mem (argAt 0 ws))]))

/-- Number `d` set to number `x` where the mask `ecx` is all ones, else kept;
`edi` counts, and is set back. -/
def select (x d : Nat) (ws : Nat := 8) : Prog isa :=
  .seq (.block (slotPtr .ebp x .edx ++ slotPtr .ebx d .edx ++ [.mov .edi (.reg .edx)]))
    (.seq (.loop (.block [.mov .eax (.mem (at_ .ebx 0)), .mov .edx (.mem (at_ .ebp 0)),
      .alu .xor .edx (.reg .eax), .alu .and .edx (.reg .ecx), .alu .xor .eax (.reg .edx),
      .store (at_ .ebx 0) .eax, .alu .add .ebp (.imm 4), .alu .add .ebx (.imm 4),
      .alu .sub .edi (.imm 4)]) .ne)
      (.block [.mov .edi (.mem (argAt 0 ws))]))

/-- `T = 2 T mod M`, `esi` down one; `edi` set back from argument `ws`. -/
def doubleStep (ws : Nat := 8) : Prog isa :=
  .seq double (.seq (reduce ws) (.seq (select 5 4 ws) (.block [.alu .sub .esi (.imm 1)])))

/-- `R² mod M` in number 4: one, doubled `16 B` (`128 W`) times. -/
def powerTwo : Prog isa :=
  .seq (setOne 4) (.seq (.block (widthB 0 .esi ++ List.replicate 4 (.alu .add .esi (.reg .esi))))
    (.loop doubleStep .ne))

/-- `eax = 256 + j B`, the offset of number `j`, from `edx = B`. -/
def offEax (j : Nat) : List Instr :=
  .mov .eax (.imm (BitVec.ofNat 32 numOff)) :: List.replicate j (.alu .add .eax (.reg .edx))

/-- The arguments of `vg_rsa_mont_mul_at` for the numbers `o`, `a` and `b`, stored
into the frame at `esp`: `ws` (`edi`), `ws_len`, the width, `m`, `inv`, `s`,
`o`, `a` and `b`, `ws_len` from argument `wl`. Only `eax` and `edx` change. -/
def mulArgs (o a b : Nat) (wl : Nat := 9) : List Instr :=
  widthB 9 .edx ++
    [.mov .eax (.mem (argAt 9 wl)), .store (at_ .esp 4) .eax, .store (at_ .esp 0) .edi,
      .mov .eax (.reg .edx), .shift .shr .eax 3, .store (at_ .esp 8) .eax,
      .mov .eax (.imm (BitVec.ofNat 32 numOff)), .store (at_ .esp 12) .eax,
      .mov .eax (.imm (BitVec.ofNat 32 invOff)), .store (at_ .esp 16) .eax] ++
    offEax 5 ++ [.store (at_ .esp 20) .eax] ++ offEax o ++ [.store (at_ .esp 24) .eax] ++
    offEax a ++ [.store (at_ .esp 28) .eax] ++ offEax b ++ [.store (at_ .esp 32) .eax]

/-- `[o] = [a] [b] R⁻¹ mod M` for the numbers `o`, `a` and `b`, by a call of
`vg_rsa_mont_mul_at` with its arguments in a frame of 36 bytes, which keeps
`ebx`, `esi`, `ebp` and `edi`. -/
def mul (o a b : Nat) (wl : Nat := 9) : Prog isa :=
  .frame (.alloc 36) (.seq (.block (mulArgs o a b wl)) (.call "vg_rsa_mont_mul_at" Sse2.atBody)) (.free 36)

/-- A round of the exponent's public schedule: the result times the base
where its low bit is set, the exponent shifted, and the base squared only
when another bit remains. The final square would never be consumed. -/
def sparseRound : Prog isa :=
  .seq (.seq (.block PublicContext.bitTest) (.ite .e (.block []) (mul 2 2 1))) <|
  .seq (.block (VG.Impl.Mont.X86.Dynamic.shiftExponent 2 PublicContext.exponentOffset ++ PublicContext.exponentLeft)) <|
  .ite .e (.block []) (.seq (mul 1 1 1) (.block PublicContext.exponentLeft))

/-- Copy the converted input into the accumulator, word by word. -/
def seedCopy : Prog isa :=
  .seq (.block (slotPtr .esi 1 .ecx ++ slotPtr .ebp 2 .ecx))
    (.loop (.block [.mov .eax (.mem (at_ .esi 0)), .store (at_ .ebp 0) .eax,
      .alu .add .esi (.imm 4), .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 4)]) .ne)

/-- Consume an odd exponent's low bit, without borrowing into its high word. -/
def seedConsume : List Instr :=
  [.mov .eax (.mem (sc 128)), .alu .sub .eax (.imm 1), .store (sc 128) .eax]

/-- An odd public exponent starts at the converted input and consumes its
low bit. The even case retains Montgomery one. -/
def seed : Prog isa :=
  .seq (.block PublicContext.bitTest)
    (.ite .e (mul 2 4 3) (.seq seedCopy (.block seedConsume)))

/-- The result `X^e mod M`: convert the input, seed the accumulator, process
the remaining exponent bits, and leave Montgomery form. -/
def exponentiate : Prog isa :=
  .seq (mul 1 1 4) <|
  .seq seed <|
  .seq (.loop sparseRound .ne) (mul 2 2 3)

/-- The result cleared where the input was not accepted (the mask at 144). -/
def maskOut : Prog isa :=
  .seq (.block (slotPtr .ebp 2 .edx ++ [.mov .ecx (.mem (sc acceptanceOffset))]))
    (.loop (.block [.mov .eax (.mem (at_ .ebp 0)), .alu .and .eax (.reg .ecx), .store (at_ .ebp 0) .eax,
      .alu .add .ebp (.imm 4), .alu .sub .edx (.imm 4)]) .ne)

/-- The result's `n_len` bytes to `out`, big-endian, and `eax` the acceptance. -/
def write : Prog isa :=
  .seq (.block (outputArgs ++ slotPtr .esi 2 .edx ++ [.alu .add .esi (.reg .ecx), .alu .sub .esi (.imm 1)]))
    (.seq reverseBytes (.block [.mov .eax (.mem (sc acceptanceOffset)), .alu .and .eax (.imm 1)]))

/-- The numbers read, the input's acceptance, `-M⁻¹ mod 2³²`, one and `R² mod M`. -/
def prepare : Prog isa :=
  .seq (load 0 2 3) <|
  .seq (load 1 6 7) <|
  .seq compare <|
  .seq (.block ([.store (sc acceptanceOffset) .ecx] ++
    VG.Impl.Mont.X86.Dynamic.setupInverse numOff invOff)) <|
  .seq (setOne 3) powerTwo

def sized : Prog isa := .seq prepare (.seq exponentiate (.seq maskOut write))

def valid : Prog isa := .seq (.block saveExponent) sized

def checkExponent : Prog isa :=
  .seq scanExponent (.seq (.block [.alu .cmp .eax (.imm 0)]) (.ite .e failure valid))

def body : Prog isa :=
  .seq (.block modulusArgs) (.seq (.block modulusCheck) (.ite .e checkExponent failure))

def code : Prog isa := .seq (.block entry) (.seq body (.block restore))

end VG.Impl.Bignum.X86.PublicRt
