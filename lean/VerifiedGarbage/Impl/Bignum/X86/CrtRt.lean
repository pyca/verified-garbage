module

public import VerifiedGarbage.Impl.Rsa.X86.Chain
public import VerifiedGarbage.Impl.Mont.X86.Sse2
public import VerifiedGarbage.Impl.Bignum.X86.PublicRt
public import VerifiedGarbage.Impl.Bignum.X86.ModulusCheck
public import VerifiedGarbage.Impl.Mont.X86.RepeatSquares
public import VerifiedGarbage.Impl.Mont.X86.Window

/-! # Private CRT RSA at a width read at run time (i686 cdecl)

`vg_rsa_private_crt` without a copy per width. The modulus's length `n_len`
gives the width `B = 8 ⌈n_len / 8⌉` in bytes, and a factor that fits half of
it is raised in a context of `Bh = 8 ⌈B / 16⌉` bytes (`Ctx.half`), a longer
one in a context of `B` bytes (`Ctx.wide`). Every width and offset is
computed from the arguments on the stack, every loop runs over a count of
bytes through pointers into the working space (`edi`), and every Montgomery
multiplication calls `vg_rsa_mont_mul_at`.

The working space: a header of 256 bytes (the inverse `-M⁻¹ mod 2³²`, the
window, the acceptance mask, the saved registers and a multiplier word), the
product of two numbers (`prodOff`, `2 B + 4` bytes) and its multiplicand
(`mulAOff`, `B` bytes), each at a fixed offset, so that a row of the product
reads its multiplier at a fixed distance from the row; then the slots, of
`2 Bc + 32` bytes each in a context of `Bc` bytes, from `numBase`. A context
occupies slots 0 to 8 (the modulus, the callee's range, one, `R² mod M`, the
base, the result, a temporary and the exponent); the key's components are in
the wide slots 9 to 17, and the table of a windowed exponentiation's 16
entries in the wide slots from 20. The half context lies within the wide
context's slots.

Only the public lengths choose branches and loop counts. The acceptance of
the key and the input is a mask, applied to the result; a factor that is not
an odd number above one is replaced by three under a mask, so that every
multiplication's modulus is valid.
-/

@[expose] public section
namespace VG.Impl.Bignum.X86.CrtRt
open VG VG.X86 VG.Impl.Mont.X86
open VG.Impl.Bignum.X86.PublicRt (argAt widthB)

/-- A context's width: the modulus's (`wide`), or half of it (`half`). -/
inductive Ctx | wide | half
  deriving DecidableEq, Repr

/-- The header word holding `-M⁻¹ mod 2³²` of the current context. -/
def invOff : Nat := 0
/-- The header word holding the current window. -/
def winOff : Nat := 4
/-- The header word holding the acceptance mask. -/
def accOff : Nat := 8
/-- The header word holding a saved mask. -/
def maskOff : Nat := 12
def savedRegisters : List (Reg × Nat) := [(.ebx, 32), (.ebp, 36), (.esi, 40), (.edi, 44)]
/-- The header words holding the current factor's length, the other factor's, and
the count of factors left. -/
def lenOff : Nat := 16
def otherLenOff : Nat := 20
def leftOff : Nat := 24
/-- The header word holding a product row's multiplier. -/
def multOff : Nat := 48
/-- The product of two numbers: `2 B + 4` bytes. -/
def prodOff : Nat := 256
/-- The multiplicand of a product, `B` bytes, at a fixed distance from the product. -/
def mulAOff : Nat := 2312
/-- The first slot. -/
def numBase : Nat := 3336

/-- The arguments holding the working space and its length. -/
def wsArg : Nat := 16
def wsLenArg : Nat := 17

/-- `r = Bc`, the bytes of a number of the context, with `k` words pushed. -/
def widthC (k : Nat) : Ctx → Reg → List Instr
  | .wide, r => widthB k r
  | .half, r => widthB k r ++ [.shift .shr r 3, .alu .add r (.imm 1), .shift .shr r 1,
      .alu .add r (.reg r), .alu .add r (.reg r), .alu .add r (.reg r)]

/-- `t = 2 Bc + 32`, the stride of the context's slots. -/
def strideC (c : Ctx) (t : Reg) : List Instr :=
  widthC 0 c t ++ [.alu .add t (.reg t), .alu .add t (.imm 32)]

/-- A number: slot `j` of a context, or the bytes at a fixed offset. -/
inductive Loc | slot (c : Ctx) (j : Nat) | fixed (off : Nat)

def prod : Loc := .fixed prodOff
def mulA : Loc := .fixed mulAOff

/-- `r` points to the number; `t` changes. -/
def ptrTo : Loc → Reg → Reg → List Instr
  | .slot c j, r, t => strideC c t ++ [.mov r (.reg .edi), .alu .add r (.imm (BitVec.ofNat 32 numBase))] ++
      List.replicate j (.alu .add r (.reg t))
  | .fixed o, r, _ => [.mov r (.reg .edi), .alu .add r (.imm (BitVec.ofNat 32 o))]

/-- A count of bytes: `k Bc + e` for `k` one or two. -/
structure Cnt where
  c : Ctx
  two : Bool := false
  extra : Nat := 0

/-- `r` the count. -/
def cntTo (n : Cnt) (r : Reg) : List Instr :=
  widthC 0 n.c r ++ (if n.two then [.alu .add r (.reg r)] else []) ++
    (if n.extra = 0 then [] else [.alu .add r (.imm (BitVec.ofNat 32 n.extra))])

def one (c : Ctx) : Cnt := { c }
def two (c : Ctx) : Cnt := { c, two := true }

/-- `edi` back to the working space. -/
def restoreEdi : List Instr := [.mov .edi (.mem (argAt 0 wsArg))]

/-! ## Loops -/

/-- `[ebp]` zeroed, `ecx` bytes. -/
def zeroLoop : Prog isa :=
  .loop (.block [.store (at_ .ebp 0) .eax, .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 4)]) .ne

/-- `[ebx] = [ebp]` where the mask `ecx` is all ones, else kept; `edi` bytes. -/
def selectLoop : Prog isa :=
  .loop (.block [.mov .eax (.mem (at_ .ebx 0)), .mov .edx (.mem (at_ .ebp 0)),
    .alu .xor .edx (.reg .eax), .alu .and .edx (.reg .ecx), .alu .xor .eax (.reg .edx),
    .store (at_ .ebx 0) .eax, .alu .add .ebp (.imm 4), .alu .add .ebx (.imm 4),
    .alu .sub .edi (.imm 4)]) .ne

/-- `selectLoop` sixteen bytes at a time with SSE2: the mask `ecx` in every
doubleword of `xmm7`, `edi / 16` blocks counted in `eax`, then the last
`edi mod 16` bytes by `selectLoop`; at least sixteen bytes. -/
def selectLoopX : Prog isa :=
  .seq (.block [.mov .eax (.reg .edi), .shift .shr .eax 4, .xop (.movd .xmm7 .ecx),
    .xop (.pshufd .xmm7 .xmm7 0)]) <|
  .seq (.loop (.block [.movdquLoad .xmm0 (at_ .ebx 0), .movdquLoad .xmm1 (at_ .ebp 0),
    .xop (.bin .pxor .xmm1 .xmm0), .xop (.bin .pand .xmm1 .xmm7), .xop (.bin .pxor .xmm0 .xmm1),
    .movdquStore (at_ .ebx 0) .xmm0, .alu .add .ebp (.imm 16), .alu .add .ebx (.imm 16),
    .alu .sub .eax (.imm 1)]) .ne) <|
  .seq (.block [.alu .and .edi (.imm 15)]) (.ite .ne selectLoop (.block []))

/-- `[edi] = [ebp] op [ebx]` with the carry (or borrow) as a mask in `ecx`; `edx` bytes.
Reuse the key-workspace loop: eight words per iteration, then scalar tails. -/
def chainLoop (op : AluOp) : Prog isa := VG.Impl.Rsa.X86.Chain.loop op

/-- `ecx` all ones if `[esi]` is below `[ebp]`, `edx` bytes. -/
def compareLoop : Prog isa :=
  .loop (.block [.mov .eax (.mem (at_ .esi 0)), .alu .add .ecx (.reg .ecx),
    .alu .sbb .eax (.mem (at_ .ebp 0)), .alu .sbb .ecx (.reg .ecx), .alu .add .esi (.imm 4),
    .alu .add .ebp (.imm 4), .alu .sub .edx (.imm 4)]) .ne

/-- `[ebp]` shifted up by four bits, the carried bits in `ecx`; `edx` bytes. -/
def shiftLoop : Prog isa :=
  .loop (.block [.mov .eax (.mem (at_ .ebp 0)), .mov .ebx (.reg .eax), .shift .shr .ebx 28,
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .ecx), .store (at_ .ebp 0) .eax,
    .mov .ecx (.reg .ebx), .alu .add .ebp (.imm 4), .alu .sub .edx (.imm 4)]) .ne

/-- `[ebp] &= ecx`, `edx` bytes. -/
def maskLoop : Prog isa :=
  .loop (.block [.mov .eax (.mem (at_ .ebp 0)), .alu .and .eax (.reg .ecx), .store (at_ .ebp 0) .eax,
    .alu .add .ebp (.imm 4), .alu .sub .edx (.imm 4)]) .ne

/-- A product row: `[ebp] += [mo] [ecx]` with the carry word in `ebx`; `esi` bytes. -/
def rowLoopAt (mo : Nat) : Prog isa := .loop (.block (Rt.mulStepAt mo)) .ne

/-- `rowLoopAt` with the multiplier at `multOff`. -/
def rowLoop : Prog isa := rowLoopAt multOff

/-! ## Numbers -/

/-- The number zeroed. -/
def zero (x : Loc) (n : Cnt) : Prog isa :=
  .seq (.block (ptrTo x .ebp .edx ++ cntTo n .ecx ++ [.mov .eax (.imm 0)])) zeroLoop

/-- The number set to the small value `v`. -/
def setSmall (x : Loc) (n : Cnt) (v : Nat) : Prog isa :=
  .seq (zero x n) (.block (ptrTo x .eax .edx ++ [.mov .ecx (.imm (BitVec.ofNat 32 v)), .store (at_ .eax 0) .ecx]))

/-- `d` set to `x` where the mask `ecx` is all ones, else kept. -/
def select (x d : Loc) (n : Cnt) : Prog isa :=
  .seq (.block (ptrTo x .ebp .edx ++ ptrTo d .ebx .edx ++ cntTo n .edi)) (.seq selectLoop (.block restoreEdi))

/-- `select` with `selectLoopX`, for numbers of at least sixteen bytes. -/
def selectX (x d : Loc) (n : Cnt) : Prog isa :=
  .seq (.block (ptrTo x .ebp .edx ++ ptrTo d .ebx .edx ++ cntTo n .edi)) (.seq selectLoopX (.block restoreEdi))

/-- `d` set to `x`. -/
def copy (x d : Loc) (n : Cnt) : Prog isa :=
  .seq (.block [.mov .ecx (.imm (BitVec.allOnes 32))]) (select x d n)

/-- `o = a op b` with the carry (or borrow) as a mask in `ecx`, and `ebp` just past `a`. -/
def chain (op : AluOp) (o a b : Loc) (n : Cnt) : Prog isa :=
  .seq (.block (ptrTo a .ebp .edx ++ ptrTo b .ebx .edx ++ ptrTo o .eax .edx ++ cntTo n .edx ++
      [.mov .edi (.reg .eax), .mov .ecx (.imm 0)]))
    (.seq (chainLoop op) (.block restoreEdi))

/-- `ecx` all ones if `a` is below `b`, else zero. -/
def lessThan (a b : Loc) (n : Cnt) : Prog isa :=
  .seq (.block (ptrTo a .esi .edx ++ ptrTo b .ebp .edx ++ cntTo n .edx ++ [.mov .ecx (.imm 0)])) compareLoop

/-- `ecx` all ones if `a` equals `b`, else zero. -/
def equal (a b : Loc) (n : Cnt) : Prog isa :=
  .seq (lessThan a b n) <| .seq (.block [.mov .ebx (.reg .ecx)]) <| .seq (lessThan b a n)
    (.block [.alu .or .ecx (.reg .ebx), .alu .xor .ecx (.imm (BitVec.allOnes 32))])

/-- The number from the big-endian bytes at argument `p`, as many as argument `l`. -/
def load (x : Loc) (n : Cnt) (p l : Nat) : Prog isa :=
  .seq (zero x n) (.seq (.block (ptrTo x .ebx .edx ++ [.mov .esi (.mem (argAt 0 p)),
    .mov .ecx (.mem (argAt 0 l)), .alu .add .esi (.reg .ecx), .alu .sub .esi (.imm 1)])) reverseBytes)

/-- As `load`, with the bytes at the top of the number: the bytes' value times
`256^(cb − l)`, from the byte `cb − l` of the number on, for an exponent of
`l` public bytes whose windows `windowPowerWith` takes from the top. -/
def loadTop (x : Loc) (n : Cnt) (p l : Nat) : Prog isa :=
  .seq (zero x n) (.seq (.block (ptrTo x .ebx .edx ++ cntTo n .edx ++ [.alu .add .ebx (.reg .edx),
    .mov .ecx (.mem (argAt 0 l)), .alu .sub .ebx (.reg .ecx), .mov .esi (.mem (argAt 0 p)),
    .alu .add .esi (.reg .ecx), .alu .sub .esi (.imm 1)])) reverseBytes)

/-! ## Montgomery arithmetic -/

/-- `eax` the offset of the number, from `edx` the stride. -/
def offIn : Loc → List Instr
  | .slot _ j => .mov .eax (.imm (BitVec.ofNat 32 numBase)) :: List.replicate j (.alu .add .eax (.reg .edx))
  | .fixed o => [.mov .eax (.imm (BitVec.ofNat 32 o))]

/-- The arguments of `vg_rsa_mont_mul_at` in the context `c`, for the slots `o`,
`a` and `b`, stored into the frame at `esp`: `ws` (`edi`), `ws_len`, the
width, the modulus (slot 0), the inverse, the callee's range (slot 1), `o`,
`a` and `b`. Only `eax` and `edx` change. -/
def mulArgs (c : Ctx) (o a b : Nat) : List Instr :=
  widthC 9 c .edx ++
    [.mov .eax (.mem (argAt 9 wsLenArg)), .store (at_ .esp 4) .eax, .store (at_ .esp 0) .edi,
      .mov .eax (.reg .edx), .shift .shr .eax 3, .store (at_ .esp 8) .eax,
      .alu .add .edx (.reg .edx), .alu .add .edx (.imm 32),
      .mov .eax (.imm (BitVec.ofNat 32 numBase)), .store (at_ .esp 12) .eax,
      .mov .eax (.imm (BitVec.ofNat 32 invOff)), .store (at_ .esp 16) .eax] ++
    offIn (.slot c 1) ++ [.store (at_ .esp 20) .eax] ++ offIn (.slot c o) ++ [.store (at_ .esp 24) .eax] ++
    offIn (.slot c a) ++ [.store (at_ .esp 28) .eax] ++ offIn (.slot c b) ++ [.store (at_ .esp 32) .eax]

/-- `[o] = [a] [b] R⁻¹ mod M` for the slots `o`, `a` and `b` of the context
`c`, by a call of `vg_rsa_mont_mul_at` in a frame of 36 bytes, which keeps
`ebx`, `esi`, `ebp` and `edi`. -/
def mul (c : Ctx) (o a b : Nat) : Prog isa :=
  .frame (.alloc 36) (.seq (.block (mulArgs c o a b)) (.call "vg_rsa_mont_mul_at" Sse2.atBody)) (.free 36)

/-- `T = 2 T mod M` for `T` in slot 4: the sum into slot 1 with its carry in the
word after it, the sum minus `M` into slot 4, and the sum back where it is
below `M`; `esi` down one. -/
def doubleStep (c : Ctx) : Prog isa :=
  .seq (chain .adc (.slot c 1) (.slot c 4) (.slot c 4) (one c)) <|
  .seq (.block (ptrTo (.slot c 1) .eax .edx ++ cntTo (one c) .edx ++
    [.alu .add .eax (.reg .edx), .mov .edx (.imm 0), .alu .sub .edx (.reg .ecx), .store (at_ .eax 0) .edx])) <|
  .seq (chain .sbb (.slot c 4) (.slot c 1) (.slot c 0) (one c)) <|
  .seq (.block [.mov .eax (.mem (at_ .ebp 0)), .alu .add .ecx (.reg .ecx), .alu .sbb .eax (.imm 0),
    .alu .sbb .eax (.reg .eax), .mov .ecx (.reg .eax)]) <|
  .seq (selectX (.slot c 1) (.slot c 4) (one c)) (.block [.alu .sub .esi (.imm 1)])

/-- `2^(8 Bc + Bc / 8) mod M` in slot 4: one, doubled `8 Bc + Bc / 8` times. -/
def powerTwo (c : Ctx) : Prog isa :=
  .seq (setSmall (.slot c 4) (one c) 1) <|
  .seq (.block (widthC 0 c .esi ++ [.mov .eax (.reg .esi), .shift .shr .eax 3, .alu .add .esi (.reg .esi),
    .alu .add .esi (.reg .esi), .alu .add .esi (.reg .esi), .alu .add .esi (.reg .eax)])) (.loop (doubleStep c) .ne)

/-- The context's modulus (slot 0) replaced by three unless it is an odd
number above one; one in slot 3, `-M⁻¹ mod 2³²`, and `2^(8 Bc + Bc / 8) mod M`
in slot 4. -/
def prepBase (c : Ctx) : Prog isa :=
  .seq (setSmall (.slot c 3) (one c) 1) <|
  .seq (setSmall (.slot c 7) (one c) 3) <|
  .seq (lessThan (.slot c 3) (.slot c 0) (one c)) <|
  .seq (.block [.mov .edx (.mem (sc numBase)), .alu .and .edx (.imm 1), .mov .eax (.imm 0),
    .alu .sub .eax (.reg .edx), .alu .and .ecx (.reg .eax), .alu .xor .ecx (.imm (BitVec.allOnes 32))]) <|
  .seq (select (.slot c 7) (.slot c 0) (one c)) <|
  .seq (.block (VG.Impl.Mont.X86.Dynamic.setupInverse numBase invOff)) (powerTwo c)

/-- The context set up: `prepBase`, and six Montgomery squares of slot 4 by
the shared squaring loop, each taking `2^(8 Bc + d) mod M` to
`2^(16 Bc + 2 d) R⁻¹ = 2^(8 Bc + 2 d) mod M`: `2^(8 Bc + 64 (Bc / 8)) =
2^(16 Bc) = R² mod M`, with half the doublings of computing it by doubling
alone. -/
def prepare (c : Ctx) : Prog isa := .seq (prepBase c) (VG.Impl.Mont.X86.Dynamic.repeatSquaresWith (mul c 4 4 4) 6)

/-- `[o] = [a] - [b] mod M` for `a` and `b` below `M`, through slot 1. -/
def subMod (c : Ctx) (o a b : Nat) : Prog isa :=
  .seq (chain .sbb (.slot c o) (.slot c a) (.slot c b) (one c)) <|
  .seq (.block [.store (sc maskOff) .ecx]) <|
  .seq (chain .adc (.slot c 1) (.slot c o) (.slot c 0) (one c)) <|
  .seq (.block [.mov .ecx (.mem (sc maskOff))]) (select (.slot c 1) (.slot c o) (one c))

/-! ## Windowed exponentiation -/

/-- `r` points to entry `j` of the table (the wide slot 20 on, `Bc` bytes each); `t` changes. -/
def entryPtr (c : Ctx) (r : Reg) (j : Nat) (t : Reg) : List Instr :=
  ptrTo (.slot .wide 20) r t ++ widthC 0 c t ++ List.replicate j (.alu .add r (.reg t))

/-- The next entry: slot 7 times the base (slot 5), into slot 7 and the entry at
`esi`, `esi` past it; ZF at the table's end. -/
def tableStep (c : Ctx) : Prog isa :=
  .seq (mul c 7 7 5) <|
  .seq (.block ([.mov .ecx (.imm (BitVec.allOnes 32))] ++ ptrTo (.slot c 7) .ebp .edx ++
    [.mov .ebx (.reg .esi)] ++ cntTo (one c) .edi)) <|
  .seq (.seq selectLoop (.block restoreEdi))
    (.block ([.mov .esi (.reg .ebx)] ++ entryPtr c .edx 16 .eax ++ [.alu .cmp .esi (.reg .edx)]))

/-- The table: one (slot 6) and the base (slot 5) in Montgomery form, and their products. -/
def buildTable (c : Ctx) : Prog isa :=
  .seq (.block ([.mov .ecx (.imm (BitVec.allOnes 32))] ++ ptrTo (.slot c 6) .ebp .edx ++ entryPtr c .ebx 0 .edx ++
    cntTo (one c) .edi)) <|
  .seq (.seq selectLoop (.block restoreEdi)) <|
  .seq (.block ([.mov .ecx (.imm (BitVec.allOnes 32))] ++ ptrTo (.slot c 5) .ebp .edx ++ entryPtr c .ebx 1 .edx ++
    cntTo (one c) .edi)) <|
  .seq (.seq selectLoop (.block restoreEdi)) <|
  .seq (copy (.slot c 5) (.slot c 7) (one c)) <|
  .seq (.block (entryPtr c .esi 2 .edx)) (.loop (tableStep c) .ne)

/-- The window: the top four bits of the exponent (slot 8), and the exponent
shifted up past them. -/
def nextWindow (c : Ctx) : Prog isa :=
  .seq (.block (ptrTo (.slot c 8) .eax .edx ++ widthC 0 c .edx ++
      [.alu .add .eax (.reg .edx), .alu .sub .eax (.imm 4), .mov .eax (.mem (at_ .eax 0)),
        .shift .shr .eax 28, .store (sc winOff) .eax]))
    (.seq (.block (ptrTo (.slot c 8) .ebp .edx ++ cntTo (one c) .edx ++ [.mov .ecx (.imm 0)])) shiftLoop)

/-- The table's entry at `ebp` into slot 7 when the window word, sixteen
above the window and down one per entry, is sixteen; the word down one, `ebp`
past the entry, and ZF at the table's end. -/
def selectStep (c : Ctx) : Prog isa :=
  .seq (.block (VG.Impl.Mont.X86.Dynamic.windowMask 16 ++
      [.mov .eax (.mem (sc winOff)), .alu .sub .eax (.imm 1), .store (sc winOff) .eax] ++
      ptrTo (.slot c 7) .ebx .edx ++ cntTo (one c) .edi)) <|
  .seq (.seq selectLoopX (.block restoreEdi)) (.block (entryPtr c .edx 16 .eax ++ [.alu .cmp .ebp (.reg .edx)]))

/-- The window's entry into slot 7, by a scan of the whole table under masks:
the window word raised by sixteen, then counted down to the window. -/
def selectWindow (c : Ctx) : Prog isa :=
  .seq (.block ([.mov .eax (.mem (sc winOff)), .alu .add .eax (.imm 16), .store (sc winOff) .eax] ++
    entryPtr c .ebp 0 .edx)) (.loop (selectStep c) .ne)

def square (c : Ctx) : Prog isa := mul c 6 6 6

/-- A window: four squares, the window's entry, its product; `esi` down one. -/
def windowStep (c : Ctx) : Prog isa :=
  .seq (square c) <| .seq (square c) <| .seq (square c) <| .seq (square c) <|
  .seq (nextWindow c) <| .seq (selectWindow c) <|
  .seq (mul c 6 6 7) (.block [.alu .sub .esi (.imm 1)])

/-- The base (slot 5) to the exponent (slot 8, `Bc` bytes) modulo `M` into
slot 6, with `R² mod M` in slot 4 and one in slot 3, over the windows
`count` sets in `esi`, from the top of slot 8. -/
def windowPowerWith (c : Ctx) (count : List Instr) : Prog isa :=
  .seq (mul c 6 4 3) <|
  .seq (mul c 5 5 4) <|
  .seq (buildTable c) <|
  .seq (.block count) <|
  .seq (.loop (windowStep c) .ne) (mul c 6 6 3)

/-- `windowPowerWith` over every window of the exponent, `2 Bc`. -/
def windowPower (c : Ctx) : Prog isa := windowPowerWith c (widthC 0 c .esi ++ [.alu .add .esi (.reg .esi)])

/-- The windows of an exponent of the public length in argument `l`, which
`loadTop` loaded at the top of slot 8: `2 l`. -/
def lenCount (l : Nat) : List Instr := [.mov .esi (.mem (argAt 0 l)), .alu .add .esi (.reg .esi)]

/-! ## The private-key operation -/

/-- The modulus (2 B bytes), the input and the key's components. -/
def importComponents : Prog isa :=
  .seq (load (.slot .wide 9) (two .wide) 2 3) <|
  .seq (load (.slot .wide 15) (one .wide) 4 5) <|
  .seq (load (.slot .wide 10) (one .wide) 6 7) <|
  .seq (load (.slot .wide 11) (one .wide) 8 9) <|
  .seq (load (.slot .wide 12) (one .wide) 10 11) <|
  .seq (load (.slot .wide 13) (one .wide) 12 13) (load (.slot .wide 14) (one .wide) 14 15)

/-- The product of `mulA` and `b` (`B` bytes each) into `prod`. -/
def wideProduct (b : Loc) : Prog isa :=
  .seq (zero prod { c := .wide, two := true, extra := 4 }) <|
  .seq (.block (ptrTo prod .ebp .edx))
    (.loop (.seq (.block ([.mov .eax (.mem (at_ .ebp (mulAOff - prodOff))), .store (sc multOff) .eax] ++
        ptrTo b .ecx .edx ++ widthC 0 .wide .esi ++ [.mov .ebx (.imm 0)])) <|
      .seq rowLoop
        (.block ([.store (at_ .ebp 0) .ebx] ++ widthC 0 .wide .eax ++
          [.alu .sub .ebp (.reg .eax), .alu .add .ebp (.imm 4), .alu .add .eax (.reg .edi),
            .alu .add .eax (.imm (BitVec.ofNat 32 prodOff)), .alu .cmp .ebp (.reg .eax)]))) .ne)

/-- `ecx` and-ed into the acceptance mask. -/
def accept : List Instr :=
  [.mov .eax (.mem (sc accOff)), .alu .and .eax (.reg .ecx), .store (sc accOff) .eax]

/-- The acceptance: `p q = n`, the input below `n`, and `qInv` below `p`. -/
def validate : Prog isa :=
  .seq (copy (.slot .wide 10) mulA (one .wide)) <|
  .seq (wideProduct (.slot .wide 11)) <|
  .seq (equal prod (.slot .wide 9) (two .wide)) <|
  .seq (.block [.store (sc accOff) .ecx]) <|
  .seq (lessThan (.slot .wide 15) (.slot .wide 9) (one .wide)) <|
  .seq (.block accept) <|
  .seq (lessThan (.slot .wide 14) (.slot .wide 10) (one .wide)) (.block accept)

/-- The result (slot 6 of the context `c`) into the wide slot `o`, zero-extended to `2 B` bytes. -/
def saveResult (c : Ctx) (o : Nat) : Prog isa :=
  .seq (zero (.slot .wide o) (two .wide)) (copy (.slot c 6) (.slot .wide o) (one c))

/-- The input modulo the factor in slot `f`, the exponent in slot `e`, into
slot `o`, at half the width: the input reduced modulo the factor at the
modulus's width, then raised at half the width. -/
def narrowPower (f e o : Nat) : Prog isa :=
  .seq (copy (.slot .wide f) (.slot .wide 0) (one .wide)) <|
  .seq (copy (.slot .wide 15) (.slot .wide 5) (one .wide)) <|
  .seq (prepare .wide) <|
  .seq (mul .wide 5 5 4) <|
  .seq (mul .wide 5 5 3) <|
  .seq (copy (.slot .wide 5) (.slot .wide o) (one .wide)) <|
  .seq (copy (.slot .wide f) (.slot .half 0) (one .half)) <|
  .seq (copy (.slot .wide o) (.slot .half 5) (one .half)) <|
  .seq (copy (.slot .wide e) (.slot .half 8) (one .half)) <|
  .seq (prepare .half) <|
  .seq (windowPower .half) (saveResult .half o)

/-- The same at the modulus's width. -/
def widePower (f e o : Nat) : Prog isa :=
  .seq (copy (.slot .wide f) (.slot .wide 0) (one .wide)) <|
  .seq (copy (.slot .wide 15) (.slot .wide 5) (one .wide)) <|
  .seq (copy (.slot .wide e) (.slot .wide 8) (one .wide)) <|
  .seq (prepare .wide) <|
  .seq (windowPower .wide) (saveResult .wide o)

/-- The factor's power, at half the width if its length (the header word at `lenOff`) fits it. -/
def power (f e o : Nat) : Prog isa :=
  .seq (.block ([.mov .eax (.mem (sc lenOff))] ++ widthC 0 .half .edx ++
    [.alu .add .edx (.imm 1), .alu .cmp .eax (.reg .edx)]))
    (.ite .b (narrowPower f e o) (widePower f e o))

/-- `h = (m_p - m_q) qInv mod p` into slot 7, in the context of `p`. -/
def coefficient : Prog isa :=
  .seq (copy (.slot .wide 10) (.slot .wide 0) (one .wide)) <|
  .seq (prepare .wide) <|
  .seq (copy (.slot .wide 16) (.slot .wide 6) (one .wide)) <|
  .seq (copy (.slot .wide 17) (.slot .wide 5) (one .wide)) <|
  .seq (copy (.slot .wide 14) (.slot .wide 8) (one .wide)) <|
  .seq (mul .wide 5 5 4) <|
  .seq (mul .wide 5 5 3) <|
  .seq (subMod .wide 7 6 5) <|
  .seq (mul .wide 8 8 4) (mul .wide 7 7 8)

/-- `m = m_q + q h` into the wide slot 19. -/
def recombine : Prog isa :=
  .seq (copy (.slot .wide 11) mulA (one .wide)) <|
  .seq (wideProduct (.slot .wide 7)) (chain .adc (.slot .wide 19) prod (.slot .wide 17) (two .wide))

/-- The result cleared unless accepted, its `n_len` bytes to `out`, and `eax` the acceptance. -/
def exportResult : Prog isa :=
  .seq (.block (ptrTo (.slot .wide 19) .ebp .edx ++ cntTo (one .wide) .edx ++ [.mov .ecx (.mem (sc accOff))])) <|
  .seq maskLoop <|
  .seq (.block (PublicFn.outputArgs ++ ptrTo (.slot .wide 19) .esi .edx ++ [.alu .add .esi (.reg .ecx), .alu .sub .esi (.imm 1)]))
    (.seq reverseBytes (.block [.mov .eax (.mem (sc accOff)), .alu .and .eax (.imm 1)]))

/-- The wide slots `a` and `b` exchanged through the wide slot 18. -/
def swap (a b : Nat) (n : Cnt) : Prog isa :=
  .seq (copy (.slot .wide a) (.slot .wide 18) n) <|
  .seq (copy (.slot .wide b) (.slot .wide a) n) (copy (.slot .wide 18) (.slot .wide b) n)

/-- The factors' lengths (arguments 7 and 9) into the header, and two factors left. -/
def factorsInit : List Instr :=
  [.mov .eax (.mem (argAt 0 7)), .store (sc lenOff) .eax, .mov .eax (.mem (argAt 0 9)),
    .store (sc otherLenOff) .eax, .mov .eax (.imm 2), .store (sc leftOff) .eax]

/-- The lengths exchanged, and one factor fewer left: ZF after the last. -/
def factorNext : List Instr :=
  [.mov .eax (.mem (sc lenOff)), .mov .ecx (.mem (sc otherLenOff)), .store (sc lenOff) .ecx,
    .store (sc otherLenOff) .eax, .mov .eax (.mem (sc leftOff)), .alu .sub .eax (.imm 1), .store (sc leftOff) .eax]

/-- The power of the factor in the wide slot 10 into 16, then the factors (10
and 11), their exponents (12 and 13), their powers (16 and 17) and their lengths
exchanged: after two steps, `m_p` in 16 and `m_q` in 17, the rest as it was. -/
def factorStep : Prog isa :=
  .seq (power 10 12 16) <|
  .seq (swap 10 11 (one .wide)) <|
  .seq (swap 12 13 (one .wide)) <|
  .seq (swap 16 17 (two .wide)) (.block factorNext)

def sized : Prog isa :=
  .seq importComponents <|
  .seq validate <|
  .seq (.block factorsInit) <|
  .seq (.loop factorStep .ne) <|
  .seq coefficient <|
  .seq recombine exportResult

def save : List Instr := savedRegisters.map fun (r, d) => .store (at_ .eax d) r
def restore : List Instr := savedRegisters.map fun (r, d) => .mov r (.mem (sc d))

def entry : List Instr := [.mov .eax (.mem (argAt 0 wsArg))] ++ save ++ [.mov .edi (.reg .eax)]

def body : Prog isa :=
  .seq (.block PublicFn.modulusArgs) (.seq (.block modulusCheck) (.ite .e sized PublicFn.failure))

def code : Prog isa := .seq (.block entry) (.seq body (.block restore))

end VG.Impl.Bignum.X86.CrtRt
