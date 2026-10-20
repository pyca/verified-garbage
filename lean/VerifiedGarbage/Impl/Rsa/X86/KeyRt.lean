module

public import VerifiedGarbage.Impl.Rsa.X86.Inverse
public import VerifiedGarbage.Impl.Bignum.X86.CrtRt

/-! # The RSA key workspace at a width read at run time (i686)

`KeyWs`'s arrays without a copy of the code per width: array `j` is at
`edi + hdr + j (B + 8)`, `B = 8 ⌈len / 8⌉` the bytes of a number of `w = B / 4`
words, with `len` the modulus's length, an argument (`Lay.len`). Every
operation computes its arrays' addresses from it and runs one of `CrtRt`'s
loops, which count a register down by four bytes: `chainLoop` for sums and
differences (and, on one array, for a shift up by a bit), `selectLoop` for
copies and masked selections, `zeroLoop`, and `shiftDownLoop` for halving.
The loops move `edi`, which is set back from the working space's argument
(`Lay.ws`) after them. A bit an operation leaves for a later one is in `ebx`,
as in `KeyWs`, or, across a loop, in a header word.
-/

@[expose] public section
namespace VG.Impl.Rsa.X86.KeyRt
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Rsa.X86.Keys

/-- Where an operation finds the modulus's length and the working space: arguments, with no
words pushed. -/
structure Lay where
  len : Nat
  ws : Nat

/-- Argument `i`. -/
def argOp (i : Nat) : MemOp := at_ .esp (4 + 4 * i)

/-- The header word holding the bit a division's shift carries out. -/
def sCy : Nat := 136

/-- The header word holding a division step's quotient bit. -/
def sQb : Nat := 140

variable (L : Lay)

/-- `r = B = 8 ⌈len / 8⌉`, the bytes of a number: `PublicRt.widthB`, its argument at `L.len`
(`argAt (L.len - 1) 1`, for `1 ≤ L.len`). -/
def bytesB (r : Reg) : List Instr := PublicRt.widthB (L.len - 1) r

/-- `r = edi + hdr + j (B + 8)`, array `j`, and `t = B + 8`. -/
def arrPtr (r : Reg) (j : Nat) (t : Reg) : List Instr :=
  bytesB L t ++ [.alu .add t (.imm 8), .mov r (.reg .edi), .alu .add r (.imm (BitVec.ofNat 32 hdr))] ++
    List.replicate j (.alu .add r (.reg t))

/-- `r = B`, or `B + 4` with the extra word. -/
def count (r : Reg) (extra : Bool) : List Instr :=
  bytesB L r ++ (if extra then [.alu .add r (.imm 4)] else [])

/-- `edi` back at the working space. -/
def restoreEdi : List Instr := [.mov .edi (.mem (argOp L.ws))]

/-! ## Loops -/

/-- `[ebp]` halved, a word at a time from the bottom, each taking the low bit of the
word above it: `edx` bytes. -/
def shiftDownLoop : Prog isa :=
  .loop (.block [.mov .eax (.mem (at_ .ebp 4)), .alu .and .eax (.imm 1), .shift .ror .eax 1,
    .mov .ecx (.mem (at_ .ebp 0)), .shift .shr .ecx 1, .alu .add .ecx (.reg .eax),
    .store (at_ .ebp 0) .ecx, .alu .add .ebp (.imm 4), .alu .sub .edx (.imm 4)]) .ne

/-- `[edi] = [ebx]` where the mask `ecx` is all ones, else `[ebp]`; `edx` bytes. -/
def select3Loop : Prog isa :=
  .loop (.block [.mov .eax (.mem (at_ .ebp 0)), .alu .xor .eax (.mem (at_ .ebx 0)), .alu .and .eax (.reg .ecx),
    .alu .xor .eax (.mem (at_ .ebp 0)), .store (at_ .edi 0) .eax, .alu .add .ebp (.imm 4),
    .alu .add .ebx (.imm 4), .alu .add .edi (.imm 4), .alu .sub .edx (.imm 4)]) .ne

/-! ## Operations -/

/-- `[o] = [a] op [b]` (`adc` or `sbb`), `w` words or `w + 1` with `extra`, the carry (or
borrow) as a mask in `ecx`. -/
def chain (op : AluOp) (o a b : Nat) (extra : Bool) : Prog isa :=
  .seq (.block (arrPtr L .ebp a .edx ++ arrPtr L .ebx b .edx ++ arrPtr L .edi o .edx ++ count L .edx extra ++
      [.mov .ecx (.imm 0)]))
    (.seq (CrtRt.chainLoop op) (.block (restoreEdi L)))

/-- `[o] = [a] - [b]`, `w` words, and `ebx` the borrow. -/
def sub3 (o a b : Nat) : Prog isa :=
  .seq (chain L .sbb o a b false) (.block [.mov .ebx (.reg .ecx), .alu .and .ebx (.imm 1)])

/-- `[o] = [a]` where the mask `ecx` is all ones, else kept; `w` words, or `w + 1` with `extra`. -/
def selectIn (o a : Nat) (extra : Bool) : Prog isa :=
  .seq (.block (arrPtr L .ebp a .edx ++ arrPtr L .ebx o .edx ++ count L .edi extra))
    (.seq CrtRt.selectLoop (.block (restoreEdi L)))

/-- `[o] = [a]`, `w` words. -/
def copy (o a : Nat) : Prog isa :=
  .seq (.block [.mov .ecx (.imm (-1))]) (selectIn L o a false)

/-- `[o] = [b]` where the mask `ecx` is all ones, else `[a]`, `w` words. -/
def select3 (o a b : Nat) : Prog isa :=
  .seq (.block (arrPtr L .ebp a .edx ++ arrPtr L .ebx b .edx ++ arrPtr L .edi o .edx ++ count L .edx false))
    (.seq select3Loop (.block (restoreEdi L)))

/-- `[o] = [b]` if the header word `sl` is one, else `[a]`, for `sl` zero or one. -/
def sel (o a b sl : Nat) : Prog isa :=
  if o = b then
    .seq (.block [.mov .ecx (.mem (sc sl)), .alu .sub .ecx (.imm 1)]) (selectIn L o a false)
  else if o = a then
    .seq (.block [.mov .ecx (.imm 0), .alu .sub .ecx (.mem (sc sl))]) (selectIn L o b false)
  else
    .seq (.block [.mov .ecx (.imm 0), .alu .sub .ecx (.mem (sc sl))]) (select3 L o a b)

/-- `[j]` halved with `ebx` as its word `w`'s, `w + 1` words. -/
def half (j : Nat) : Prog isa :=
  .seq (.block (arrPtr L .ebp j .edx ++ bytesB L .edx ++ [.alu .add .ebp (.reg .edx), .store (at_ .ebp 0) .ebx] ++
      arrPtr L .ebp j .edx ++ bytesB L .edx))
    (.seq shiftDownLoop
      (.block [.mov .eax (.mem (at_ .ebp 0)), .shift .shr .eax 1, .store (at_ .ebp 0) .eax]))

/-- The header word `sl` the low bit of `[j]`. -/
def bitOf (sl j : Nat) : List Instr :=
  arrPtr L .eax j .edx ++ [.mov .eax (.mem (at_ .eax 0)), .alu .and .eax (.imm 1), .store (sc sl) .eax]

/-- `[j]`'s low word one. -/
def setOne (j : Nat) : List Instr :=
  arrPtr L .eax j .edx ++ [.mov .ecx (.imm 1), .store (at_ .eax 0) .ecx]

/-- `[j]`'s low bit set. -/
def orOne (j : Nat) : List Instr :=
  arrPtr L .eax j .edx ++ [.mov .ecx (.mem (at_ .eax 0)), .alu .or .ecx (.imm 1), .store (at_ .eax 0) .ecx]

/-- `[j]`'s low bit cleared. -/
def clrLow (j : Nat) : List Instr :=
  arrPtr L .eax j .edx ++
    [.mov .ecx (.mem (at_ .eax 0)), .alu .or .ecx (.imm 1), .alu .xor .ecx (.imm 1), .store (at_ .eax 0) .ecx]

/-- The header word `d` one if `[a] = [b]`, else zero, through `[t]`. -/
def eqS (d a b t : Nat) : Prog isa :=
  .seq (sub3 L t a b) (.seq (.block [.store (sc sT) .ebx]) (.seq (sub3 L t b a)
    (.block [.alu .or .ebx (.mem (sc sT)), .alu .xor .ebx (.imm 1), .store (sc d) .ebx])))

/-- The first `n` arrays zeroed. -/
def zeroArrays (n : Nat) : Prog isa :=
  .seq (.block (arrPtr L .ebp 0 .edx ++ [.mov .ecx (.imm 0)] ++ List.replicate n (.alu .add .ecx (.reg .edx)) ++
      [.mov .eax (.imm 0)]))
    CrtRt.zeroLoop

/-- `[j]` zeroed, `w + 1` words. -/
def zeroWide (j : Nat) : Prog isa :=
  .seq (.block (arrPtr L .ebp j .edx ++ count L .ecx true ++ [.mov .eax (.imm 0)])) CrtRt.zeroLoop

/-- `[j]`'s low word plus the header word `sl`. -/
def addLow (j sl : Nat) : List Instr :=
  arrPtr L .eax j .edx ++ [.mov .ecx (.mem (at_ .eax 0)), .alu .add .ecx (.mem (sc sl)), .store (at_ .eax 0) .ecx]

/-- `esi = 32 w = 8 B`, the bits of a number. -/
def bits : List Instr := bytesB L .esi ++ [.alu .add .esi (.reg .esi), .alu .add .esi (.reg .esi), .alu .add .esi (.reg .esi)]

/-! ## Division

`Div.code`'s schedule: `32 w` steps, each shifting the quotient `q` (`w`
words) and the remainder `r` (`w + 1`) up by a bit, the quotient's top bit
into the remainder's bottom, then the remainder less the divisor `d` into
the temporary `t`, kept where it did not borrow, and that bit into the
quotient's bottom. -/

/-- One step of the division. -/
def divStep (q r d t : Nat) : Prog isa :=
  .seq (chain L .adc q q q false) <|
  .seq (.block [.mov .eax (.reg .ecx), .alu .and .eax (.imm 1), .store (sc sCy) .eax]) <|
  .seq (chain L .adc r r r true) <|
  .seq (.block (addLow L r sCy)) <|
  .seq (chain L .sbb t r d true) <|
  .seq (.block ([.mov .ebx (.reg .ecx), .alu .xor .ebx (.imm (-1)), .alu .and .ebx (.imm 1),
    .alu .xor .ecx (.imm (-1)), .store (sc sQb) .ebx])) <|
  .seq (selectIn L r t true) <|
  .block (addLow L q sQb ++ [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)])

/-- `[q] = [r₀] / [d]` and `[r] = [r₀] mod [d]` for the dividend `r₀` in `q`: `q`'s bits
shifted through `r`. -/
def div (q r d t : Nat) : Prog isa :=
  .seq (.seq (zeroWide L r) (.block (bits L))) (.loop (divStep L q r d t) .ne)

/-! ## The inverse

`Keys.inverse`'s schedule and arrays, every operation the run-time width's. -/

/-- `[o] := [a] - [b] mod m` for `[a], [b] < m`, through `aT1` and `aT4`. -/
def subModP (o a b : Nat) : List (Prog isa) :=
  [sub3 L aT1 a b, .block [.store (sc sB) .ebx], sel L aT4 aZero aNM sB, sub3 L o aT1 aT4]

/-- One step from the bank at `A` to the bank at `B`. -/
def invStep (A B : Nat) : Prog isa := seqs ([
  .block (bitOf L sOdd A),
  sub3 L aT1 A (A + 1),
  .block ([.store (sc sB) .ebx] ++ andS sC sOdd sB),
  sub3 L aT2 (A + 1) A,
  sel L (B + 1) (A + 1) A sC,
  sel L aT3 aT1 aT2 sC,
  sel L B A aT3 sOdd,
  .block [.mov .ebx (.imm 0)],
  half L B] ++
  subModP L aT3 (A + 2) (A + 3) ++ subModP L aT2 (A + 3) (A + 2) ++ [
  sel L (B + 3) (A + 3) (A + 2) sC,
  sel L aT1 aT3 aT2 sC,
  sel L aT3 (A + 2) aT1 sOdd,
  .block (bitOf L sB aT3),
  sel L aT4 aZero aNM sB,
  sub3 L (B + 2) aT3 aT4,
  .block [.alu .xor .ebx (.mem (sc sB))],
  half L (B + 2)])

/-- `32 w` iterations of two steps, counted down in `esi`. -/
def inverse : Prog isa :=
  .seq (.block (bits L))
    (.loop (.seq (invStep L 0 4) (.seq (invStep L 4 0) (.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)]))) .ne)

/-! ## Modular multiplication

`Keys.mulMod`'s schedule: per bit of the multiplier `[y]`, from the bottom,
the multiplicand `[x]` (or zero) added into `[a]` and `[x]` doubled, both
modulo `[m]`, then `[y]` halved; `esi` counts the steps. -/

/-- `[o] = [a] + [b] mod [m]` for `[a], [b] < m`, through `t`, `t + 1`, `t + 2`, with `[z]` zero. -/
def addMod (o a b m z t : Nat) : List (Prog isa) :=
  [sub3 L t z b, sub3 L (t + 1) a t, sub3 L (t + 2) (t + 1) m,
   .block [.store (sc sC) .ebx], sel L o (t + 2) (t + 1) sC]

/-- `[t]` the multiplicand where `[y]`'s low bit is set, else zero. -/
def mulHead (z y x t : Nat) : Prog isa :=
  .seq (.block (bitOf L sB y)) (sel L t z x sB)

/-- `[y]` halved, and the count. -/
def mulTail (y : Nat) : Prog isa :=
  seqs [.block [.mov .ebx (.imm 0)], half L y,
    .block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)]]

def mulModStep (z y x a m t : Nat) : Prog isa :=
  seqs [mulHead L z y x t, seqs (addMod L a a t m z (t + 1)),
    seqs (addMod L x x x m z (t + 1)), mulTail L y]

/-- `esi` steps of `mulModStep`. -/
def mulMod (z y x a m t : Nat) : Prog isa := .loop (mulModStep L z y x a m t) .ne

/-! ## Inputs -/

/-- Array `j` from the big-endian bytes at argument `arg`, as many as argument `arg + 1`, into its zeroed words. -/
def load (arg j : Nat) : Prog isa :=
  .seq (.block ([.mov .esi (.mem (VG.Impl.Bignum.X86.PublicFn.argument arg)),
      .mov .ecx (.mem (VG.Impl.Bignum.X86.PublicFn.argument (arg + 1)))] ++ arrPtr L .ebx j .edx ++
      [.alu .add .esi (.reg .ecx), .alu .sub .esi (.imm 1)]))
    VG.Impl.Bignum.X86.reverseBytes

end VG.Impl.Rsa.X86.KeyRt
