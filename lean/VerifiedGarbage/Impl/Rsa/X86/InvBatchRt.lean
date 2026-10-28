module

public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
public import VerifiedGarbage.Impl.Rsa.X86.KeyRt

/-! # The batched RSA CRT inversion at a width read at run time (i686)

`InvBatch.body w n`'s computation without a copy per width: the same arrays
(`InvBatch.offset w j`, `KeyRt`'s), steps and order, with every operation on
the arrays a loop whose pointers and count come from the modulus's length
(`Lay.len`), `w` its 32-bit words and `n = w / 2` the primes'. The 30
low-word divsteps and the matrix they build run in a window of eight header
words at `win` instead of array 3, so that their code and the coefficients'
addresses are those of `InvBatch` at a fixed offset; the reduction keeps its
sign word in the header word `signSlot` across its product row.

Each loop counts a register down by bytes. `edi`, which some loops move, is
set back from the working space's argument (`Lay.ws`) after them.
-/

@[expose] public section
namespace VG.Impl.Rsa.X86.InvBatchRt
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass.X86.Inv
open VG.Impl.Rsa.X86.KeyRt
open VG.Impl.Rsa.X86.Keys (seqs)

/-- The divstep window: delta, low `f` and `g`, the matrix `u v q r`, and `-p⁻¹ mod 2³²`. -/
def win : Nat := 16

/-- The reduction's sign word, kept across its product row. -/
def signSlot : Nat := 48

/-- The arrays whose addresses `init` keeps in the header, from `slotBase` on, and the header word
holding `4 n`, the bytes of `n` words. -/
def cached : List Nat := [0, 1, 2, 4, 5, 6, 7, 11, 12, 13, 14]
def slotBase : Nat := 52
def halfSlot : Nat := 96

/-- The header word holding array `j`'s address, if it is cached. -/
def slot (j : Nat) : Option Nat := (cached.idxOf? j).map fun i => slotBase + 4 * i

/-- An address in the arrays: `offset w arr + 4 n · half + byte`. -/
structure Ref where
  arr : Nat
  half : Nat := 0
  byte : Nat := 0
  deriving DecidableEq

variable (L : Lay)

/-- `r` at a `Ref`, through `t`: the array's address from its header word if it is cached, else
`KeyRt.arrPtr`; then `4 n` bytes `half` times, then `byte`. -/
def ptr (r : Reg) (x : Ref) (t : Reg) : List Instr :=
  (match slot x.arr with
    | some d => [.mov r (.mem (sc d))]
    | none => arrPtr L r x.arr t) ++
    List.replicate x.half (.alu .add r (.mem (sc halfSlot))) ++
    (if x.byte = 0 then [] else [.alu .add r (.imm (BitVec.ofNat 32 x.byte))])

/-- `r = 4 (n + e)`, the bytes of `n + e` words. -/
def nBytes (r : Reg) (e : Nat) : List Instr :=
  .mov r (.mem (sc halfSlot)) :: (if e = 0 then [] else [.alu .add r (.imm (BitVec.ofNat 32 (4 * e)))])

/-- `r = 4 (n - 1)`. -/
def nBytesLess (r : Reg) : List Instr := [.mov r (.mem (sc halfSlot)), .alu .sub r (.imm 4)]

/-- `r = 4 w`, the bytes of `w` words. -/
def wBytes (r : Reg) : List Instr := [.mov r (.mem (sc halfSlot)), .alu .add r (.reg r)]

/-- The cached arrays' addresses and `4 n` into the header. -/
def slots : List Instr :=
  cached.flatMap (fun j => arrPtr L .eax j .edx ++ [.store (sc (slotBase + 4 * cached.idxOf j)) .eax]) ++
  bytesB L .eax ++ [.shift .shr .eax 1, .store (sc halfSlot) .eax]

/-! ## Array operations -/

/-- `[o] = [a]` where the mask `ecx` is all ones, else kept: `cnt` bytes (`cnt` writing `edi`). -/
def selIn (o a : Ref) (cnt : List Instr) : Prog isa :=
  .seq (.block (ptr L .ebp a .edx ++ ptr L .ebx o .edx ++ cnt)) (.seq selectLoopX (.block (restoreEdi L)))

/-- `[o] = [a]`, `cnt` bytes. -/
def copy (o a : Ref) (cnt : List Instr) : Prog isa :=
  .seq (.block [.mov .ecx (.imm (-1))]) (selIn L o a cnt)

/-- `[o]` zeroed, `cnt` bytes (`cnt` writing `ecx`). -/
def zeros (o : Ref) (cnt : List Instr) : Prog isa :=
  .seq (.block (ptr L .ebp o .edx ++ cnt ++ [.mov .eax (.imm 0)])) VG.Impl.Bignum.X86.CrtRt.zeroLoop

/-- `[o] = [a] op [b]` (`adc` or `sbb`) from no carry, `cnt` bytes (`cnt` writing `edx`), the carry
out as a mask in `ecx`. -/
def chain (op : AluOp) (o a b : Ref) (cnt : List Instr) : Prog isa :=
  .seq (.block (ptr L .ebp a .edx ++ ptr L .ebx b .edx ++ cnt ++ ptr L .edi o .eax ++ [.mov .ecx (.imm 0)]))
    (.seq (VG.Impl.Rsa.X86.Chain.loop op) (.block (restoreEdi L)))

/-- `ecx` all ones exactly when the word at `x` is negative as a signed word. -/
def maskAt (x : Ref) : List Instr :=
  ptr L .ebx x .edx ++ [.mov .eax (.mem (at_ .ebx 0)), .shift .shr .eax 31, .mov .ecx (.imm 0),
    .alu .sub .ecx (.reg .eax)]

/-- `[ebp + d] += ecx · [edi + d] + ebx`, the carry word into `ebx`: `Mont.mulStep`'s step through
pointers. -/
def macWord (d : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .edi d)), .mul .ecx, .alu .add .eax (.reg .ebx), .alu .adc .edx (.imm 0),
   .alu .add .eax (.mem (at_ .ebp d)), .alu .adc .edx (.imm 0), .store (at_ .ebp d) .eax, .mov .ebx (.reg .edx)]

/-- `[ebp + d] = ecx · [edi + d] + ebx`, the carry word into `ebx`: the first row of a product, which
the accumulator's clearing would otherwise precede. -/
def macSet (d : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .edi d)), .mul .ecx, .alu .add .eax (.reg .ebx), .alu .adc .edx (.imm 0),
   .store (at_ .ebp d) .eax, .mov .ebx (.reg .edx)]

/-- `edi` and `ebp` up `k` bytes, `esi` down. -/
def advance (k : Nat) : List Instr :=
  [.alu .add .edi (.imm (BitVec.ofNat 32 k)), .alu .add .ebp (.imm (BitVec.ofNat 32 k)),
   .alu .sub .esi (.imm (BitVec.ofNat 32 k))]

/-- `[acc] = ecx · [src]` (with `set`) or `[acc] += ecx · [src]`, `cnt` bytes (`cnt` writing `esi`),
and the carry into the two words after (written, or added): `InvMemory.rowAdd`'s `mulRow` with the
multiplier in `ecx`, four words at a time, then one at a time. -/
def mulRow (set : Bool) (acc src : Ref) (cnt : List Instr) : Prog isa :=
  let mac := if set then macSet else macWord
  .seq (.block (ptr L .ebp acc .edx ++ cnt ++ ptr L .edi src .edx ++ [.mov .ebx (.imm 0)])) <|
  .seq (.loop (.seq (.block [.alu .cmp .esi (.imm 16)])
    (.seq (.ite .ae (.block (mac 0 ++ mac 4 ++ mac 8 ++ mac 12 ++ advance 16)) (.block (mac 0 ++ advance 4)))
      (.block [.alu .cmp .esi (.imm 0)]))) .ne)
  (.block ((if set then [.store (at_ .ebp 0) .ebx, .mov .eax (.imm 0), .store (at_ .ebp 4) .eax]
    else [.mov .eax (.mem (at_ .ebp 0)), .alu .add .eax (.reg .ebx), .store (at_ .ebp 0) .eax,
      .mov .eax (.mem (at_ .ebp 4)), .alu .adc .eax (.imm 0), .store (at_ .ebp 4) .eax]) ++ restoreEdi L))

/-- `[acc] (+)= [sc coefficient] · [src]`, `cnt` bytes. -/
def rowAdd (set : Bool) (coefficient : Nat) (acc src : Ref) (cnt : List Instr) : Prog isa :=
  .seq (.block [.mov .ecx (.mem (sc coefficient))]) (mulRow L set acc src cnt)

/-- `[acc] = [u] [a] + [v] [b]` as unsigned products, `cnt` bytes of each input. -/
def linearUnsigned (u v : Nat) (acc a b : Ref) (cnt : List Instr) : Prog isa :=
  .seq (rowAdd L true u acc a cnt) (rowAdd L false v acc b cnt)

/-- `[ebx] = [ebp]` and the mask `ecx`, `edi` bytes: sixteen at a time with SSE2, then a word at a
time (`KeyRt.selectLoopX`'s shape). -/
def maskLoopX : Prog isa :=
  .seq (.block [.mov .eax (.reg .edi), .shift .shr .eax 4, .xop (.movd .xmm7 .ecx),
    .xop (.pshufd .xmm7 .xmm7 0)]) <|
  .seq (.ite .ne (.loop (.block [.movdquLoad .xmm0 (at_ .ebp 0), .xop (.bin .pand .xmm0 .xmm7),
    .movdquStore (at_ .ebx 0) .xmm0, .alu .add .ebp (.imm 16), .alu .add .ebx (.imm 16),
    .alu .sub .eax (.imm 1)]) .ne) (.block [])) <|
  .seq (.block [.alu .and .edi (.imm 15)])
    (.ite .ne (.loop (.block [.mov .eax (.mem (at_ .ebp 0)), .alu .and .eax (.reg .ecx), .store (at_ .ebx 0) .eax,
      .alu .add .ebp (.imm 4), .alu .add .ebx (.imm 4), .alu .sub .edi (.imm 4)]) .ne) (.block []))

/-- `[o] = [a]` and the mask `ecx`, `cnt` bytes (`cnt` writing `edi`). -/
def maskIn (o a : Ref) (cnt : List Instr) : Prog isa :=
  .seq (.block (ptr L .ebp a .edx ++ ptr L .ebx o .edx ++ cnt)) (.seq maskLoopX (.block (restoreEdi L)))

/-- The correction of an unsigned product for a negative coefficient at the header word `c`:
`[acc + 4] -= [src]`, `n` words, if it is negative, through `[tmp]`. -/
def correction (c : Nat) (acc src tmp : Ref) : Prog isa :=
  .seq (.block (maskOf c)) (.seq (maskIn L tmp src (nBytes .edi 0))
    (chain L .sbb { acc with byte := acc.byte + 4 } { acc with byte := acc.byte + 4 } tmp (nBytes .edx 0)))

/-- `InvMemory.linear`'s signed combination, for inputs of `n + e` words, retained modulo `n + 1`
words. -/
def linear (u v : Nat) (acc a b tmp : Ref) (e : Nat) : Prog isa :=
  .seq (linearUnsigned L u v acc a b (nBytes .esi e))
    (.seq (correction L u acc a tmp) (correction L v acc b tmp))

/-- `[edi + d] = ([ebp + d] >> 30) + ([ebp + d + 4] << 2)`: `InvMemory.shrStep` through pointers. -/
def shrWord (d : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .ebp d)), .mov .ebx (.mem (at_ .ebp (d + 4))), .shift .shr .eax 30,
   .alu .add .ebx (.reg .ebx), .alu .add .ebx (.reg .ebx), .alu .add .eax (.reg .ebx), .store (at_ .edi d) .eax]

/-- `[dst] = [src] >> 30`, signed, `n + 1` words for an even `n`. -/
def shr30 (dst src : Ref) : Prog isa :=
  .seq (.block (ptr L .ebp src .edx ++ nBytes .esi 0 ++ ptr L .edi dst .edx)) <|
  .seq (.loop (.block (shrWord 0 ++ shrWord 4 ++ [.alu .add .ebp (.imm 8), .alu .add .edi (.imm 8),
      .alu .sub .esi (.imm 8)])) .ne)
  (.block ([.mov .eax (.mem (at_ .ebp 0)), .shift .shr .eax 31, .mov .ecx (.imm 0), .alu .sub .ecx (.reg .eax),
      .mov .eax (.mem (at_ .ebp 0)), .mov .ebx (.reg .ecx), .shift .shr .eax 30, .alu .add .ebx (.reg .ebx),
      .alu .add .ebx (.reg .ebx), .alu .add .eax (.reg .ebx), .store (at_ .edi 0) .eax] ++ restoreEdi L))

/-- `[x] = 0`, one word. -/
def zeroWord (x : Ref) : List Instr := ptr L .ebx x .edx ++ [.mov .eax (.imm 0), .store (at_ .ebx 0) .eax]

/-! ## The reduction, `InvBatch.reduce` -/

/-- The modulus `[2]`, the temporary `[12]`. -/
def mo : Ref := { arr := 2 }
def tmp : Ref := { arr := 12 }

/-- `InvBatch.redSum`: the sign mask of `[acc + 4 n]` into `esi`, `[acc + 4 (n + 1)]` zeroed, the
digit `q = [acc] · iv` into `ecx`, `[acc] += q [mo]`, and the sign word added at the top. -/
def redSum (acc : Ref) : Prog isa :=
  .seq (.block (maskAt L { acc with half := 1 } ++ [.mov .esi (.reg .ecx)] ++
      zeroWord L { acc with half := 1, byte := 4 } ++
      ptr L .ebx acc .edx ++ [.mov .eax (.mem (at_ .ebx 0)), .mov .ecx (.mem (sc (win + 28))), .mul .ecx,
        .mov .ecx (.reg .eax), .store (sc signSlot) .esi])) <|
  .seq (mulRow L false acc mo (nBytes .esi 0))
  (.block (ptr L .ebx { acc with half := 1, byte := 4 } .edx ++
    [.mov .eax (.mem (at_ .ebx 0)), .alu .add .eax (.mem (sc signSlot)), .store (at_ .ebx 0) .eax]))

/-- `InvMemory.addIfNeg`: `[acc] += [mo]`, `n + 1` words, if `[acc + 4 n]` is negative. -/
def addIfNeg (acc : Ref) : Prog isa :=
  .seq (.block (maskAt L { acc with half := 1 })) <|
  .seq (maskIn L tmp mo (nBytes .edi 0)) <|
  .seq (.block (zeroWord L { tmp with half := 1 }))
  (chain L .adc acc acc tmp (nBytes .edx 1))

/-- `Mont.csub` of `[src]` (`n` words and a top word 0 or 1) by `[mo]` into `[o]`: the difference
into `[tmp]`, then selected where it did not borrow. -/
def csub (src o : Ref) : Prog isa :=
  .seq (chain L .sbb tmp src mo (nBytes .edx 0)) <|
  .seq (.block (ptr L .ebx { src with half := 1 } .edx ++
    [.mov .eax (.mem (at_ .ebx 0)), .alu .add .ecx (.reg .ecx), .alu .sbb .eax (.imm 0), .alu .sbb .eax (.reg .eax),
      .alu .xor .eax (.imm (-1)), .mov .ecx (.reg .eax)])) <|
  if o = src then selIn L o tmp (nBytes .edi 0)
  else .seq (.block (ptr L .ebp src .edx ++ ptr L .ebx tmp .edx ++ nBytes .edx 0 ++ ptr L .edi o .eax))
    (.seq select3LoopX (.block (restoreEdi L)))

def reduce (out : Ref) : Prog isa :=
  .seq (redSum L { arr := 11 }) (.seq (addIfNeg L { arr := 11, byte := 4 }) (csub L { arr := 11, byte := 4 } out))

/-! ## The batch -/

def a (j : Nat) : Ref := { arr := j }

/-- `InvBatch.virtualize` of `[2]`: one more than `2` if it is 1. -/
def virtualize : Prog isa :=
  .seq (.block (ptr L .ebp (a 2) .edx ++ [.mov .eax (.mem (at_ .ebp 0)), .alu .xor .eax (.imm 1),
    .mov .ebx (.reg .ebp), .alu .add .ebx (.imm 4)] ++ nBytesLess .esi)) <|
  .seq (.loop (.block [.alu .or .eax (.mem (at_ .ebx 0)), .alu .add .ebx (.imm 4), .alu .sub .esi (.imm 4)]) .ne)
  (.block [.alu .sub .eax (.imm 1), .alu .sbb .eax (.reg .eax), .alu .and .eax (.imm 2),
    .mov .ecx (.mem (at_ .ebp 0)), .alu .or .ecx (.reg .eax), .store (at_ .ebp 0) .ecx])

/-- `[100] = 3 (n + 1)`, the batches; `esi = 6 (n + 1)`, the doublings (which keep `esi`), likewise
from `4 (n + 1)`. -/
def batches : List Instr :=
  nBytes .eax 1 ++ [.shift .shr .eax 2, .mov .ecx (.reg .eax), .alu .add .eax (.reg .ecx),
    .alu .add .eax (.reg .ecx), .store (sc 100) .eax]
def doublings : List Instr :=
  nBytes .esi 1 ++ [.shift .shr .esi 1, .mov .eax (.reg .esi), .alu .add .esi (.reg .eax),
    .alu .add .esi (.reg .eax)]

def init : Prog isa := seqs [
  .block (slots L), copy L (a 2) (a 8) (nBytes .edi 0), virtualize L,
  copy L (a 4) (a 2) (nBytes .edi 0), .block (zeroWord L { arr := 4, half := 1 }),
  copy L (a 5) (a 0) (nBytes .edi 0), .block (zeroWord L { arr := 5, half := 1 }),
  zeros L (a 12) (nBytes .ecx 1),
  .block (GcdBatch.evenMask (InvBatch.offset 0 0)), selIn L (a 12) (a 2) (nBytes .edi 0),
  chain L .adc (a 5) (a 5) (a 12) (nBytes .edx 1),
  .block [.mov .eax (.imm 1), .store (sc win) .eax],
  zeros L (a 6) (nBytes .ecx 1), zeros L (a 7) (nBytes .ecx 1),
  .block (ptr L .eax (a 7) .edx ++ [.mov .ecx (.imm 1), .store (at_ .eax 0) .ecx]),
  .block (ptr L .eax (a 2) .edx ++ [.mov .ebx (.mem (at_ .eax 0))] ++ Dynamic.inverse ++ [.store (sc (win + 28)) .eax]),
  .block batches]

def start : List Instr :=
  ptr L .ebx (a 4) .edx ++ [.mov .eax (.mem (at_ .ebx 0)), .store (sc (win + 4)) .eax] ++
  ptr L .ebx (a 5) .edx ++ [.mov .eax (.mem (at_ .ebx 0)), .store (sc (win + 8)) .eax] ++
  setConst 2 (win + 12) (1 + 2 ^ 96)

def update : Prog isa := seqs [
  linear L (win + 12) (win + 16) (a 11) (a 4) (a 5) (a 12) 1, shr30 L (a 0) (a 11),
  linear L (win + 20) (win + 24) (a 11) (a 4) (a 5) (a 12) 1, shr30 L (a 1) (a 11),
  linear L (win + 12) (win + 16) (a 11) (a 6) (a 7) (a 12) 0, reduce L (a 13),
  linear L (win + 20) (win + 24) (a 11) (a 6) (a 7) (a 12) 0, reduce L (a 14),
  copy L (a 4) (a 0) (nBytes .edi 1), copy L (a 5) (a 1) (nBytes .edi 1),
  copy L (a 6) (a 13) (nBytes .edi 0), copy L (a 7) (a 14) (nBytes .edi 0)]

def normalize : Prog isa := seqs [
  copy L (a 12) (a 2) (nBytes .edi 0), chain L .sbb (a 12) (a 12) (a 6) (nBytes .edx 0),
  .block (maskAt L { arr := 4, half := 1 }), selIn L (a 6) (a 12) (nBytes .edi 0),
  csub L (a 6) (a 6)]

def twice : Prog isa := seqs [
  chain L .adc (a 6) (a 6) (a 6) (nBytes .edx 1), csub L (a 6) (a 6),
  .block (zeroWord L { arr := 6, half := 1 })]

def finish : Prog isa := seqs [
  zeros L (a 1) (wBytes .ecx), chain L .sbb (a 1) (a 1) (a 4) (nBytes .edx 0),
  .block (maskAt L { arr := 4, half := 1 } ++ [.alu .xor .ecx (.imm (-1))]),
  selIn L (a 1) (a 4) (nBytes .edi 0),
  zeros L (a 3) (wBytes .ecx), copy L (a 3) (a 6) (nBytes .edi 0)]

def body : Prog isa := seqs [
  init L,
  .loop (seqs [.block (start L), wordSteps win 30, update L,
    .block [.mov .esi (.mem (sc 100)), decCounter, .store (sc 100) .esi, testCounter]]) .ne,
  normalize L,
  .block doublings,
  .loop (.seq (twice L) (.block [decCounter, testCounter])) .ne,
  finish L]

end VG.Impl.Rsa.X86.InvBatchRt
