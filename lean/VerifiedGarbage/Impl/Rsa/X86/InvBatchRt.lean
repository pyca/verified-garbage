module

public import VerifiedGarbage.Impl.Rsa.X86.GcdBatch
public import VerifiedGarbage.Impl.Rsa.X86.KeyRt
public import VerifiedGarbage.Impl.Mont.X86.Inverse

/-! # The batched RSA CRT inversion at a width read at run time (i686)

The inverse of the CRT's coefficient by batches of 30 divsteps on `w`-word numbers (`Divstep.W32`),
in `KeyRt`'s arrays (`offset w j`), with every operation on them a loop whose pointers and count come
from the modulus's length (`Lay.len`), `w` its 32-bit words and `n = w / 2` the primes'. The 30
low-word divsteps and the matrix they build run in a window of eight header words at `win`; each
batch then updates `f, g` and `d, e` in one pass each over interleaved arrays (`body`, "The fused
batches" below); `linear` and `shr30` are `GcdBatchRt`'s.

Each loop counts a register down by bytes. `edi`, which some loops move, is set back from the
working space's argument (`Lay.ws`) after them.
-/

@[expose] public section
namespace VG.Impl.Rsa.X86.InvBatchRt
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass.X86.Inv
open VG.Impl.Rsa.X86.KeyRt
open VG.Impl.Rsa.X86.Keys (seqs)

/-- Array `j`'s offset in the working space, for `w`-word numbers. -/
def offset (w j : Nat) : Nat := 160 + j * (4 * w + 8)

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
`KeyRt.arrPtr`; then `4 n` bytes `half` times (read into `t` first: an addition from memory would make
`r` secret to the constant-time analysis), then `byte`. -/
def ptr (r : Reg) (x : Ref) (t : Reg) : List Instr :=
  (match slot x.arr with
    | some d => [.mov r (.mem (sc d))]
    | none => arrPtr L r x.arr t) ++
    (if x.half = 0 then [] else .mov t (.mem (sc halfSlot)) :: List.replicate x.half (.alu .add r (.reg t))) ++
    (if x.byte = 0 then [] else [.alu .add r (.imm (BitVec.ofNat 32 x.byte))])

/-- `r = 4 (n + e)`, the bytes of `n + e` words; the addition, even of 0, makes the flags (on which
the loops that take the count branch) a function of `r` alone. -/
def nBytes (r : Reg) (e : Nat) : List Instr :=
  [.mov r (.mem (sc halfSlot)), .alu .add r (.imm (BitVec.ofNat 32 (4 * e)))]

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

/-- `ecx` all ones exactly when the word at `ebx` is negative as a signed word. -/
def signOf : List Instr :=
  [.mov .eax (.mem (at_ .ebx 0)), .shift .shr .eax 31, .mov .ecx (.imm 0), .alu .sub .ecx (.reg .eax)]

/-- `ecx` all ones exactly when the word at `x` is negative as a signed word. -/
def maskAt (x : Ref) : List Instr := ptr L .ebx x .edx ++ signOf


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

/-- The correction of an unsigned product for a negative coefficient at the header word `c`:
`[acc + 4] -= [src]`, `n` words, if it is negative: the difference into `[tmp]`, then selected
into place by the coefficient's sign. -/
def correction (c : Nat) (acc src tmp : Ref) : Prog isa :=
  .seq (chain L .sbb tmp { acc with byte := acc.byte + 4 } src (nBytes .edx 0))
    (.seq (.block (maskOf c)) (selIn L { acc with byte := acc.byte + 4 } tmp (nBytes .edi 0)))

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

/-! ## The reduction -/

/-- The modulus `[2]`, the temporary `[12]`. -/
def mo : Ref := { arr := 2 }
def tmp : Ref := { arr := 12 }

/-- `redSum`'s start: the sign mask of `[acc + 4 n]` into the header word `signSlot`,
`[acc + 4 (n + 1)]` zeroed, and the digit `q = [acc] · iv` into `ecx`. -/
def redHead (acc : Ref) : List Instr :=
  maskAt L { acc with half := 1 } ++ [.mov .esi (.reg .ecx)] ++ zeroWord L { acc with half := 1, byte := 4 } ++
    ptr L .ebx acc .edx ++ [.mov .eax (.mem (at_ .ebx 0)), .mov .ecx (.mem (sc (win + 28))), .mul .ecx,
      .mov .ecx (.reg .eax), .store (sc signSlot) .esi]

/-- `redSum`'s end: the sign word added at `[acc + 4 (n + 1)]`. -/
def redTail (acc : Ref) : List Instr :=
  ptr L .ebx { acc with half := 1, byte := 4 } .edx ++
    [.mov .eax (.mem (at_ .ebx 0)), .alu .add .eax (.mem (sc signSlot)), .store (at_ .ebx 0) .eax]

/-- `redSum`: the sign mask of `[acc + 4 n]` into `esi`, `[acc + 4 (n + 1)]` zeroed, the
digit `q = [acc] · iv` into `ecx`, `[acc] += q [mo]`, and the sign word added at the top. -/
def redSum (acc : Ref) : Prog isa :=
  .seq (.block (redHead L acc)) (.seq (mulRow L false acc mo (nBytes .esi 0)) (.block (redTail L acc)))

/-- `[tmp + 4 n] = [acc + 4 n]` plus the carry of `ecx`'s mask, and the mask of `[acc + 4 n]`'s sign
into `ecx` (through `ebx`, still at that word: the store would make its slot secret). -/
def negTop (acc : Ref) : List Instr :=
  ptr L .ebx { acc with half := 1 } .edx ++ ptr L .ebp { tmp with half := 1 } .edx ++
    [.mov .eax (.mem (at_ .ebx 0)), .alu .add .ecx (.reg .ecx), .alu .adc .eax (.imm 0), .store (at_ .ebp 0) .eax] ++
    signOf

/-- `InvMemory.addIfNeg`: `[acc] += [mo]`, `n + 1` words (`mo`'s top word zero), if `[acc + 4 n]` is
negative: the sum into `[tmp]`, its top word `[acc + 4 n]` plus the carry, then selected into
place by that word's sign. -/
def addIfNeg (acc : Ref) : Prog isa :=
  .seq (chain L .adc tmp acc mo (nBytes .edx 0)) (.seq (.block (negTop L acc)) (selIn L acc tmp (nBytes .edi 1)))

/-- `ecx` all ones where `[src + 4 n]` does not borrow the carry of `ecx`'s mask. -/
def borrowMask (src : Ref) : List Instr :=
  ptr L .ebx { src with half := 1 } .edx ++
    [.mov .eax (.mem (at_ .ebx 0)), .alu .add .ecx (.reg .ecx), .alu .sbb .eax (.imm 0), .alu .sbb .eax (.reg .eax),
      .alu .xor .eax (.imm (-1)), .mov .ecx (.reg .eax)]

/-- `Mont.csub` of `[src]` (`n` words and a top word 0 or 1) by `[mo]` into `[o]`: the difference
into `[tmp]`, then selected where it did not borrow. -/
def csub (src o : Ref) : Prog isa :=
  .seq (chain L .sbb tmp src mo (nBytes .edx 0)) <|
  .seq (.block (borrowMask L src)) <|
  if o = src then selIn L o tmp (nBytes .edi 0)
  else .seq (.block (ptr L .ebp src .edx ++ ptr L .ebx tmp .edx ++ nBytes .edx 0 ++ ptr L .edi o .eax))
    (.seq select3LoopX (.block (restoreEdi L)))

def reduce (out : Ref) : Prog isa :=
  .seq (redSum L { arr := 11 }) (.seq (addIfNeg L { arr := 11, byte := 4 }) (csub L { arr := 11, byte := 4 } out))

/-! ## The batch -/

def a (j : Nat) : Ref := { arr := j }

/-- `[2]` replaced by 3 where it is 1, an odd modulus the batches can run on. -/
def virtualize : Prog isa :=
  .seq (.block (ptr L .ebp (a 2) .edx ++ [.mov .eax (.mem (at_ .ebp 0)), .alu .xor .eax (.imm 1),
    .mov .ebx (.reg .ebp), .alu .add .ebx (.imm 4)] ++ nBytesLess .esi)) <|
  .seq (.loop (.block [.alu .or .eax (.mem (at_ .ebx 0)), .alu .add .ebx (.imm 4), .alu .sub .esi (.imm 4)]) .ne)
  (.block [.alu .sub .eax (.imm 1), .alu .sbb .eax (.reg .eax), .alu .and .eax (.imm 2),
    .mov .ecx (.mem (at_ .ebp 0)), .alu .or .ecx (.reg .eax), .store (at_ .ebp 0) .ecx])

/-- `[100] = 3 (n + 1)`, the batches. -/
def batches : List Instr :=
  nBytes .eax 1 ++ [.shift .shr .eax 2, .mov .ecx (.reg .eax), .alu .add .eax (.reg .ecx),
    .alu .add .eax (.reg .ecx), .store (sc 100) .eax]

/-- A batch's window from `f`, `g` (arrays 4 and 5) and the matrix's identity. -/
def start : List Instr :=
  ptr L .ebx (a 4) .edx ++ [.mov .eax (.mem (at_ .ebx 0)), .store (sc (win + 4)) .eax] ++
  ptr L .ebx (a 5) .edx ++ [.mov .eax (.mem (at_ .ebx 0)), .store (sc (win + 8)) .eax] ++
  setConst 2 (win + 12) (1 + 2 ^ 96)

/-! ## The fused batches

The state in two interleaved arrays, from one scratch element on (which the first word of a row
writes): `[f, g, f', g']` per word from array 4 (element size 16) and `[d, e, d', e', p]` from
array 11 (element size 20), `n + 1` words each, two's complement. A batch reads one half of each
element and writes the other, the next batch the other way. Each output is a row
`(c₁ x + c₂ y (+ c₃ p)) / 2^30` in one pass over the words: the products as unsigned ones less
`2^32 x` where the coefficient is negative, a signed 64-bit accumulator in `ebx:ecx`, and the
words shifted by 30 as they go (`sP` keeps the previous word's top two bits). `d, e` divide by
`2^30` modulo `p` exactly: `md, me` clear the low 30 bits (`-p⁻¹ mod 2^32`), with `u`, `v` added
where `d`, `e` are negative, which keeps them in `(-2p, p)`. -/

def fgArr : Nat := 4
def deArr : Nat := 11
def fgSz : Nat := 16
def deSz : Nat := 20

/-- Words at fixed places, in array 0 (`offset w 0 = 160`), which the batches no longer read: the
coefficients' sign masks (`sMu` to `sMu + 12`), the previous word's top bits, the row's end,
the signs of `d` and `e`, `md` and `me`, and their masks. -/
def sMu : Nat := 160
def sP : Nat := 176
def sE : Nat := 180
def sMd : Nat := 184
def sMm : Nat := 200

def neg (k : Nat) : Nat := 2 ^ 32 - k

/-- A term of a row: the input's byte in the element, its coefficient's and mask's header words. -/
structure Term where
  x : Nat
  c : Nat
  m : Nat

/-- `ebx:ecx(:ebp) += c · [esi + x]` for the signed coefficient `c`: the accumulator three words
wide (`ebp` its top) where `wide`. -/
def termI (wide : Bool) (t : Term) : List Instr :=
  [.mov .eax (.mem (sc t.c)), .mov .edx (.mem (at_ .esi t.x)), .mul .edx,
   .alu .add .ebx (.reg .eax), .alu .adc .ecx (.reg .edx)] ++
  (if wide then [.alu .adc .ebp (.imm 0)] else []) ++
  [.mov .eax (.mem (at_ .esi t.x)), .alu .and .eax (.mem (sc t.m)), .alu .sub .ecx (.reg .eax)] ++
  (if wide then [.alu .sbb .ebp (.imm 0)] else [])

/-- `eax` all ones where it is negative. -/
def signEax : List Instr := [.alu .add .eax (.reg .eax), .alu .sbb .eax (.reg .eax)]

/-- The end of a word of a row (see `wordI`). -/
def tailI (wide : Bool) (sz o k : Nat) : List Instr :=
  [.mov .eax (.reg .ebx), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax)] ++
  (if wide then [.alu .add .eax (.mem (sc sP))] else [.alu .add .eax (.reg .ebp)]) ++
  [.store (at_ .esi ((neg sz + o + k) % 2 ^ 32)) .eax, .shift .shr .ebx 30] ++
  (if wide then [.store (sc sP) .ebx, .mov .ebx (.reg .ecx), .mov .ecx (.reg .ebp), .alu .add .ebp (.reg .ebp),
      .alu .sbb .ebp (.reg .ebp)]
   else [.mov .ebp (.reg .ebx), .mov .ebx (.reg .ecx), .alu .add .ecx (.reg .ecx), .alu .sbb .ecx (.reg .ecx)])

/-- A word of a row at byte `k` from `esi`: the sum's word `S` in `ebx`; the previous element's
output word `prev + S · 4`; the top bits of `S` kept (in `ebp` for a narrow row, else at `sP`);
the accumulator shifted down a word, with its sign. -/
def wordI (wide : Bool) (ts : List Term) (sz o k : Nat) : List Instr :=
  (ts.map fun t => { t with x := t.x + k }).flatMap (termI wide) ++ tailI wide sz o k

/-- Two words of a row, then on to the next two. -/
def rowStep (wide : Bool) (ts : List Term) (sz o : Nat) : List Instr :=
  wordI wide ts sz o 0 ++ wordI wide ts sz o sz ++
  [.alu .add .esi (.imm (BitVec.ofNat 32 (2 * sz))), .alu .cmp .esi (.mem (sc sE))]

/-- The sign of the top word of a signed input, times its coefficient, taken from the
accumulator. -/
def topFix (wide : Bool) (sz : Nat) (t : Term) : List Instr :=
  [.mov .eax (.mem (at_ .esi (neg sz + t.x)))] ++ signEax ++
  [.alu .and .eax (.mem (sc t.c)), .mov .edx (.reg .eax), .alu .add .edx (.reg .edx), .alu .sbb .edx (.reg .edx),
   .alu .sub .ebx (.reg .eax), .alu .sbb .ecx (.reg .edx)] ++
  (if wide then [.alu .sbb .ebp (.reg .edx)] else [])

/-- `esi` at the first element of the array `arr` (after its scratch element), and `sE` past its
first `n` elements of `sz` bytes. -/
def rowStart (arr sz : Nat) : List Instr :=
  ptr L .esi { arr := arr, byte := sz } .edx ++
  [.mov .eax (.mem (sc halfSlot)), .mov .edx (.reg .eax)] ++
  (if sz = 16 then [.alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax)]
   else [.alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .edx)]) ++
  [.alu .add .eax (.reg .esi), .store (sc sE) .eax]

/-- A row: `(Σ cᵢ xᵢ) / 2^30` into byte `o` of each element, the terms `signed` sign-extended: two
words at a time over the first `n` (`n` even), then word `n`. -/
def row (wide : Bool) (arr sz o : Nat) (ts signed : List Term) : Prog isa :=
  .seq (.block (rowStart L arr sz ++ [.mov .ebx (.imm 0), .mov .ecx (.imm 0), .mov .ebp (.imm 0)] ++
      (if wide then [.store (sc sP) .ebx] else [])))
    (.seq (.loop (.block (rowStep wide ts sz o)) .ne)
      (.block (wordI wide ts sz o 0 ++ [.alu .add .esi (.imm (BitVec.ofNat 32 sz))] ++
        signed.flatMap (topFix wide sz) ++
        [.alu .add .ebx (.reg .ebx), .alu .add .ebx (.reg .ebx)] ++
        (if wide then [.alu .add .ebx (.mem (sc sP))] else [.alu .add .ebx (.reg .ebp)]) ++
        [.store (at_ .esi (neg sz + o)) .ebx] ++ restoreEdi L)))

/-- The masks of the matrix's signs. -/
def coefMasks : List Instr :=
  (List.range 4).flatMap fun j => [.mov .eax (.mem (sc (win + 12 + 4 * j)))] ++ signEax ++ [.store (sc (sMu + 4 * j)) .eax]

/-- `md` and `me` from the signs of `d`, `e` (at bytes `dx`, `dx + 4` of the elements) and their low
words, and their masks. -/
def mdme (dx : Nat) : List Instr :=
  ptr L .esi { arr := deArr, byte := deSz } .edx ++
  -- `ebx`, `ecx`: the low words; the top words' signs into `sMd`, `sMd + 4` for now.
  [.mov .ebx (.mem (at_ .esi dx)), .mov .ecx (.mem (at_ .esi (dx + 4))),
   .mov .eax (.mem (sc halfSlot)), .mov .edx (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
   .alu .add .eax (.reg .edx), .alu .add .esi (.reg .eax),
   .mov .eax (.mem (at_ .esi dx))] ++ signEax ++ [.store (sc sMd) .eax,
   .mov .eax (.mem (at_ .esi (dx + 4)))] ++ signEax ++ [.store (sc (sMd + 4)) .eax] ++
  (List.range 2).flatMap (fun j =>
    let cu := win + 12 + 8 * j
    let cv := win + 16 + 8 * j
    -- `md₀ = (u & sd) + (v & se)` into `esi`.
    [.mov .esi (.mem (sc cu)), .alu .and .esi (.mem (sc sMd)), .mov .eax (.mem (sc cv)),
     .alu .and .eax (.mem (sc (sMd + 4))), .alu .add .esi (.reg .eax),
     -- `cd = u d₀ + v e₀ mod 2^32` into `ebp`.
     .mov .eax (.mem (sc cu)), .mul .ebx, .mov .ebp (.reg .eax), .mov .eax (.mem (sc cv)), .mul .ecx,
     .alu .add .ebp (.reg .eax),
     -- `md = md₀ - ((md₀ + p⁻¹ cd) mod 2^30)`, with `-p⁻¹` at `win + 28`.
     .mov .eax (.mem (sc (win + 28))), .mul .ebp, .mov .edx (.reg .esi), .alu .sub .edx (.reg .eax),
     .alu .and .edx (.imm 0x3FFFFFFF), .alu .sub .esi (.reg .edx),
     .store (sc (sMd + 8 + 4 * j)) .esi]) ++
  [.mov .eax (.mem (sc (sMd + 8)))] ++ signEax ++ [.store (sc sMm) .eax,
   .mov .eax (.mem (sc (sMd + 12)))] ++ signEax ++ [.store (sc (sMm + 4)) .eax] ++ restoreEdi L

/-- A batch from the half `h` of the elements to the other. -/
def batchF (h : Bool) : Prog isa :=
  let i := if h then 0 else 8
  let o := if h then 8 else 0
  let u : Term := ⟨i, win + 12, sMu⟩
  let v : Term := ⟨i + 4, win + 16, sMu + 4⟩
  let q : Term := ⟨i, win + 20, sMu + 8⟩
  let r : Term := ⟨i + 4, win + 24, sMu + 12⟩
  seqs [
    .block (ptr L .ebx { arr := fgArr, byte := fgSz } .edx ++
      [.mov .eax (.mem (at_ .ebx i)), .store (sc (win + 4)) .eax, .mov .eax (.mem (at_ .ebx (i + 4))),
       .store (sc (win + 8)) .eax] ++ setConst 2 (win + 12) (1 + 2 ^ 96)),
    wordSteps win 30,
    .block coefMasks,
    row L false fgArr fgSz o [u, v] [u, v],
    row L false fgArr fgSz (o + 4) [q, r] [q, r],
    .block (mdme L i),
    row L true deArr deSz o [u, v, ⟨16, sMd + 8, sMm⟩] [u, v],
    row L true deArr deSz (o + 4) [q, r, ⟨16, sMd + 12, sMm + 4⟩] [q, r]]

/-- `[esi + x]` for `n + 1` elements of `sz` bytes from `[ebp]`, words; `ecx` the count. -/
def scatterLoop (sz x : Nat) : Prog isa :=
  .loop (.block [.mov .eax (.mem (at_ .ebp 0)), .store (at_ .esi x) .eax, .alu .add .ebp (.imm 4),
    .alu .add .esi (.imm (BitVec.ofNat 32 sz)), .alu .sub .ecx (.imm 1)]) .ne

def gatherLoop (sz x : Nat) : Prog isa :=
  .loop (.block [.mov .eax (.mem (at_ .esi x)), .store (at_ .ebp 0) .eax, .alu .add .ebp (.imm 4),
    .alu .add .esi (.imm (BitVec.ofNat 32 sz)), .alu .sub .ecx (.imm 1)]) .ne

def scatter (arr sz x : Nat) (src : Ref) : Prog isa :=
  .seq (.block (ptr L .esi { arr := arr, byte := sz } .edx ++ ptr L .ebp src .edx ++ nBytes .ecx 1 ++
    [.shift .shr .ecx 2])) (scatterLoop sz x)

def gather (arr sz x : Nat) (dst : Ref) : Prog isa :=
  .seq (.block (ptr L .esi { arr := arr, byte := sz } .edx ++ ptr L .ebp dst .edx ++ nBytes .ecx 1 ++
    [.shift .shr .ecx 2])) (gatherLoop sz x)

/-- The start: `p` as before (its word `n` zero, as `n + 1` words of it are read), `g = a`
(`a + p` if `a` is even) in array 7, then interleaved;
`(d, e) = (0, 1)`. -/
def initF : Prog isa := seqs [
  .block (slots L), copy L (a 2) (a 8) (nBytes .edi 0), virtualize L, .block (zeroWord L { arr := 2, half := 1 }),
  copy L (a 7) (a 0) (nBytes .edi 0), .block (zeroWord L { arr := 7, half := 1 }),
  zeros L (a 12) (nBytes .ecx 1),
  .block (GcdBatch.evenMask (offset 0 0)), selIn L (a 12) (a 2) (nBytes .edi 0),
  chain L .adc (a 7) (a 7) (a 12) (nBytes .edx 1),
  scatter L fgArr fgSz 0 (a 2), scatter L fgArr fgSz 4 (a 7),
  -- Zeros from `[3]`, apart from the elements (`[12]` is among them); `[3]` is the result, later.
  zeros L (a 3) (nBytes .ecx 1),
  scatter L deArr deSz 0 (a 3), scatter L deArr deSz 4 (a 3), scatter L deArr deSz 16 (a 2),
  .block (ptr L .eax { arr := deArr, byte := deSz } .edx ++ [.mov .ecx (.imm 1), .store (at_ .eax 4) .ecx]),
  .block [.mov .eax (.imm 1), .store (sc win) .eax],
  .block (ptr L .eax (a 2) .edx ++ [.mov .ebx (.mem (at_ .eax 0))] ++ Dynamic.inverse ++ [.store (sc (win + 28)) .eax]),
  -- `(3 n + 2) / 2` double batches, then one: `3 (n + 1)`.
  .block (nBytes .eax 0 ++ [.shift .shr .eax 2, .mov .ecx (.reg .eax), .alu .add .eax (.reg .ecx),
    .alu .add .eax (.reg .ecx), .alu .add .eax (.imm 2), .shift .shr .eax 1, .store (sc 100) .eax])]

/-- `[x] := [x] + p` where `[x]` (`n + 1` words) is negative. -/
def addIfNegF (x : Ref) : Prog isa := seqs [
  chain L .adc tmp x mo (nBytes .edx 1),
  .block (maskAt L { x with half := 1 }), selIn L x tmp (nBytes .edi 1)]

/-- The end, after an odd number of batches (the state in the elements' second half): `f` and `d`
gathered into arrays 14 and 7; `x = ±d` brought into `[0, p)`; then
`[1] = |f|` and `[3] = x`. -/
def finishF : Prog isa := seqs [
  gather L fgArr fgSz 8 (a 14), gather L deArr deSz 8 (a 7),
  -- `d := -d` if `f < 0`.
  zeros L tmp (nBytes .ecx 1), chain L .sbb tmp tmp (a 7) (nBytes .edx 1),
  .block (maskAt L { arr := 14, half := 1 }), selIn L (a 7) tmp (nBytes .edi 1),
  addIfNegF L (a 7), addIfNegF L (a 7), csub L (a 7) (a 7),
  zeros L (a 1) (wBytes .ecx), chain L .sbb (a 1) (a 1) (a 14) (nBytes .edx 0),
  .block (maskAt L { arr := 14, half := 1 } ++ [.alu .xor .ecx (.imm (-1))]),
  selIn L (a 1) (a 14) (nBytes .edi 0),
  zeros L (a 3) (wBytes .ecx), copy L (a 3) (a 7) (nBytes .edi 0)]

def body : Prog isa := seqs [
  initF L,
  .loop (seqs [batchF L true, batchF L false,
    .block [.mov .esi (.mem (sc 100)), decCounter, .store (sc 100) .esi, testCounter]]) .ne,
  batchF L true,
  finishF L]

/-! ## The choice -/

/-- A rejected guard clears CF. -/
def reject : Prog isa := .block [.alu .cmp .eax (.reg .eax)]

/-- CF set exactly for the lengths the batches take: `n_len` (argument 7) a multiple of 16 and at
least 128, and the primes' lengths (arguments 9 and 11) at most `n_len / 2`. -/
def guard : Prog isa :=
  .seq (.block [.mov .eax (.mem (argOp 7)), .alu .and .eax (.imm 15)]) <|
  .ite .e (.seq (.block [.mov .eax (.mem (argOp 7)), .alu .cmp .eax (.imm 128)]) <|
    .ite .ae (.seq (.block [.mov .eax (.mem (argOp 7)), .shift .shr .eax 1, .alu .add .eax (.imm 1),
        .mov .ecx (.mem (argOp 9)), .alu .cmp .ecx (.reg .eax)]) <|
      .ite .b (.block [.mov .ecx (.mem (argOp 11)), .alu .cmp .ecx (.reg .eax)]) reject) reject) reject

/-- The batches where the guard allows them, else `fallback`, each emitted once. -/
def dispatch (fallback : Prog isa) : Prog isa := .seq guard (.ite .b (body L) fallback)

end VG.Impl.Rsa.X86.InvBatchRt
