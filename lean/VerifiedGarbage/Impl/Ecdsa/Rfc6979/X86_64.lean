module

public import VerifiedGarbage.Impl.Mgf1.X86_64.Table
public import VerifiedGarbage.Impl.Weierstrass.X86_64

/-!
# Deterministic ECDSA (RFC 6979) on x86-64, with HMAC through a table

`vg_ecdsa_<curve>_sign(out = rdi, d = rsi, digest = rdx, digest_len = rcx,
scratch = r8, hmac = r9) -> eax` (`signCode`), for a curve of `Q`-byte
scalars in `w` words: RFC 6979 §3.2 with HMAC over the hash function of the
table `hmac` of the interface `Hmac` (`Spec/HmacTable.lean`), whose
functions it calls indirectly (`tcall`): HMAC's `init` (word 0), which keys
the inner and outer streaming states, the streaming `update` (word 1), on
the inner state, and HMAC's `finalize` (word 2), which writes the MAC; and
each candidate tried by calling `core`, the signature with a given `k`
(`vg_ecdsa_<curve>_sign_k`), which reads `Q` bytes of the digest and of `k`,
and takes their leftmost `qlen` bits (`bits2int`, a right shift by
`sh = 8 Q - qlen` bits).

One body serves every hash function: the digest length `D` and HMAC's block
size `B` are the table's words of data 4 and 5, which the code copies to the
frame (`entry`, `pushRs`) and reads wherever it needs them, as the lengths and counts it
passes (all public). Nothing in the code depends on the hash function but
those two words and the table's functions.

Each HMAC is `init` with the key `K` (`D` bytes, in the frame) or the states
for `K` restored (`restore`, from a copy `save` made after an earlier
`init` with the same `K`), the inner state updated with `V` (`D` bytes, in
the frame), then with the message `b ‖ d ‖ h` or `b` (`msg`, in `scratch`,
its length the curve's), and `finalize`, which writes the MAC to `K` or `V`
in the frame, with the count `B + D + len`.

The digest's leftmost `min(D, Q)` bytes, after `Q - min(D, Q)` zero bytes,
are `X` (`prepX`, by a byte loop, `cpLoop`), a `Q`-byte number: the digest's
`bits2int` if `sh = 0`. Then:

* unless `big` (all but P-521): `h = bits2octets(digest)` is `X` minus `n` if
  it is at least `n` (a conditional subtraction, `reduce`, as
  `2^(8 Q) < 2 n`), and `core` reads `X` as its digest;
* if `big` (P-521, whose scalars are longer than every digest, with
  `sh ≠ 0`): `X`'s integer is below `n`, so `h` is `X` itself, and `core`
  reads the digest's integer shifted left by `sh` bits (`prepC`, at `fXc`:
  `Q - 1 - D` zero bytes, the digest and a zero byte, shifted right by
  `8 - sh` bits through the words at `scratch + sSlot`, `conv`).

The candidate `k` is the leftmost `Q` bytes of `T`, the `V`s of successive
`V = HMAC_K(V)` while `T` is shorter than `Q` bytes (`cand`: a loop whose
count is public, each `V` appended to `T` by `cpLoop`), shifted right by `sh`
bits in place if `big` (`candTop`).

Everything runs in one stack frame of `28 + extra` words (`pushRs`), pushed
from `r9` (the table, `fTab`), `extra - 2` copies of `rax`, `r11` and `r10`
(`B` and `D`, loaded from the table on entry), `rdi`, `rsi`, `rdx`, `rcx`
(`scratch`, moved from `r8`) and 23 copies of `rax`: from `rsp`, `K` and `V`
(64 bytes each, of which the first `D` are used), the length of `T`, 40
bytes unused, the number of candidates left, then the pointers `scratch`,
`digest`, `d` and `out`; above them, `D`, `B`, a word below `h` (`reduce`
stores the zero bytes of a short top word there), `h`, `X` and `core`'s
digest if `big` (72 bytes each), and `T` (136 bytes); then the table's
address. The calls use only `scratch`, which `core` overwrites
entirely, and the stack below the frame; `K`, `V` and the words above the
pointers but `D` and `B` are cleared before the frame is popped. In `scratch`: HMAC's inner and outer streaming states (192
bytes each), the working space of the table's functions, the message, the
words of a shift, and the copy of the states for `K`.

1. `X`; `h` (`reduce`, or `prepC`); `V = 0x01…`, `K = 0x00…`.
2. Steps d to g: `K = HMAC_K(V ‖ 0x00 ‖ d ‖ h)`, `V = HMAC_K(V)`,
   `K = HMAC_K(V ‖ 0x01 ‖ d ‖ h)`, `V = HMAC_K(V)`.
3. At most `tries` times: the candidate `k` (`cand`) and
   `core(out, d, digest, k, scratch)`; if it failed and candidates are left,
   `K = HMAC_K(V ‖ 0x00)`, `V = HMAC_K(V)` and again. Whether to go on is
   computed without branches, so that the code branches only on it: the
   number of candidates tried is all it reveals.

`core` writes the signature or zeros to `out`, and its return value is ours.

A block addresses memory only at `rsp`, at `rsp` plus a constant, at the
table (through `r9`, on entry), or at a pointer an earlier block
loaded from the frame (`msgPtrs`, `scrPtr`, the table's address in
`tcall`), plus public offsets: the taint analysis of each block, once for
each curve, knows its addresses are public.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Rfc6979.X86_64

open VG.X86_64
open VG.Impl.Mgf1.X86_64.Table (Fns)
open VG.Impl.Mgf1.X86_64 (ix)

/-- `[rsp + d]`, in the frame. -/
def stk (d : Nat) : MemOp := { base := .rsp, disp := d }

/-- `[b + d]`. -/
def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-! Where things are in the frame. -/
def fK : Nat := 0
def fV : Nat := 64
/-- The length of `T`. -/
def fTlen : Nat := 128
def fCnt : Nat := 176
def fScratch : Nat := 184
def fDigest : Nat := 192
def fD : Nat := 200
def fOut : Nat := 208
/-- Above the pointers: the digest length `D` and HMAC's block size `B`. -/
def fDl : Nat := 216
def fBl : Nat := 224
/-- `h` (72 bytes), unless `big`, after a word that `reduce` may write. -/
def fH : Nat := 248
/-- `X` (72 bytes): the digest's leftmost bytes, as a `Q`-byte number; `h` if `big`. -/
def fX : Nat := 320
/-- If `big`: the digest for `core` (72 bytes). -/
def fXc : Nat := 392
/-- The candidate `T` (136 bytes). -/
def fT : Nat := 464
/-- The words above the pointers. -/
def extra : Nat := 48
/-- The table's address, the frame's top word. -/
def fTab : Nat := 216 + 8 * extra

/-! Where things are in `scratch`. -/
def sInner : Nat := 0
def sOuter : Nat := 192
def sWork : Nat := 384
def sMsg : Nat := 2256
/-- The words of a conversion, if `big`. -/
def sSlot : Nat := 2560
/-- A copy of HMAC's two states just after `init`, for the key `K`. -/
def sSave : Nat := 3072

/-- What the code needs of a curve. -/
structure Cfg where
  /-- The functions an indirect call of a table's functions may reach. -/
  f : Fns
  /-- The words of the curve's scalars. -/
  w : Nat
  /-- The bytes of the curve's scalars, `Q`. -/
  len : Nat := 8 * w
  /-- Whether the scalars are longer than every digest, with `sh ≠ 0` (P-521's). -/
  big : Bool := false
  /-- The bits `core` shifts its digest right by, `8 Q - qlen`. -/
  sh : Nat := 0
  /-- The order of the curve's base point. -/
  n : Nat
  /-- The most candidates to try. -/
  tries : Nat
  /-- The signature with a given `k`, and its name. -/
  coreN : String
  coreC : Prog isa

namespace Cfg

variable (c : Cfg)

/-- Where `h` is in the frame. -/
def fHo : Nat := if c.big then fX else fH

/-- Where `core` reads its digest in the frame. -/
def fDg : Nat := if c.big then fXc else fX

/-- `d ← [rsp + fScratch] + a`: an address in `scratch`. -/
def scr (d : Reg) (a : Nat) : List Instr :=
  [.mov d (.mem (stk fScratch)), .alu .add d (.imm (BitVec.ofNat 32 a))]

/-- `d ← rsp + o`: an address in the frame. -/
def fr (d : Reg) (o : Nat) : List Instr :=
  [.mov d (.reg .rsp), .alu .add d (.imm (BitVec.ofNat 32 o))]

/-- `scratch` in `rdi`. -/
def scrPtr : List Instr := [.mov .rdi (.mem (stk fScratch))]

/-! ## HMAC through the table -/

/-- The indirect call of the table's function `j`, among `ts`: the table's
address into `r11`, its word `j` into `r11`, then `call r11`. -/
def tcall (j : Nat) (ts : List (String × Prog isa)) : Prog isa :=
  .seq (.block [.mov .r11 (.mem (stk fTab)), .mov .r11 (.mem (at_ .r11 (8 * j)))])
    (Code.icalls (.callr .r11) ts)

/-- The arguments of HMAC's `init`: the states, the key `K` of `D` bytes,
the working space. -/
def initArgs : List Instr :=
  scr .rdi sInner ++ scr .rsi sOuter ++ fr .rdx fK ++ ([.mov .rcx (.mem (stk fDl))] : List Instr) ++
    scr .r8 sWork

/-- The arguments of the streaming `update` with `V`: the inner state, the
`B` bytes it holds, `V`'s `D` bytes, the working space. -/
def updVArgs : List Instr :=
  scr .rdi sInner ++ ([.mov .rsi (.mem (stk fBl))] : List Instr) ++ fr .rdx fV ++
    ([.mov .rcx (.mem (stk fDl))] : List Instr) ++ scr .r8 sWork

/-- The arguments of the streaming `update` with the message: the inner
state, the `B + D` bytes it holds, the message's `len` bytes, the working
space. -/
def updMArgs (len : Nat) : List Instr :=
  scr .rdi sInner ++ ([.mov .rsi (.mem (stk fBl)), .alu .add .rsi (.mem (stk fDl))] : List Instr) ++
    scr .rdx sMsg ++ ([.mov32 .rcx (.imm (BitVec.ofNat 32 len))] : List Instr) ++ scr .r8 sWork

/-- The arguments of HMAC's `finalize`: the states, the `B + D + len` bytes
the inner one holds, the MAC's place in the frame, the working space. -/
def finArgs (len dst : Nat) : List Instr :=
  scr .rdi sInner ++ scr .rsi sOuter ++
    ([.mov .rdx (.mem (stk fBl)), .alu .add .rdx (.mem (stk fDl)),
      .alu .add .rdx (.imm (BitVec.ofNat 32 len))] : List Instr) ++ fr .rcx dst ++ scr .r8 sWork

/-- HMAC's states for `K`, by `init`. -/
def initK : Prog isa := .seq (.block initArgs) (tcall 0 c.f.init)

/-- The inner state updated with `V`. -/
def updV : Prog isa := .seq (.block updVArgs) (tcall 1 c.f.upd)

/-- The inner state updated with the message's `len` bytes. -/
def updM (len : Nat) : Prog isa := .seq (.block (updMArgs len)) (tcall 1 c.f.upd)

/-- The MAC, of `D + len` bytes of text, to the frame at `dst`. -/
def fin (len dst : Nat) : Prog isa := .seq (.block (finArgs len dst)) (tcall 2 c.f.fin)

/-- The `8 k` bytes at `[src + so]` to `[dst + d]`, a word at a time through `rax`. -/
def copyN (k : Nat) (src : Reg) (so : Nat) (dst : Reg) (d : Nat) : List Instr :=
  (List.range k).flatMap fun j =>
    [.mov .rax (.mem (at_ src (so + 8 * j))), .store (at_ dst (d + 8 * j)) .rax]

/-- The `len` bytes at `[src + so]` to `[dst + d]` (`8 ≤ len`), a word at a
time through `rax`: `copyN` for the whole words, then the last eight bytes
again if `len` is not a multiple of 8. -/
def copyBytes (len : Nat) (src : Reg) (so : Nat) (dst : Reg) (d : Nat) : List Instr :=
  copyN (len / 8) src so dst d ++
    (if len % 8 = 0 then [] else
      [.mov .rax (.mem (at_ src (so + len - 8))), .store (at_ dst (d + len - 8)) .rax])

/-- HMAC's two states (384 bytes) copied from `scratch + sInner` to `scratch + sSave`
(`toSave`) or back, with `scratch` in `rdi`, through `rax`. -/
def copyStates (toSave : Bool) : List Instr :=
  if toSave then copyN 48 .rdi sInner .rdi sSave else copyN 48 .rdi sSave .rdi sInner

/-- The states for `K` saved. -/
def save : List Instr := scrPtr ++ copyStates true

/-- The states for `K` restored from the copy. -/
def restore : List Instr := scrPtr ++ copyStates false

/-- `V = HMAC_K(V)`, saving the states for `K`. -/
def hmacVS : Prog isa := .seq c.initK (.seq (.block save) (.seq c.updV (c.fin 0 fV)))

/-- `V = HMAC_K(V)`, from the saved states for `K`. -/
def hmacVR : Prog isa := .seq (.block restore) (.seq c.updV (c.fin 0 fV))

/-- `K = HMAC_K(V ‖ msg)`, for the message's `len` bytes, from the states
for `K` by `init` (`fresh`) or restored. -/
def hmacK (fresh : Bool) (len : Nat) : Prog isa :=
  .seq (if fresh then c.initK else .block restore) (.seq c.updV (.seq (c.updM len) (c.fin len fK)))

/-- The pointers the messages need: `scratch` in `rdi`, `d` in `rsi`. -/
def msgPtrs : List Instr := [.mov .rdi (.mem (stk fScratch)), .mov .rsi (.mem (stk fD))]

/-- The message `b` (and `‖ d ‖ h` if `full`, `Q` bytes each) at
`scratch + sMsg`, with `scratch` in `rdi` and `d` in `rsi`: `b` a byte, then
the private key and `h` from the frame. -/
def msg (b : Nat) (full : Bool) : List Instr :=
  ([.mov32 .rax (.imm (BitVec.ofNat 32 b)), .store8 (at_ .rdi sMsg) .rax] : List Instr) ++
    (if full then copyBytes c.len .rsi 0 .rdi (sMsg + 1) ++ copyBytes c.len .rsp c.fHo .rdi (sMsg + 1 + c.len)
    else [])

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g), the
states for the new `K` saved; for `b = 1` (step f), the states for `K` are
the copy step e saved. -/
def rekeyFull (b : Nat) : Prog isa :=
  .seq (.block msgPtrs) (.seq (.block (c.msg b true)) (.seq (c.hmacK (b = 0) (1 + 2 * c.len)) c.hmacVS))

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
def rekey : Prog isa :=
  .seq (.block msgPtrs) (.seq (.block (c.msg 0 false)) (.seq (c.hmacK true 1) c.hmacVS))

/-! ## Bytes, numbers and `h` -/

/-- A byte of `[rsi + r8]` to `[rdi + r8]`, through `rax`. -/
def cpBody : List Instr := [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rdi .r8) .rax]

/-- The `rcx` bytes at `rsi` to `rdi` (`rcx > 0`), a byte at a time, `r8`
counting from 0. -/
def cpLoop : Prog isa := Impl.Mgf1.X86_64.byteLoop cpBody (.reg .rcx)

/-- Nine zero words at `rsp + o`. -/
def zero9 (o : Nat) : List Instr :=
  (List.range 9).flatMap fun j => [.alu32 .xor .rax (.reg .rax), .store (stk (o + 8 * j)) .rax]

/-- The arguments of `X`'s copy: `X` cleared; then `rcx = min(D, Q)`, the
digest in `rsi`, `X + Q - rcx` in `rdi` and `r8 = 0`. -/
def xArgs : List Instr :=
  zero9 fX ++
    ([.mov .rcx (.mem (stk fDl)), .mov32 .rax (.imm (BitVec.ofNat 32 c.len)), .alu .cmp .rcx (.reg .rax),
      .cmov .ae .rcx (.reg .rax), .mov .rdi (.reg .rsp), .alu .add .rdi (.imm (BitVec.ofNat 32 (fX + c.len))),
      .alu .sub .rdi (.reg .rcx), .mov .rsi (.mem (stk fDigest)), .alu32 .xor .r8 (.reg .r8)] : List Instr)

/-- `X`: `Q - min(D, Q)` zero bytes, then the digest's leftmost `min(D, Q)`. -/
def prepX : Prog isa := .seq (.block c.xArgs) cpLoop

/-- The 64-bit words of `n`, least significant first. -/
def nWord (j : Nat) : BitVec 64 := BitVec.ofNat 64 (c.n >>> (64 * j))

/-- Word `j` of the `Q`-byte number at `rsi`, least significant first, in
`rax`: the byte reversal of the word at `rsi + Q - 8 (j + 1)`, or, for a top
word of four bytes (`Q % 8 = 4`), of the first four, zero-extended. Neither
changes the flags, which carry the borrow from one word to the next. -/
def loadWord (j : Nat) : List Instr :=
  if 8 * (j + 1) ≤ c.len then [.mov .rax (.mem (at_ .rsi (c.len - 8 * (j + 1)))), .bswap .rax]
  else if c.len ≤ 8 * j then [.mov .rax (.imm 0)]
  else [.mov32 .rax (.mem (at_ .rsi 0)), .bswap32 .rax]

/-- Word `j` of the number at `rsi`, least significant first, to `V`'s
place, and word `j` of it minus `n` (with the borrow of the words before) to
`K`'s: `rax` and `rdx` change, and the borrow is the carry flag. -/
def subWord (j : Nat) : List Instr :=
  c.loadWord j ++ ([.store (stk (fV + 8 * j)) .rax,
    .movImm64 .rdx (c.nWord j), .alu (if j = 0 then .sub else .sbb) .rax (.reg .rdx),
    .store (stk (fK + 8 * j)) .rax] : List Instr)

/-- Word `j` of the result, by the mask `rdx` (all ones if subtracting `n`
borrowed): the number's word if so, the difference's if not, big-endian to
`h + Q - 8 (j + 1)`. A top word of fewer bytes is stored partly below `h`,
in the word there, its zero bytes there and the rest `h`'s first bytes. -/
def selWord (j : Nat) : List Instr :=
  [.mov .rax (.mem (stk (fV + 8 * j))), .mov .rcx (.mem (stk (fK + 8 * j))), .alu .xor .rax (.reg .rcx),
    .alu .and .rax (.reg .rdx), .alu .xor .rax (.reg .rcx), .bswap .rax,
    .store (stk (fH + c.len - 8 * (j + 1))) .rax]

/-- `h`, unless `big`: `X` (at `rsi`), as a big-endian number, minus `n` if
that does not borrow, big-endian into the frame's `Q` bytes at `h`. -/
def reduce : List Instr :=
  fr .rsi fX ++ (List.range c.w).flatMap c.subWord ++ ([.alu .sbb .rdx (.reg .rdx)] : List Instr) ++
    (List.range c.w).flatMap c.selWord

/-- The `Q` bytes at `rsp + o`, as a big-endian number, shifted right by `s`
bits in place, through the words at `scratch + sSlot` (with `scratch` in
`rdi`). -/
def conv (o s : Nat) : List Instr :=
  fr .rsi o ++ Impl.Weierstrass.X86_64.loadBytes c.len c.w sSlot .rsi ++
    Impl.Weierstrass.X86_64.shrWords c.w sSlot s ++ ([.movImm64 .rcx (BitVec.allOnes 64)] : List Instr) ++
    Impl.Weierstrass.X86_64.storeBytes c.len c.w .rsp o sSlot

/-- The arguments of the copy of `core`'s digest, if `big`: it cleared;
then `rcx = D`, the digest in `rsi`, `fXc + Q - 1 - D` in `rdi` and `r8 = 0`. -/
def xcArgs : List Instr :=
  zero9 fXc ++
    ([.mov .rcx (.mem (stk fDl)), .mov .rdi (.reg .rsp),
      .alu .add .rdi (.imm (BitVec.ofNat 32 (fXc + c.len - 1))), .alu .sub .rdi (.reg .rcx),
      .mov .rsi (.mem (stk fDigest)), .alu32 .xor .r8 (.reg .r8)] : List Instr)

/-- If `big`: `core`'s digest, `Q - 1 - D` zero bytes, the digest and a zero
byte, shifted right by `8 - sh` bits: the digest's integer shifted left by
`sh` bits. -/
def prepC : Prog isa := .seq (.block c.xcArgs) (.seq cpLoop (.block (scrPtr ++ c.conv fXc (8 - c.sh))))

/-- `h`: `reduce`, or, if `big`, `X` itself, with `core`'s digest. -/
def prepH : Prog isa := if c.big then c.prepC else .block c.reduce

/-- `V = 0x01…`, `K = 0x00…`, all 64 bytes of each. -/
def initKV : List Instr :=
  ([.movImm64 .rax (BitVec.ofNat 64 0x0101010101010101), .alu32 .xor .rcx (.reg .rcx)] : List Instr) ++
    (List.range 8).flatMap fun j => [.store (stk (fV + 8 * j)) .rax, .store (stk (fK + 8 * j)) .rcx]

/-- The candidates left. -/
def initCnt : List Instr :=
  [.mov32 .rax (.imm (BitVec.ofNat 32 c.tries)), .store (stk fCnt) .rax]

/-! ## The candidates -/

/-- `T` empty. -/
def tInit : List Instr := [.alu32 .xor .rax (.reg .rax), .store (stk fTlen) .rax]

/-- The arguments of `V`'s copy to the end of `T`: `rcx = D`, `V` in `rsi`,
`T + |T|` in `rdi` and `r8 = 0`. -/
def keepArgs : List Instr :=
  fr .rsi fV ++ fr .rdi fT ++
    ([.alu .add .rdi (.mem (stk fTlen)), .mov .rcx (.mem (stk fDl)), .alu32 .xor .r8 (.reg .r8)] : List Instr)

/-- `T` longer by `D` bytes, and the carry flag set iff it is still shorter
than `Q`. -/
def tStep : List Instr :=
  [.mov .rax (.mem (stk fTlen)), .alu .add .rax (.mem (stk fDl)), .store (stk fTlen) .rax,
    .alu .cmp .rax (.imm (BitVec.ofNat 32 c.len))]

/-- One `V` of the candidate: `V = HMAC_K(V)`, appended to `T`. -/
def candStep : Prog isa := .seq c.hmacVR (.seq (.block keepArgs) (.seq cpLoop (.block c.tStep)))

/-- If `big`: `T`'s first `Q` bytes shifted right by `sh` bits. -/
def candTop : List Instr := if c.big then scrPtr ++ c.conv fT c.sh else []

/-- The candidate: `T`, the `V`s of successive `V = HMAC_K(V)` while it is
shorter than `Q` bytes, its leftmost `Q` bytes shifted right by `sh` bits if
`big`. -/
def cand : Prog isa := .seq (.block tInit) (.seq (.loop c.candStep .b) (.block c.candTop))

/-- `core(out, d, digest, k, scratch)`: the digest `X` (or, if `big`, the
one at `fXc`) and `k = T`. -/
def coreArgs : List Instr :=
  ([.mov .rdi (.mem (stk fOut)), .mov .rsi (.mem (stk fD))] : List Instr) ++ fr .rdx c.fDg ++ fr .rcx fT ++
    ([.mov .r8 (.mem (stk fScratch))] : List Instr)

/-- One candidate fewer, and `rdx ≠ 0` (and `ZF` clear) iff the signature
failed (`eax = 0`) and candidates are left: `rdx = -(eax < 1) & (count - 1)`. -/
def goOn : List Instr :=
  [.mov .rcx (.mem (stk fCnt)), .alu .sub .rcx (.imm 1), .store (stk fCnt) .rcx,
    .alu32 .cmp .rax (.imm 1), .alu .sbb .rdx (.reg .rdx), .alu .and .rdx (.reg .rcx),
    .alu .test .rdx (.reg .rdx)]

/-- `ZF` clear: go on. -/
def again : List Instr := [.mov32 .rdx (.imm 1), .alu .test .rdx (.reg .rdx)]

/-- `ZF` set: stop. -/
def stop : List Instr := [.alu32 .xor .rdx (.reg .rdx)]

/-- One candidate: `cand`, `core` with it, then, if it failed
and candidates are left, step h.3. -/
def tryOne : Prog isa :=
  .seq c.cand
  (.seq (.block c.coreArgs)
  (.seq (.call c.coreN c.coreC)
  (.seq (.block goOn)
    (.ite .ne (.seq c.rekey (.block again)) (.block stop)))))

/-- `K` and `V`, and the words above the pointers but `D` and `B`, cleared
(`rax`, the result, kept). -/
def wipe : List Instr :=
  ([.alu32 .xor .rcx (.reg .rcx)] : List Instr) ++ (List.range 16).map (fun j => .store (stk (8 * j)) .rcx) ++
    (List.range (extra - 2)).map fun j => .store (stk (fBl + 8 + 8 * j)) .rcx

/-- The frame's body. -/
def body : Prog isa :=
  .seq c.prepX
  (.seq c.prepH
  (.seq (.block initKV)
  (.seq (c.rekeyFull 0)
  (.seq (c.rekeyFull 1)
  (.seq (.block c.initCnt)
  (.seq (.loop c.tryOne .ne)
    (.block wipe)))))))

/-- The registers the frame's push stores: the table's address, then `B`
(in `r11`) and `D` (in `r10`) at their places above the pointers, the
pointers, and copies of `rax`. -/
def pushRs : List Reg :=
  .r9 :: ((List.replicate (extra - 2) .rax ++ [.r11, .r10]) ++ [.rdi, .rsi, .rdx, .rcx] ++
    List.replicate 23 .rax)

/-- The frame. -/
def sign : Prog isa := .frame (.push pushRs) c.body (.pop .rcx (28 + extra))

end Cfg

/-- `scratch` to `rcx`, and `D` and `B`, the table's words of data 4 and 5,
to `r10` and `r11`, for the frame's push. -/
def entry : List Instr := [.mov .rcx (.reg .r8), .mov .r10 (.mem (at_ .r9 32)), .mov .r11 (.mem (at_ .r9 40))]

/-- `vg_ecdsa_<curve>_sign`. -/
def signCode (c : Cfg) : Prog isa := .seq (.block entry) c.sign

end VG.Impl.Ecdsa.Rfc6979.X86_64
