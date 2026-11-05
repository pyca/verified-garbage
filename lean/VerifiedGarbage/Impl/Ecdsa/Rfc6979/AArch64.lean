module

public import VerifiedGarbage.Impl.RsaOaep.AArch64.Mgf1.Table
public import VerifiedGarbage.Impl.Weierstrass.AArch64

/-!
# Deterministic ECDSA (RFC 6979) on AArch64, with HMAC through a table

`vg_ecdsa_<curve>_sign(out = x0, d = x1, digest = x2, digest_len = x3,
scratch = x4, hmac = x5) -> w0` (`signCode`), as on x86-64
(`Impl/Ecdsa/Rfc6979/X86_64.lean`), for a curve of `Q`-byte scalars in `w`
64-bit words: RFC 6979 §3.2 with HMAC over the hash function of the table
`hmac` of the interface `Hmac` (`Spec/HmacTable.lean`), whose functions it
calls indirectly (`tcall`: the table's word `j` into `x16`, then
`blr x16`): HMAC's `init` (word 0), which keys the inner and outer
streaming states, the streaming `update` (word 1), on the inner state, and
HMAC's `finalize` (word 2), which writes the MAC; and each candidate tried
by calling `core`, the signature with a given `k`
(`vg_ecdsa_<curve>_sign_k`), which reads `Q` bytes of the digest and of `k`,
and takes their leftmost `qlen` bits (`bits2int`, a right shift by
`sh = 8 Q - qlen` bits).

One body serves every hash function: the digest length `D` and HMAC's block
size `B` are the table's words of data 4 and 5, which the code loads on
entry (`entry`, into `x6` and `x7`), stores in the frame (`saveArgs`) and
reads wherever it needs them, as the lengths and counts it passes (all
public). Nothing in the code depends on the hash function but those two
words and the table's functions.

Each HMAC is `init` with the key `K` (`D` bytes, in the frame) or the states
for `K` restored (`restore`, from a copy `save` made after an earlier
`init` with the same `K`), the inner state updated with `V` (`D` bytes, in
the frame), then with the message `b ‖ d ‖ h` or `b` (`msg`, in `scratch`,
its length the curve's), and `finalize`, which writes the MAC to `K` or `V`
in the frame, with the count `B + D + len`.

The digest's leftmost `min(D, Q)` bytes, after `Q - min(D, Q)` zero bytes,
are `X` (`prepX`, by a byte loop, `cpLoop`, the minimum by `csel`), a
`Q`-byte number: the digest's `bits2int` if `sh = 0`. Then:

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

The return address `x30` is pushed (the calls replace it), then a frame of
608 bytes is allocated: from `sp`, `K` and `V` (64 bytes each, of which the
first `D` are used), the length of `T`, 40 bytes unused, the number of
candidates left, then the pointers `scratch`, `digest`, `d` and `out`;
above them, `D`, `B`, a word below `h` (`reduce` stores the zero bytes of a
short top word there), `h`, `X` and `core`'s digest if `big` (72 bytes
each), and `T` (136 bytes); then the table's address. The calls use only
`scratch`, which `core` overwrites entirely, and the 16 bytes below the
frame (HMAC's functions); `K`, `V` and the words above the pointers but `D`
and `B` are cleared before the frame is freed. In `scratch`: HMAC's inner and
outer streaming states (192 bytes each), the working space of the table's
functions, the message, the words of a shift, and the copy of the states
for `K`.

1. `X`; `h` (`reduce`, or `prepC`); `V = 0x01…`, `K = 0x00…`.
2. Steps d to g: `K = HMAC_K(V ‖ 0x00 ‖ d ‖ h)`, `V = HMAC_K(V)`,
   `K = HMAC_K(V ‖ 0x01 ‖ d ‖ h)`, `V = HMAC_K(V)`.
3. At most `tries` times: the candidate `k` (`cand`) and
   `core(out, d, digest, k, scratch)`; if it failed and candidates are left,
   `K = HMAC_K(V ‖ 0x00)`, `V = HMAC_K(V)` and again. Whether to go on, in
   `x12`, is computed without branches, so that the code branches only on
   it: the number of candidates tried is all it reveals.

`core` writes the signature or zeros to `out`, and its return value is ours.

A block addresses memory only at `sp` (through `x15`, set by `addSp`, or
`sp` itself), at the table (through `x5`, on entry), or at a pointer an
earlier block loaded from the frame (`msgPtrs`, `scrPtr`, the table's
address in `tcall`), plus public offsets: the taint analysis of each block,
once for each curve, knows its addresses are public.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Rfc6979.AArch64

open VG.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)
open VG.Impl.Mont.AArch64 (const64)

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
/-- The frame's size, a multiple of 16. -/
def frameBytes : Nat := fTab + 8

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
  /-- The 64-bit words of the curve's scalars. -/
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

/-- `d ← scratch + a`: an address in `scratch`. -/
def scr (d : Reg) (a : Nat) : List Instr := [.ldrSp d fScratch, .addImm .x d d a]

/-- `d ← sp + o`: an address in the frame. -/
def fr (d : Reg) (o : Nat) : List Instr := [.addSp d o]

/-- `scratch` in `x9`. -/
def scrPtr : List Instr := [.ldrSp .x9 fScratch]

/-- `out`, `d`, `digest`, `scratch`, `D`, `B` and the table into the frame. -/
def saveArgs : List Instr :=
  [.addSp .x15 0, .str .x .x0 .x15 fOut, .str .x .x1 .x15 fD, .str .x .x2 .x15 fDigest,
    .str .x .x4 .x15 fScratch, .str .x .x6 .x15 fDl, .str .x .x7 .x15 fBl, .str .x .x5 .x15 fTab]

/-! ## HMAC through the table -/

/-- The indirect call of the table's function `j`, among `ts`: the table's
address into `x16`, its word `j` into `x16`, then `blr x16`. -/
def tcall (j : Nat) (ts : List (String × Prog isa)) : Prog isa :=
  .seq (.block [.ldrSp .x16 fTab, .ldr .x .x16 .x16 (8 * j)]) (Code.icalls (.blr .x16) ts)

/-- The arguments of HMAC's `init`: the states, the key `K` of `D` bytes,
the working space. -/
def initArgs : List Instr :=
  scr .x0 sInner ++ scr .x1 sOuter ++ fr .x2 fK ++ ([.ldrSp .x3 fDl] : List Instr) ++ scr .x4 sWork

/-- The arguments of the streaming `update` with `V`: the inner state, the
`B` bytes it holds, `V`'s `D` bytes, the working space. -/
def updVArgs : List Instr :=
  scr .x0 sInner ++ ([.ldrSp .x1 fBl] : List Instr) ++ fr .x2 fV ++ ([.ldrSp .x3 fDl] : List Instr) ++
    scr .x4 sWork

/-- The arguments of the streaming `update` with the message: the inner
state, the `B + D` bytes it holds, the message's `len` bytes, the working
space. -/
def updMArgs (len : Nat) : List Instr :=
  scr .x0 sInner ++ ([.ldrSp .x1 fBl, .ldrSp .x9 fDl, .add .x .x1 .x1 .x9] : List Instr) ++
    scr .x2 sMsg ++ ([.movz .x .x3 (BitVec.ofNat 16 len) 0] : List Instr) ++ scr .x4 sWork

/-- The arguments of HMAC's `finalize`: the states, the `B + D + len` bytes
the inner one holds, the MAC's place in the frame, the working space. -/
def finArgs (len dst : Nat) : List Instr :=
  scr .x0 sInner ++ scr .x1 sOuter ++
    ([.ldrSp .x2 fBl, .ldrSp .x9 fDl, .add .x .x2 .x2 .x9, .addImm .x .x2 .x2 len] : List Instr) ++
    fr .x3 dst ++ scr .x4 sWork

/-- HMAC's states for `K`, by `init`. -/
def initK : Prog isa := .seq (.block initArgs) (tcall 0 c.f.init)

/-- The inner state updated with `V`. -/
def updV : Prog isa := .seq (.block updVArgs) (tcall 1 c.f.upd)

/-- The inner state updated with the message's `len` bytes. -/
def updM (len : Nat) : Prog isa := .seq (.block (updMArgs len)) (tcall 1 c.f.upd)

/-- The MAC, of `D + len` bytes of text, to the frame at `dst`. -/
def fin (len dst : Nat) : Prog isa := .seq (.block (finArgs len dst)) (tcall 2 c.f.fin)

/-- The `8 k` bytes at `[src + so]` to `[dst + d]`, a word at a time through
`x11`. -/
def copyN (k : Nat) (src : Reg) (so : Nat) (dst : Reg) (d : Nat) : List Instr :=
  (List.range k).flatMap fun j => [.ldr .x .x11 src (so + 8 * j), .str .x .x11 dst (d + 8 * j)]

/-- The `len` bytes at `[src]` to `[dst]` (`8 ≤ len`), a word at a time
through `x11`: `copyN` for the whole words, then the last eight bytes again,
through `x13` and `x14`, if `len` is not a multiple of 8 (an 8-byte load's
offset is a multiple of 8). -/
def copyBytes (len : Nat) (src dst : Reg) : List Instr :=
  copyN (len / 8) src 0 dst 0 ++
    (if len % 8 = 0 then []
    else [.addImm .x .x13 src (len - 8), .addImm .x .x14 dst (len - 8), .ldr .x .x11 .x13 0,
      .str .x .x11 .x14 0])

/-- A byte of `[x11]` to `[x12]`, through `x10`, both pointers advanced and
the count in `x13` one less. -/
def cpBody : List Instr :=
  [.ldrb .x10 .x11 0, .strb .x10 .x12 0, .addImm .x .x11 .x11 1, .addImm .x .x12 .x12 1, .subImm .x .x13 .x13 1]

/-- The `x13` bytes at `x11` to `x12` (`x13 > 0`), a byte at a time. -/
def cpLoop : Prog isa := .loop (.block cpBody) (.nonzero .x .x13)

/-- The arguments of the copy of HMAC's two states (384 bytes) from
`scratch + sInner` to `scratch + sSave` (`toSave`) or back, with `scratch`
in `x9`: the source in `x11`, the destination in `x12`, the count in `x13`. -/
def copyArgs (toSave : Bool) : List Instr :=
  if toSave then [.addImm .x .x11 .x9 sInner, .addImm .x .x12 .x9 sSave, .movz .x .x13 (BitVec.ofNat 16 384) 0]
  else [.addImm .x .x11 .x9 sSave, .addImm .x .x12 .x9 sInner, .movz .x .x13 (BitVec.ofNat 16 384) 0]

/-- The states for `K` saved, by `cpLoop`. -/
def save : Prog isa := .seq (.block (scrPtr ++ copyArgs true)) cpLoop

/-- The states for `K` restored from the copy, by `cpLoop`. -/
def restore : Prog isa := .seq (.block (scrPtr ++ copyArgs false)) cpLoop

/-- `V = HMAC_K(V)`, saving the states for `K`. -/
def hmacVS : Prog isa := .seq c.initK (.seq save (.seq c.updV (c.fin 0 fV)))

/-- `V = HMAC_K(V)`, from the saved states for `K`. -/
def hmacVR : Prog isa := .seq restore (.seq c.updV (c.fin 0 fV))

/-- `K = HMAC_K(V ‖ msg)`, for the message's `len` bytes, from the states
for `K` by `init` (`fresh`) or restored. -/
def hmacK (fresh : Bool) (len : Nat) : Prog isa :=
  .seq (if fresh then c.initK else restore) (.seq c.updV (.seq (c.updM len) (c.fin len fK)))

/-- The pointers the messages need: `scratch` in `x9`, `d` in `x10`, the
frame in `x15`. -/
def msgPtrs : List Instr := [.ldrSp .x9 fScratch, .ldrSp .x10 fD, .addSp .x15 0]

/-- The message `b` (and `‖ d ‖ h` if `full`, `Q` bytes each) at
`scratch + sMsg`, with `scratch` in `x9`, `d` in `x10` and the frame in
`x15`: `b` a byte, then the private key and `h` from the frame, through
`x12` (which points after `b`), and `x13` and `x14`, as an 8-byte store's
offset is a multiple of 8. -/
def msg (b : Nat) (full : Bool) : List Instr :=
  ([.movz .x .x11 (BitVec.ofNat 16 b) 0, .strb .x11 .x9 sMsg] : List Instr) ++
    (if full then
      .addImm .x .x12 .x9 (sMsg + 1) :: copyBytes c.len .x10 .x12 ++
        ([.addImm .x .x13 .x15 c.fHo, .addImm .x .x14 .x12 c.len] : List Instr) ++ copyBytes c.len .x13 .x14
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

/-- Nine zero words at `sp + o`, through `x15` and `x14`. -/
def zero9 (o : Nat) : List Instr :=
  ([.addSp .x15 0, .movz .x .x14 0 0] : List Instr) ++ (List.range 9).map fun j => .str .x .x14 .x15 (o + 8 * j)

/-- The arguments of `X`'s copy: `X` cleared; then `x13 = min(D, Q)`, the
digest in `x11` and `X + Q - x13` in `x12`. -/
def xArgs : List Instr :=
  zero9 fX ++
    ([.ldrSp .x13 fDl, .movz .x .x9 (BitVec.ofNat 16 c.len) 0, .subs .x .x10 .x13 .x9, .csel .x .x13 .x9 .x13,
      .addSp .x12 (fX + c.len), .sub .x .x12 .x12 .x13, .ldrSp .x11 fDigest] : List Instr)

/-- `X`: `Q - min(D, Q)` zero bytes, then the digest's leftmost `min(D, Q)`. -/
def prepX : Prog isa := .seq (.block c.xArgs) cpLoop

/-- The 64-bit words of `n`, least significant first. -/
def nWord (j : Nat) : BitVec 64 := BitVec.ofNat 64 (c.n >>> (64 * j))

/-- Where the words of the number `X` (at `x1`) are loaded from, and those
of `h` stored to (from the frame in `x15`): `x1` and `x15`, or, if `Q` is not
a multiple of 8, `x13 = X + Q % 8` and `x14 = sp + Q % 8`, so that each
8-byte access's offset is a multiple of 8. -/
def dgBase : Reg := if c.len % 8 = 0 then .x1 else .x13

/-- Where the words of `h` are stored from (see `dgBase`). -/
def hBase : Reg := if c.len % 8 = 0 then .x15 else .x14

/-- Word `j` of the `Q`-byte number at `x1`, least significant first, in
`x8`: the byte reversal of the word at `x1 + Q - 8 (j + 1)`, or, for a top
word of four bytes (`Q % 8 = 4`), of the first four, zero-extended. -/
def loadWord (j : Nat) : List Instr :=
  if 8 * (j + 1) ≤ c.len then [.ldr .x .x8 c.dgBase (c.len - c.len % 8 - 8 * (j + 1)), .rev .x8 .x8]
  else if c.len ≤ 8 * j then [.movz .x .x8 0 0]
  else [.ldr .w .x8 .x1 0, .rev32 .x8 .x8]

/-- Word `j` of the number at `x1`, least significant first, to `V`'s
place, and word `j` of it minus `n` (with the borrow of the words before)
to `K`'s, with the frame in `x15`: `x8`, `x2` and `x12` change, and the
borrow is the carry flag (clear if it borrowed). -/
def subWord (j : Nat) : List Instr :=
  c.loadWord j ++ ([.str .x .x8 .x15 (fV + 8 * j)] : List Instr) ++
    const64 .x12 (c.nWord j) ++
    [if j = 0 then .subs .x .x2 .x8 .x12 else .sbcs .x .x2 .x8 .x12, .str .x .x2 .x15 (fK + 8 * j)]

/-- Word `j` of the result, by the mask `x6` (all ones if subtracting `n`
borrowed): the number's word if so, the difference's if not, big-endian to
`h + Q - 8 (j + 1)`. A top word of fewer bytes is stored partly below `h`,
in the word there, its zero bytes there and the rest `h`'s first bytes. -/
def selWord (j : Nat) : List Instr :=
  [.ldr .x .x8 .x15 (fV + 8 * j), .ldr .x .x2 .x15 (fK + 8 * j),
    -- `x = d ^ ((x ^ d) & mask)`: `x` if it borrowed, `d` if not.
    .logic .eor .x .x8 .x8 .x2, .logic .and .x .x8 .x8 .x6, .logic .eor .x .x8 .x8 .x2,
    .rev .x8 .x8, .str .x .x8 c.hBase (fH + c.len - c.len % 8 - 8 * (j + 1))]

/-- `h`, unless `big`: `X` (at `x1`), as a big-endian number, minus `n` if
that does not borrow, big-endian into the frame's `Q` bytes at `h`. -/
def reduce : List Instr :=
  ([.addSp .x1 fX, .movz .x .x7 0 0, .addSp .x15 0] : List Instr) ++
    (if c.len % 8 = 0 then [] else [.addImm .x .x13 .x1 (c.len % 8), .addImm .x .x14 .x15 (c.len % 8)]) ++
    (List.range c.w).flatMap c.subWord ++ ([.sbc .x .x6 .x7 .x7] : List Instr) ++
    (List.range c.w).flatMap c.selWord

/-- `conv`'s block, with `scratch` in `x0`. -/
def convB (o s : Nat) : List Instr :=
  .addSp .x6 o :: Impl.Weierstrass.AArch64.loadBytes c.len c.w sSlot .x6 ++
    Impl.Weierstrass.AArch64.shrWords c.w sSlot s ++
    ([.movz .x .x3 0 0, .subImm .x .x3 .x3 1] : List Instr) ++ Impl.Weierstrass.AArch64.storeBytes c.len c.w .x6 0 sSlot

/-- The `Q` bytes at `sp + o`, as a big-endian number, shifted right by `s`
bits in place (`0 < s < 64`), through the words at `scratch + sSlot`, with
`scratch` in `x0` (loaded first) and `sp + o` in `x6`. -/
def conv (o s : Nat) : Prog isa := .seq (.block [.ldrSp .x0 fScratch]) (.block (c.convB o s))

/-- The arguments of the copy of `core`'s digest, if `big`: it cleared;
then `x13 = D`, the digest in `x11` and `fXc + Q - 1 - D` in `x12`. -/
def xcArgs : List Instr :=
  zero9 fXc ++
    ([.ldrSp .x13 fDl, .addSp .x12 (fXc + c.len - 1), .sub .x .x12 .x12 .x13, .ldrSp .x11 fDigest] : List Instr)

/-- If `big`: `core`'s digest, `Q - 1 - D` zero bytes, the digest and a zero
byte, shifted right by `8 - sh` bits: the digest's integer shifted left by
`sh` bits. -/
def prepC : Prog isa := .seq (.block c.xcArgs) (.seq cpLoop (c.conv fXc (8 - c.sh)))

/-- `h`: `reduce`, or, if `big`, `X` itself, with `core`'s digest. -/
def prepH : Prog isa := if c.big then c.prepC else .block c.reduce

/-- `V = 0x01…`, `K = 0x00…`, all 64 bytes of each. -/
def initKV : List Instr :=
  const64 .x9 (BitVec.ofNat 64 0x0101010101010101) ++ ([.movz .x .x10 0 0, .addSp .x15 0] : List Instr) ++
    (List.range 8).flatMap fun j => [.str .x .x9 .x15 (fV + 8 * j), .str .x .x10 .x15 (fK + 8 * j)]

/-- The candidates left. -/
def initCnt : List Instr :=
  [.movz .x .x9 (BitVec.ofNat 16 c.tries) 0, .addSp .x15 0, .str .x .x9 .x15 fCnt]

/-! ## The candidates -/

/-- `T` empty. -/
def tInit : List Instr := [.movz .x .x9 0 0, .addSp .x15 0, .str .x .x9 .x15 fTlen]

/-- The arguments of `V`'s copy to the end of `T`: `x13 = D`, `V` in `x11`
and `T + |T|` in `x12`. -/
def keepArgs : List Instr :=
  [.addSp .x11 fV, .addSp .x12 fT, .ldrSp .x9 fTlen, .add .x .x12 .x12 .x9, .ldrSp .x13 fDl]

/-- `T` longer by `D` bytes, and `x12` nonzero iff it is still shorter than
`Q`: all ones if `|T| - Q` borrows. -/
def tStep : List Instr :=
  [.ldrSp .x9 fTlen, .ldrSp .x10 fDl, .add .x .x9 .x9 .x10, .addSp .x15 0, .str .x .x9 .x15 fTlen,
    .movz .x .x10 (BitVec.ofNat 16 c.len) 0, .subs .x .x12 .x9 .x10, .sbc .x .x12 .x12 .x12]

/-- One `V` of the candidate: `V = HMAC_K(V)`, appended to `T`. -/
def candStep : Prog isa := .seq c.hmacVR (.seq (.block keepArgs) (.seq cpLoop (.block c.tStep)))

/-- If `big`: `T`'s first `Q` bytes shifted right by `sh` bits. -/
def candTop : Prog isa := if c.big then c.conv fT c.sh else .block []

/-- The candidate: `T`, the `V`s of successive `V = HMAC_K(V)` while it is
shorter than `Q` bytes, its leftmost `Q` bytes shifted right by `sh` bits if
`big`. -/
def cand : Prog isa := .seq (.block tInit) (.seq (.loop c.candStep (.nonzero .x .x12)) c.candTop)

/-- `core(out, d, digest, k, scratch)`: the digest `X` (or, if `big`, the
one at `fXc`) and `k = T`. -/
def coreArgs : List Instr :=
  ([.ldrSp .x0 fOut, .ldrSp .x1 fD] : List Instr) ++ fr .x2 c.fDg ++ fr .x3 fT ++ ([.ldrSp .x4 fScratch] : List Instr)

/-- One candidate fewer, and `x12 ≠ 0` iff the signature failed (`w0 = 0`)
and candidates are left: `x12 = -(w0 < 1) & (count - 1)`. -/
def goOn : List Instr :=
  [.ldrSp .x9 fCnt, .subImm .x .x9 .x9 1, .addSp .x15 0, .str .x .x9 .x15 fCnt,
    .movz .x .x7 0 0, .movz .x .x10 1 0, .subs .w .x16 .x0 .x10, .sbc .x .x11 .x7 .x7,
    .logic .and .x .x12 .x11 .x9]

/-- Go on. -/
def again : List Instr := [.movz .x .x12 1 0]

/-- Stop. -/
def stop : List Instr := [.movz .x .x12 0 0]

/-- One candidate: `cand`, `core` with it, then, if it failed and candidates
are left, step h.3. -/
def tryOne : Prog isa :=
  .seq c.cand
  (.seq (.block c.coreArgs)
  (.seq (.call c.coreN c.coreC)
  (.seq (.block goOn)
    (.ite (.nonzero .x .x12) (.seq c.rekey (.block again)) (.block stop)))))

/-- `K` and `V` cleared, and the words above the pointers but `D` and `B`
(`x0`, the result, kept). -/
def wipe : List Instr :=
  ([.addSp .x15 0, .movz .x .x14 0 0] : List Instr) ++ (List.range 16).map (fun j => .str .x .x14 .x15 (8 * j)) ++
    (List.range (extra - 2)).map fun j => .str .x .x14 .x15 (fBl + 8 + 8 * j)

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block saveArgs)
  (.seq c.prepX
  (.seq c.prepH
  (.seq (.block initKV)
  (.seq (c.rekeyFull 0)
  (.seq (c.rekeyFull 1)
  (.seq (.block c.initCnt)
  (.seq (.loop c.tryOne (.nonzero .x .x12))
    (.block wipe))))))))

/-- The frame. -/
def sign : Prog isa :=
  .frame (.push .x30) (.frame (.alloc frameBytes) c.body (.free frameBytes)) (.pop .x30)

end Cfg

/-- `D` and `B`, the table's words of data 4 and 5, to `x6` and `x7`. -/
def entry : List Instr := [.ldr .x .x6 .x5 32, .ldr .x .x7 .x5 40]

/-- `vg_ecdsa_<curve>_sign`. -/
def signCode (c : Cfg) : Prog isa := .seq (.block entry) c.sign

end VG.Impl.Ecdsa.Rfc6979.AArch64
