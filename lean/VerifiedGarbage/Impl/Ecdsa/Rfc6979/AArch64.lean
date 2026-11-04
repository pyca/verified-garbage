module

public import VerifiedGarbage.Impl.RsaOaep.AArch64.Mgf1.Table
public import VerifiedGarbage.Impl.Weierstrass.AArch64

/-!
# Deterministic ECDSA (RFC 6979) on AArch64, with the hash function of a table

`vg_ecdsa_<curve>_sign(out = x0, d = x1, digest = x2, digest_len = x3,
scratch = x4, hash = x5) -> w0` (`signT`), as on x86-64
(`Impl/Ecdsa/Rfc6979/X86_64.lean`): for a curve of `Q`-byte scalars in `w`
64-bit words, RFC 6979 §3.2 with HMAC over the hash function of the table
`hash` of the interface `Hash` (`Spec/HashTable.lean`), whose streaming
`init`, `update` and `finalize` (its words 0 to 2) it calls indirectly
(`tcall`: their address into `x16`, then `blr x16`), and each candidate
tried by calling `core`, the signature with a given `k`
(`vg_ecdsa_<curve>_sign_k`), which reads `Q` bytes of the digest and of `k`,
and takes the digest's leftmost `qlen` bits (`bits2int`, a right shift by
`sh = 8 Q - qlen` bits).

Which table `hash` is, is public (`Abi.withTables`), and so is the hash
function's index in `Mgf1.hashes`, its word 3: `signT` chooses by it
(`byIdx`, a comparison with each index of `idxs`, `cbz` of the difference)
the code for that hash function's digest length `D` and block size `B`
(`shapeOf`), `sign` of a `Cfg`, in which both are constants. Everything
below is that code.

HMAC (`hmac`) is computed from the table's streaming functions: the key `K`
(`D` bytes, in the frame) padded to a block and XORed with `ipad` (`padBlk`,
a 32-bit word at a time, into `scratch + sPad`), the inner state set by
`init` and updated with it, the same with `opad` for the outer state
(`hinit`); the inner state updated with the data (`hupd`); then the inner
state finalized into `scratch + sTmp`, the outer one updated with that
digest and finalized there too, and its first `D` bytes copied to the MAC's
place in the frame (`hfin`).

Two kinds of curve and hash function:

* `Q ≤ D` (and `qlen = 8 Q`, the scalars' words full or the top one of four
  bytes): one `V` makes a candidate, its leftmost `Q` bytes; `bits2octets`
  is a conditional subtraction of `n` from the digest's leftmost `Q` bytes
  (`reduce`); and `core` reads the digest and `V` in place.
* `D < Q` (`wide`): `m` `V`s make a candidate `T` (`candW`), at the frame's
  top at `fT`, of which `core` reads the first `Q` bytes, shifted right in
  place by `sh` bits; the digest's integer is below `n`, so
  `h = bits2octets(digest)` is `Q - D` zero bytes then the digest (`hPrep`,
  at `fX`); and `core` reads `h`, or, if `sh ≠ 0` (P-521), the digest's
  integer shifted left by `sh` bits (`xPrep`, at `fXc`: `Q - D - 1` zero
  bytes, the digest and a zero byte, shifted right by `8 - sh` bits). The
  shifts are through the 64-bit words at `scratch + sSlot` (`conv`, with
  `scratch` in `x0`).

The return address `x30` is pushed (the calls replace it), then a frame of
`224 + extra` bytes is allocated: from `sp`, `K` and `V` (64 bytes each, of
which the first `D` are used), `h` (`bits2octets`, in 48 bytes, unless
`wide` or `hHigh`), the number of candidates left, then `scratch`, `digest`,
`d`, `out` and the table's address; and, if `wide`, `h`, the digest for
`core` and `T` (72, 72 and 128 bytes), or, if `hHigh` (64-byte scalars, as
brainpoolP512r1's), `h` in 64 bytes. The calls use only `scratch`, which
`core` overwrites entirely, and the 16 bytes below the frame (the streaming
functions'); `K`, `V`, `h` and the bytes at the frame's top are cleared
before the frame is freed. In `scratch`: HMAC's inner and outer streaming
states, the working space of the streaming functions, the padded key and
the inner digest, the message of steps d, f and h.3, and the words of a
shift.

1. `h = bits2octets(digest)`: unless `wide`, the leftmost `Q` bytes, minus
   `n` if they are at least `n` (a conditional subtraction, as
   `2^(8 Q) < 2n`), a word at a time through memory: the words of the digest
   to `V`'s place, those of the difference to `K`'s (before steps b and c set
   them), and the one the borrow selects, big-endian, to `h` (a top word of
   four bytes by 32-bit loads, and stored ending at `h`'s fourth byte, its
   zero bytes in `V`'s place, which step b then sets). If `wide`, `hPrep`
   and `xPrep`.
2. Steps b to g: `V = 0x01…`, `K = 0x00…`, `K = HMAC_K(V ‖ 0x00 ‖ d ‖ h)`,
   `V = HMAC_K(V)`, `K = HMAC_K(V ‖ 0x01 ‖ d ‖ h)`, `V = HMAC_K(V)`.
3. At most `tries` times: `V = HMAC_K(V)` (`m` times, each copied to `T`, if
   `wide`), the candidate `k`, and `core(out, d, digest, k, scratch)`; if it
   failed and candidates are left, `K = HMAC_K(V ‖ 0x00)`, `V = HMAC_K(V)`
   and again. Whether to go on, in `x12`, is computed without branches, so
   that the code branches only on it: the number of candidates tried is all
   it reveals.

`core` writes the signature or zeros to `out`, and its return value is ours.

A block addresses memory only at `sp` (directly, or through `x15`, set by
`addSp`) or at a pointer an earlier block loaded from the frame
(`digestPtr`, `msgPtrs`, `scrPtr`, the table's address in `tcall`), never
one it loads itself, so that the taint analysis of each block knows its
addresses are public. The blocks that depend on the hash function depend
only on `D` and `B`, so that the taint analysis checks them for each size.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Rfc6979.AArch64

open VG.AArch64
open VG.Impl.Mont.AArch64 (const64)
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)

/-! Where things are in the frame. -/
def fK : Nat := 0
def fV : Nat := 64
def fH : Nat := 128
def fCnt : Nat := 176
def fScratch : Nat := 184
def fDigest : Nat := 192
def fD : Nat := 200
def fOut : Nat := 208
/-- The table's address. -/
def fTab : Nat := 216
/-- At the frame's top: `h`, if `wide` or `hHigh`. -/
def fX : Nat := 224
/-- If `wide`: the digest for `core`, if `sh ≠ 0`. -/
def fXc : Nat := 296
/-- If `wide`: the candidate `T`. -/
def fT : Nat := 368

/-! Where things are in `scratch`. -/
def sInner : Nat := 0
def sOuter : Nat := 192
def sWork : Nat := 384
/-- The padded key, `K₀ ⊕ ipad` or `K₀ ⊕ opad`. -/
def sPad : Nat := 1792
/-- What the streaming `finalize` writes. -/
def sTmp : Nat := 1920
def sMsg : Nat := 2256
/-- The words of a conversion, if `wide`. -/
def sSlot : Nat := 2560

/-- `ipad` and `opad` (RFC 2104), in each byte of a 32-bit word. -/
def ipad32 : BitVec 32 := 0x36363636
def opad32 : BitVec 32 := 0x5c5c5c5c

/-- What the code needs of a curve and a hash function. -/
structure Cfg where
  /-- The hash function's digest length and block size. -/
  D : Nat
  B : Nat
  /-- The functions an indirect call of a table's functions may reach. -/
  f : Fns
  /-- The 64-bit words of the curve's scalars. -/
  w : Nat
  /-- The bytes of the curve's scalars, `Q`. -/
  len : Nat := 8 * w
  /-- The bits `core` shifts its digest right by, `8 Q - qlen`. -/
  sh : Nat := 0
  /-- Whether `h` is kept at the frame's top, in 64 more bytes: for scalars
  of 64 bytes, which the 48 bytes below the pointers do not hold (and the
  hash is no shorter). -/
  hHigh : Bool := false
  /-- The order of the curve's base point. -/
  n : Nat
  /-- The most candidates to try. -/
  tries : Nat
  /-- The signature with a given `k`, and its name. -/
  coreN : String
  coreC : Prog isa

namespace Cfg

variable (c : Cfg)

/-- Whether the hash is shorter than the scalars. -/
def wide : Bool := decide (c.D < c.len)

/-- The number of `V`s in a candidate: the least `m` with `8 D m ≥ qlen`. -/
def m : Nat := (8 * c.len - c.sh + 8 * c.D - 1) / (8 * c.D)

/-- The bytes at the frame's top. -/
def extra : Nat := if c.wide then 272 else if c.hHigh then 64 else 0

/-- The frame's size, a multiple of 16. -/
def frameBytes : Nat := 224 + c.extra

/-- Where `h` is in the frame. -/
def fHo : Nat := if c.wide || c.hHigh then fX else fH

/-- `d ← scratch + a`: an address in `scratch`. -/
def scr (d : Reg) (a : Nat) : List Instr := [.ldrSp d fScratch, .addImm .x d d a]

/-- `d ← sp + o`: an address in the frame. -/
def fr (d : Reg) (o : Nat) : List Instr := [.addSp d o]

/-- `scratch` in `x9`. -/
def scrPtr : List Instr := [.ldrSp .x9 fScratch]

/-- `out`, `d`, `digest`, `scratch` and the table's address into the frame. -/
def saveArgs : List Instr :=
  [.addSp .x15 0, .str .x .x0 .x15 fOut, .str .x .x1 .x15 fD, .str .x .x2 .x15 fDigest,
    .str .x .x4 .x15 fScratch, .str .x .x5 .x15 fTab]

/-! ## HMAC through the table -/

/-- The indirect call of the table's function `j`, among `ts`: the table's
address into `x16`, its word `j` into `x16`, then `blr x16`. -/
def tcall (j : Nat) (ts : List (String × Prog isa)) : Prog isa :=
  .seq (.block [.ldrSp .x16 fTab]) (.seq (.block [.ldr .x .x16 .x16 (8 * j)]) (Code.icalls (.blr .x16) ts))

/-- The streaming `init` of the state at `scratch + o`. -/
def initCall (o : Nat) : Prog isa := .seq (.block (scr .x0 o)) (tcall 0 c.f.init)

/-- The arguments of the streaming `update` of the state at `scratch + o`,
which holds `cnt` bytes, with the data (at the address `dataA` sets `x2`
to) of `len` bytes, and the working space. -/
def updArgs (o cnt : Nat) (dataA : List Instr) (len : Nat) : List Instr :=
  scr .x0 o ++ ([.movz .x .x1 (BitVec.ofNat 16 cnt) 0] : List Instr) ++ dataA ++
    ([.movz .x .x3 (BitVec.ofNat 16 len) 0] : List Instr) ++ scr .x4 sWork

def updCall (o cnt : Nat) (dataA : List Instr) (len : Nat) : Prog isa :=
  .seq (.block (updArgs o cnt dataA len)) (tcall 1 c.f.upd)

/-- The arguments of the streaming `finalize` of the state at `scratch + o`,
which holds `cnt` bytes, into `scratch + sTmp`, with the working space. -/
def finArgs (o cnt : Nat) : List Instr :=
  scr .x0 o ++ ([.movz .x .x1 (BitVec.ofNat 16 cnt) 0] : List Instr) ++ scr .x2 sTmp ++ scr .x3 sWork

def finCall (o cnt : Nat) : Prog isa := .seq (.block (finArgs o cnt)) (tcall 2 c.f.fin)

/-- Word `k` of the key `K` (the frame's first `D` bytes, the frame in
`x15`) padded to `B` bytes, XORed with the pad in `w10`, to
`scratch + sPad` (`scratch` in `x9`). -/
def padW (k : Nat) : List Instr :=
  if k < c.D / 4 then
    [.ldr .w .x11 .x15 (fK + 4 * k), .logic .eor .w .x11 .x11 .x10, .str .w .x11 .x9 (sPad + 4 * k)]
  else [.str .w .x10 .x9 (sPad + 4 * k)]

/-- `K₀ ⊕ pad`, with `scratch` in `x9`. -/
def padBody (x : BitVec 32) : List Instr :=
  ([.addSp .x15 0, .movz .x .x10 (x.extractLsb' 0 16) 0, .movk .x .x10 (x.extractLsb' 16 16) 1] : List Instr) ++
    (List.range (c.B / 4)).flatMap c.padW

/-- `K₀ ⊕ pad` (a block) at `scratch + sPad`. -/
def padBlk (x : BitVec 32) : List Instr := scrPtr ++ c.padBody x

/-- HMAC's states for the key `K`: each set by `init`, then updated with
the padded key. -/
def hinit : Prog isa :=
  .seq (c.initCall sInner) (.seq (c.initCall sOuter)
  (.seq (.block (c.padBlk ipad32)) (.seq (c.updCall sInner 0 (scr .x2 sPad) c.B)
  (.seq (.block (c.padBlk opad32)) (c.updCall sOuter 0 (scr .x2 sPad) c.B)))))

/-- The inner state updated with `len` bytes of data at the address `dataA`
sets `x2` to. -/
def hupd (dataA : List Instr) (len : Nat) : Prog isa := c.updCall sInner c.B dataA len

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

/-- The digest at `scratch + sTmp` (`scratch` in `x9`) to the frame at `dst`
(the frame in `x15`). -/
def copyOut (dst : Nat) : List Instr :=
  ([.addSp .x15 0, .addImm .x .x13 .x9 sTmp, .addImm .x .x14 .x15 dst] : List Instr) ++ copyBytes c.D .x13 .x14

/-- The MAC, for `len` bytes of data, to the frame at `dst`: the inner state
finalized, the outer one updated with that digest and finalized, and its
first `D` bytes copied. -/
def hfin (len dst : Nat) : Prog isa :=
  .seq (c.finCall sInner (c.B + len)) (.seq (c.updCall sOuter c.B (scr .x2 sTmp) c.D)
  (.seq (c.finCall sOuter (c.B + c.D)) (.block (scrPtr ++ c.copyOut dst))))

/-- `HMAC_K(data)` into the frame at `dst`, for `len` bytes of `data` at the
address `dataA` sets `x2` to. -/
def hmac (dataA : List Instr) (len dst : Nat) : Prog isa :=
  .seq c.hinit (.seq (c.hupd dataA len) (c.hfin len dst))

/-- `V = HMAC_K(V)`. -/
def hmacV : Prog isa := c.hmac (fr .x2 fV) c.D fV

/-- The pointers the messages need: `scratch` in `x9`, `d` in `x10` and the
frame in `x15`. -/
def msgPtrs : List Instr := [.ldrSp .x9 fScratch, .ldrSp .x10 fD, .addSp .x15 0]

/-- `V`'s `D` bytes from the frame (in `x15`) to `scratch + sMsg` (`scratch`
in `x9`): a word at a time, or, if `D` is not a multiple of 8, through `x13`
and `x14` (`copyBytes`). -/
def copyV (D : Nat) : List Instr :=
  if D % 8 = 0 then copyN (D / 8) .x15 fV .x9 sMsg
  else ([.addImm .x .x13 .x15 fV, .addImm .x .x14 .x9 sMsg] : List Instr) ++ copyBytes D .x13 .x14

/-- `d` (from `x10`) and `h` (from the frame, in `x15`, at `ho`), `Q` bytes
each, to `x12`: `w` words each when the encoding fills them, otherwise
`copyBytes` (`h`'s through `x13` and `x14`). -/
def copyDH (w Q : Nat) (ho : Nat := fH) : List Instr :=
  if Q % 8 = 0 ∧ Q = 8 * w then copyN w .x10 0 .x12 0 ++ copyN w .x15 ho .x12 (8 * w)
  else copyBytes Q .x10 .x12 ++ ([.addImm .x .x13 .x15 ho, .addImm .x .x14 .x12 Q] : List Instr) ++ copyBytes Q .x13 .x14

/-- The message `V ‖ b` (and `‖ d ‖ h` if `full`, `Q` bytes each) at
`scratch + sMsg`, for `V` of `D` bytes, with `scratch` in `x9`, `d` in `x10`
and the frame in `x15`: `V` from the frame, `b` a byte, `d`, and `h` from the
frame at `ho`, `d ‖ h` through `x12`, which points after `b`. -/
def msg (w Q D b : Nat) (full : Bool) (ho : Nat := fH) : List Instr :=
  copyV D ++
    ([.movz .x .x11 (BitVec.ofNat 16 b) 0, .strb .x11 .x9 (sMsg + D)] : List Instr) ++
    (if full then .addImm .x .x12 .x9 (sMsg + D + 1) :: copyDH w Q ho else [])

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
def rekeyFull (b : Nat) : Prog isa :=
  .seq (.block msgPtrs) (.seq (.block (msg c.w c.len c.D b true c.fHo))
    (.seq (c.hmac (scr .x2 sMsg) (c.D + 2 * c.len + 1) fK) c.hmacV))

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
def rekey : Prog isa :=
  .seq (.block msgPtrs) (.seq (.block (msg c.w c.len c.D 0 false))
    (.seq (c.hmac (scr .x2 sMsg) (c.D + 1) fK) c.hmacV))

/-- The `Q` bytes at `sp + o`, as a big-endian number, shifted right by `s`
bits in place (`0 < s < 64`), through the words at `scratch + sSlot`, with
`scratch` in `x0` and `sp + o` in `x6`. -/
def convB (o s : Nat) : List Instr :=
  .addSp .x6 o :: Impl.Weierstrass.AArch64.loadBytes c.len c.w sSlot .x6 ++
    Impl.Weierstrass.AArch64.shrWords c.w sSlot s ++
    ([.movz .x .x3 0 0, .subImm .x .x3 .x3 1] : List Instr) ++ Impl.Weierstrass.AArch64.storeBytes c.len c.w .x6 0 sSlot

/-- `convB`, with `scratch` loaded into `x0` first. -/
def conv (o s : Nat) : Prog isa := .seq (.block [.ldrSp .x0 fScratch]) (.block (c.convB o s))

/-- Nine zero words at `sp + o` (the frame in `x15`), through `x11`. -/
def zero9 (o : Nat) : List Instr :=
  .movz .x .x11 0 0 :: (List.range 9).map fun j => .str .x .x11 .x15 (o + 8 * j)

/-- If `wide`: `h`, `Q - D` zero bytes then the digest (at `x1`), at `fX`. -/
def hPrep : List Instr :=
  .addSp .x15 0 :: zero9 fX ++ ([.addImm .x .x14 .x15 (fX + c.len - c.D)] : List Instr) ++ copyBytes c.D .x1 .x14

/-- If `wide` and `sh ≠ 0`: the digest for `core`, `Q - D - 1` zero bytes,
the digest (at `x1`) and a zero byte, shifted right by `8 - sh` bits: the
digest's integer shifted left by `sh` bits, at `fXc` (`scratch` in `x0`). -/
def xPrep : List Instr :=
  if c.sh = 0 then [] else
    zero9 fXc ++ ([.addImm .x .x14 .x15 (fXc + c.len - c.D - 1)] : List Instr) ++ copyBytes c.D .x1 .x14 ++
      c.convB fXc (8 - c.sh)

/-- The 64-bit words of `n`, least significant first. -/
def nWord (j : Nat) : BitVec 64 := BitVec.ofNat 64 (c.n >>> (64 * j))

/-- `digest` in `x1`, and, if `wide`, `scratch` in `x0`. -/
def digestPtr : List Instr := ([.ldrSp .x1 fDigest] : List Instr) ++ (if c.wide then [.ldrSp .x0 fScratch] else [])

/-- Where the words of the number at `digest` (in `x1`) are loaded from,
and those of `h` stored to (from the frame in `x15`): `x1` and `x15`, or, if
`Q` is not a multiple of 8, `x13 = digest + Q % 8` and `x14 = sp + Q % 8`,
so that each 8-byte access's offset is a multiple of 8. -/
def dgBase : Reg := if c.len % 8 = 0 then .x1 else .x13

/-- Where the words of `h` are stored from (see `dgBase`). -/
def hBase : Reg := if c.len % 8 = 0 then .x15 else .x14

/-- Word `j` of the `Q`-byte number at `digest`, least significant first, in
`x8`: the byte reversal of the word at `digest + Q - 8 (j + 1)`, or, for a
top word of four bytes (`Q % 8 = 4`), of the first four, zero-extended. -/
def loadWord (j : Nat) : List Instr :=
  if 8 * (j + 1) ≤ c.len then [.ldr .x .x8 c.dgBase (c.len - c.len % 8 - 8 * (j + 1)), .rev .x8 .x8]
  else if c.len ≤ 8 * j then [.movz .x .x8 0 0]
  else [.ldr .w .x8 .x1 0, .rev32 .x8 .x8]

/-- Word `j` of the number at `digest` (in `x1`), least significant first,
to `V`'s place, and word `j` of it minus `n` (with the borrow of the words
before) to `K`'s, with the frame in `x15`: `x8`, `x2` and `x12` change, and
the borrow is the carry flag (clear if it borrowed). -/
def subWord (j : Nat) : List Instr :=
  c.loadWord j ++ ([.str .x .x8 .x15 (fV + 8 * j)] : List Instr) ++
    const64 .x12 (c.nWord j) ++
    [if j = 0 then .subs .x .x2 .x8 .x12 else .sbcs .x .x2 .x8 .x12, .str .x .x2 .x15 (fK + 8 * j)]

/-- Word `j` of the result, by the mask `x6` (all ones if subtracting `n`
borrowed): the number's word if so, the difference's if not, big-endian to
`h + Q - 8 (j + 1)`. A top word of four bytes is stored below `h`, in `V`'s
place (which `initKV` then sets), its zero bytes there and the rest `h`'s
first bytes. -/
def selWord (j : Nat) : List Instr :=
  [.ldr .x .x8 .x15 (fV + 8 * j), .ldr .x .x2 .x15 (fK + 8 * j),
    -- `x = d ^ ((x ^ d) & mask)`: `x` if it borrowed, `d` if not.
    .logic .eor .x .x8 .x8 .x2, .logic .and .x .x8 .x8 .x6, .logic .eor .x .x8 .x8 .x2,
    .rev .x8 .x8, .str .x .x8 c.hBase (c.fHo + c.len - c.len % 8 - 8 * (j + 1))]

/-- `h`: the `Q` bytes at `digest` (in `x1`), as a big-endian number, minus
`n` if that does not borrow, big-endian into the frame's `Q` bytes at `h`. -/
def reduce : List Instr :=
  ([.movz .x .x7 0 0, .addSp .x15 0] : List Instr) ++
    (if c.len % 8 = 0 then [] else [.addImm .x .x13 .x1 (c.len % 8), .addImm .x .x14 .x15 (c.len % 8)]) ++
    (List.range c.w).flatMap c.subWord ++ ([.sbc .x .x6 .x7 .x7] : List Instr) ++
    (List.range c.w).flatMap c.selWord

/-- `V = 0x01…`, `K = 0x00…`, all 64 bytes of each. -/
def initKV : List Instr :=
  const64 .x9 (BitVec.ofNat 64 0x0101010101010101) ++ ([.movz .x .x10 0 0, .addSp .x15 0] : List Instr) ++
    (List.range 8).flatMap fun j => [.str .x .x9 .x15 (fV + 8 * j), .str .x .x10 .x15 (fK + 8 * j)]

/-- The candidates left. -/
def initCnt : List Instr :=
  [.movz .x .x9 (BitVec.ofNat 16 c.tries) 0, .addSp .x15 0, .str .x .x9 .x15 fCnt]

/-- Where `core` reads the digest, if `wide`: `h`, or the digest shifted
left by `sh` bits. -/
def fDg : Nat := if c.sh = 0 then fX else fXc

/-- `core(out, d, digest, k, scratch)`: `k = V`, or, if `wide`, the digest
and the candidate at the frame's top. -/
def coreArgs : List Instr :=
  ([.ldrSp .x0 fOut, .ldrSp .x1 fD] : List Instr) ++
    (if c.wide then fr .x2 c.fDg ++ fr .x3 fT else ([.ldrSp .x2 fDigest] : List Instr) ++ fr .x3 fV) ++
    ([.ldrSp .x4 fScratch] : List Instr)

/-- If `wide`: `V`'s `D` bytes to `T + j D`. -/
def keepV (j : Nat) : List Instr :=
  ([.addSp .x15 0, .addImm .x .x13 .x15 fV, .addImm .x .x14 .x15 (fT + j * c.D)] : List Instr) ++
    copyBytes c.D .x13 .x14

/-- If `wide`: `V = HMAC_K(V)` and its `D` bytes to `T + j D`, for each
`j < k`. -/
def candW : Nat → Prog isa
  | 0 => .block []
  | k + 1 => .seq (candW k) (.seq c.hmacV (.block (c.keepV k)))

/-- If `wide` and `sh ≠ 0`: `T`'s first `Q` bytes shifted right by `sh` bits. -/
def candTop : Prog isa := if c.sh = 0 then .block [] else c.conv fT c.sh

/-- The candidate: `V = HMAC_K(V)`, which is `k`; or, if `wide`, the
leftmost `Q` bytes of `m` successive `V = HMAC_K(V)`, shifted right by `sh`
bits. -/
def cand : Prog isa :=
  if c.wide then .seq (c.candW c.m) c.candTop else c.hmacV

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

/-- `K`, `V` and `h` cleared, and the bytes at the frame's top (`x0`, the
result, kept). -/
def wipe : List Instr :=
  ([.addSp .x15 0, .movz .x .x14 0 0] : List Instr) ++ (List.range 22).map (fun j => .str .x .x14 .x15 (8 * j)) ++
    (List.range (c.extra / 8)).map fun j => .str .x .x14 .x15 (fX + 8 * j)

/-- `h` (and, if `wide`, the digest for `core`), then `V = 0x01…`, `K = 0x00…`. -/
def prep : List Instr := (if c.wide then c.hPrep ++ c.xPrep else c.reduce) ++ initKV

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block saveArgs)
  (.seq (.block c.digestPtr)
  (.seq (.block c.prep)
  (.seq (c.rekeyFull 0)
  (.seq (c.rekeyFull 1)
  (.seq (.block c.initCnt)
  (.seq (.loop c.tryOne (.nonzero .x .x12))
    (.block c.wipe)))))))

/-- The signature for the hash function of this size. -/
def sign : Prog isa :=
  .frame (.push .x30) (.frame (.alloc c.frameBytes) c.body (.free c.frameBytes)) (.pop .x30)

end Cfg

/-! ## The choice by the hash function -/

/-- The indices in `Mgf1.hashes` of the hash functions with HMAC
(`Spec.Ecdsa.Rfc6979.hmacOf`): MD5, SHA-1, SHA-224, SHA-256, SHA-384,
SHA-512, SHA-512/224 and SHA-512/256. -/
def idxs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]

/-- The digest length and block size of the hash function of index `i`. -/
def shapeOf : Nat → Nat × Nat
  | 0 => (16, 64)
  | 1 => (20, 64)
  | 2 => (28, 64)
  | 3 => (32, 64)
  | 4 => (48, 128)
  | 5 => (64, 128)
  | 6 => (28, 128)
  | _ => (32, 128)

/-- `b i` for the index `i` in `x16`, by comparisons with each of `is`
(`x17 = x16 - i`, then `cbz x17`): the last is taken for every other value. -/
def byIdx (b : Nat → Prog isa) : List Nat → Prog isa
  | [] => .block []
  | [i] => b i
  | i :: is => .seq (.block [.subImm .x .x17 .x16 i]) (.ite (.zero .x .x17) (b i) (byIdx b is))

/-- The hash function's index (the table's word 3) to `x16`. -/
def entry : List Instr := [.ldr .x .x16 .x5 24]

/-- `vg_ecdsa_<curve>_sign`: the signature with the code `cfg i` for the
hash function of index `i` of the table `hash`. -/
def signT (cfg : Nat → Cfg) : Prog isa :=
  .seq (.block entry) (byIdx (fun i => (cfg i).sign) idxs)

end VG.Impl.Ecdsa.Rfc6979.AArch64
