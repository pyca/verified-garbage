module

public import VerifiedGarbage.Impl.Pbkdf2.Md.AArch64
public import VerifiedGarbage.Impl.Mont.AArch64
public import VerifiedGarbage.Impl.Weierstrass.AArch64
public import VerifiedGarbage.Impl.Dispatch.AArch64

/-!
# Deterministic ECDSA (RFC 6979) on AArch64, with the hash function as an argument

`sign (out = x0, d = x1, digest = x2, digest_len = x3, scratch = x4, hash = x5) -> w0`:
RFC 6979 §3.2 for a curve of `Q`-byte scalars in `w` 64-bit words, with
HMAC computed by calling HMAC's `init`, the streaming `update` and HMAC's
`finalize` of the hash function `hash` names (`hashIds`, 1 to 7: SHA-1 and
the SHA-2 functions), one of `hs` (the tier's, by number), each call chosen
by a dispatch on `hash` (`Dispatch.AArch64.chain`, the selector in `x9` and
the test in `x10`); and each candidate tried by calling `core`, the
signature with a given `k` (`vg_ecdsa_<curve>_sign`), which reads `Q` bytes
of the digest and of `k`, and takes the digest's leftmost `qlen` bits
(`bits2int`, a right shift by `sh = 8 Q - qlen` bits).

The hash function's sizes are not immediates: its output length `D` is
`digest_len`, and its block size `B` is computed from `hash` (64 for 1 to
3, 128 for 4 to 7, `64 + 64 ((hash + 4) >> 3)`), and both are kept in the
frame with `hash`, from where the code that needs them loads them. Only
the copy of the digest into the frame depends on `D` other than through
them, and is chosen by the same dispatch.

Two kinds of curve:

* `qlen = 8 Q` (`wide = false`): the digest's leftmost `Q` bytes, or, if it
  is shorter, the digest after `Q - D` zero bytes, are `G`, which `core`
  reads; `h = bits2octets(digest)` is `G` minus `n` if it is at least `n`
  (a conditional subtraction, as `2^(8 Q) < 2n`).
* `qlen < 8 Q` (P-521, `wide`): every digest is shorter than the scalars,
  and its integer below `n`, so `h` is the digest after `Q - D` zero bytes;
  `G` is the digest's integer shifted left by `sh` bits, the digest after
  `Q - D - 1` zero bytes and before one, shifted right by `8 - sh` bits (in
  place, through the 64-bit words at `scratch + sSlot`: `loadBytes`,
  `shrWords`, `storeBytes`).

The return address `x30` is pushed (the calls replace it), then a frame of
480 bytes is allocated: from `sp`, `K` and `V` (64 bytes each, of which the
first `D` are used), `h` (72 bytes, of which `Q` are used), the number of
candidates left, the length of `T` so far, then `scratch`, `digest`, `d`,
`out`, `hash`, `D` and `B`; then `G` (72 bytes) and `T` (136). The calls use
only `scratch`, which `core` overwrites entirely, and the 16 bytes below the
frame (HMAC's functions); `K`, `V`, `h`, `G` and `T` are cleared before the
frame is freed. In `scratch`: HMAC's inner and outer streaming states (192
bytes each), the working space of HMAC's and the hash function's functions
(at most 2048 bytes), the message of steps d, f and h.3, and the words of
the conversions.

1. `G` and `h`, as above.
2. Steps b to g: `V = 0x01…`, `K = 0x00…`, `K = HMAC_K(V ‖ 0x00 ‖ d ‖ h)`,
   `V = HMAC_K(V)`, `K = HMAC_K(V ‖ 0x01 ‖ d ‖ h)`, `V = HMAC_K(V)`.
3. At most `tries` times: `T`, the concatenation of `V = HMAC_K(V)` until
   it has at least `Q` bytes (each `V`'s 64 bytes copied after the `D`
   before, so a later one overwrites the rest); the candidate `k`, its
   leftmost `Q` bytes (shifted right by `sh` bits if `wide`); and
   `core(out, d, G, k, scratch)`; if it failed and candidates are left,
   `K = HMAC_K(V ‖ 0x00)`, `V = HMAC_K(V)` and again. Whether to go on, in
   `x12`, is computed without branches, so that the code branches only on
   it: the number of candidates tried is all it reveals.

`core` writes the signature or zeros to `out`, and its return value is ours.

A block addresses memory only at `sp` (through `x15`, set by `addSp`) or at
a pointer an earlier block loaded from the frame (`digestPtr`, `msgPtrs`,
`candLd`), never one it loads itself, so that the taint analysis of each
block knows its addresses are public; the lengths an address is computed
from (`D`, `T`'s length) are loaded the same way.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Rfc6979.AArch64

open VG.AArch64 VG.Impl.Pbkdf2.Md.AArch64
open VG.Impl.Mont.AArch64 (const64)

/-- The numbers of the hash functions the code takes (`VG.Spec.HashId`):
SHA-1 to SHA-512/256. -/
def hashIds : List Nat := [1, 2, 3, 4, 5, 6, 7]

/-! Where things are in the frame. -/
def fK : Nat := 0
def fV : Nat := 64
def fH : Nat := 128
def fCnt : Nat := 200
def fTl : Nat := 208
def fScratch : Nat := 216
def fDigest : Nat := 224
def fD : Nat := 232
def fOut : Nat := 240
def fSel : Nat := 248
def fDl : Nat := 256
def fBl : Nat := 264
def fG : Nat := 272
def fT : Nat := 344
/-- The frame's size, a multiple of 16. -/
def frameBytes : Nat := 480

/-! Where things are in `scratch`. -/
def sInner : Nat := 0
def sOuter : Nat := 192
def sWork : Nat := 384
def sMsg : Nat := 2432
/-- The words of a conversion, if `wide`. -/
def sSlot : Nat := 2640

/-- What the code needs of a curve and of the hash functions. -/
structure Cfg where
  /-- The hash functions' code and names, by number (a tier's). -/
  hs : List Hash
  /-- The 64-bit words of the curve's scalars. -/
  w : Nat
  /-- The bytes of the curve's scalars, `Q`. -/
  len : Nat := 8 * w
  /-- Whether `qlen < 8 Q` (P-521). -/
  wide : Bool := false
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

/-- `d ← scratch + a`: an address in `scratch`. -/
def scr (d : Reg) (a : Nat) : List Instr := [.ldrSp d fScratch, .addImm .x d d a]

/-- `d ← sp + o`: an address in the frame. -/
def fr (d : Reg) (o : Nat) : List Instr := [.addSp d o]

/-- The selector, for a dispatch. -/
def selLd : List Instr := [.ldrSp .x9 fSel]

/-- `f H` for the hash function `H` that `hash` names, by a dispatch on it
(in `x9`). -/
def disp (f : Hash → Prog isa) : Prog isa :=
  Dispatch.AArch64.chain .x10 .x9 (hashIds.map fun k => (k, match c.hs[k]? with
    | some H => f H
    | none => .block []))

/-- `out`, `d`, `digest`, `digest_len` (`D`) and `scratch` into the frame,
and `hash` and `B`, computed from it. -/
def saveArgs : List Instr :=
  [.addSp .x15 0, .addImm .x .x6 .x5 4, .lsr .x .x6 .x6 3, .lsl .x .x6 .x6 6,
    .addImm .x .x6 .x6 64, .str .x .x0 .x15 fOut, .str .x .x1 .x15 fD, .str .x .x2 .x15 fDigest,
    .str .x .x3 .x15 fDl, .str .x .x4 .x15 fScratch, .str .x .x5 .x15 fSel, .str .x .x6 .x15 fBl]

/-- The arguments of HMAC's `init`: the states, the key `K` of `D` bytes,
the working space; and the selector. -/
def hmacArgs₁ : List Instr :=
  scr .x0 sInner ++ scr .x1 sOuter ++ fr .x2 fK ++ ([.ldrSp .x3 fDl] : List Instr) ++ scr .x4 sWork ++ selLd

/-- The arguments of the streaming `update`: the inner state, the `B` bytes
it holds, the data (at the address `dataA` sets `x2` to) of `D + ex` bytes,
the working space; and the selector. -/
def hmacArgs₂ (dataA : List Instr) (ex : Nat) : List Instr :=
  scr .x0 sInner ++ ([.ldrSp .x1 fBl] : List Instr) ++ dataA ++
    ([.ldrSp .x3 fDl, .addImm .x .x3 .x3 ex] : List Instr) ++ scr .x4 sWork ++ selLd

/-- The arguments of HMAC's `finalize`: the states, the `B + D + ex` bytes
the inner one holds, the MAC's place in the frame, the working space; and
the selector. -/
def hmacArgs₃ (ex dst : Nat) : List Instr :=
  scr .x0 sInner ++ scr .x1 sOuter ++
    ([.ldrSp .x2 fBl, .ldrSp .x3 fDl, .add .x .x2 .x2 .x3, .addImm .x .x2 .x2 ex] : List Instr) ++
    fr .x3 dst ++ scr .x4 sWork ++ selLd

/-- `HMAC_K(data)` into the frame at `dst`, for `D + ex` bytes of `data` at
the address `dataA` sets `x2` to: HMAC's `init` with the key `K`, `update`
on the inner state, and `finalize`, each of the hash function `hash` names. -/
def hmac (dataA : List Instr) (ex dst : Nat) : Prog isa :=
  .seq (.block hmacArgs₁)
  (.seq (c.disp fun H => .call H.hmacInitN H.hmacInit)
  (.seq (.block (hmacArgs₂ dataA ex))
  (.seq (c.disp fun H => .call H.updN H.updC)
  (.seq (.block (hmacArgs₃ ex dst))
    (c.disp fun H => .call H.hmacFinN H.hmacFin)))))

/-- `V = HMAC_K(V)`. -/
def hmacV : Prog isa := c.hmac (fr .x2 fV) 0 fV

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

/-- The pointers and the length the messages need: `scratch` in `x9`, `d`
in `x10`, the frame in `x15`, and `D` in `x8` (loaded first, so that every
address the message's block computes is from them). -/
def msgPtrs : List Instr := [.ldrSp .x9 fScratch, .ldrSp .x10 fD, .addSp .x15 0, .ldrSp .x8 fDl]

/-- `d` (from `x10`) and `h` (from the frame, in `x15`, at `ho`), `Q` bytes
each, to `x12`: `w` words each when the encoding fills them, otherwise
`copyBytes` (`h`'s through `x13` and `x14`). -/
def copyDH (w Q : Nat) (ho : Nat := fH) : List Instr :=
  if Q % 8 = 0 ∧ Q = 8 * w then copyN w .x10 0 .x12 0 ++ copyN w .x15 ho .x12 (8 * w)
  else copyBytes Q .x10 .x12 ++ ([.addImm .x .x13 .x15 ho, .addImm .x .x14 .x12 Q] : List Instr) ++ copyBytes Q .x13 .x14

/-- The message `V ‖ b` (and `‖ d ‖ h` if `full`, `Q` bytes each) at
`scratch + sMsg`, for `V` of `D` bytes, with `scratch` in `x9`, `d` in
`x10`, the frame in `x15` and `D` in `x8`: all 64 bytes of `V`'s place from
the frame, then `b` after its first `D`, then `d` and `h`, through `x12`,
which points after `b`. -/
def msg (w Q b : Nat) (full : Bool) : List Instr :=
  copyN 8 .x15 fV .x9 sMsg ++
    ([.add .x .x12 .x9 .x8, .movz .x .x11 (BitVec.ofNat 16 b) 0, .strb .x11 .x12 sMsg] : List Instr) ++
    (if full then .addImm .x .x12 .x12 (sMsg + 1) :: copyDH w Q else [])

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
def rekeyFull (b : Nat) : Prog isa :=
  .seq (.block msgPtrs) (.seq (.block (msg c.w c.len b true))
    (.seq (c.hmac (scr .x2 sMsg) (2 * c.len + 1) fK) c.hmacV))

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
def rekey : Prog isa :=
  .seq (.block msgPtrs) (.seq (.block (msg c.w c.len 0 false))
    (.seq (c.hmac (scr .x2 sMsg) 1 fK) c.hmacV))

/-- The `Q` bytes at `sp + o`, as a big-endian number, shifted right by `s`
bits in place (`0 < s < 64`), through the words at `scratch + sSlot`, with
`scratch` in `x0` (loaded first) and `sp + o` in `x6`. -/
def conv (o s : Nat) : Prog isa :=
  .seq (.block [.ldrSp .x0 fScratch]) <| .block <|
    .addSp .x6 o :: Impl.Weierstrass.AArch64.loadBytes c.len c.w sSlot .x6 ++
      Impl.Weierstrass.AArch64.shrWords c.w sSlot s ++
      ([.movz .x .x3 0 0, .subImm .x .x3 .x3 1] : List Instr) ++ Impl.Weierstrass.AArch64.storeBytes c.len c.w .x6 0 sSlot

/-- Nine zero words at `sp + o`, through `x11` (with the frame in `x15`). -/
def zero9 (o : Nat) : List Instr := (List.range 9).map fun j => .str .x .x11 .x15 (o + 8 * j)

/-- Nine zero words at `sp + o` (through `x11`), then the `m` bytes at `x1`
after the first `p` of them (through `x12`), with the frame in `x15`. -/
def zcopy (o p m : Nat) : List Instr :=
  .movz .x .x11 0 0 :: zero9 o ++ (.addImm .x .x12 .x15 (o + p) :: copyBytes m .x1 .x12)

/-- The digest (at `x1`) of `D` bytes into the frame: unless `wide`, `G`, its
leftmost `Q` bytes, or, if it is shorter, the digest after `Q - D` zero
bytes; if `wide`, `h`, the digest after `Q - D` zero bytes, and the digest
after `Q - D - 1` zero bytes and before one at `G`, which `start` shifts. -/
def digG (D : Nat) : List Instr :=
  .addSp .x15 0 ::
    (if c.wide then zcopy fH (c.len - D) D ++ zcopy fG (c.len - D - 1) D
    else zcopy fG (c.len - min D c.len) (min D c.len))

/-- The 64-bit words of `n`, least significant first. -/
def nWord (j : Nat) : BitVec 64 := BitVec.ofNat 64 (c.n >>> (64 * j))

/-- `digest` in `x1`. -/
def digestPtr : List Instr := [.ldrSp .x1 fDigest]

/-- `G` in `x1`. -/
def gPtr : List Instr := [.addSp .x1 fG]

/-- Where the words of the number at `x1` are loaded from, and those of `h`
stored to (from the frame in `x15`): `x1` and `x15`, or, if `Q` is not a
multiple of 8, `x13 = x1 + Q % 8` and `x14 = sp + Q % 8`, so that each 8-byte
access's offset is a multiple of 8. -/
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
place, and word `j` of it minus `n` (with the borrow of the words before) to
`K`'s, with the frame in `x15`: `x8`, `x2` and `x12` change, and the borrow
is the carry flag (clear if it borrowed). -/
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
    .rev .x8 .x8, .str .x .x8 c.hBase (fH + c.len - c.len % 8 - 8 * (j + 1))]

/-- `h`: the `Q` bytes at `x1`, as a big-endian number, minus `n` if that
does not borrow, big-endian into the frame's `Q` bytes at `h`. -/
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

/-- `G` and `h`, and the initial `K` and `V`: the digest's copy for the hash
function `hash` names, then, unless `wide`, `h` from `G`, or, if `wide`, `G`
shifted. -/
def start : Prog isa :=
  .seq (.block (digestPtr ++ selLd)) (.seq (c.disp fun H => .block (c.digG H.D))
    (if c.wide then .seq (c.conv fG (8 - c.sh)) (.block initKV) else .block (gPtr ++ c.reduce ++ initKV)))

/-- `T`'s length, zero. -/
def candInit : List Instr := [.movz .x .x9 0 0, .addSp .x15 0, .str .x .x9 .x15 fTl]

/-- `D` in `x8` and `T`'s length in `x9`. -/
def candLd : List Instr := [.ldrSp .x8 fDl, .ldrSp .x9 fTl]

/-- `V`'s 64 bytes after `T`'s first `x9` (through `x13`), `T`'s length
`D` more, and `x12 ≠ 0` iff it is still below `Q`: `x12 = (len - Q) >> 63`. -/
def candCopy : List Instr :=
  ([.addSp .x15 0, .addSp .x13 fT, .add .x .x13 .x13 .x9] : List Instr) ++ copyN 8 .x15 fV .x13 0 ++
    [.add .x .x9 .x9 .x8, .str .x .x9 .x15 fTl, .movz .x .x11 (BitVec.ofNat 16 c.len) 0,
      .sub .x .x12 .x9 .x11, .lsr .x .x12 .x12 63]

/-- One `V` of `T`. -/
def candStep : Prog isa := .seq c.hmacV (.seq (.block candLd) (.block c.candCopy))

/-- The candidate: `T`, from `V = HMAC_K(V)` until it has `Q` bytes, and, if
`wide`, its first `Q` bytes shifted right by `sh` bits. -/
def cand : Prog isa :=
  .seq (.block candInit) (if c.wide then .seq (.loop c.candStep (.nonzero .x .x12)) (c.conv fT c.sh)
    else .loop c.candStep (.nonzero .x .x12))

/-- `core(out, d, G, k, scratch)`, with `k` at `T`. -/
def coreArgs : List Instr :=
  ([.ldrSp .x0 fOut, .ldrSp .x1 fD] : List Instr) ++ fr .x2 fG ++ fr .x3 fT ++ ([.ldrSp .x4 fScratch] : List Instr)

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
  (.seq (.block coreArgs)
  (.seq (.call c.coreN c.coreC)
  (.seq (.block goOn)
    (.ite (.nonzero .x .x12) (.seq c.rekey (.block again)) (.block stop)))))

/-- `K`, `V`, `h`, `G` and `T` cleared (`x0`, the result, kept). -/
def wipe : List Instr :=
  ([.addSp .x15 0, .movz .x .x14 0 0] : List Instr) ++ (List.range 25).map (fun j => .str .x .x14 .x15 (8 * j)) ++
    (List.range 26).map fun j => .str .x .x14 .x15 (fG + 8 * j)

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block saveArgs)
  (.seq c.start
  (.seq (c.rekeyFull 0)
  (.seq (c.rekeyFull 1)
  (.seq (.block c.initCnt)
  (.seq (.loop c.tryOne (.nonzero .x .x12))
    (.block wipe))))))

/-- `vg_ecdsa_<curve>_rfc6979_sign`. -/
def sign : Prog isa :=
  .frame (.push .x30) (.frame (.alloc frameBytes) c.body (.free frameBytes)) (.pop .x30)

end Cfg

end VG.Impl.Ecdsa.Rfc6979.AArch64
