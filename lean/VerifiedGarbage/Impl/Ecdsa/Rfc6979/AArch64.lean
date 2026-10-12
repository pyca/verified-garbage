module

public import VerifiedGarbage.Impl.Pbkdf2.Md.AArch64
public import VerifiedGarbage.Impl.Mont.AArch64
public import VerifiedGarbage.Impl.Weierstrass.AArch64

/-!
# Deterministic ECDSA (RFC 6979) on AArch64

`sign R H core (out = x0, d = x1, digest = x2, scratch = x3) -> w0`, as on
x86-64 (`Impl/Ecdsa/Rfc6979/X86_64.lean`): RFC 6979 §3.2 for a curve of
`Q`-byte scalars in `w` 64-bit words and a Merkle–Damgård hash function `H`
whose output is `D` bytes, a multiple of 4 from 28 to 64, with HMAC computed by
calling `H`'s HMAC `init`, streaming `update` and HMAC `finalize`, and each
candidate tried by calling `core`, the signature with a given `k`
(`vg_ecdsa_<curve>_sign`), which reads `Q` bytes of the digest and of `k`,
and takes the digest's leftmost `qlen` bits (`bits2int`, a right shift by
`sh = 8 Q - qlen` bits).

Two kinds of curve and hash function, as on x86-64:

* `Q ≤ D` and `qlen = 8 Q`, the scalars' words full or the top one of four
  bytes (P-224, P-256 and P-384, `wide = false`): one `V` makes a candidate,
  its leftmost `Q` bytes; `bits2octets` is a conditional subtraction of `n`
  from the digest's leftmost `Q` bytes; and `core` reads the digest and `V`
  in place.
* `8 D < qlen ≤ 16 D` and `Q ≤ D + 8` (P-521 with SHA-512, `wide`): two `V`s
  make a candidate, the leftmost `Q` bytes of the second's concatenation with
  the first, shifted right by `sh` bits; the digest's integer is below `n`,
  so `bits2octets` is the digest after `Q - D` zero bytes; and `core` reads
  the digest shifted left by `sh` bits, which it shifts back. The candidate
  and that digest are made in `Q` bytes at the frame's top, through the
  64-bit words at `scratch + sSlot` (`loadBytes`, `shrWords`, `storeBytes`,
  with `scratch` in `x0`).

The return address `x30` is pushed (the calls replace it), then a frame of
224 bytes, 368 if `wide`, is allocated: from `sp`, `K` and `V` (64 bytes
each, of which the first `D` are used), `h` (48 bytes, unless `wide`), the
number of candidates left, then `scratch`, `digest`, `d` and `out`; and, if
`wide`, the digest for `core` and the candidate (72 bytes each). The calls
use only `scratch`, which `core` overwrites entirely, and the 16 bytes below
the frame (HMAC's functions); `K`, `V`, `h` and, if `wide`, the digest for
`core` and the candidate are cleared before the frame is freed. In
`scratch`, as on x86-64: HMAC's inner and outer streaming states, the working
space of HMAC's and `H`'s functions, the message of steps d, f and h.3, and
the words of the conversions.

1. `h = bits2octets(digest)`: unless `wide`, the leftmost `Q` bytes, minus
   `n` if they are at least `n` (a conditional subtraction, as
   `2^(8 Q) < 2n`), a word at a time through memory: the words of the digest
   to `V`'s place, those of the difference to `K`'s (before steps b and c set
   them), and the one the borrow selects, big-endian, to `h` (a top word of
   four bytes by 32-bit loads, and stored ending at `h`'s fourth byte, its
   zero bytes in `V`'s place, which step b then sets). If `wide`, the
   digest for `core` instead: the digest then `Q - D` zero bytes, shifted
   right by `8 (Q - D) - sh` bits.
2. Steps b to g: `V = 0x01…`, `K = 0x00…`, `K = HMAC_K(V ‖ 0x00 ‖ d ‖ h)`,
   `V = HMAC_K(V)`, `K = HMAC_K(V ‖ 0x01 ‖ d ‖ h)`, `V = HMAC_K(V)`.
3. At most `tries` times: `V = HMAC_K(V)` (twice if `wide`), the candidate
   `k`, and `core(out, d, digest, k, scratch)`; if it failed and candidates are left,
   `K = HMAC_K(V ‖ 0x00)`, `V = HMAC_K(V)` and again. Whether to go on, in
   `x12`, is computed without branches, so that the code branches only on
   it: the number of candidates tried is all it reveals.

`core` writes the signature or zeros to `out`, and its return value is ours.

A block addresses memory only at `sp` (through `x15`, set by `addSp`) or at
a pointer an earlier block loaded from the frame (`digestPtr`, `msgPtrs`),
never one it loads itself, so that the taint analysis of each block knows
its addresses are public.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Rfc6979.AArch64

open VG.AArch64 VG.Impl.Pbkdf2.Md.AArch64
open VG.Impl.Mont.AArch64 (const64)

/-! Where things are in the frame. -/
def fK : Nat := 0
def fV : Nat := 64
def fH : Nat := 128
def fCnt : Nat := 176
def fScratch : Nat := 184
def fDigest : Nat := 192
def fD : Nat := 200
def fOut : Nat := 208
/-- If `wide`: the digest for `core`, and the candidate. -/
def fX : Nat := 224
def fKb : Nat := 296
/-- The bytes at the frame's top: the digest for `core` and the candidate,
if `wide`. -/
def extra (wide : Bool) : Nat := if wide then 144 else 0
/-- The frame's size, a multiple of 16. -/
def frameBytes (wide : Bool) : Nat := 224 + extra wide

/-! Where things are in `scratch`. -/
def sInner : Nat := 0
def sOuter : Nat := 192
def sWork : Nat := 384
def sMsg : Nat := 2256
/-- The words of a conversion, if `wide`. -/
def sSlot : Nat := 2560

/-- What the code needs of a curve and a hash function. -/
structure Cfg where
  /-- The hash function's code and names. -/
  H : Hash
  /-- The 64-bit words of the curve's scalars. -/
  w : Nat
  /-- The bytes of the curve's scalars, `Q`. -/
  len : Nat := 8 * w
  /-- Whether the hash is shorter than the scalars (two `V`s make a candidate). -/
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

/-- `out`, `d`, `digest` and `scratch` into the frame. -/
def saveArgs : List Instr :=
  [.addSp .x15 0, .str .x .x0 .x15 fOut, .str .x .x1 .x15 fD, .str .x .x2 .x15 fDigest,
    .str .x .x3 .x15 fScratch]

/-- The arguments of HMAC's `init`: the states, the key `K` of `D` bytes,
the working space. -/
def hmacArgs₁ (D : Nat) : List Instr :=
  scr .x0 sInner ++ scr .x1 sOuter ++ fr .x2 fK ++ ([.movz .x .x3 (BitVec.ofNat 16 D) 0] : List Instr) ++ scr .x4 sWork

/-- The arguments of the streaming `update`: the inner state, the `B` bytes
it holds, the data (at the address `dataA` sets `x2` to) of `len` bytes,
the working space. -/
def hmacArgs₂ (B : Nat) (dataA : List Instr) (len : Nat) : List Instr :=
  scr .x0 sInner ++ ([.movz .x .x1 (BitVec.ofNat 16 B) 0] : List Instr) ++ dataA ++
    ([.movz .x .x3 (BitVec.ofNat 16 len) 0] : List Instr) ++ scr .x4 sWork

/-- The arguments of HMAC's `finalize`: the states, the `B + len` bytes the
inner one holds, the MAC's place in the frame, the working space. -/
def hmacArgs₃ (B len dst : Nat) : List Instr :=
  scr .x0 sInner ++ scr .x1 sOuter ++ ([.movz .x .x2 (BitVec.ofNat 16 (B + len)) 0] : List Instr) ++ fr .x3 dst ++
    scr .x4 sWork

/-- `HMAC_K(data)` into the frame at `dst`, for `len` bytes of `data` at the
address `dataA` sets `x2` to: HMAC's `init` with the key `K`, `update` on
the inner state, and `finalize`. -/
def hmac (dataA : List Instr) (len dst : Nat) : Prog isa :=
  .seq (.block (hmacArgs₁ c.H.D))
  (.seq (.call c.H.hmacInitN c.H.hmacInit)
  (.seq (.block (hmacArgs₂ c.H.P.B dataA len))
  (.seq (.call c.H.updN c.H.updC)
  (.seq (.block (hmacArgs₃ c.H.P.B len dst))
    (.call c.H.hmacFinN c.H.hmacFin)))))

/-- `V = HMAC_K(V)`. -/
def hmacV : Prog isa := c.hmac (fr .x2 fV) c.H.D fV

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

/-- The pointers the messages need: `scratch` in `x9`, `d` in `x10`, the
frame in `x15`, and, if `wide`, `digest` in `x8` (loaded first, so that every
address the message's block computes is from them). -/
def msgPtrs (wide : Bool) : List Instr :=
  ([.ldrSp .x9 fScratch, .ldrSp .x10 fD, .addSp .x15 0] : List Instr) ++ (if wide then [.ldrSp .x8 fDigest] else [])

/-- `V`'s `D` bytes from the frame (in `x15`) to `scratch + sMsg` (`scratch`
in `x9`): a word at a time, or, if `D` is not a multiple of 8, through `x13`
and `x14` (`copyBytes`). -/
def copyV (D : Nat) : List Instr :=
  if D % 8 = 0 then copyN (D / 8) .x15 fV .x9 sMsg
  else ([.addImm .x .x13 .x15 fV, .addImm .x .x14 .x9 sMsg] : List Instr) ++ copyBytes D .x13 .x14

/-- `d` (from `x10`) and `h` (from the frame, in `x15`), `Q` bytes each, to
`x12`: `w` words each when the encoding fills them, otherwise `copyBytes`
(`h`'s through `x13` and `x14`). -/
def copyDH (w Q : Nat) : List Instr :=
  if Q % 8 = 0 ∧ Q = 8 * w then copyN w .x10 0 .x12 0 ++ copyN w .x15 fH .x12 (8 * w)
  else copyBytes Q .x10 .x12 ++ ([.addImm .x .x13 .x15 fH, .addImm .x .x14 .x12 Q] : List Instr) ++ copyBytes Q .x13 .x14

/-- The message `V ‖ b` (and `‖ d ‖ h` if `full`, `Q` bytes each) at
`scratch + sMsg`, for `V` of `D` bytes, with `scratch` in `x9`, `d` in `x10`
and the frame in `x15`: `V` from the frame, `b` a byte, `d`, and `h` from the
frame; or, if `wide`, `Q - D` zero bytes (a zero word, which the digest's
words then overwrite but for them) and the digest (from `x8`). `d ‖ h`
through `x12`, which points after `b`, and the rest through `x13` and `x14`,
as an 8-byte store's offset is a multiple of 8. -/
def msg (w Q D b : Nat) (full wide : Bool) : List Instr :=
  copyV D ++
    ([.movz .x .x11 (BitVec.ofNat 16 b) 0, .strb .x11 .x9 (sMsg + D)] : List Instr) ++
    (if full then
      .addImm .x .x12 .x9 (sMsg + D + 1) ::
        (if wide then
          copyBytes Q .x10 .x12 ++
            ([.addImm .x .x13 .x9 (sMsg + D + 1 + Q), .movz .x .x11 0 0, .str .x .x11 .x13 0,
              .addImm .x .x14 .x9 (sMsg + 1 + 2 * Q)] : List Instr) ++ copyN (D / 8) .x8 0 .x14 0
        else copyDH w Q)
      else [])

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
def rekeyFull (b : Nat) : Prog isa :=
  .seq (.block (msgPtrs c.wide)) (.seq (.block (msg c.w c.len c.H.D b true c.wide))
    (.seq (c.hmac (scr .x2 sMsg) (c.H.D + 2 * c.len + 1) fK) c.hmacV))

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
def rekey : Prog isa :=
  .seq (.block (msgPtrs false)) (.seq (.block (msg c.w c.len c.H.D 0 false false))
    (.seq (c.hmac (scr .x2 sMsg) (c.H.D + 1) fK) c.hmacV))

/-- The `Q` bytes at `sp + o`, as a big-endian number, shifted right by `s`
bits in place (`0 < s < 64`), through the words at `scratch + sSlot`, with
`scratch` in `x0` (loaded first) and `sp + o` in `x6`. -/
def conv (o s : Nat) : Prog isa :=
  .seq (.block [.ldrSp .x0 fScratch]) <| .block <|
    .addSp .x6 o :: Impl.Weierstrass.AArch64.loadBytes c.len c.w sSlot .x6 ++
      Impl.Weierstrass.AArch64.shrWords c.w sSlot s ++
      ([.movz .x .x3 0 0, .subImm .x .x3 .x3 1] : List Instr) ++ Impl.Weierstrass.AArch64.storeBytes c.len c.w .x6 0 sSlot

/-- If `wide`: the digest for `core`, the digest (at `x1`) then `Q - D` zero
bytes, shifted right by `8 (Q - D) - sh` bits: the digest's integer shifted
left by `sh` bits. -/
def coreDigest : Prog isa :=
  .seq (.block (([.addSp .x15 0, .movz .x .x11 0 0, .str .x .x11 .x15 (fX + c.H.D)] : List Instr) ++
    copyN (c.H.D / 8) .x1 0 .x15 fX))
    (c.conv fX (8 * (c.len - c.H.D) - c.sh))

/-- The 64-bit words of `n`, least significant first. -/
def nWord (j : Nat) : BitVec 64 := BitVec.ofNat 64 (c.n >>> (64 * j))

/-- `digest` in `x1`. -/
def digestPtr : List Instr := [.ldrSp .x1 fDigest]

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
    .rev .x8 .x8, .str .x .x8 c.hBase (fH + c.len - c.len % 8 - 8 * (j + 1))]

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

/-- `core(out, d, digest, k, scratch)`, with `k = V`, or, if `wide`, the
digest and the candidate at the frame's top. -/
def coreArgs (wide : Bool) : List Instr :=
  ([.ldrSp .x0 fOut, .ldrSp .x1 fD] : List Instr) ++
    (if wide then fr .x2 fX ++ fr .x3 fKb else ([.ldrSp .x2 fDigest] : List Instr) ++ fr .x3 fV) ++ ([.ldrSp .x4 fScratch] : List Instr)

/-- If `wide`: `V`'s first `D` bytes to the candidate's place. -/
def keepV : List Instr := .addSp .x15 0 :: copyN (c.H.D / 8) .x15 fV .x15 fKb

/-- If `wide`: the next eight bytes of the candidate from `V`, then the
candidate's `Q` bytes shifted right by `sh` bits. -/
def candTop : Prog isa :=
  .seq (.block [.addSp .x15 0, .ldr .x .x11 .x15 fV, .str .x .x11 .x15 (fKb + c.H.D)]) (c.conv fKb c.sh)

/-- The candidate: `V = HMAC_K(V)`, which is `k`; or, if `wide`, the
leftmost `Q` bytes of `V = HMAC_K(V)` then `V = HMAC_K(V)` again, shifted
right by `sh` bits. -/
def cand : Prog isa :=
  if c.wide then .seq c.hmacV (.seq (.block c.keepV) (.seq c.hmacV c.candTop)) else c.hmacV

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
  (.seq (.block (coreArgs c.wide))
  (.seq (.call c.coreN c.coreC)
  (.seq (.block goOn)
    (.ite (.nonzero .x .x12) (.seq c.rekey (.block again)) (.block stop)))))

/-- `K`, `V` and `h` cleared, and the words at the frame's top (`x0`, the
result, kept). -/
def wipe (wide : Bool) : List Instr :=
  ([.addSp .x15 0, .movz .x .x14 0 0] : List Instr) ++ (List.range 22).map (fun j => .str .x .x14 .x15 (8 * j)) ++
    (List.range (extra wide / 8)).map fun j => .str .x .x14 .x15 (fX + 8 * j)

/-- `h`, or, if `wide`, the digest for `core`; and the initial `K` and `V`. -/
def start : Prog isa :=
  if c.wide then .seq c.coreDigest (.block initKV) else .block (c.reduce ++ initKV)

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block saveArgs)
  (.seq (.block digestPtr)
  (.seq c.start
  (.seq (c.rekeyFull 0)
  (.seq (c.rekeyFull 1)
  (.seq (.block c.initCnt)
  (.seq (.loop c.tryOne (.nonzero .x .x12))
    (.block (wipe c.wide))))))))

/-- `vg_ecdsa_<curve>_<hash>_sign`. -/
def sign : Prog isa :=
  .frame (.push .x30) (.frame (.alloc (frameBytes c.wide)) c.body (.free (frameBytes c.wide))) (.pop .x30)

end Cfg

end VG.Impl.Ecdsa.Rfc6979.AArch64
