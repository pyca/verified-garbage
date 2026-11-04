module

public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Impl.Mont.PPC64LE
public import VerifiedGarbage.Impl.Weierstrass.PPC64LE
public import VerifiedGarbage.Impl.RsaOaep.PPC64LE

/-!
# Deterministic ECDSA (RFC 6979) on PPC64LE, with the hash function of a table

`vg_ecdsa_<curve>_sign(out = r3, d = r4, digest = r5, digest_len = r6,
scratch = r7, hash = r8) -> r3` (`signT`), for a curve of `Q`-byte scalars:
RFC 6979 §3.2 with HMAC over the hash function of the table `hash` of the
interface `Hash` (`Spec/HashTable.lean`), whose streaming `init`, `update`
and `finalize` (its words 0 to 2) it calls indirectly (`tcall`: the table's
address from the frame into `r12`, its word into `r12`, then `bctrl`), and
each candidate tried by calling `core`, the signature with a given `k`
(`vg_ecdsa_<curve>_sign_k`), which reads `Q` bytes of the digest and of
`k`, and takes the digest's leftmost `qlen` bits (`bits2int`, a right shift
by `sh = 8 Q - qlen` bits).

Which table `hash` is, is public, and so is the hash function's index in
`Mgf1.hashes`, its word 3: `signT`, in a frame that saves the return
address, moves `scratch` to `r6` and chooses by the index (`byIdx`,
comparisons with each index of `idxs`) the code for that hash function's
digest length `D` and block size `B` (`shapeOf`), `sign` of a `Cfg`, in
which both are constants, and calls it: each is a function of its own
(`vg_ecdsa_<curve>_sign_d<D>b<B>`), so that the comparisons' branches, which
reach 32 KiB at most, skip only calls. Everything below is that code.

HMAC (`hmac`) is computed from the table's streaming functions: the key `K`
(`D` bytes, in the frame) padded to a block and XORed with `ipad` (`padBlk`,
a 32-bit word at a time, into `scratch + sPad`), the inner state set by
`init` and updated with it, the same with `opad` for the outer state
(`hinit`); the inner state updated with the data (`hupd`); then the inner
state finalized into `scratch + sTmp`, the outer one updated with that
digest and finalized there too, and its first `D` bytes copied to the MAC's
place in the frame (`hfin`).

Two kinds of curve and hash function:

* `Q ≤ D` (the order `n` of exactly `8 Q` bits with `2^(8 Q) < 2n`, `Q` a
  multiple of 4): one `V` makes a candidate, its leftmost `Q` bytes;
  `bits2octets` is a conditional subtraction of `n` from the digest's
  leftmost `Q` bytes (`reduce`); and `core` reads the digest and `V` in place.
* `D < Q` (`wide`): `m` `V`s make a candidate `T` (`candW`), at the frame's
  `fT`, of which `core` reads the first `Q` bytes, shifted right in place by
  `sh` bits; the digest's integer is below `n`, so `h = bits2octets(digest)`
  is `Q - D` zero bytes then the digest (`hPrep`, at `fX`); and `core` reads
  `h`, or, if `sh ≠ 0` (P-521), the digest's integer shifted left by `sh`
  bits (`xPrep`, at `fXc`: `Q - D - 1` zero bytes, the digest and a zero
  byte, shifted right by `8 - sh` bits). The shifts are through the words at
  `scratch + sSlot` (`conv`).

The return address is moved to `r0` and pushed (the calls replace it), then
a frame of `256 + extra` bytes is allocated: above its 32-byte header, `K`
and `V` (64 bytes each, of which the first `D` are used), `h` (48 bytes, of
which `Q` are used, unless `wide` or `hHigh`), the number of candidates left,
then `scratch`, `digest`, `d`, `out` and the table's address; and `extra`
bytes above them: if `wide`, `h`, the digest for `core` and `T` (72, 72 and
128 bytes), or, if `hHigh` (scalars of 64 bytes, as brainpoolP512r1's, with a
hash no shorter), `h` in 64 bytes. The calls use only `scratch`, which `core`
overwrites entirely, and the stack below the frame; `K`, `V`, `h` and the
frame's top are cleared before the frame is freed. In `scratch`: HMAC's inner
and outer streaming states, the working space of the streaming functions,
the padded key and the inner digest, the message of steps d, f and h.3, and
the words of a shift.

1. `h = bits2octets(digest)`: unless `wide`, the leftmost `Q` bytes, minus
   `n` if they are at least `n` (a conditional subtraction, as
   `2^(8 Q) < 2n`), by 32-bit digits, without the carry bit (as in
   `Impl/Mont/PPC64LE.lean`): the digits of the digest to `V`'s place, those
   of the difference to `K`'s (before steps b and c set them), and the one
   the borrow selects, big-endian, to `h`. If `wide`, `hPrep` and `xPrep`.
2. Steps b to g: `V = 0x01…`, `K = 0x00…`, `K = HMAC_K(V ‖ 0x00 ‖ d ‖ h)`,
   `V = HMAC_K(V)`, `K = HMAC_K(V ‖ 0x01 ‖ d ‖ h)`, `V = HMAC_K(V)`.
3. At most `tries` times: the candidate (`V = HMAC_K(V)`, `m` times, each
   copied to `T`, if `wide`), and `core(out, d, digest, k, scratch)`; if it
   failed and candidates are left, `K = HMAC_K(V ‖ 0x00)`, `V = HMAC_K(V)`
   and again. Whether to go on, in `r12`, is computed without branches from
   the low bit of `core`'s result (the bits its contract determines), so
   that the code branches only on it: the number of candidates tried is all
   it reveals.

`core` writes the signature or zeros to `out`, and its result is ours.

A block addresses memory only at the frame (through `r11` or `r12`, set by
`addSp`) or at a pointer it loads from the frame before using it, so that
the taint analysis of each block knows its addresses are public. The blocks
that depend on the hash function depend only on `D` and `B`, so that the
taint analysis checks them for each size.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Rfc6979.PPC64LE

open VG.PPC64LE
open VG.Impl.Mont.PPC64LE (movImm mask32)
open VG.Impl.RsaOaep.PPC64LE (Fns)

/-! Where things are in the frame. -/
def fK : Nat := 32
def fV : Nat := 96
def fH : Nat := 160
def fCnt : Nat := 208
def fScratch : Nat := 216
def fDigest : Nat := 224
def fD : Nat := 232
def fOut : Nat := 240
/-- The table's address. -/
def fTab : Nat := 248
/-- Above the pointers: `h`, if `wide` or `hHigh`. -/
def fX : Nat := 256
/-- If `wide`: the digest for `core`, if `sh ≠ 0`. -/
def fXc : Nat := 328
/-- If `wide`: the candidate `T`. -/
def fT : Nat := 400
/-- The bytes above `fX`: 272 if `wide`, 64 if `hHigh`. -/
def extra (hHigh : Bool) (wide : Bool := false) : Nat := if wide then 272 else if hHigh then 64 else 0
/-- The frame's size, a multiple of 16. -/
def frameBytes (hHigh : Bool := false) (wide : Bool := false) : Nat := 256 + extra hHigh wide

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
  /-- The bytes of the curve's scalars, `Q`. -/
  len : Nat
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
abbrev wide : Bool := decide (c.D < c.len)

/-- Whether `h` is at the frame's top: scalars of more than 48 bytes, unless
`wide`. -/
abbrev hHigh : Bool := !c.wide && decide (48 < c.len)

/-- The bits of `Q` bytes that are not the order's, `8 Q - qlen` (P-521's 7). -/
def sh : Nat := 8 * c.len - (c.n.log2 + 1)

/-- The 64-bit words of `Q` bytes. -/
def w : Nat := (c.len + 7) / 8

/-- The number of `V`s in a candidate: the least `m` with `8 D m ≥ qlen`. -/
def m : Nat := (8 * c.len - c.sh + 8 * c.D - 1) / (8 * c.D)

/-- Where `h` is. -/
def fHo : Nat := if c.wide || c.hHigh then fX else fH

/-- `r11 ← sp`, `r12 ← scratch`. -/
def scrBase : List Instr := [.addSp .r11 0, .load .d .r12 .r11 fScratch]

/-! ## HMAC through the table -/

/-- The indirect call of the table's function `j`, among `ts`: the table's
address into `r12`, its word `j` into `r12`, then `bctrl`. -/
def tcall (j : Nat) (ts : List (String × Prog isa)) : Prog isa :=
  .seq (.block [.addSp .r12 0, .load .d .r12 .r12 fTab, .load .d .r12 .r12 (8 * j)]) (Code.icalls .bctrl ts)

/-- The streaming `init` of the state at `scratch + o`. -/
def initCall (o : Nat) : Prog isa := .seq (.block (scrBase ++ [.addi .r3 .r12 o])) (tcall 0 c.f.init)

/-- The arguments of the streaming `update` of the state at `scratch + o`,
which holds `cnt` bytes, with the data (at the address `dataA` sets `r5`
to, from `scratch` in `r12`) of `len` bytes, and the working space. -/
def updArgs (o cnt : Nat) (dataA : List Instr) (len : Nat) : List Instr :=
  scrBase ++ ([.addi .r3 .r12 o, .li .r4 cnt] : List Instr) ++ dataA ++
    ([.li .r6 len, .addi .r7 .r12 sWork] : List Instr)

def updCall (o cnt : Nat) (dataA : List Instr) (len : Nat) : Prog isa :=
  .seq (.block (updArgs o cnt dataA len)) (tcall 1 c.f.upd)

/-- The arguments of the streaming `finalize` of the state at `scratch + o`,
which holds `cnt` bytes, into `scratch + sTmp`, with the working space. -/
def finArgs (o cnt : Nat) : List Instr :=
  scrBase ++ [.addi .r3 .r12 o, .li .r4 cnt, .addi .r5 .r12 sTmp, .addi .r6 .r12 sWork]

def finCall (o cnt : Nat) : Prog isa := .seq (.block (finArgs o cnt)) (tcall 2 c.f.fin)

/-- Word `k` of the key `K` (the frame's first `D` bytes at `fK`) padded to
`B` bytes, XORed with the pad in `r9`, to `scratch + sPad` (the frame in
`r11`, `scratch` in `r12`). -/
def padW (k : Nat) : List Instr :=
  if k < c.D / 4 then
    [.load .w .r8 .r11 (fK + 4 * k), .logic .xor .r8 .r8 .r9, .store .w .r8 .r12 (sPad + 4 * k)]
  else [.store .w .r9 .r12 (sPad + 4 * k)]

/-- `K₀ ⊕ pad` (a block) at `scratch + sPad`. -/
def padBlk (x : BitVec 32) : List Instr :=
  scrBase ++ movImm .r9 x ++ (List.range (c.B / 4)).flatMap c.padW

/-- HMAC's states for the key `K`: each set by `init`, then updated with
the padded key. -/
def hinit : Prog isa :=
  .seq (c.initCall sInner) (.seq (c.initCall sOuter)
  (.seq (.block (c.padBlk ipad32)) (.seq (c.updCall sInner 0 [.addi .r5 .r12 sPad] c.B)
  (.seq (.block (c.padBlk opad32)) (c.updCall sOuter 0 [.addi .r5 .r12 sPad] c.B)))))

/-- The inner state updated with `len` bytes of data at the address `dataA`
sets `r5` to. -/
def hupd (dataA : List Instr) (len : Nat) : Prog isa := c.updCall sInner c.B dataA len

/-- Copying 32-bit word `k` from `so(src)` to `d(dst)`, through `r8`. -/
def cpw (src : Reg) (so : Nat) (dst : Reg) (d k : Nat) : List Instr :=
  [.load .w .r8 src (so + 4 * k), .store .w .r8 dst (d + 4 * k)]

/-- The `4 k` bytes at `so(src)` to `d(dst)`. -/
def copyW (k : Nat) (src : Reg) (so : Nat) (dst : Reg) (d : Nat) : List Instr :=
  (List.range k).flatMap (cpw src so dst d)

/-- The MAC, for `len` bytes of data, to the frame at `dst`: the inner state
finalized, the outer one updated with that digest and finalized, and its
first `D` bytes copied. -/
def hfin (len dst : Nat) : Prog isa :=
  .seq (c.finCall sInner (c.B + len)) (.seq (c.updCall sOuter c.B [.addi .r5 .r12 sTmp] c.D)
  (.seq (c.finCall sOuter (c.B + c.D)) (.block (scrBase ++ copyW (c.D / 4) .r12 sTmp .r11 dst))))

/-- `HMAC_K(data)` into the frame at `dst`, for `len` bytes of `data` at the
address `dataA` sets `r5` to. -/
def hmac (dataA : List Instr) (len dst : Nat) : Prog isa :=
  .seq c.hinit (.seq (c.hupd dataA len) (c.hfin len dst))

/-- `V = HMAC_K(V)`. -/
def hmacV : Prog isa := c.hmac [.addSp .r5 fV] c.D fV

/-- The pointers the messages need: the frame in `r11`, `scratch` in `r9`
and `d` in `r10`. -/
def msgPtrs : List Instr := [.addSp .r11 0, .load .d .r9 .r11 fScratch, .load .d .r10 .r11 fD]

/-- Copying byte `k` from `so(src)` to `d(dst)`, through `r8`. -/
def cpb (src : Reg) (so : Nat) (dst : Reg) (d k : Nat) : List Instr :=
  [.lbz .r8 src (so + k), .stb .r8 dst (d + k)]

/-- The `n` bytes at `so(src)` to `d(dst)`: 32-bit words, then the last
`n % 4` bytes one at a time. -/
def copyN (n : Nat) (src : Reg) (so : Nat) (dst : Reg) (d : Nat) : List Instr :=
  copyW (n / 4) src so dst d ++ (List.range (n % 4)).flatMap fun k => cpb src so dst d (4 * (n / 4) + k)

/-- The message `V ‖ b` (and `‖ d ‖ h` if `full`, `Q` bytes each, `h` at
the frame's `ho`) at `scratch + sMsg`, for `V` of `D` bytes, with the frame
in `r11`, `scratch` in `r9` and `d` in `r10`. -/
def msg (Q D b : Nat) (full : Bool) (ho : Nat := fH) : List Instr :=
  copyW (D / 4) .r11 fV .r9 sMsg ++ ([.li .r8 b, .stb .r8 .r9 (sMsg + D)] : List Instr) ++
    (if full then copyN Q .r10 0 .r9 (sMsg + D + 1) ++ copyN Q .r11 ho .r9 (sMsg + D + 1 + Q) else [])

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
def rekeyFull (b : Nat) : Prog isa :=
  .seq (.block (msgPtrs ++ msg c.len c.D b true c.fHo))
    (.seq (c.hmac [.addi .r5 .r12 sMsg] (c.D + 2 * c.len + 1) fK) c.hmacV)

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
def rekey : Prog isa :=
  .seq (.block (msgPtrs ++ msg c.len c.D 0 false))
    (.seq (c.hmac [.addi .r5 .r12 sMsg] (c.D + 1) fK) c.hmacV)

/-- The 32-bit digits of `n`, least significant first. -/
def nDigit (j : Nat) : BitVec 32 := BitVec.ofNat 32 (c.n >>> (32 * j))

/-- Digit `j` of the `Q`-byte number at `digest` (in `r9`), least
significant first, to `V`'s place, and digit `j` of it minus `n` (from the
carry `r10`, 1 for the first) to `K`'s, with the frame in `r11` and
`r0 = 2³² - 1`: the digit is the big-endian word at `digest + Q - 4 (j + 1)`;
`r7`, `r8` and `r12` change, and the carry goes to `r10`. -/
def subDigit (j : Nat) : List Instr :=
  ([.li .r8 (c.len - 4 * (j + 1)), .loadRev .w .r7 .r9 .r8, .store .w .r7 .r11 (fV + 4 * j)] : List Instr) ++
    movImm .r12 (c.nDigit j) ++
    [.logic .and .r12 .r12 .r0, .add .r7 .r7 .r0, .sub .r7 .r7 .r12, .add .r7 .r7 .r10,
      .store .w .r7 .r11 (fK + 4 * j), .lsr .d .r10 .r7 32]

/-- Digit `j` of the result, by the mask `r10` (all ones if subtracting `n`
did not borrow): the difference's if so, the number's if not, big-endian to
`h + Q - 4 (j + 1)` (`h` at the frame's `fHo`). -/
def selDigit (j : Nat) : List Instr :=
  [.load .w .r7 .r11 (fV + 4 * j), .load .w .r8 .r11 (fK + 4 * j),
    -- `x = d ^ ((d ^ x) & mask)`: the difference if it did not borrow.
    .logic .xor .r8 .r8 .r7, .logic .and .r8 .r8 .r10, .logic .xor .r7 .r7 .r8,
    .li .r12 (c.fHo + c.len - 4 * (j + 1)), .storeRev .w .r7 .r11 .r12]

/-- `h`: the `Q` bytes at `digest`, as a big-endian number, minus `n` if
that does not borrow, big-endian into the frame's `Q` bytes at `h`. -/
def reduce : List Instr :=
  ([.addSp .r11 0, .load .d .r9 .r11 fDigest] : List Instr) ++ mask32 ++ [.li .r10 1] ++
    (List.range (c.len / 4)).flatMap c.subDigit ++ ([.li .r12 0, .sub .r10 .r12 .r10] : List Instr) ++
    (List.range (c.len / 4)).flatMap c.selDigit

/-- `V = 0x01…`, `K = 0x00…`, all 64 bytes of each. -/
def initKV : List Instr :=
  ([.addSp .r11 0, .lis .r9 0x0101, .ori .r9 .r9 0x0101, .li .r10 0] : List Instr) ++
    (List.range 16).flatMap fun j => [.store .w .r9 .r11 (fV + 4 * j), .store .w .r10 .r11 (fK + 4 * j)]

/-- The candidates left. -/
def initCnt : List Instr := [.li .r9 c.tries, .addSp .r11 0, .store .d .r9 .r11 fCnt]

/-- Where `core` reads the digest, if `wide`: `h`, or the digest shifted
left by `sh` bits. -/
def fDg : Nat := if c.sh = 0 then fX else fXc

/-- `core(out, d, digest, k, scratch)`, with `k = V`, or, if `wide`, the
digest for `core` and the candidate at the frame's top. -/
def coreArgs : List Instr :=
  [.addSp .r11 0, .load .d .r3 .r11 fOut, .load .d .r4 .r11 fD] ++
    (if c.wide then [.addSp .r5 c.fDg, .addSp .r6 fT] else [.load .d .r5 .r11 fDigest, .addSp .r6 fV]) ++
    [.load .d .r7 .r11 fScratch]

/-- A conversion's block, after `scratch`'s load into `r3` (as `loadBytes`,
`shrWords` and `storeBytes` take their working space): the frame's `o` in
`r7`, and the mask `r10` all ones. -/
def convBody (o s : Nat) : List Instr :=
  .addSp .r7 o :: Impl.Weierstrass.PPC64LE.loadBytes c.len c.w sSlot .r7 ++
    Impl.Weierstrass.PPC64LE.shrWords c.w sSlot s ++ ([.li .r10 0, .subi .r10 .r10 1] : List Instr) ++
    Impl.Weierstrass.PPC64LE.storeBytes c.len c.w .r7 0 sSlot

/-- The `Q` bytes at the frame's `o`, as a big-endian number, shifted right by
`s` bits in place (`0 < s < 64`), through the words at `scratch + sSlot`. -/
def conv (o s : Nat) : Prog isa :=
  .seq (.block [.addSp .r11 0, .load .d .r3 .r11 fScratch]) (.block (c.convBody o s))

/-- Nine zero words at the frame's `o`, with the frame in `r11`. -/
def zero9 (o : Nat) : List Instr := .li .r8 0 :: (List.range 9).map fun j => .store .d .r8 .r11 (o + 8 * j)

/-- If `wide`: `h`, `Q - D` zero bytes then the digest, at `fX`, with the
frame in `r11` and the digest in `r9`. -/
def hPrep : List Instr :=
  ([.addSp .r11 0, .load .d .r9 .r11 fDigest] : List Instr) ++ zero9 fX ++ copyW (c.D / 4) .r9 0 .r11 (fX + c.len - c.D)

/-- If `wide` and `sh ≠ 0`: the digest for `core`, `Q - D - 1` zero bytes,
the digest and a zero byte, shifted right by `8 - sh` bits: the digest's
integer shifted left by `sh` bits, at `fXc`. -/
def xPrep : Prog isa :=
  if c.sh = 0 then .block [] else
    .seq (.block (([.addSp .r11 0, .load .d .r9 .r11 fDigest] : List Instr) ++ zero9 fXc ++
      copyW (c.D / 4) .r9 0 .r11 (fXc + c.len - c.D - 1))) (c.conv fXc (8 - c.sh))

/-- If `wide`: `V`'s `D` bytes to `T + j D`. -/
def keepV (j : Nat) : List Instr := .addSp .r11 0 :: copyW (c.D / 4) .r11 fV .r11 (fT + j * c.D)

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

/-- One candidate fewer, and `r12 ≠ 0` iff the signature failed (the low bit
of `r3` is 0) and candidates are left: `r12 = ((r3 & 1) - 1) & (count - 1)`. -/
def goOn : List Instr :=
  [.addSp .r11 0, .load .d .r9 .r11 fCnt, .subi .r9 .r9 1, .store .d .r9 .r11 fCnt,
    .li .r10 1, .logic .and .r8 .r3 .r10, .sub .r8 .r8 .r10, .logic .and .r12 .r8 .r9]

/-- Go on. -/
def again : List Instr := [.li .r12 1]

/-- Stop. -/
def stop : List Instr := [.li .r12 0]

/-- One candidate: `cand`, `core` with it, then, if it failed and
candidates are left, step h.3. -/
def tryOne : Prog isa :=
  .seq c.cand
  (.seq (.block c.coreArgs)
  (.seq (.call c.coreN c.coreC)
  (.seq (.block goOn)
    (.ite (.nonzero .d .r12) (.seq c.rekey (.block again)) (.block stop)))))

/-- `K`, `V` and `h` cleared, and the bytes above `fX` (`r3`, the result,
kept). -/
def wipe (hHigh : Bool := false) (wide : Bool := false) : List Instr :=
  ([.addSp .r11 0, .li .r12 0] : List Instr) ++ (List.range 22).map (fun j => .store .d .r12 .r11 (fK + 8 * j)) ++
    (List.range (extra hHigh wide / 8)).map fun j => .store .d .r12 .r11 (fX + 8 * j)

/-- `out`, `d`, `digest`, `scratch` and the table into the frame. -/
def saveArgs : List Instr :=
  [.addSp .r11 0, .store .d .r3 .r11 fOut, .store .d .r4 .r11 fD, .store .d .r5 .r11 fDigest,
    .store .d .r6 .r11 fScratch, .store .d .r8 .r11 fTab]

/-- `h` (and, if `wide`, the digest for `core`); and the initial `K` and `V`. -/
def start : Prog isa :=
  if c.wide then .seq (.block c.hPrep) (.seq c.xPrep (.block initKV)) else .block (c.reduce ++ initKV)

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block saveArgs)
  (.seq c.start
  (.seq (c.rekeyFull 0)
  (.seq (c.rekeyFull 1)
  (.seq (.block c.initCnt)
  (.seq (.loop c.tryOne (.nonzero .d .r12))
    (.block (wipe c.hHigh c.wide)))))))

/-- The signature for the hash function of this size, with `scratch` in
`r6` and the table in `r8`. -/
def sign : Prog isa :=
  .seq (.block [.mflr .r0])
    (.seq (.frame (.push .r0) (.frame (.alloc (frameBytes c.hHigh c.wide)) c.body (.free (frameBytes c.hHigh c.wide))) (.pop .r0))
      (.block [.mtlr .r0]))

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

/-- `b i` for the index `i` in `r9`, by comparisons with each of `is`
(`r9 - i` into `r10`): the last is taken for every other value. -/
def byIdx (b : Nat → Prog isa) : List Nat → Prog isa
  | [] => .block []
  | [i] => b i
  | i :: is => .seq (.block [.subi .r10 .r9 i]) (.ite (.zero .d .r10) (b i) (byIdx b is))

/-- `scratch` to `r6`, and the hash function's index (the table's word 3)
to `r9`. -/
def entry : List Instr := [.logic .or .r6 .r7 .r7, .load .d .r9 .r8 24]

/-- The function of the code `c` for a hash function's sizes, for the
signature `name`. -/
def shapeName (name : String) (c : Cfg) : String := s!"{name}_d{c.D}b{c.B}"

/-- `vg_ecdsa_<curve>_sign` (`name`): the signature with the code `cfg i` for
the hash function of index `i` of the table `hash`, which it calls (a
function of its own, `shapeName`, so that the comparisons' branches skip
only calls), in a frame that saves the return address. -/
def signT (name : String) (cfg : Nat → Cfg) : Prog isa :=
  .seq (.block [.mflr .r0])
    (.seq (.frame (.push .r0)
        (.seq (.block entry) (byIdx (fun i => .call (shapeName name (cfg i)) (cfg i).sign) idxs)) (.pop .r0))
      (.block [.mtlr .r0]))

end VG.Impl.Ecdsa.Rfc6979.PPC64LE
