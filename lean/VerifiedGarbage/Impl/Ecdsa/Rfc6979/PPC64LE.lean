module

public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Impl.Mont.PPC64LE
public import VerifiedGarbage.Impl.Weierstrass.PPC64LE
public import VerifiedGarbage.Impl.RsaOaep.PPC64LE

/-!
# Deterministic ECDSA (RFC 6979) on PPC64LE, with HMAC through a table

`vg_ecdsa_<curve>_sign(out = r3, d = r4, digest = r5, digest_len = r6,
scratch = r7, hmac = r8) -> r3` (`sign`), for a curve of `Q`-byte scalars in
`w` words, as on x86-64 (`Impl/Ecdsa/Rfc6979/X86_64.lean`): RFC 6979 §3.2
with HMAC over the hash function of the table `hmac` of the interface
`Hmac` (`Spec/HmacTable.lean`), whose functions it calls indirectly
(`tcall`: the table's word into `r12`, then `bctrl`): HMAC's `init` (word
0), which keys the inner and outer streaming states, the streaming `update`
(word 1), on the inner state, and HMAC's `finalize` (word 2), which writes
the MAC; and each candidate tried by calling `core`, the signature with a
given `k` (`vg_ecdsa_<curve>_sign_k`), which reads `Q` bytes of the digest
and of `k`, and takes their leftmost `qlen` bits (`bits2int`, a right shift
by `sh = 8 Q - qlen` bits).

One body serves every hash function: the digest length `D` and HMAC's block
size `B` are the table's words of data 4 and 5, which the code copies to the
frame on entry (`saveArgs`) and reads wherever it needs them, as the lengths
and counts it passes (all public). Nothing in the code depends on the hash
function but those two words and the table's functions.

Each HMAC is `init` with the key `K` (`D` bytes, in the frame) or the states
for `K` restored (`restore`, from a copy `save` made after an earlier
`init` with the same `K`), the inner state updated with `V` (`D` bytes, in
the frame), then with the message `b ‖ d ‖ h` or `b` (`msg`, in `scratch`,
its length the curve's), and `finalize`, which writes the MAC to `K` or `V`
in the frame, with the count `B + D + len`.

The digest's leftmost `min(D, Q)` bytes, after `Q - min(D, Q)` zero bytes,
are `X` (`prepX`, by a byte loop, `copyLoop`, the minimum chosen without a
branch), a `Q`-byte number: the digest's `bits2int` if `sh = 0`. Then:

* unless `big` (all but P-521, whose `Q` is a multiple of 4): `h =
  bits2octets(digest)` is `X` minus `n` if it is at least `n` (a conditional
  subtraction by 32-bit digits, `reduce`, as `2^(8 Q) < 2 n`), and `core`
  reads `X` as its digest;
* if `big` (P-521, whose scalars are longer than every digest, with
  `sh ≠ 0`): `X`'s integer is below `n`, so `h` is `X` itself, and `core`
  reads the digest's integer shifted left by `sh` bits (`prepC`, at `fXc`:
  `Q - 1 - D` zero bytes, the digest and a zero byte, shifted right by
  `8 - sh` bits through the words at `scratch + sSlot`, `conv`).

The candidate `k` is the leftmost `Q` bytes of `T`, the `V`s of successive
`V = HMAC_K(V)` while `T` is shorter than `Q` bytes (`cand`: a loop whose
count is public, each `V` appended to `T` by `copyLoop`), shifted right by
`sh` bits in place if `big` (`candTop`).

The return address is moved to `r0` and pushed (the calls replace it), then
a frame of `frameBytes` bytes is allocated: above its 32-byte header, `K` and
`V` (64 bytes each, of which the first `D` are used), the length of `T`, the
number of candidates left, the pointers `scratch`, `digest`, `d` and `out`,
`D`, `B` and the table's address; then `h` (72 bytes, unless `big`), `X`,
`core`'s digest if `big` (72 bytes each), and `T` (136 bytes). The calls use
only `scratch`, which `core` overwrites entirely, and the 96 bytes of stack
below the frame; `K`, `V` and everything above the table's address are
cleared before the frame is freed. In `scratch`: HMAC's inner and outer
streaming states (192 bytes each), the working space of the table's
functions, the message, the words of a shift, and the copy of the states
for `K`.

1. `X`; `h` (`reduce`, or `prepC`); `V = 0x01…`, `K = 0x00…`.
2. Steps d to g: `K = HMAC_K(V ‖ 0x00 ‖ d ‖ h)`, `V = HMAC_K(V)`,
   `K = HMAC_K(V ‖ 0x01 ‖ d ‖ h)`, `V = HMAC_K(V)`.
3. At most `tries` times: the candidate `k` (`cand`) and
   `core(out, d, digest, k, scratch)`; if it failed and candidates are left,
   `K = HMAC_K(V ‖ 0x00)`, `V = HMAC_K(V)` and again. Whether to go on, in
   `r12`, is computed without branches from the low bit of `core`'s result,
   so that the code branches only on it: the number of candidates tried is
   all it reveals.

`core` writes the signature or zeros to `out`, and its result is ours.

A block addresses memory only at the frame (through `r11`, set by `addSp`),
at the table (through `r8`, on entry), or at a pointer an earlier
instruction of the block loaded from the frame (the table's address in
`tcall`), plus public offsets: the taint analysis of each block, once for
each curve, knows its addresses are public.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Rfc6979.PPC64LE

open VG.PPC64LE
open VG.Impl.Mont.PPC64LE (movImm mask32)
open VG.Impl.RsaOaep.PPC64LE (Fns copyLoop)

/-! Where things are in the frame. -/
def fK : Nat := 32
def fV : Nat := 96
/-- The length of `T`. -/
def fTlen : Nat := 160
def fCnt : Nat := 168
def fScratch : Nat := 176
def fDigest : Nat := 184
def fD : Nat := 192
def fOut : Nat := 200
/-- The digest length `D` and HMAC's block size `B`. -/
def fDl : Nat := 208
def fBl : Nat := 216
/-- The table's address. -/
def fTab : Nat := 224
/-- `h` (72 bytes), unless `big`. -/
def fH : Nat := 232
/-- `X` (72 bytes): the digest's leftmost bytes, as a `Q`-byte number; `h` if `big`. -/
def fX : Nat := 304
/-- If `big`: the digest for `core` (72 bytes). -/
def fXc : Nat := 376
/-- The candidate `T` (136 bytes). -/
def fT : Nat := 448
/-- The frame's size, a multiple of 16. -/
def frameBytes : Nat := 592

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

/-- `r12 ← scratch`, with the frame in `r11`. -/
def scrBase : List Instr := [.addSp .r11 0, .load .d .r12 .r11 fScratch]

/-! ## HMAC through the table -/

/-- The indirect call of the table's function `j`, among `ts`: the table's
address into `r12`, its word `j` into `r12`, then `bctrl`. -/
def tcall (j : Nat) (ts : List (String × Prog isa)) : Prog isa :=
  .seq (.block [.addSp .r12 0, .load .d .r12 .r12 fTab, .load .d .r12 .r12 (8 * j)])
    (Code.icalls .bctrl ts)

/-- The arguments of HMAC's `init`: the states, the key `K` of `D` bytes,
the working space. -/
def initArgs : List Instr :=
  scrBase ++ [.addi .r3 .r12 sInner, .addi .r4 .r12 sOuter, .addSp .r5 fK, .load .d .r6 .r11 fDl,
    .addi .r7 .r12 sWork]

/-- The arguments of the streaming `update` with `V`: the inner state, the
`B` bytes it holds, `V`'s `D` bytes, the working space. -/
def updVArgs : List Instr :=
  scrBase ++ [.addi .r3 .r12 sInner, .load .d .r4 .r11 fBl, .addSp .r5 fV, .load .d .r6 .r11 fDl,
    .addi .r7 .r12 sWork]

/-- The arguments of the streaming `update` with the message: the inner
state, the `B + D` bytes it holds, the message's `len` bytes, the working
space. -/
def updMArgs (len : Nat) : List Instr :=
  scrBase ++ [.addi .r3 .r12 sInner, .load .d .r4 .r11 fBl, .load .d .r6 .r11 fDl, .add .r4 .r4 .r6,
    .addi .r5 .r12 sMsg, .li .r6 len, .addi .r7 .r12 sWork]

/-- The arguments of HMAC's `finalize`: the states, the `B + D + len` bytes
the inner one holds, the MAC's place in the frame, the working space. -/
def finArgs (len dst : Nat) : List Instr :=
  scrBase ++ [.addi .r3 .r12 sInner, .addi .r4 .r12 sOuter, .load .d .r5 .r11 fBl, .load .d .r6 .r11 fDl,
    .add .r5 .r5 .r6, .addi .r5 .r5 len, .addSp .r6 dst, .addi .r7 .r12 sWork]

/-- HMAC's states for `K`, by `init`. -/
def initK : Prog isa := .seq (.block initArgs) (tcall 0 c.f.init)

/-- The inner state updated with `V`. -/
def updV : Prog isa := .seq (.block updVArgs) (tcall 1 c.f.upd)

/-- The inner state updated with the message's `len` bytes. -/
def updM (len : Nat) : Prog isa := .seq (.block (updMArgs len)) (tcall 1 c.f.upd)

/-- The MAC, of `D + len` bytes of text, to the frame at `dst`. -/
def fin (len dst : Nat) : Prog isa := .seq (.block (finArgs len dst)) (tcall 2 c.f.fin)

/-- Doubleword `j` from `so(src)` to `d(dst)`, through `r9`. -/
def cpd (src : Reg) (so : Nat) (dst : Reg) (d j : Nat) : List Instr :=
  [.load .d .r9 src (so + 8 * j), .store .d .r9 dst (d + 8 * j)]

/-- HMAC's two states (384 bytes) copied from `scratch + sInner` to `scratch + sSave`
(`toSave`) or back, with `scratch` in `r12`, through `r9`. -/
def copyStates (toSave : Bool) : List Instr :=
  if toSave then (List.range 48).flatMap (cpd .r12 sInner .r12 sSave)
  else (List.range 48).flatMap (cpd .r12 sSave .r12 sInner)

/-- The states for `K` saved. -/
def save : List Instr := scrBase ++ copyStates true

/-- The states for `K` restored from the copy. -/
def restore : List Instr := scrBase ++ copyStates false

/-- `V = HMAC_K(V)`, saving the states for `K`. -/
def hmacVS : Prog isa := .seq c.initK (.seq (.block save) (.seq c.updV (c.fin 0 fV)))

/-- `V = HMAC_K(V)`, from the saved states for `K`. -/
def hmacVR : Prog isa := .seq (.block restore) (.seq c.updV (c.fin 0 fV))

/-- `K = HMAC_K(V ‖ msg)`, for the message's `len` bytes, from the states
for `K` by `init` (`fresh`) or restored. -/
def hmacK (fresh : Bool) (len : Nat) : Prog isa :=
  .seq (if fresh then c.initK else .block restore) (.seq c.updV (.seq (c.updM len) (c.fin len fK)))

/-- The pointers the messages need: the frame in `r11`, `scratch` in `r9`,
`d` in `r10`. -/
def msgPtrs : List Instr := [.addSp .r11 0, .load .d .r9 .r11 fScratch, .load .d .r10 .r11 fD]

/-- Copying 32-bit word `k` from `so(src)` to `d(dst)`, through `r8`. -/
def cpw (src : Reg) (so : Nat) (dst : Reg) (d k : Nat) : List Instr :=
  [.load .w .r8 src (so + 4 * k), .store .w .r8 dst (d + 4 * k)]

/-- Copying byte `k` from `so(src)` to `d(dst)`, through `r8`. -/
def cpb (src : Reg) (so : Nat) (dst : Reg) (d k : Nat) : List Instr :=
  [.lbz .r8 src (so + k), .stb .r8 dst (d + k)]

/-- The `n` bytes at `so(src)` to `d(dst)`: 32-bit words, then the last
`n % 4` bytes one at a time. -/
def copyN (n : Nat) (src : Reg) (so : Nat) (dst : Reg) (d : Nat) : List Instr :=
  (List.range (n / 4)).flatMap (cpw src so dst d) ++
    (List.range (n % 4)).flatMap fun k => cpb src so dst d (4 * (n / 4) + k)

/-- The message `b` (and `‖ d ‖ h` if `full`, `Q` bytes each) at
`scratch + sMsg`, with the frame in `r11`, `scratch` in `r9` and `d` in
`r10`: `b` a byte, then the private key and `h` from the frame. -/
def msg (b : Nat) (full : Bool) : List Instr :=
  ([.li .r8 b, .stb .r8 .r9 sMsg] : List Instr) ++
    (if full then copyN c.len .r10 0 .r9 (sMsg + 1) ++ copyN c.len .r11 c.fHo .r9 (sMsg + 1 + c.len) else [])

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g), the
states for the new `K` saved; for `b = 1` (step f), the states for `K` are
the copy step e saved. -/
def rekeyFull (b : Nat) : Prog isa :=
  .seq (.block msgPtrs) (.seq (.block (c.msg b true)) (.seq (c.hmacK (b = 0) (1 + 2 * c.len)) c.hmacVS))

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
def rekey : Prog isa :=
  .seq (.block msgPtrs) (.seq (.block (c.msg 0 false)) (.seq (c.hmacK true 1) c.hmacVS))

/-! ## Bytes, numbers and `h` -/

/-- Nine zero doublewords at the frame's `o`, with the frame in `r11`. -/
def zero9 (o : Nat) : List Instr :=
  .li .r9 0 :: (List.range 9).map fun j => .store .d .r9 .r11 (o + 8 * j)

/-- `r6 = min(D, Q)`, without a branch, with the frame in `r11`: `r10` all
ones if `D < Q` (the borrow of `D - Q`), and `Q ^ ((D ^ Q) & r10)`. -/
def minDQ : List Instr :=
  [.load .d .r6 .r11 fDl, .li .r9 c.len, .subc .r10 .r6 .r9, .sube .r10 .r10 .r10, .logic .xor .r12 .r6 .r9,
    .logic .and .r12 .r12 .r10, .logic .xor .r6 .r9 .r12]

/-- The arguments of `X`'s copy: `X` cleared; then `r6 = min(D, Q)`, the
digest in `r4`, `X + Q - r6` in `r5`. -/
def xArgs : List Instr :=
  .addSp .r11 0 :: zero9 fX ++ c.minDQ ++
    ([.addSp .r5 (fX + c.len), .sub .r5 .r5 .r6, .load .d .r4 .r11 fDigest] : List Instr)

/-- `X`: `Q - min(D, Q)` zero bytes, then the digest's leftmost `min(D, Q)`. -/
def prepX : Prog isa := .seq (.block c.xArgs) copyLoop

/-- The 32-bit digits of `n`, least significant first. -/
def nDigit (j : Nat) : BitVec 32 := BitVec.ofNat 32 (c.n >>> (32 * j))

/-- Digit `j` of the `Q`-byte number `X` (at `r9`), least significant first,
to `V`'s place, and digit `j` of it minus `n` (from the carry `r10`, 1 for
the first) to `K`'s, with the frame in `r11` and `r0 = 2³² - 1`: the digit
is the big-endian word at `X + Q - 4 (j + 1)`; `r7`, `r8` and `r12` change,
and the carry goes to `r10`. -/
def subDigit (j : Nat) : List Instr :=
  ([.li .r8 (c.len - 4 * (j + 1)), .loadRev .w .r7 .r9 .r8, .store .w .r7 .r11 (fV + 4 * j)] : List Instr) ++
    movImm .r12 (c.nDigit j) ++
    [.logic .and .r12 .r12 .r0, .add .r7 .r7 .r0, .sub .r7 .r7 .r12, .add .r7 .r7 .r10,
      .store .w .r7 .r11 (fK + 4 * j), .lsr .d .r10 .r7 32]

/-- Digit `j` of the result, by the mask `r10` (all ones if subtracting `n`
did not borrow): the difference's if so, the number's if not, big-endian to
`h + Q - 4 (j + 1)`. -/
def selDigit (j : Nat) : List Instr :=
  [.load .w .r7 .r11 (fV + 4 * j), .load .w .r8 .r11 (fK + 4 * j),
    -- `x = d ^ ((d ^ x) & mask)`: the difference if it did not borrow.
    .logic .xor .r8 .r8 .r7, .logic .and .r8 .r8 .r10, .logic .xor .r7 .r7 .r8,
    .li .r12 (fH + c.len - 4 * (j + 1)), .storeRev .w .r7 .r11 .r12]

/-- `h`, unless `big`: `X`, as a big-endian number, minus `n` if that does
not borrow, big-endian into the frame's `Q` bytes at `h`. -/
def reduce : List Instr :=
  ([.addSp .r11 0, .addSp .r9 fX] : List Instr) ++ mask32 ++ [.li .r10 1] ++
    (List.range (c.len / 4)).flatMap c.subDigit ++ ([.li .r12 0, .sub .r10 .r12 .r10] : List Instr) ++
    (List.range (c.len / 4)).flatMap c.selDigit

/-- A conversion's block, after `scratch`'s load into `r3` (as `loadBytes`,
`shrWords` and `storeBytes` take their working space): the frame's `o` in
`r7`, and the mask `r10` all ones. -/
def convBody (o s : Nat) : List Instr :=
  .addSp .r7 o :: Impl.Weierstrass.PPC64LE.loadBytes c.len c.w sSlot .r7 ++
    Impl.Weierstrass.PPC64LE.shrWords c.w sSlot s ++ ([.li .r10 0, .subi .r10 .r10 1] : List Instr) ++
    Impl.Weierstrass.PPC64LE.storeBytes c.len c.w .r7 0 sSlot

/-- The `Q` bytes at the frame's `o`, as a big-endian number, shifted right by
`s` bits in place (`0 < s < 64`), through the words at `scratch + sSlot`. -/
def conv (o s : Nat) : List Instr := [.addSp .r11 0, .load .d .r3 .r11 fScratch] ++ c.convBody o s

/-- The arguments of the copy of `core`'s digest, if `big`: it cleared;
then `r6 = D`, the digest in `r4`, `fXc + Q - 1 - D` in `r5`. -/
def xcArgs : List Instr :=
  .addSp .r11 0 :: zero9 fXc ++
    ([.load .d .r6 .r11 fDl, .addSp .r5 (fXc + c.len - 1), .sub .r5 .r5 .r6, .load .d .r4 .r11 fDigest] :
      List Instr)

/-- If `big`: `core`'s digest, `Q - 1 - D` zero bytes, the digest and a zero
byte, shifted right by `8 - sh` bits: the digest's integer shifted left by
`sh` bits. -/
def prepC : Prog isa := .seq (.block c.xcArgs) (.seq copyLoop (.block (c.conv fXc (8 - c.sh))))

/-- `h`: `reduce`, or, if `big`, `X` itself, with `core`'s digest. -/
def prepH : Prog isa := if c.big then c.prepC else .block c.reduce

/-- `V = 0x01…`, `K = 0x00…`, all 64 bytes of each. -/
def initKV : List Instr :=
  ([.addSp .r11 0, .lis .r9 0x0101, .ori .r9 .r9 0x0101, .li .r10 0] : List Instr) ++
    (List.range 16).flatMap fun j => [.store .w .r9 .r11 (fV + 4 * j), .store .w .r10 .r11 (fK + 4 * j)]

/-- The candidates left. -/
def initCnt : List Instr := [.li .r9 c.tries, .addSp .r11 0, .store .d .r9 .r11 fCnt]

/-! ## The candidates -/

/-- `T` empty. -/
def tInit : List Instr := [.li .r9 0, .addSp .r11 0, .store .d .r9 .r11 fTlen]

/-- The arguments of `V`'s copy to the end of `T`: `r6 = D`, `V` in `r4`,
`T + |T|` in `r5`. -/
def keepArgs : List Instr :=
  [.addSp .r11 0, .addSp .r4 fV, .addSp .r5 fT, .load .d .r9 .r11 fTlen, .add .r5 .r5 .r9,
    .load .d .r6 .r11 fDl]

/-- `T` longer by `D` bytes, and `r12` nonzero (all ones) iff it is still
shorter than `Q` (the borrow of `|T| - Q`). -/
def tStep : List Instr :=
  [.addSp .r11 0, .load .d .r9 .r11 fTlen, .load .d .r10 .r11 fDl, .add .r9 .r9 .r10, .store .d .r9 .r11 fTlen,
    .li .r10 c.len, .subc .r12 .r9 .r10, .sube .r12 .r12 .r12]

/-- One `V` of the candidate: `V = HMAC_K(V)`, appended to `T`. -/
def candStep : Prog isa := .seq c.hmacVR (.seq (.block keepArgs) (.seq copyLoop (.block c.tStep)))

/-- If `big`: `T`'s first `Q` bytes shifted right by `sh` bits. -/
def candTop : List Instr := if c.big then c.conv fT c.sh else []

/-- The candidate: `T`, the `V`s of successive `V = HMAC_K(V)` while it is
shorter than `Q` bytes, its leftmost `Q` bytes shifted right by `sh` bits if
`big`. -/
def cand : Prog isa := .seq (.block tInit) (.seq (.loop c.candStep (.nonzero .d .r12)) (.block c.candTop))

/-- `core(out, d, digest, k, scratch)`: the digest `X` (or, if `big`, the
one at `fXc`) and `k = T`. -/
def coreArgs : List Instr :=
  [.addSp .r11 0, .load .d .r3 .r11 fOut, .load .d .r4 .r11 fD, .addSp .r5 c.fDg, .addSp .r6 fT,
    .load .d .r7 .r11 fScratch]

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

/-- `K` and `V`, and everything above the table's address, cleared (`r3`,
the result, kept). -/
def wipe : List Instr :=
  ([.addSp .r11 0, .li .r12 0] : List Instr) ++ (List.range 16).map (fun j => .store .d .r12 .r11 (fK + 8 * j)) ++
    (List.range 45).map fun j => .store .d .r12 .r11 (fH + 8 * j)

/-- `out`, `d`, `digest`, `scratch` and the table into the frame, and `D`
and `B`, the table's words of data 4 and 5. -/
def saveArgs : List Instr :=
  [.addSp .r11 0, .store .d .r3 .r11 fOut, .store .d .r4 .r11 fD, .store .d .r5 .r11 fDigest,
    .store .d .r7 .r11 fScratch, .store .d .r8 .r11 fTab, .load .d .r9 .r8 32, .store .d .r9 .r11 fDl,
    .load .d .r9 .r8 40, .store .d .r9 .r11 fBl]

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block saveArgs)
  (.seq c.prepX
  (.seq c.prepH
  (.seq (.block initKV)
  (.seq (c.rekeyFull 0)
  (.seq (c.rekeyFull 1)
  (.seq (.block c.initCnt)
  (.seq (.loop c.tryOne (.nonzero .d .r12))
    (.block wipe))))))))

/-- `vg_ecdsa_<curve>_sign`. -/
def sign : Prog isa :=
  .seq (.block [.mflr .r0])
    (.seq (.frame (.push .r0) (.frame (.alloc frameBytes) c.body (.free frameBytes)) (.pop .r0))
      (.block [.mtlr .r0]))

end Cfg

end VG.Impl.Ecdsa.Rfc6979.PPC64LE
