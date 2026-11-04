module

public import VerifiedGarbage.Impl.RsaOaep.Arm
public import VerifiedGarbage.Impl.Weierstrass.Arm

/-!
# Deterministic ECDSA (RFC 6979) on 32-bit ARM, with the hash function of a table

`vg_ecdsa_<curve>_sign(out = r0, d = r1, digest = r2, digest_len = r3,
scratch = [sp], hash = [sp, #4]) -> r0` (`signT`), for a curve of `Q`-byte
scalars in `w` 32-bit words: RFC 6979 §3.2 with HMAC over the hash function
of the table `hash` of the interface `Hash` (`Spec/HashTable.lean`), whose
streaming `init`, `update` and `finalize` (its words 0 to 2) it calls
indirectly (`tcall`), and each candidate tried by calling `core`, the
signature with a given `k` (`vg_ecdsa_<curve>_sign_k`), which reads `Q` bytes
of the digest and of `k`, and takes the digest's leftmost `qlen` bits
(`bits2int`, a right shift by `sh = 8 Q - qlen` bits), as on x86-64
(`Impl/Ecdsa/Rfc6979/X86_64.lean`).

Which table `hash` is, is public (`Abi.withTables`), and so is the hash
function's index in `Mgf1.hashes`, its word 3: `signT` chooses by it
(`byIdx`, comparisons of `r12` with each index of `idxs`) the code for that
hash function's digest length `D` and block size `B` (`shapeOf`), `sign` of a
`Cfg`, in which both are constants. Everything below is that code.

HMAC (`hmac`) is computed from the table's streaming functions: the key `K`
(`D` bytes, in the frame) padded to a block and XORed with `ipad` (`padBlk`,
a word at a time, into `scratch + sPad`), the inner state set by `init` and
updated with it, the same with `opad` for the outer state (`hinit`); the
inner state updated with the data (`hupd`); then the inner state finalized
into `scratch + sTmp`, the outer one updated with that digest and finalized
there too, and its first `D` bytes copied to the MAC's place in the frame
(`hfin`). `update`'s stack arguments (the data, its length and the working
space, in `r1`, `r7` and `r10`) are pushed by a frame of its own
(`push {r1, r7, r10, r12}`, the function's address in `r12`, the padding),
and `finalize`'s (its output and the working space, `r1` and `r12`) by
`push {r1, r12}`, the function's address in `r7`: the stack pointer stays
8-byte aligned.

Two kinds of curve and hash function, as on x86-64:

* `Q ≤ D` (P-192, P-224, P-256 and P-384, and brainpoolP512r1 with SHA-512):
  one `V` makes a candidate, its leftmost `Q` bytes; `bits2octets` is a
  conditional subtraction of `n` from the digest's leftmost `Q` bytes
  (`reduce`), by 16-bit digits (the model's `adc` sets no flags); and `core`
  reads the digest and `V` in place.
* `D < Q` (`wide`): `m` `V`s make a candidate `T` (`candW`), at `fT`, of which
  `core` reads the first `Q` bytes, shifted right in place by `sh` bits; the
  digest's integer is below `n`, so `h = bits2octets(digest)` is `Q - D` zero
  bytes then the digest (`hPrep`, at `fX`); and `core` reads `h`, or, if
  `sh ≠ 0` (P-521), the digest's integer shifted left by `sh` bits (`xPrep`,
  at `fXc`: `Q - D - 1` zero bytes, the digest and a zero byte, shifted right
  by `8 - sh` bits). The shifts are through the words at `scratch + sSlot`
  (`conv`, with the table and `d` kept in `r2` and `r3` meanwhile, as it
  uses `r4` and `r5`).

A frame of `216 + 4 e` bytes is allocated: from `sp`, `K` and `V` (64 bytes
each, of which the first `D` are used), `h` (48 bytes, unless `wide` or
`hHigh`), `out`, and our caller's `r4`–`r11` and `lr` (the calls replace
`lr`); then, if `wide`, `h`, the digest for `core` and `T` (72, 72 and 128
bytes), or, if `hHigh` (64-byte scalars, as brainpoolP512r1's), `h` in 64
bytes. The functions we call preserve `r4`–`r11`, which hold what lives
across the calls: the table in `r4`, `d` and `digest` in `r5` and `r6`, the
frame in `r8`, the number of candidates left in `r9` and `scratch` in `r11`
(the last two read from the stack in the prologue). The calls use only
`scratch`, which `core` overwrites entirely, and the stack below the frame;
`K`, `V`, `h` and the words at the frame's top are cleared before the frame
is freed. In `scratch`: HMAC's inner and outer streaming states, the working
space of the streaming functions, the padded key and the inner digest, the
message of steps d, f and h.3, and the words of the conversions.

1. `h = bits2octets(digest)`: unless `wide`, the leftmost `Q` bytes, minus
   `n` if they are at least `n` (`reduce`, as `2^(8 Q) < 2n`). If `wide`,
   `hPrep` and `xPrep`.
2. Steps b to g: `V = 0x01…`, `K = 0x00…`, `K = HMAC_K(V ‖ 0x00 ‖ d ‖ h)`,
   `V = HMAC_K(V)`, `K = HMAC_K(V ‖ 0x01 ‖ d ‖ h)`, `V = HMAC_K(V)`.
3. At most `tries` times: `V = HMAC_K(V)` (`m` times, each copied to `T`, if
   `wide`), the candidate `k`, and `core(out, d, digest, k, scratch)`; if it
   failed and candidates are left, `K = HMAC_K(V ‖ 0x00)`, `V = HMAC_K(V)`
   and again. Whether to go on is computed without branches, so that the
   code branches only on it: the number of candidates tried is all it
   reveals.

`core` writes the signature or zeros to `out`, and its return value is ours.
Every address is the frame's base (in `r8`, from `sp` in the prologue, and
in `r12` for the prologue and the epilogue), the table (`r4`) or a pointer
argument plus a constant (in a conversion, `r1` and `r12` are the frame's
base and `scratch` plus a constant).
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Rfc6979.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Stream.Arm (scrAt)
open VG.Impl.RsaOaep.Arm (Fns)

/-! Where things are in the frame. -/
def fK : Nat := 0
def fV : Nat := 64
def fH : Nat := 128
/-- `out`. -/
def fOut : Nat := 176
def fSave : Nat := 180
/-- Above the saved registers: `h`, if `wide` or `hHigh`. -/
def fX : Nat := 216
/-- If `wide`: the digest for `core`, if `sh ≠ 0`. -/
def fXc : Nat := 288
/-- If `wide`: the candidate `T`. -/
def fT : Nat := 360

/-- The words at the frame's top: `h`, the digest for `core` and `T`, if
`wide`, or `h`, if `hHigh`. -/
def extra (wide : Bool) (hHigh : Bool := false) : Nat := if wide then 68 else if hHigh then 16 else 0
/-- The frame's size, a multiple of 8. -/
def frameBytes (wide : Bool) (hHigh : Bool := false) : Nat := 216 + 4 * extra wide hHigh

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

/-- Our caller's registers, where the frame keeps them (`r8`, the frame's
base afterwards, last). -/
def saved : List (Reg × Nat) :=
  [(.r4, fSave), (.r5, fSave + 4), (.r6, fSave + 8), (.r7, fSave + 12), (.r9, fSave + 16),
    (.r10, fSave + 20), (.r11, fSave + 24), (.lr, fSave + 28), (.r8, fSave + 32)]

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
  /-- The 32-bit words of the curve's scalars (seven for P-224; otherwise an even number). -/
  w : Nat
  /-- The bytes of the curve's scalars, `Q`. -/
  len : Nat := 4 * w
  /-- The bits `core` shifts its digest right by, `8 Q - qlen`. -/
  sh : Nat := 0
  /-- Whether `h` is kept at the frame's top, in 16 more words: for scalars
  of 64 bytes, which the 48 bytes below `out` do not hold (and the hash is
  no shorter). -/
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

/-- The frame's size. -/
def fb : Nat := frameBytes c.wide c.hHigh

/-- Where `h` is in the frame. -/
def fHo : Nat := if c.wide || c.hHigh then fX else fH

/-- Our caller's registers into the frame (through `r12`, its base); the
table (`hash`, our stack argument 1) to `r4`, `out` to the frame, `d` and
`digest` to `r5` and `r6`, `scratch` (stack argument 0) to `r11`, and the
frame's base to `r8`. -/
def prologue : List Instr :=
  .addSp .r12 0 :: saved.map (fun p => .str p.1 .r12 p.2) ++
    ([.ldr .r4 .r12 (c.fb + 4), .str .r0 .r12 fOut, .mov .r5 (.reg .r1), .mov .r6 (.reg .r2),
      .ldr .r11 .r12 c.fb, .mov .r8 (.reg .r12)] : List Instr)

/-- Our caller's registers back, through `r12` (the frame's base). -/
def epilogue : List Instr := saved.map fun p => .ldr p.1 .r12 p.2

/-! ## HMAC through the table -/

/-- The table's word `j`, the address of its function `j`, into `r`. -/
def tload (r : Reg) (j : Nat) : List Instr := [.ldr r .r4 (4 * j)]

/-- The streaming `init` of the state at `scratch + o`. -/
def initCall (o : Nat) : Prog isa :=
  .seq (.block (scrAt .r0 o)) (.seq (.block (tload .r12 0)) (Code.icalls (.blx .r12) c.f.init))

/-- The arguments of the streaming `update` of the state at `scratch + o`,
which holds `cnt` bytes (`r2:r3`), with the data (at the address `dataA` sets
`r1` to) of `len` bytes (`r7`), and the working space (`r10`). -/
def updArgs (o cnt : Nat) (dataA : List Instr) (len : Nat) : List Instr :=
  scrAt .r0 o ++ dataA ++ ([.movw .r2 (BitVec.ofNat 16 cnt), .mov .r3 (.imm 0),
    .movw .r7 (BitVec.ofNat 16 len)] : List Instr) ++ scrAt .r10 sWork

def updCall (o cnt : Nat) (dataA : List Instr) (len : Nat) : Prog isa :=
  .seq (.block (updArgs o cnt dataA len)) (.seq (.block (tload .r12 1))
    (.frame (.push [.r1, .r7, .r10, .r12]) (Code.icalls (.blx .r12) c.f.upd) (.pop .r1 16)))

/-- The arguments of the streaming `finalize` of the state at `scratch + o`,
which holds `cnt` bytes, into `scratch + sTmp` (`r1`), with the working
space (`r12`). -/
def finArgs (o cnt : Nat) : List Instr :=
  scrAt .r0 o ++ ([.movw .r2 (BitVec.ofNat 16 cnt), .mov .r3 (.imm 0)] : List Instr) ++ scrAt .r1 sTmp ++
    scrAt .r12 sWork

def finCall (o cnt : Nat) : Prog isa :=
  .seq (.block (finArgs o cnt)) (.seq (.block (tload .r7 2))
    (.frame (.push [.r1, .r12]) (Code.icalls (.blx .r7) c.f.fin) (.pop .r1 8)))

/-- Word `k` of the key `K` (the frame's first `D` bytes) padded to `B`
bytes, XORed with the pad in `r1`, to `scratch + sPad`. -/
def padW (k : Nat) : List Instr :=
  if k < c.D / 4 then [.ldr .r0 .r8 (fK + 4 * k), .dp .eor .r0 .r0 (.reg .r1), .str .r0 .r11 (sPad + 4 * k)]
  else [.str .r1 .r11 (sPad + 4 * k)]

/-- `K₀ ⊕ pad` (a block) at `scratch + sPad`. -/
def padBlk (x : BitVec 32) : List Instr :=
  ([.movw .r1 (x.setWidth 16), .movt .r1 ((x >>> 16).setWidth 16)] : List Instr) ++
    (List.range (c.B / 4)).flatMap c.padW

/-- HMAC's states for the key `K`: each set by `init`, then updated with
the padded key. -/
def hinit : Prog isa :=
  .seq (c.initCall sInner) (.seq (c.initCall sOuter)
  (.seq (.block (c.padBlk ipad32)) (.seq (c.updCall sInner 0 (scrAt .r1 sPad) c.B)
  (.seq (.block (c.padBlk opad32)) (c.updCall sOuter 0 (scrAt .r1 sPad) c.B)))))

/-- The inner state updated with `len` bytes of data at the address `dataA`
sets `r1` to. -/
def hupd (dataA : List Instr) (len : Nat) : Prog isa := c.updCall sInner c.B dataA len

/-- The `4 k` bytes at `[src + so]` to `[dst + d]`, a word at a time through `r0`. -/
def copyN (k : Nat) (src : Reg) (so : Nat) (dst : Reg) (d : Nat) : List Instr :=
  (List.range k).flatMap fun j => [.ldr .r0 src (so + 4 * j), .str .r0 dst (d + 4 * j)]

/-- The `len` bytes at `[src + so]` to `[dst + d]` (`4 ≤ len`), a word at a
time through `r0`: `copyN` for the whole words, then the last four bytes
again if `len` is not a multiple of 4. -/
def copyBytes (len : Nat) (src : Reg) (so : Nat) (dst : Reg) (d : Nat) : List Instr :=
  copyN (len / 4) src so dst d ++
    (if len % 4 = 0 then [] else [.ldr .r0 src (so + len - 4), .str .r0 dst (d + len - 4)])

/-- The MAC, for `len` bytes of data, to the frame at `dst`: the inner state
finalized, the outer one updated with that digest and finalized, and its
first `D` bytes copied. -/
def hfin (len dst : Nat) : Prog isa :=
  .seq (c.finCall sInner (c.B + len)) (.seq (c.updCall sOuter c.B (scrAt .r1 sTmp) c.D)
  (.seq (c.finCall sOuter (c.B + c.D)) (.block (copyN (c.D / 4) .r11 sTmp .r8 dst))))

/-- `HMAC_K(data)` into the frame at `dst`, for `len` bytes of `data` at the
address `dataA` sets `r1` to. -/
def hmac (dataA : List Instr) (len dst : Nat) : Prog isa :=
  .seq c.hinit (.seq (c.hupd dataA len) (c.hfin len dst))

/-- `V = HMAC_K(V)`. -/
def hmacV : Prog isa := c.hmac [.dp .add .r1 .r8 (.imm (BitVec.ofNat 32 fV))] c.D fV

/-- The message `V ‖ b` (and `‖ d ‖ h` if `full`, `Q` bytes each) at
`scratch + sMsg`, for `V` of `D` bytes: `V` from the frame (`r8`), `b` a
byte, `d` from `r5`, and `h` from the frame at `ho`. -/
def msg (Q D b : Nat) (full : Bool) (ho : Nat := fH) : List Instr :=
  copyN (D / 4) .r8 fV .r11 sMsg ++ ([.mov .r0 (.imm (BitVec.ofNat 32 b)), .strb .r0 .r11 (sMsg + D)] : List Instr) ++
    (if full then copyBytes Q .r5 0 .r11 (sMsg + D + 1) ++ copyBytes Q .r8 ho .r11 (sMsg + D + 1 + Q) else [])

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
def rekeyFull (b : Nat) : Prog isa :=
  .seq (.block (msg c.len c.D b true c.fHo))
    (.seq (c.hmac (scrAt .r1 sMsg) (c.D + 2 * c.len + 1) fK) c.hmacV)

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
def rekey : Prog isa :=
  .seq (.block (msg c.len c.D 0 false)) (.seq (c.hmac (scrAt .r1 sMsg) (c.D + 1) fK) c.hmacV)

/-- The `Q` bytes at `r8 + o`, as a big-endian number, shifted right by `s`
bits in place (`0 < s < 32`), through the words at `scratch + sSlot`: the
table and `d` to `r2` and `r3` and back, as the conversions use `r4` and
`r5`. -/
def conv (o s : Nat) : List Instr :=
  ([.mov .r2 (.reg .r4), .mov .r3 (.reg .r5), .dp .add .r1 .r8 (.imm (BitVec.ofNat 32 o)), .mov .r12 (.reg .r11)] : List Instr) ++
    Impl.Weierstrass.Arm.loadBytes c.len (c.w / 2) sSlot .r1 ++ Impl.Weierstrass.Arm.shrWords (c.w / 2) sSlot s ++
    ([.movw .r10 0xffff, .movt .r10 0xffff] : List Instr) ++ Impl.Weierstrass.Arm.storeBytes c.len (c.w / 2) .r8 o sSlot ++
    ([.mov .r4 (.reg .r2), .mov .r5 (.reg .r3)] : List Instr)

/-- Eighteen zero words at `r8 + o`. -/
def zero18 (o : Nat) : List Instr :=
  .mov .r0 (.imm 0) :: (List.range 18).map fun j => .str .r0 .r8 (o + 4 * j)

/-- If `wide`: `h`, `Q - D` zero bytes then the digest (at `r6`), at `fX`. -/
def hPrep : List Instr := zero18 fX ++ copyN (c.D / 4) .r6 0 .r8 (fX + c.len - c.D)

/-- If `wide` and `sh ≠ 0`: the digest for `core`, `Q - D - 1` zero bytes,
the digest (at `r6`) and a zero byte, shifted right by `8 - sh` bits: the
digest's integer shifted left by `sh` bits, at `fXc`. -/
def xPrep : List Instr :=
  if c.sh = 0 then [] else
    zero18 fXc ++ copyN (c.D / 4) .r6 0 .r8 (fXc + c.len - c.D - 1) ++ c.conv fXc (8 - c.sh)

/-- The 32-bit words of `n`, least significant first. -/
def nWord (j : Nat) : Nat := (c.n >>> (32 * j)) % 2 ^ 32

/-- `r1 = x mod 2³²`. -/
def movImm (x : Nat) : List Instr :=
  [.movw .r1 (BitVec.ofNat 16 x), .movt .r1 (BitVec.ofNat 16 (x >>> 16))]

/-- Digit `k` (0 low, 1 high) of `[digest] - n`, from the carry `r7` (1
for the first): `r2` (the low digit) or `r3` (the high one, shifted to its
place), the carry to `r7`; `r0` and `r1` hold word `j` of the digest's
number and of `n`, `r10` is `0xffff`. -/
def subDigit (k : Nat) : List Instr :=
  if k = 0 then
    [.dp .and .r2 .r0 (.reg .r10), .dp .and .r3 .r1 (.reg .r10), .dp .add .r2 .r2 (.reg .r10),
      .dp .sub .r2 .r2 (.reg .r3), .dp .add .r2 .r2 (.reg .r7), .mov .r7 (.shifted .r2 .lsr 16),
      .dp .and .r2 .r2 (.reg .r10)]
  else
    [.mov .r3 (.shifted .r0 .lsr 16), .mov .r12 (.shifted .r1 .lsr 16), .dp .add .r3 .r3 (.reg .r10),
      .dp .sub .r3 .r3 (.reg .r12), .dp .add .r3 .r3 (.reg .r7), .mov .r7 (.shifted .r3 .lsr 16),
      .mov .r3 (.shifted .r3 .lsl 16)]

/-- Word `j` (least significant first) of the `Q` bytes at `digest` (`r6`),
as a big-endian number, to `h`'s place, and that word of the difference
with `n` to `K`'s: both at the offset of the word's bytes. -/
def subWord (j : Nat) : List Instr :=
  ([.ldr .r0 .r6 (4 * (c.w - 1 - j)), .rev .r0 .r0, .str .r0 .r8 (c.fHo + 4 * (c.w - 1 - j))] : List Instr) ++ movImm (c.nWord j) ++
    subDigit 0 ++ subDigit 1 ++ ([.dp .orr .r2 .r2 (.reg .r3), .str .r2 .r8 (fK + 4 * (c.w - 1 - j))] : List Instr)

/-- Word `j` of `h`: the difference's if subtracting `n` did not borrow (the
mask in `r7`), the digest's number's if it did, big-endian into `h`. -/
def selWord (j : Nat) : List Instr :=
  [.ldr .r0 .r8 (c.fHo + 4 * (c.w - 1 - j)), .ldr .r1 .r8 (fK + 4 * (c.w - 1 - j)),
    -- `x = d ^ ((x ^ d) & mask)`: the difference `x` if it did not borrow, `d` if it did.
    .dp .eor .r1 .r1 (.reg .r0), .dp .and .r1 .r1 (.reg .r7), .dp .eor .r0 .r0 (.reg .r1),
    .rev .r0 .r0, .str .r0 .r8 (c.fHo + 4 * (c.w - 1 - j))]

/-- `h`: the `Q` bytes at `digest`, minus `n` if that does not borrow. -/
def reduce : List Instr :=
  ([.movw .r10 0xffff, .mov .r7 (.imm 1)] : List Instr) ++ (List.range c.w).flatMap c.subWord ++
    ([.mov .r12 (.imm 0), .dp .sub .r7 .r12 (.reg .r7)] : List Instr) ++ (List.range c.w).flatMap c.selWord

/-- `V = 0x01…`, `K = 0x00…`, all 64 bytes of each. -/
def initKV : List Instr :=
  ([.movw .r0 0x0101, .movt .r0 0x0101, .mov .r1 (.imm 0)] : List Instr) ++
    (List.range 16).flatMap fun j => [.str .r0 .r8 (fV + 4 * j), .str .r1 .r8 (fK + 4 * j)]

/-- The candidates left, in `r9`. -/
def initCnt : List Instr := [.movw .r9 (BitVec.ofNat 16 c.tries)]

/-- Where `core` reads the digest, if `wide`: `h`, or the digest shifted
left by `sh` bits. -/
def fDg : Nat := if c.sh = 0 then fX else fXc

/-- `core(out, d, digest, k, scratch)`'s arguments, `scratch` pushed, with
`k = V`, or, if `wide`, the digest and the candidate at the frame's top. -/
def coreArgs : List Instr :=
  ([.ldr .r0 .r8 fOut, .mov .r1 (.reg .r5)] : List Instr) ++
    (if c.wide then [.dp .add .r2 .r8 (.imm (BitVec.ofNat 32 c.fDg)), .dp .add .r3 .r8 (.imm (BitVec.ofNat 32 fT))]
    else [.mov .r2 (.reg .r6), .dp .add .r3 .r8 (.imm (BitVec.ofNat 32 fV))]) ++
    ([.mov .r12 (.reg .r11)] : List Instr)

/-- If `wide`: `V`'s `D` bytes to `T + j D`. -/
def keepV (j : Nat) : List Instr := copyN (c.D / 4) .r8 fV .r8 (fT + j * c.D)

/-- If `wide`: `V = HMAC_K(V)` and its `D` bytes to `T + j D`, for each
`j < k`. -/
def candW : Nat → Prog isa
  | 0 => .block []
  | k + 1 => .seq (candW k) (.seq c.hmacV (.block (c.keepV k)))

/-- If `wide` and `sh ≠ 0`: `T`'s first `Q` bytes shifted right by `sh` bits. -/
def candTop : List Instr := if c.sh = 0 then [] else c.conv fT c.sh

/-- The candidate: `V = HMAC_K(V)`, which is `k`; or, if `wide`, the
leftmost `Q` bytes of `m` successive `V = HMAC_K(V)`, shifted right by `sh`
bits. -/
def cand : Prog isa :=
  if c.wide then .seq (c.candW c.m) (.block c.candTop) else c.hmacV

/-- One candidate fewer, and `Z` clear iff the signature failed (`r0 = 0`)
and candidates are left: `r7 = (C - 1) & count`, `C` the carry of `r0 - 1`
(set iff `r0 ≥ 1`). -/
def goOn : List Instr :=
  [.dp .sub .r9 .r9 (.imm 1), .subs .r10 .r0 (.imm 1), .mov .r10 (.imm 0), .adc .r10 .r10 (.imm 0),
    .dp .sub .r10 .r10 (.imm 1), .dp .and .r7 .r10 (.reg .r9), .cmp .r7 (.imm 0)]

/-- `Z` clear: go on. -/
def again : List Instr := [.mov .r7 (.imm 1), .cmp .r7 (.imm 0)]

/-- `Z` set: stop. -/
def stop : List Instr := [.mov .r7 (.imm 0), .cmp .r7 (.imm 0)]

/-- One candidate: `cand`, `core` with it, then, if it failed and candidates
are left, step h.3. -/
def tryOne : Prog isa :=
  .seq c.cand
  (.seq (.block c.coreArgs)
  (.seq (.frame (.push [.r12, .lr]) (.call c.coreN c.coreC) (.pop .r12 8))
  (.seq (.block goOn)
    (.ite .ne (.seq c.rekey (.block again)) (.block stop)))))

/-- The 44 words of `K`, `V` and `h`, each from `r1`. -/
def zeros : List (Reg × Nat) := (List.range 44).map fun j => (.r1, 4 * j)

/-- The words at the frame's top, each from `r1`. -/
def zerosHigh (wide : Bool) (hHigh : Bool := false) : List (Reg × Nat) :=
  (List.range (extra wide hHigh)).map fun j => (.r1, fX + 4 * j)

/-- `K`, `V` and `h` cleared, and the words at the frame's top (`r0`, the
result, kept), and our caller's registers back, through `r12` (the frame's
base). -/
def wipe (wide : Bool) (hHigh : Bool := false) : List Instr :=
  ([.mov .r12 (.reg .r8), .mov .r1 (.imm 0)] : List Instr) ++ zeros.map (fun p => .str p.1 .r12 p.2) ++
    (zerosHigh wide hHigh).map (fun p => .str p.1 .r12 p.2) ++ epilogue

/-- `h` (and, if `wide`, the digest for `core`). -/
def prep : List Instr := if c.wide then c.hPrep ++ c.xPrep else c.reduce

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block (c.prologue ++ c.prep ++ initKV))
  (.seq (c.rekeyFull 0)
  (.seq (c.rekeyFull 1)
  (.seq (.block c.initCnt)
  (.seq (.loop c.tryOne .ne)
    (.block (wipe c.wide c.hHigh))))))

/-- The signature for the hash function of this size. -/
def sign : Prog isa := .frame (.alloc c.fb) c.body (.free c.fb)

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

/-- `b i` for the index `i` in `r12`, by comparisons with each of `is`: the
last is taken for every other value. -/
def byIdx (b : Nat → Prog isa) : List Nat → Prog isa
  | [] => .block []
  | [i] => b i
  | i :: is => .seq (.block [.cmp .r12 (.imm (BitVec.ofNat 32 i))]) (.ite .eq (b i) (byIdx b is))

/-- The hash function's index (the word 3 of the table, our stack argument
1) to `r12`. -/
def entry : List Instr := [.ldrSp .r12 4, .ldr .r12 .r12 12]

/-- `vg_ecdsa_<curve>_sign`: the signature with the code `cfg i` for the
hash function of index `i` of the table `hash`. -/
def signT (cfg : Nat → Cfg) : Prog isa :=
  .seq (.block entry) (byIdx (fun i => (cfg i).sign) idxs)

end VG.Impl.Ecdsa.Rfc6979.Arm
