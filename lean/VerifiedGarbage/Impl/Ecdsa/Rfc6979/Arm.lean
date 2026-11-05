module

public import VerifiedGarbage.Impl.Pbkdf2.Stream.Arm
public import VerifiedGarbage.Impl.Weierstrass.Arm
public import VerifiedGarbage.Impl.AesGcm.Arm
public import VerifiedGarbage.Impl.ICall

/-!
# Deterministic ECDSA (RFC 6979) on 32-bit ARM, with HMAC through a table

`vg_ecdsa_<curve>_sign(out = r0, d = r1, digest = r2, digest_len = r3,
scratch = [sp], hmac = [sp + 4]) -> r0` (`Cfg.sign`), for a curve of
`Q`-byte scalars in `w` 32-bit words: RFC 6979 §3.2, as on x86-64
(`Impl/Ecdsa/Rfc6979/X86_64.lean`), with HMAC over the hash function of the
table `hmac` of the interface `Hmac` (`Spec/HmacTable.lean`), whose
functions it calls indirectly (`tcall`: the table's word `j` into `lr`, then
`blx lr`, in the frame of the call's stack arguments): HMAC's `init` (word
0), the streaming `update` (word 1), on the inner state, and HMAC's
`finalize` (word 2); and each candidate tried by calling `core`, the
signature with a given `k` (`vg_ecdsa_<curve>_sign_k`), which reads `Q`
bytes of the digest and of `k`, and takes their leftmost `qlen` bits
(`bits2int`, a right shift by `sh = 8 Q - qlen` bits).

One body serves every hash function: the digest length `D` and HMAC's block
size `B` are the table's words of data 4 and 5 (at `hmac + 16` and
`hmac + 20`), which the code reads from the table wherever it needs them, as
the lengths and counts it passes (all public).

Each HMAC is `init` with the key `K` (`D` bytes, in the frame), the inner
state updated with `V` (`D` bytes, in the frame), then, for a new `K`, with
the message `b ‖ d ‖ h` or `b` (`msg`, in `scratch`), and `finalize`, which
writes the MAC to `K` or `V` in the frame, with the count `B + D + len`.

The digest's leftmost `min(D, Q)` bytes, after `Q - min(D, Q)` zero bytes,
are `X` (`prepX`, by a byte loop, `copyLoop`), a `Q`-byte number. Then:

* unless `big` (all but P-521): `h = bits2octets(digest)` is `X` minus `n` if
  it is at least `n` (a conditional subtraction, `reduce`, by 16-bit digits,
  as the model's `adc` sets no flags), and `core` reads `X` as its digest;
* if `big` (P-521): `X`'s integer is below `n`, so `h` is `X` itself, and
  `core` reads the digest's integer shifted left by `sh` bits (`prepC`, at
  `fXc`: `Q - 1 - D` zero bytes, the digest and a zero byte, shifted right by
  `8 - sh` bits through the words at `scratch + sSlot`, `conv`).

The candidate `k` is the leftmost `Q` bytes of `T`, the `V`s of successive
`V = HMAC_K(V)` while `T` is shorter than `Q` bytes (`cand`: a loop whose
count is public, each `V` appended to `T` by `copyLoop`), shifted right by
`sh` bits in place if `big` (`candTop`).

The frame is 512 bytes (`frameBytes`): from `sp`, `K` and `V` (64 bytes
each, of which the first `D` are used), `h` (64 bytes), `X` and `core`'s
digest if `big` (68 bytes each), `T` (136 bytes), the length of `T`, our
caller's `r4`–`r11` and `lr`, and the pointer `digest`. The functions we
call preserve `r4`–`r11`, which hold what lives across the calls: `out` and
`d` in `r4` and `r5`, the table in `r6`, the frame in `r8`, the number of
candidates left in `r9` and `scratch` in `r11`. Each call's arguments beyond
`r0`–`r3` are pushed by a frame of its own, as on main: `push {r12, lr}` for
HMAC's `init` and for `core`, `push {r1, r7, r10, r12}` for `update` and
`push {r10, r12}` for HMAC's `finalize`, so that the stack pointer stays
8-byte aligned. The calls use only `scratch`, which `core` overwrites
entirely, and the stack below the frame; the frame below the saved
registers is cleared (`wipe`, a loop of word stores) before it is freed. In
`scratch`: HMAC's inner and outer streaming states (192 bytes each), the
working space of the table's functions, the message, and the words of a
shift.

1. `X`; `h` (`reduce`, or `prepC`); `V = 0x01…`, `K = 0x00…`.
2. Steps d to g: `K = HMAC_K(V ‖ 0x00 ‖ d ‖ h)`, `V = HMAC_K(V)`,
   `K = HMAC_K(V ‖ 0x01 ‖ d ‖ h)`, `V = HMAC_K(V)`.
3. At most `tries` times: the candidate `k` (`cand`) and
   `core(out, d, X, k, scratch)`; if it failed and candidates are left,
   `K = HMAC_K(V ‖ 0x00)`, `V = HMAC_K(V)` and again. Whether to go on is
   computed without branches, so that the code branches only on it: the
   number of candidates tried is all it reveals.

`core` writes the signature or zeros to `out`, and its return value is ours.
Every address is the frame's base (in `r8`, and in `r12` for the prologue,
the wipe and the epilogue), the table (in `r6`), or a pointer argument or
the frame's base plus a public offset.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Rfc6979.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Stream.Arm (scrAt)
open VG.Impl.AesGcm.Arm (copyLoop addI imm)

/-! Where things are in the frame. -/
def fK : Nat := 0
def fV : Nat := 64
/-- `h` (64 bytes), unless `big`. -/
def fH : Nat := 128
/-- `X` (68 bytes): the digest's leftmost bytes, as a `Q`-byte number; `h` if `big`. -/
def fX : Nat := 192
/-- If `big`: the digest for `core` (68 bytes). -/
def fXc : Nat := 260
/-- The candidate `T` (136 bytes). -/
def fT : Nat := 328
/-- The length of `T`. -/
def fTlen : Nat := 464
/-- Our caller's registers. -/
def fSave : Nat := 468
/-- The pointer `digest`. -/
def fDigest : Nat := 504
/-- The frame's size, a multiple of 8. -/
def frameBytes : Nat := 512
/-- The words the wipe clears: the frame below the saved registers. -/
def wipeWords : Nat := 117

/-! Where things are in `scratch`. -/
def sInner : Nat := 0
def sOuter : Nat := 192
def sWork : Nat := 384
def sMsg : Nat := 2256
/-- The words of a conversion, if `big`. -/
def sSlot : Nat := 2560

/-! Where the table's data is. -/
/-- The digest length `D`, the table's word 4. -/
def tD : Nat := 16
/-- HMAC's block size `B`, the table's word 5. -/
def tB : Nat := 20

/-- Our caller's registers, where the frame keeps them (`r8`, the frame's
base afterwards, last). -/
def saved : List (Reg × Nat) :=
  [(.r4, fSave), (.r5, fSave + 4), (.r6, fSave + 8), (.r7, fSave + 12), (.r9, fSave + 16),
    (.r10, fSave + 20), (.r11, fSave + 24), (.lr, fSave + 28), (.r8, fSave + 32)]

/-- The functions an indirect call of each of a table's functions may
reach: for each of `init`, `update` and `finalize`, that function of every
table of the interface, by name. -/
structure Fns where
  init : List (String × Prog isa)
  upd : List (String × Prog isa)
  fin : List (String × Prog isa)

/-- What the code needs of a curve. -/
structure Cfg where
  /-- The functions an indirect call of a table's functions may reach. -/
  f : Fns
  /-- The 32-bit words of the curve's scalars (P-521's 66 bytes take 18). -/
  w : Nat
  /-- The bytes of the curve's scalars, `Q`. -/
  len : Nat := 4 * w
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

/-- Our caller's registers into the frame (through `r12`, its base); `out`,
`d`, `scratch` and the table to the registers that keep them, `digest` to
the frame, and the frame's base to `r8`. -/
def prologue : List Instr :=
  .addSp .r12 0 :: saved.map (fun p => .str p.1 .r12 p.2) ++
    ([.mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .str .r2 .r12 fDigest, .ldr .r11 .r12 frameBytes,
      .ldr .r6 .r12 (frameBytes + 4), .mov .r8 (.reg .r12)] : List Instr)

/-- Our caller's registers back, through `r12` (the frame's base). -/
def epilogue : List Instr := saved.map fun p => .ldr p.1 .r12 p.2

/-! ## HMAC through the table -/

/-- The call of the table's function `j`, among `ts`: its address (the
table's word `j`) into `lr`, then `blx lr`, in a frame pushing `rs` (its
stack arguments) and popping `n` bytes. -/
def tcall (j : Nat) (ts : List (String × Prog isa)) (rs : List Reg) (n : Nat) : Prog isa :=
  .seq (.block [.ldr .lr .r6 (4 * j)]) (.frame (.push rs) (Code.icalls (.blx .lr) ts) (.pop .r12 n))

/-- The arguments of HMAC's `init`: the states, the key `K` of `D` bytes,
and the working space (pushed). -/
def initArgs : List Instr :=
  scrAt .r0 sInner ++ scrAt .r1 sOuter ++ ([.dp .add .r2 .r8 (imm fK), .ldr .r3 .r6 tD] : List Instr) ++
    scrAt .r12 sWork

/-- The arguments of the streaming `update` with `V`: the inner state, the
`B` bytes it holds (`r2:r3`), and, pushed, `V` (`r1`), its `D` bytes (`r7`)
and the working space (`r10`). -/
def updVArgs : List Instr :=
  scrAt .r0 sInner ++ ([.dp .add .r1 .r8 (imm fV), .ldr .r2 .r6 tB, .mov .r3 (imm 0), .ldr .r7 .r6 tD] :
    List Instr) ++ scrAt .r10 sWork

/-- The arguments of the streaming `update` with the message: the inner
state, the `B + D` bytes it holds, and, pushed, the message, its `len` bytes
and the working space. -/
def updMArgs (len : Nat) : List Instr :=
  scrAt .r0 sInner ++ scrAt .r1 sMsg ++
    ([.ldr .r2 .r6 tB, .ldr .r3 .r6 tD, .dp .add .r2 .r2 (.reg .r3), .mov .r3 (imm 0),
      .movw .r7 (BitVec.ofNat 16 len)] : List Instr) ++ scrAt .r10 sWork

/-- The arguments of HMAC's `finalize`: the states, the `B + D + len` bytes
the inner one holds (`r2:r3`), and, pushed, the MAC's place in the frame
(`r10`) and the working space (`r12`). -/
def finArgs (len dst : Nat) : List Instr :=
  scrAt .r0 sInner ++ scrAt .r1 sOuter ++
    ([.ldr .r2 .r6 tB, .ldr .r3 .r6 tD, .dp .add .r2 .r2 (.reg .r3), .dp .add .r2 .r2 (imm len),
      .mov .r3 (imm 0), .dp .add .r10 .r8 (imm dst)] : List Instr) ++ scrAt .r12 sWork

/-- HMAC's states for `K`, by `init`. -/
def initK : Prog isa := .seq (.block initArgs) (tcall 0 c.f.init [.r12, .lr] 8)

/-- The inner state updated with `V`. -/
def updV : Prog isa := .seq (.block updVArgs) (tcall 1 c.f.upd [.r1, .r7, .r10, .r12] 16)

/-- The inner state updated with the message's `len` bytes. -/
def updM (len : Nat) : Prog isa := .seq (.block (updMArgs len)) (tcall 1 c.f.upd [.r1, .r7, .r10, .r12] 16)

/-- The MAC, of `D + len` bytes of text, to the frame at `dst`. -/
def fin (len dst : Nat) : Prog isa := .seq (.block (finArgs len dst)) (tcall 2 c.f.fin [.r10, .r12] 8)

/-- `V = HMAC_K(V)`. -/
def hmacV : Prog isa := .seq c.initK (.seq c.updV (c.fin 0 fV))

/-- `K = HMAC_K(V ‖ msg)`, for the message's `len` bytes. -/
def hmacK (len : Nat) : Prog isa := .seq c.initK (.seq c.updV (.seq (c.updM len) (c.fin len fK)))

/-- The `4 k` bytes at `[src + so]` to `[dst + d]`, a word at a time through `r0`. -/
def copyN (k : Nat) (src : Reg) (so : Nat) (dst : Reg) (d : Nat) : List Instr :=
  (List.range k).flatMap fun j => [.ldr .r0 src (so + 4 * j), .str .r0 dst (d + 4 * j)]

/-- The `len` bytes at `[src + so]` to `[dst + d]` (`4 ≤ len`), a word at a
time through `r0`: `copyN` for the whole words, then the last four bytes
again if `len` is not a multiple of 4. -/
def copyBytes (len : Nat) (src : Reg) (so : Nat) (dst : Reg) (d : Nat) : List Instr :=
  copyN (len / 4) src so dst d ++
    (if len % 4 = 0 then [] else [.ldr .r0 src (so + len - 4), .str .r0 dst (d + len - 4)])

/-- The message `b` (and `‖ d ‖ h` if `full`, `Q` bytes each) at
`scratch + sMsg`: `b` a byte, then the private key (from `r5`) and `h` from
the frame. -/
def msg (b : Nat) (full : Bool) : List Instr :=
  ([.mov .r0 (imm b), .strb .r0 .r11 sMsg] : List Instr) ++
    (if full then copyBytes c.len .r5 0 .r11 (sMsg + 1) ++ copyBytes c.len .r8 c.fHo .r11 (sMsg + 1 + c.len)
    else [])

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
def rekeyFull (b : Nat) : Prog isa := .seq (.block (c.msg b true)) (.seq (c.hmacK (1 + 2 * c.len)) c.hmacV)

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
def rekey : Prog isa := .seq (.block (c.msg 0 false)) (.seq (c.hmacK 1) c.hmacV)

/-! ## Bytes, numbers and `h` -/

/-- `k` zero words at `r8 + o`. -/
def zeroN (k o : Nat) : List Instr :=
  .mov .r0 (imm 0) :: (List.range k).map fun j => .str .r0 .r8 (o + 4 * j)

/-- The arguments of `X`'s copy: `X` cleared; then `r3 = min(D, Q)` (as
`Q + ((D - Q) & mask)`, the mask all ones iff `D < Q`, from the carry of
`D - Q`), the digest in `r1`, `X + Q - r3` in `r2`. -/
def xArgs : List Instr :=
  zeroN 17 fX ++
    ([.ldr .r3 .r6 tD, .movw .r0 (BitVec.ofNat 16 c.len), .subs .r12 .r3 (.reg .r0), .mov .r7 (imm 0),
      .adc .r7 .r7 (imm 0), .dp .sub .r7 .r7 (imm 1), .dp .and .r12 .r12 (.reg .r7),
      .dp .add .r3 .r0 (.reg .r12), .movw .r2 (BitVec.ofNat 16 (fX + c.len)), .dp .add .r2 .r2 (.reg .r8),
      .dp .sub .r2 .r2 (.reg .r3), .ldr .r1 .r8 fDigest] : List Instr)

/-- `X`: `Q - min(D, Q)` zero bytes, then the digest's leftmost `min(D, Q)`. -/
def prepX : Prog isa := .seq (.block c.xArgs) copyLoop

/-- The 32-bit words of `n`, least significant first. -/
def nWord (j : Nat) : Nat := (c.n >>> (32 * j)) % 2 ^ 32

/-- `r1 = x mod 2³²`. -/
def movImm (x : Nat) : List Instr :=
  [.movw .r1 (BitVec.ofNat 16 x), .movt .r1 (BitVec.ofNat 16 (x >>> 16))]

/-- Digit `k` (0 low, 1 high) of `X - n`, from the carry `r7` (1 for the
first): `r2` (the low digit) or `r3` (the high one, shifted to its place),
the carry to `r7`; `r0` and `r1` hold word `j` of `X`'s number and of `n`,
`r10` is `0xffff`. -/
def subDigit (k : Nat) : List Instr :=
  if k = 0 then
    [.dp .and .r2 .r0 (.reg .r10), .dp .and .r3 .r1 (.reg .r10), .dp .add .r2 .r2 (.reg .r10),
      .dp .sub .r2 .r2 (.reg .r3), .dp .add .r2 .r2 (.reg .r7), .mov .r7 (.shifted .r2 .lsr 16),
      .dp .and .r2 .r2 (.reg .r10)]
  else
    [.mov .r3 (.shifted .r0 .lsr 16), .mov .r12 (.shifted .r1 .lsr 16), .dp .add .r3 .r3 (.reg .r10),
      .dp .sub .r3 .r3 (.reg .r12), .dp .add .r3 .r3 (.reg .r7), .mov .r7 (.shifted .r3 .lsr 16),
      .mov .r3 (.shifted .r3 .lsl 16)]

/-- Word `j` (least significant first) of the `Q` bytes of `X`, as a
big-endian number, to `h`'s place, and that word of the difference with `n`
to `K`'s: both at the offset of the word's bytes. -/
def subWord (j : Nat) : List Instr :=
  ([.ldr .r0 .r8 (fX + 4 * (c.w - 1 - j)), .rev .r0 .r0, .str .r0 .r8 (fH + 4 * (c.w - 1 - j))] : List Instr) ++
    movImm (c.nWord j) ++
    subDigit 0 ++ subDigit 1 ++ ([.dp .orr .r2 .r2 (.reg .r3), .str .r2 .r8 (fK + 4 * (c.w - 1 - j))] : List Instr)

/-- Word `j` of `h`: the difference's if subtracting `n` did not borrow (the
mask in `r7`), `X`'s number's if it did, big-endian into `h`. -/
def selWord (j : Nat) : List Instr :=
  [.ldr .r0 .r8 (fH + 4 * (c.w - 1 - j)), .ldr .r1 .r8 (fK + 4 * (c.w - 1 - j)),
    -- `x = d ^ ((x ^ d) & mask)`: the difference `x` if it did not borrow, `d` if it did.
    .dp .eor .r1 .r1 (.reg .r0), .dp .and .r1 .r1 (.reg .r7), .dp .eor .r0 .r0 (.reg .r1),
    .rev .r0 .r0, .str .r0 .r8 (fH + 4 * (c.w - 1 - j))]

/-- `h`, unless `big`: `X`, minus `n` if that does not borrow. -/
def reduce : List Instr :=
  ([.movw .r10 0xffff, .mov .r7 (imm 1)] : List Instr) ++ (List.range c.w).flatMap c.subWord ++
    ([.mov .r12 (imm 0), .dp .sub .r7 .r12 (.reg .r7)] : List Instr) ++ (List.range c.w).flatMap c.selWord

/-- The `Q` bytes at `r8 + o`, as a big-endian number, shifted right by `s`
bits in place (`0 < s < 32`), through the words at `scratch + sSlot`: `out`
and `d` to `r2` and `r3` and back, as the conversions use `r4` and `r5`. -/
def conv (o s : Nat) : List Instr :=
  ([.mov .r2 (.reg .r4), .mov .r3 (.reg .r5), .dp .add .r1 .r8 (imm o), .mov .r12 (.reg .r11)] : List Instr) ++
    Impl.Weierstrass.Arm.loadBytes c.len (c.w / 2) sSlot .r1 ++ Impl.Weierstrass.Arm.shrWords (c.w / 2) sSlot s ++
    ([.movw .r10 0xffff, .movt .r10 0xffff] : List Instr) ++ Impl.Weierstrass.Arm.storeBytes c.len (c.w / 2) .r8 o sSlot ++
    ([.mov .r4 (.reg .r2), .mov .r5 (.reg .r3)] : List Instr)

/-- The arguments of the copy of `core`'s digest, if `big`: it cleared;
then `r3 = D`, the digest in `r1`, `fXc + Q - 1 - D` in `r2`. -/
def xcArgs : List Instr :=
  zeroN 17 fXc ++
    ([.ldr .r3 .r6 tD, .movw .r2 (BitVec.ofNat 16 (fXc + c.len - 1)), .dp .add .r2 .r2 (.reg .r8),
      .dp .sub .r2 .r2 (.reg .r3), .ldr .r1 .r8 fDigest] : List Instr)

/-- If `big`: `core`'s digest, `Q - 1 - D` zero bytes, the digest and a zero
byte, shifted right by `8 - sh` bits: the digest's integer shifted left by
`sh` bits. -/
def prepC : Prog isa := .seq (.block c.xcArgs) (.seq copyLoop (.block (c.conv fXc (8 - c.sh))))

/-- `h`: `reduce`, or, if `big`, `X` itself, with `core`'s digest. -/
def prepH : Prog isa := if c.big then c.prepC else .block c.reduce

/-- `V = 0x01…`, `K = 0x00…`, all 64 bytes of each. -/
def initKV : List Instr :=
  ([.movw .r0 0x0101, .movt .r0 0x0101, .mov .r1 (imm 0)] : List Instr) ++
    (List.range 16).flatMap fun j => [.str .r0 .r8 (fV + 4 * j), .str .r1 .r8 (fK + 4 * j)]

/-- The candidates left, in `r9`. -/
def initCnt : List Instr := [.movw .r9 (BitVec.ofNat 16 c.tries)]

/-! ## The candidates -/

/-- `T` empty. -/
def tInit : List Instr := [.mov .r0 (imm 0), .str .r0 .r8 fTlen]

/-- The arguments of `V`'s copy to the end of `T`: `V` in `r1`, `T + |T|` in
`r2`, `r3 = D`. -/
def keepArgs : List Instr :=
  [.dp .add .r1 .r8 (imm fV), .dp .add .r2 .r8 (imm fT), .ldr .r0 .r8 fTlen, .dp .add .r2 .r2 (.reg .r0),
    .ldr .r3 .r6 tD]

/-- `T` longer by `D` bytes, and `Z` clear iff it is still shorter than `Q`:
`r7 = C - 1`, `C` the carry of `|T| - Q` (set iff `|T| ≥ Q`). -/
def tStep : List Instr :=
  [.ldr .r0 .r8 fTlen, .ldr .r1 .r6 tD, .dp .add .r0 .r0 (.reg .r1), .str .r0 .r8 fTlen,
    .subs .r12 .r0 (imm c.len), .mov .r7 (imm 0), .adc .r7 .r7 (imm 0), .dp .sub .r7 .r7 (imm 1),
    .cmp .r7 (imm 0)]

/-- One `V` of the candidate: `V = HMAC_K(V)`, appended to `T`. -/
def candStep : Prog isa := .seq c.hmacV (.seq (.block keepArgs) (.seq copyLoop (.block c.tStep)))

/-- If `big`: `T`'s first `Q` bytes shifted right by `sh` bits. -/
def candTop : List Instr := if c.big then c.conv fT c.sh else []

/-- The candidate: `T`, the `V`s of successive `V = HMAC_K(V)` while it is
shorter than `Q` bytes, its leftmost `Q` bytes shifted right by `sh` bits if
`big`. -/
def cand : Prog isa := .seq (.block tInit) (.seq (.loop c.candStep .ne) (.block c.candTop))

/-- `core(out, d, X, k, scratch)`'s arguments, `scratch` pushed: the digest
`X` (or, if `big`, the one at `fXc`) and `k = T`. -/
def coreArgs : List Instr :=
  [.mov .r0 (.reg .r4), .mov .r1 (.reg .r5), .dp .add .r2 .r8 (imm c.fDg), .dp .add .r3 .r8 (imm fT),
    .mov .r12 (.reg .r11)]

/-- One candidate fewer, and `Z` clear iff the signature failed (`r0 = 0`)
and candidates are left: `r7 = (C - 1) & count`, `C` the carry of `r0 - 1`
(set iff `r0 ≥ 1`). -/
def goOn : List Instr :=
  [.dp .sub .r9 .r9 (imm 1), .subs .r10 .r0 (imm 1), .mov .r10 (imm 0), .adc .r10 .r10 (imm 0),
    .dp .sub .r10 .r10 (imm 1), .dp .and .r7 .r10 (.reg .r9), .cmp .r7 (imm 0)]

/-- `Z` clear: go on. -/
def again : List Instr := [.mov .r7 (imm 1), .cmp .r7 (imm 0)]

/-- `Z` set: stop. -/
def stop : List Instr := [.mov .r7 (imm 0), .cmp .r7 (imm 0)]

/-- One candidate: `cand`, `core` with it, then, if it failed and candidates
are left, step h.3. -/
def tryOne : Prog isa :=
  .seq c.cand
  (.seq (.block c.coreArgs)
  (.seq (.frame (.push [.r12, .lr]) (.call c.coreN c.coreC) (.pop .r12 8))
  (.seq (.block goOn)
    (.ite .ne (.seq c.rekey (.block again)) (.block stop)))))

/-- The wipe's arguments: the frame's base in `r12`, zero in `r1`, the words
in `r3`. -/
def wipeArgs : List Instr := [.mov .r12 (.reg .r8), .mov .r1 (imm 0), .movw .r3 (BitVec.ofNat 16 wipeWords)]

/-- A word of the wipe: zero to `[r12]`, the next word, one fewer left. -/
def wipeBody : List Instr := [.str .r1 .r12 0, addI .r12 .r12 4, .subs .r3 .r3 (imm 1)]

/-- The frame below the saved registers cleared (`r0`, the result, kept),
then our caller's registers back, through `r12` (the frame's base). -/
def wipe : Prog isa :=
  .seq (.block wipeArgs) (.seq (.loop (.block wipeBody) .ne) (.block (.mov .r12 (.reg .r8) :: epilogue)))

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block prologue)
  (.seq c.prepX
  (.seq c.prepH
  (.seq (.block initKV)
  (.seq (c.rekeyFull 0)
  (.seq (c.rekeyFull 1)
  (.seq (.block c.initCnt)
  (.seq (.loop c.tryOne .ne)
    wipe)))))))

/-- `vg_ecdsa_<curve>_sign`. -/
def sign : Prog isa := .frame (.alloc frameBytes) c.body (.free frameBytes)

end Cfg

end VG.Impl.Ecdsa.Rfc6979.Arm
