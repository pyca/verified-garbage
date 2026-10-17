module

public import VerifiedGarbage.Impl.Pbkdf2.Whole.Arm
public import VerifiedGarbage.Impl.Weierstrass.Arm
public import VerifiedGarbage.Impl.Dispatch.Arm

/-!
# Deterministic ECDSA (RFC 6979) on 32-bit ARM, with the hash function as an argument

`sign R hs core (out = r0, d = r1, digest = r2, digest_len = r3, [scratch,
hash]) -> r0`: RFC 6979 §3.2 for a curve of `Q`-byte scalars in `w` 32-bit
words, with HMAC with the Merkle–Damgård hash function `hash` names, one of
`hs` (SHA-1 and the SHA-2 functions: their HMAC `init`, streaming `update`
and HMAC `finalize`, the functions PBKDF2's code calls), whose output is
`D = digest_len` bytes (20, 28, 32, 48 or 64) and block `B` bytes (64 or
128), and each candidate tried by calling `core`, the signature with a given
`k` (`vg_ecdsa_<curve>_sign`), which reads `Q` bytes of the digest and of
`k`, and takes the digest's leftmost `qlen` bits (`bits2int`, a right shift
by `sh = 8 Q - qlen` bits).

What depends on the hash function is computed from one register, `r6`, the
hash function's *code* `D + (B = 128 ? 1 : 0)` (`code`: 20, 28, 32, 49, 65,
29 and 33 for the numbers 1 to 7), which the prologue computes from
`digest_len` and `hash` (`hash ≥ 4` iff `B = 128`, so the code is
`digest_len + ((hash + 4) >> 3)`): `D` is `r6 & 0xfe`, `B` is
`64 + ((r6 & 1) << 6)`, and each call of a hash function is a dispatch on
`r6` (`Dispatch.Arm.chain`, a `cmp` and a branch per hash function but the
last), a direct call of that hash function's function in each case. The
functions we call preserve `r6`, as every register that lives across them.

1. The digest's integer, as `bits2int` gives it, in `Q` bytes at `h`'s
   place: zeros, then the digest's first `min(D, Q)` bytes (`dgCopy`, a loop
   over its words). If `sh = 0` (every curve but P-521), `h =
   bits2octets(digest)` is that minus `n` if it is at least `n` (a
   conditional subtraction, as `2^(8 Q) < 2n`: `reduce`), and `core`
   reads it as the digest (`signWith` reduces the digest's integer modulo
   `n`). If `sh ≠ 0` (P-521, whose 66 bytes no digest fills), the integer
   is below `n`, so it is `h`; and `core`'s digest is it shifted left by
   `sh` bits: the digest after `65 - D` zero bytes, then a zero byte, shifted
   right by `8 - sh` bits (`dgCopy`, then `conv`).
2. Steps b to g: `V = 0x01…`, `K = 0x00…`, `K = HMAC_K(V ‖ 0x00 ‖ d ‖ h)`,
   `V = HMAC_K(V)`, `K = HMAC_K(V ‖ 0x01 ‖ d ‖ h)`, `V = HMAC_K(V)`.
3. At most `tries` times: the candidate `k` (`cand`), the leftmost `Q`
   bytes of `T`, the concatenation of successive `V = HMAC_K(V)`, as many as
   make `Q` bytes (`blocks` of RFC 6979: a step for each of the at most
   `steps` `V`s, run if the bytes before it are fewer than `Q`), shifted
   right by `sh` bits; then `core(out, d, digest, k, scratch)`; if it
   failed and candidates are left, `K = HMAC_K(V ‖ 0x00)`, `V = HMAC_K(V)`
   and again. Whether to go on is computed without branches, so that the
   code branches only on it: the number of candidates tried is all it
   reveals, besides the hash function.

A frame of 432 bytes is allocated: from `sp`, `K` and `V` (64 bytes each, of
which the first `D` are used), `h` (68 bytes, of which the first `Q`), `T`
(132 bytes: a step copies all 64 bytes of `V`'s place to `T`'s at `i D`,
`i D < Q`), `core`'s digest if `sh ≠ 0` (68 bytes), and our caller's `r4`–`r11`
and `lr` (the calls replace `lr`). The registers that live across the
calls: `out`, `d` and the code in `r4`–`r6`, the frame in `r8`, the
candidates left in `r9` and `scratch` in `r11`; `digest` is in `r10` until
the steps on `K` and `V`. Each call's arguments beyond `r0`–`r3` are pushed
by a frame of its own, as in PBKDF2's code (`VG.Impl.Pbkdf2.Whole.Arm`):
`push {r12, lr}` for HMAC's `init` and for `core`, `push {r1, r7, r10, r12}`
for `update` and `push {r10, r12}` for HMAC's `finalize`. The calls use only
`scratch`, which `core` overwrites entirely, and the stack below the frame;
the frame's first 396 bytes (`K`, `V`, `h`, `T` and `core`'s digest) are
cleared before it is freed. In `scratch`: HMAC's inner and outer streaming
states, the working space of HMAC's and the hash function's functions, the
message of steps d, f and h.3 (`V`'s 64 bytes, then from `D` on the rest),
and the words of the conversions.

Every address is the frame's base (in `r8`, from `sp` in the prologue, and
in `r12` for the prologue and the epilogue) or a pointer argument plus a
constant or `D` (in a conversion, `r1` and `r12` are the frame's base and
`scratch` plus a constant).
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Rfc6979.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Stream.Arm (scrAt)

/-! Where things are in the frame. -/
def fK : Nat := 0
def fV : Nat := 64
def fH : Nat := 128
def fT : Nat := 196
/-- `core`'s digest, if `sh ≠ 0`. -/
def fX : Nat := 328
def fSave : Nat := 396
/-- The frame's size, a multiple of 8. -/
def frameBytes : Nat := 432

/-! Where things are in `scratch`. -/
def sInner : Nat := 0
def sOuter : Nat := 192
def sWork : Nat := 384
def sMsg : Nat := 2256
/-- The words of a conversion. -/
def sSlot : Nat := 2560

/-- Our caller's registers, where the frame keeps them (`r8`, the frame's
base afterwards, last). -/
def saved : List (Reg × Nat) :=
  [(.r4, fSave), (.r5, fSave + 4), (.r6, fSave + 8), (.r7, fSave + 12), (.r9, fSave + 16),
    (.r10, fSave + 20), (.r11, fSave + 24), (.lr, fSave + 28), (.r8, fSave + 32)]

/-- A hash function's code: its output's length `D`, plus one if its block is 128 bytes. -/
def code (F : Impl.Pbkdf2.Whole.Arm.Fns) : Nat := F.H.D + F.H.B / 128

/-- What the code needs of a curve and the hash functions. -/
structure Cfg where
  /-- The hash functions: for each, the functions PBKDF2's code calls (its
  streaming `update`, and HMAC's `init` and `finalize` with their working
  space as an argument). -/
  hs : List Impl.Pbkdf2.Whole.Arm.Fns
  /-- The 32-bit words of the curve's scalars (seven for P-224; otherwise an even number). -/
  w : Nat
  /-- The bytes of the curve's scalars, `Q`. -/
  len : Nat := 4 * w
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

/-- The most `V`s a candidate takes: for the shortest digest, SHA-1's 20 bytes. -/
def steps : Nat := (c.len + 19) / 20

/-- Our caller's registers into the frame (through `r12`, its base); the
arguments to the registers that keep them, `scratch` and the code of the
hash function `hash` from the stack, and the frame's base to `r8`. -/
def prologue : List Instr :=
  .addSp .r12 0 :: saved.map (fun p => .str p.1 .r12 p.2) ++
    ([.ldrSp .r11 frameBytes, .ldrSp .r7 (frameBytes + 4), .mov .r4 (.reg .r0), .mov .r5 (.reg .r1),
      .mov .r10 (.reg .r2), .mov .r8 (.reg .r12), .dp .add .r7 .r7 (.imm 4), .mov .r7 (.shifted .r7 .lsr 3),
      .dp .add .r6 .r3 (.reg .r7)] : List Instr)

/-- Our caller's registers back, through `r12` (the frame's base). -/
def epilogue : List Instr := saved.map fun p => .ldr p.1 .r12 p.2

/-- `d = D`, the output's length, from the code. -/
def dOut (d : Reg) : List Instr := [.dp .and d .r6 (.imm 0xfe)]

/-- `d = B`, the block's length, from the code. -/
def dBlk (d : Reg) : List Instr :=
  [.dp .and d .r6 (.imm 1), .mov d (.shifted d .lsl 6), .dp .add d d (.imm 64)]

/-- The case of `hs` whose code is in `r6`, each `f F`. -/
def disp (f : Impl.Pbkdf2.Whole.Arm.Fns → Prog isa) : Prog isa :=
  Dispatch.Arm.chain .r6 (c.hs.map fun F => (code F, f F))

/-- The arguments of HMAC's `init`: the states, the key `K` of `D` bytes,
and the working space (pushed). -/
def hmacArgs₁ : List Instr :=
  scrAt .r0 sInner ++ scrAt .r1 sOuter ++ ([.dp .add .r2 .r8 (.imm (BitVec.ofNat 32 fK))] : List Instr) ++
    dOut .r3 ++ scrAt .r12 sWork

/-- The arguments of the streaming `update`: the inner state, the `B` bytes
it holds (`r2:r3`), and, pushed, the data (at the address `dataA` sets `r1`
to), its `D + lc` bytes (`r7`) and the working space (`r10`). -/
def hmacArgs₂ (dataA : List Instr) (lc : Nat) : List Instr :=
  scrAt .r0 sInner ++ dataA ++ dBlk .r2 ++ ([.mov .r3 (.imm 0)] : List Instr) ++ dOut .r7 ++
    ([.dp .add .r7 .r7 (.imm (BitVec.ofNat 32 lc))] : List Instr) ++ scrAt .r10 sWork

/-- The arguments of HMAC's `finalize`: the states, the `B + D + lc` bytes
the inner one holds (`r2:r3`), and, pushed, the MAC's place in the frame
(`r10`) and the working space (`r12`). -/
def hmacArgs₃ (lc dst : Nat) : List Instr :=
  scrAt .r0 sInner ++ scrAt .r1 sOuter ++ dBlk .r2 ++ dOut .r3 ++
    ([.dp .add .r2 .r2 (.reg .r3), .dp .add .r2 .r2 (.imm (BitVec.ofNat 32 lc)), .mov .r3 (.imm 0),
      .dp .add .r10 .r8 (.imm (BitVec.ofNat 32 dst))] : List Instr) ++ scrAt .r12 sWork

/-- HMAC's `init`, in its frame. -/
def callInit (F : Impl.Pbkdf2.Whole.Arm.Fns) : Prog isa := .frame (.push [.r12, .lr]) (.call F.hiN F.hiC) (.pop .r12 8)
/-- The streaming `update`, in its frame. -/
def callUpd (F : Impl.Pbkdf2.Whole.Arm.Fns) : Prog isa :=
  .frame (.push [.r1, .r7, .r10, .r12]) (.call F.H.updN F.H.updC) (.pop .r1 16)
/-- HMAC's `finalize`, in its frame. -/
def callFin (F : Impl.Pbkdf2.Whole.Arm.Fns) : Prog isa := .frame (.push [.r10, .r12]) (.call F.hfN F.hfC) (.pop .r12 8)

/-- `HMAC_K(data)` into the frame at `dst`, for `D + lc` bytes of `data` at
the address `dataA` sets `r1` to: HMAC's `init` with the key `K`, `update`
on the inner state, and `finalize`, each of the hash function in `r6`. -/
def hmac (dataA : List Instr) (lc dst : Nat) : Prog isa :=
  .seq (.block hmacArgs₁)
  (.seq (c.disp callInit)
  (.seq (.block (hmacArgs₂ dataA lc))
  (.seq (c.disp callUpd)
  (.seq (.block (hmacArgs₃ lc dst))
    (c.disp callFin)))))

/-- `V = HMAC_K(V)`. -/
def hmacV : Prog isa := c.hmac [.dp .add .r1 .r8 (.imm (BitVec.ofNat 32 fV))] 0 fV

/-- The `4 k` bytes at `[src + so]` to `[dst + d]`, a word at a time through `r0`. -/
def copyN (k : Nat) (src : Reg) (so : Nat) (dst : Reg) (d : Nat) : List Instr :=
  (List.range k).flatMap fun j => [.ldr .r0 src (so + 4 * j), .str .r0 dst (d + 4 * j)]

/-- The `len` bytes at `[src + so]` to `[dst + d]` (`4 ≤ len`), a word at a
time through `r0`: `copyN` for the whole words, then the last four bytes
again if `len` is not a multiple of 4. -/
def copyBytes (len : Nat) (src : Reg) (so : Nat) (dst : Reg) (d : Nat) : List Instr :=
  copyN (len / 4) src so dst d ++
    (if len % 4 = 0 then [] else [.ldr .r0 src (so + len - 4), .str .r0 dst (d + len - 4)])

/-- The message `V ‖ b` (and `‖ d ‖ h` if `full`, `Q` bytes each) at
`scratch + sMsg`, for `V` of `D` bytes: all 64 bytes of `V`'s place from the
frame (`r8`), then, from `scratch + sMsg + D` (`r1`), `b` a byte, `d` from
`r5`, and `h` from the frame. -/
def msg (Q b : Nat) (full : Bool) : List Instr :=
  copyN 16 .r8 fV .r11 sMsg ++ dOut .r1 ++
    ([.dp .add .r1 .r11 (.reg .r1), .mov .r0 (.imm (BitVec.ofNat 32 b)), .strb .r0 .r1 sMsg] : List Instr) ++
    (if full then copyBytes Q .r5 0 .r1 (sMsg + 1) ++ copyBytes Q .r8 fH .r1 (sMsg + 1 + Q) else [])

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
def rekeyFull (b : Nat) : Prog isa :=
  .seq (.block (msg c.len b true)) (.seq (c.hmac (scrAt .r1 sMsg) (2 * c.len + 1) fK) c.hmacV)

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
def rekey : Prog isa :=
  .seq (.block (msg c.len 0 false)) (.seq (c.hmac (scrAt .r1 sMsg) 1 fK) c.hmacV)

/-- The `Q` bytes at `r8 + o`, as a big-endian number, shifted right by `s`
bits in place (`0 < s < 32`), through the words at `scratch + sSlot`: `out`
and `d` to `r2` and `r3` and back, as the conversions use `r4` and `r5`. -/
def conv (o s : Nat) : List Instr :=
  ([.mov .r2 (.reg .r4), .mov .r3 (.reg .r5), .dp .add .r1 .r8 (.imm (BitVec.ofNat 32 o)), .mov .r12 (.reg .r11)] : List Instr) ++
    Impl.Weierstrass.Arm.loadBytes c.len (c.w / 2) sSlot .r1 ++ Impl.Weierstrass.Arm.shrWords (c.w / 2) sSlot s ++
    ([.movw .r10 0xffff, .movt .r10 0xffff] : List Instr) ++ Impl.Weierstrass.Arm.storeBytes c.len (c.w / 2) .r8 o sSlot ++
    ([.mov .r4 (.reg .r2), .mov .r5 (.reg .r3)] : List Instr)

/-- The `n` bytes (a positive multiple of 4, in `r3`) at `[r1]` to `[r2]`, a
word at a time through `r0`, counting down in `r3`. -/
def copyLoop : Prog isa :=
  .loop (.block [.ldr .r0 .r1 0, .str .r0 .r2 0, .dp .add .r1 .r1 (.imm 4), .dp .add .r2 .r2 (.imm 4),
    .subs .r3 .r3 (.imm 4)]) .ne

/-- The 68 bytes at `r8 + o` zero, then the digest's first `m = min(D, e)`
bytes to `r8 + o + e - m` (`m` without branches: `D - ((D - e) & -(D ≥ e))`). -/
def dgCopy (o e : Nat) : Prog isa :=
  .seq (.block (([.mov .r0 (.imm 0)] : List Instr) ++ (List.range 17).map (fun j => .str .r0 .r8 (o + 4 * j)) ++
    dOut .r3 ++
    ([.subs .r0 .r3 (.imm (BitVec.ofNat 32 e)), .mov .r1 (.imm 0), .adc .r1 .r1 (.imm 0), .mov .r2 (.imm 0),
      .dp .sub .r1 .r2 (.reg .r1), .dp .and .r0 .r0 (.reg .r1), .dp .sub .r3 .r3 (.reg .r0),
      .dp .add .r2 .r8 (.imm (BitVec.ofNat 32 o)), .dp .add .r2 .r2 (.imm (BitVec.ofNat 32 e)),
      .dp .sub .r2 .r2 (.reg .r3), .mov .r1 (.reg .r10)] : List Instr)))
    copyLoop

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

/-- Word `j` (least significant first) of the `Q` bytes at `h`'s place, as
a big-endian number, back to its place as a number, and that word of the
difference with `n` to `K`'s: both at the offset of the word's bytes. -/
def subWord (j : Nat) : List Instr :=
  ([.ldr .r0 .r8 (fH + 4 * (c.w - 1 - j)), .rev .r0 .r0, .str .r0 .r8 (fH + 4 * (c.w - 1 - j))] : List Instr) ++
    movImm (c.nWord j) ++
    subDigit 0 ++ subDigit 1 ++ ([.dp .orr .r2 .r2 (.reg .r3), .str .r2 .r8 (fK + 4 * (c.w - 1 - j))] : List Instr)

/-- Word `j` of `h`: the difference's if subtracting `n` did not borrow (the
mask in `r7`), the digest's number's if it did, big-endian into `h`. -/
def selWord (j : Nat) : List Instr :=
  [.ldr .r0 .r8 (fH + 4 * (c.w - 1 - j)), .ldr .r1 .r8 (fK + 4 * (c.w - 1 - j)),
    -- `x = d ^ ((x ^ d) & mask)`: the difference `x` if it did not borrow, `d` if it did.
    .dp .eor .r1 .r1 (.reg .r0), .dp .and .r1 .r1 (.reg .r7), .dp .eor .r0 .r0 (.reg .r1),
    .rev .r0 .r0, .str .r0 .r8 (fH + 4 * (c.w - 1 - j))]

/-- `h`: the `Q` bytes at its place, minus `n` if that does not borrow. -/
def reduce : List Instr :=
  ([.movw .r10 0xffff, .mov .r7 (.imm 1)] : List Instr) ++ (List.range c.w).flatMap c.subWord ++
    ([.mov .r12 (.imm 0), .dp .sub .r7 .r12 (.reg .r7)] : List Instr) ++ (List.range c.w).flatMap c.selWord

/-- `h` and `core`'s digest (step 1). -/
def digest : Prog isa :=
  .seq (dgCopy fH c.len)
    (if c.sh = 0 then .block c.reduce else .seq (dgCopy fX (c.len - 1)) (.block (c.conv fX (8 - c.sh))))

/-- `V = 0x01…`, `K = 0x00…`, all 64 bytes of each. -/
def initKV : List Instr :=
  ([.movw .r0 0x0101, .movt .r0 0x0101, .mov .r1 (.imm 0)] : List Instr) ++
    (List.range 16).flatMap fun j => [.str .r0 .r8 (fV + 4 * j), .str .r1 .r8 (fK + 4 * j)]

/-- The candidates left, in `r9`. -/
def initCnt : List Instr := [.movw .r9 (BitVec.ofNat 16 c.tries)]

/-- `r1 = i D`. -/
def iD (i : Nat) : List Instr := dOut .r1 ++ [.movw .r0 (BitVec.ofNat 16 i), .mul .r1 .r1 .r0]

/-- All 64 bytes of `V`'s place to `T`'s at `i D`. -/
def keepV (i : Nat) : List Instr :=
  iD i ++ ([.dp .add .r1 .r1 (.reg .r8)] : List Instr) ++
    (List.range 16).flatMap fun j => [.ldr .r0 .r8 (fV + 4 * j), .str .r0 .r1 (fT + 4 * j)]

/-- `Z` set iff `i D < Q`: `T` needs another `V`. -/
def more (i : Nat) : List Instr :=
  iD i ++ [.subs .r1 .r1 (.imm (BitVec.ofNat 32 c.len)), .mov .r1 (.imm 0), .adc .r1 .r1 (.imm 0),
    .cmp .r1 (.imm 0)]

/-- `V = HMAC_K(V)`, kept in `T` at `i D`. -/
def step (i : Nat) : Prog isa := .seq c.hmacV (.block (keepV i))

/-- The candidate's `V`s after the first: `step i` for each `i` from 1, if
`i D < Q`. -/
def moreSteps : List Nat → Prog isa
  | [] => .block []
  | i :: is => .seq (.block (c.more i)) (.seq (.ite .eq (c.step i) (.block [])) (moreSteps is))

/-- The candidate in `T`: the leftmost `Q` bytes of the `V`s, shifted right
by `sh` bits. -/
def cand : Prog isa :=
  .seq (c.step 0) (.seq (moreSteps c ((List.range c.steps).drop 1))
    (if c.sh = 0 then .block [] else .block (c.conv fT c.sh)))

/-- `core(out, d, digest, k, scratch)`'s arguments, `scratch` pushed, with
the digest `h` (or, if `sh ≠ 0`, the shifted digest) and `k` from `T`. -/
def coreArgs : List Instr :=
  ([.mov .r0 (.reg .r4), .mov .r1 (.reg .r5), .dp .add .r2 .r8 (.imm (BitVec.ofNat 32 (if c.sh = 0 then fH else fX))),
    .dp .add .r3 .r8 (.imm (BitVec.ofNat 32 fT)), .mov .r12 (.reg .r11)] : List Instr)

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

/-- The frame's first 99 words (`K`, `V`, `h`, `T`, `core`'s digest), each from `r1`. -/
def zeros : List (Reg × Nat) := (List.range 99).map fun j => (.r1, 4 * j)

/-- The frame's secrets cleared (`r0`, the result, kept), and our caller's
registers back, through `r12` (the frame's base). -/
def wipe : List Instr :=
  ([.mov .r12 (.reg .r8), .mov .r1 (.imm 0)] : List Instr) ++ zeros.map (fun p => .str p.1 .r12 p.2) ++ epilogue

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block prologue)
  (.seq c.digest
  (.seq (.block initKV)
  (.seq (c.rekeyFull 0)
  (.seq (c.rekeyFull 1)
  (.seq (.block c.initCnt)
  (.seq (.loop c.tryOne .ne)
    (.block wipe)))))))

/-- `vg_ecdsa_<curve>_rfc6979_sign`. -/
def sign : Prog isa := .frame (.alloc frameBytes) c.body (.free frameBytes)

end Cfg

end VG.Impl.Ecdsa.Rfc6979.Arm
