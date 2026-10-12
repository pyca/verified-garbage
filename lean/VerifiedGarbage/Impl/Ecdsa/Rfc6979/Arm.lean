module

public import VerifiedGarbage.Impl.Pbkdf2.Whole.Arm
public import VerifiedGarbage.Impl.Weierstrass.Arm

/-!
# Deterministic ECDSA (RFC 6979) on 32-bit ARM

`sign R H core (out = r0, d = r1, digest = r2, scratch = r3) -> r0`, as on
x86 and AArch64 (`Impl/Ecdsa/Rfc6979/X86.lean`): RFC 6979 §3.2 for a curve
of `Q`-byte scalars in `w` 32-bit words and a Merkle–Damgård hash function
`H` whose output is `D` bytes, a multiple of 8, at most 64, with HMAC
computed by calling `H`'s HMAC `init`, streaming `update` and HMAC
`finalize`, and each candidate tried by calling `core`, the signature with a
given `k` (`vg_ecdsa_<curve>_sign`), which reads `Q` bytes of the digest and
of `k`, and takes the digest's leftmost `qlen` bits (`bits2int`, a right
shift by `sh = 8 Q - qlen` bits).

Two kinds of curve and hash function, as on x86:

* `Q = 4 w ≤ D` and `qlen = 8 Q` (P-256 and P-384, `wide = false`): one `V`
  makes a candidate, its leftmost `Q` bytes; `bits2octets` is a conditional
  subtraction of `n` from the digest's leftmost `Q` bytes; and `core` reads
  the digest and `V` in place.
* `8 D < qlen ≤ 16 D` and `Q ≤ D + 4` (P-521 with SHA-512, `wide`): two `V`s
  make a candidate, the leftmost `Q` bytes of the second's concatenation with
  the first, shifted right by `sh` bits; the digest's integer is below `n`,
  so `bits2octets` is the digest after `Q - D` zero bytes; and `core` reads
  the digest shifted left by `sh` bits, which it shifts back. The candidate
  and that digest are made in `Q` bytes at the frame's top, through the
  32-bit words at `scratch + sSlot` (`loadBytes`, `shrWords`, `storeBytes`,
  with `out` and `d` kept in `r2` and `r3` meanwhile, as those use `r4` and
  `r5`).

A frame of 216 bytes is allocated, 360 if `wide`: from `sp`, `K` and `V`
(64 bytes each, of which the first `D` are used), `h` (48 bytes, unless
`wide`), a word unused, and our caller's `r4`–`r11` and `lr` (the calls
replace `lr`); and, if `wide`, the digest for `core` and the candidate (72
bytes each). The functions we call
preserve `r4`–`r11`, which hold what lives across the calls: `out`, `d` and
`digest` in `r4`–`r6`, the frame in `r8`, the number of candidates left in
`r9` and `scratch` in `r11`. Each call's arguments beyond `r0`–`r3` are
pushed by a frame of its own, as in PBKDF2's code
(`VG.Impl.Pbkdf2.Whole.Arm`): `push {r12, lr}` for HMAC's `init` and for
`core` (the working space or `scratch`, and a word of padding),
`push {r1, r7, r10, r12}` for `update` (the data, its length, the working
space and padding) and `push {r10, r12}` for HMAC's `finalize` (the MAC's
place and the working space), so that the stack pointer stays 8-byte
aligned. The calls use only `scratch`,
which `core` overwrites entirely, and the stack below the frame; `K`, `V`,
`h` and, if `wide`, the digest for `core` and the candidate are cleared
before the frame is freed. In `scratch`, as on x86: HMAC's inner and outer
streaming states, the working space of HMAC's and `H`'s functions, the
message of steps d, f and h.3, and the words of the conversions.

1. `h = bits2octets(digest)`: unless `wide`, the leftmost `Q` bytes, minus
   `n` if they are at least `n` (a conditional subtraction, as
   `2^(8 Q) < 2n`): the bytes, as `w` 32-bit words, go to `h`'s place, and
   `h - n`, by 16-bit digits (the model's `adc` sets no flags), to `K`'s; the
   mask of the borrow selects between them, word by word, big-endian into
   `h`. If `wide`, the digest for `core` instead: the digest then `Q - D`
   zero bytes, shifted right by `8 (Q - D) - sh` bits.
2. Steps b to g: `V = 0x01…`, `K = 0x00…`, `K = HMAC_K(V ‖ 0x00 ‖ d ‖ h)`,
   `V = HMAC_K(V)`, `K = HMAC_K(V ‖ 0x01 ‖ d ‖ h)`, `V = HMAC_K(V)`.
3. At most `tries` times: `V = HMAC_K(V)` (twice if `wide`), the candidate
   `k`, and `core(out, d, digest, k, scratch)`; if it failed and candidates are left,
   `K = HMAC_K(V ‖ 0x00)`, `V = HMAC_K(V)` and again. Whether to go on is
   computed without branches, so that the code branches only on it: the
   number of candidates tried is all it reveals.

`core` writes the signature or zeros to `out`, and its return value is ours.
Every address is the frame's base (in `r8`, from `sp` in the prologue, and
in `r12` for the prologue and the epilogue) or a pointer argument plus a
constant (in a conversion, `r1` and `r12` are the frame's base and `scratch`
plus a constant).
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Rfc6979.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Stream.Arm (scrAt)

/-! Where things are in the frame. -/
def fK : Nat := 0
def fV : Nat := 64
def fH : Nat := 128
def fSave : Nat := 180
/-- If `wide`: the digest for `core`, and the candidate. -/
def fX : Nat := 216
def fKb : Nat := 288
/-- The words at the frame's top: the digest for `core` and the candidate,
if `wide`. -/
def extra (wide : Bool) : Nat := if wide then 36 else 0
/-- The frame's size, a multiple of 8. -/
def frameBytes (wide : Bool) : Nat := 216 + 4 * extra wide

/-! Where things are in `scratch`. -/
def sInner : Nat := 0
def sOuter : Nat := 192
def sWork : Nat := 384
def sMsg : Nat := 2256
/-- The words of a conversion, if `wide`. -/
def sSlot : Nat := 2560

/-- Our caller's registers, where the frame keeps them (`r8`, the frame's
base afterwards, last). -/
def saved : List (Reg × Nat) :=
  [(.r4, fSave), (.r5, fSave + 4), (.r6, fSave + 8), (.r7, fSave + 12), (.r9, fSave + 16),
    (.r10, fSave + 20), (.r11, fSave + 24), (.lr, fSave + 28), (.r8, fSave + 32)]

/-- What the code needs of a curve and a hash function. -/
structure Cfg where
  /-- The hash function's streaming `update`, and HMAC's `init` and
  `finalize` with their working space as an argument (the functions
  PBKDF2's code calls). -/
  F : Impl.Pbkdf2.Whole.Arm.Fns
  /-- The 32-bit words of the curve's scalars (an even number). -/
  w : Nat
  /-- The bytes of the curve's scalars, `Q`. -/
  len : Nat := 4 * w
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

/-- Our caller's registers into the frame (through `r12`, its base); the
arguments to the registers that keep them, and the frame's base to `r8`. -/
def prologue : List Instr :=
  .addSp .r12 0 :: saved.map (fun p => .str p.1 .r12 p.2) ++
    ([.mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .mov .r6 (.reg .r2), .mov .r11 (.reg .r3), .mov .r8 (.reg .r12)] : List Instr)

/-- Our caller's registers back, through `r12` (the frame's base). -/
def epilogue : List Instr := saved.map fun p => .ldr p.1 .r12 p.2

/-- The arguments of HMAC's `init`: the states, the key `K` of `D` bytes,
and the working space (pushed). -/
def hmacArgs₁ (D : Nat) : List Instr :=
  scrAt .r0 sInner ++ scrAt .r1 sOuter ++ ([.dp .add .r2 .r8 (.imm (BitVec.ofNat 32 fK)), .movw .r3 (BitVec.ofNat 16 D)] : List Instr) ++ scrAt .r12 sWork

/-- The arguments of the streaming `update`: the inner state, the `B` bytes
it holds (`r2:r3`), and, pushed, the data (at the address `dataA` sets `r1`
to), its `len` bytes (`r7`) and the working space (`r10`). -/
def hmacArgs₂ (B : Nat) (dataA : List Instr) (len : Nat) : List Instr :=
  scrAt .r0 sInner ++ dataA ++ ([.movw .r2 (BitVec.ofNat 16 B), .mov .r3 (.imm 0),
    .movw .r7 (BitVec.ofNat 16 len)] : List Instr) ++ scrAt .r10 sWork

/-- The arguments of HMAC's `finalize`: the states, the `B + len` bytes the
inner one holds (`r2:r3`), and, pushed, the MAC's place in the frame (`r10`)
and the working space (`r12`). -/
def hmacArgs₃ (B len dst : Nat) : List Instr :=
  scrAt .r0 sInner ++ scrAt .r1 sOuter ++ ([.movw .r2 (BitVec.ofNat 16 (B + len)), .mov .r3 (.imm 0),
    .dp .add .r10 .r8 (.imm (BitVec.ofNat 32 dst))] : List Instr) ++ scrAt .r12 sWork

/-- `HMAC_K(data)` into the frame at `dst`, for `len` bytes of `data` at the
address `dataA` sets `r1` to: HMAC's `init` with the key `K`, `update` on
the inner state, and `finalize`. -/
def hmac (dataA : List Instr) (len dst : Nat) : Prog isa :=
  .seq (.block (hmacArgs₁ c.F.H.D))
  (.seq (.frame (.push [.r12, .lr]) (.call c.F.hiN c.F.hiC) (.pop .r12 8))
  (.seq (.block (hmacArgs₂ c.F.H.B dataA len))
  (.seq (.frame (.push [.r1, .r7, .r10, .r12]) (.call c.F.H.updN c.F.H.updC) (.pop .r1 16))
  (.seq (.block (hmacArgs₃ c.F.H.B len dst))
    (.frame (.push [.r10, .r12]) (.call c.F.hfN c.F.hfC) (.pop .r12 8))))))

/-- `V = HMAC_K(V)`. -/
def hmacV : Prog isa := c.hmac [.dp .add .r1 .r8 (.imm (BitVec.ofNat 32 fV))] c.F.H.D fV

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
`scratch + sMsg`, for `V` of `D` bytes: `V` from the frame (`r8`), `b` a
byte, `d` from `r5`, and `h` from the frame, or, if `wide`, `Q - D` zero
bytes (a zero word, which the digest's words then overwrite but for them)
and the digest (from `r6`). -/
def msg (w Q D b : Nat) (full wide : Bool) : List Instr :=
  copyN (D / 4) .r8 fV .r11 sMsg ++ ([.mov .r0 (.imm (BitVec.ofNat 32 b)), .strb .r0 .r11 (sMsg + D)] : List Instr) ++
    (if full then
      (if wide then
        copyBytes Q .r5 0 .r11 (sMsg + D + 1) ++
          ([.mov .r0 (.imm 0), .str .r0 .r11 (sMsg + D + 1 + Q)] : List Instr) ++ copyN (D / 4) .r6 0 .r11 (sMsg + 1 + 2 * Q)
      else copyN w .r5 0 .r11 (sMsg + D + 1) ++ copyN w .r8 fH .r11 (sMsg + D + 1 + 4 * w))
    else [])

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
def rekeyFull (b : Nat) : Prog isa :=
  .seq (.block (msg c.w c.len c.F.H.D b true c.wide))
    (.seq (c.hmac (scrAt .r1 sMsg) (c.F.H.D + 2 * c.len + 1) fK) c.hmacV)

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
def rekey : Prog isa :=
  .seq (.block (msg c.w c.len c.F.H.D 0 false false)) (.seq (c.hmac (scrAt .r1 sMsg) (c.F.H.D + 1) fK) c.hmacV)

/-- The `Q` bytes at `r8 + o`, as a big-endian number, shifted right by `s`
bits in place (`0 < s < 32`), through the words at `scratch + sSlot`: `out`
and `d` to `r2` and `r3` and back, as the conversions use `r4` and `r5`. -/
def conv (o s : Nat) : List Instr :=
  ([.mov .r2 (.reg .r4), .mov .r3 (.reg .r5), .dp .add .r1 .r8 (.imm (BitVec.ofNat 32 o)), .mov .r12 (.reg .r11)] : List Instr) ++
    Impl.Weierstrass.Arm.loadBytes c.len (c.w / 2) sSlot .r1 ++ Impl.Weierstrass.Arm.shrWords (c.w / 2) sSlot s ++
    ([.movw .r10 0xffff, .movt .r10 0xffff] : List Instr) ++ Impl.Weierstrass.Arm.storeBytes c.len (c.w / 2) .r8 o sSlot ++
    ([.mov .r4 (.reg .r2), .mov .r5 (.reg .r3)] : List Instr)

/-- If `wide`: the digest for `core`, the digest (at `r6`) then `Q - D` zero
bytes, shifted right by `8 (Q - D) - sh` bits: the digest's integer shifted
left by `sh` bits. -/
def coreDigest : List Instr :=
  ([.mov .r0 (.imm 0), .str .r0 .r8 (fX + c.len - 4)] : List Instr) ++ copyN (c.F.H.D / 4) .r6 0 .r8 fX ++
    c.conv fX (8 * (c.len - c.F.H.D) - c.sh)

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
  ([.ldr .r0 .r6 (4 * (c.w - 1 - j)), .rev .r0 .r0, .str .r0 .r8 (fH + 4 * (c.w - 1 - j))] : List Instr) ++ movImm (c.nWord j) ++
    subDigit 0 ++ subDigit 1 ++ ([.dp .orr .r2 .r2 (.reg .r3), .str .r2 .r8 (fK + 4 * (c.w - 1 - j))] : List Instr)

/-- Word `j` of `h`: the difference's if subtracting `n` did not borrow (the
mask in `r7`), the digest's number's if it did, big-endian into `h`. -/
def selWord (j : Nat) : List Instr :=
  [.ldr .r0 .r8 (fH + 4 * (c.w - 1 - j)), .ldr .r1 .r8 (fK + 4 * (c.w - 1 - j)),
    -- `x = d ^ ((x ^ d) & mask)`: the difference `x` if it did not borrow, `d` if it did.
    .dp .eor .r1 .r1 (.reg .r0), .dp .and .r1 .r1 (.reg .r7), .dp .eor .r0 .r0 (.reg .r1),
    .rev .r0 .r0, .str .r0 .r8 (fH + 4 * (c.w - 1 - j))]

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

/-- `core(out, d, digest, k, scratch)`'s arguments, `scratch` pushed, with
`k = V`, or, if `wide`, the digest and the candidate at the frame's top. -/
def coreArgs (wide : Bool) : List Instr :=
  ([.mov .r0 (.reg .r4), .mov .r1 (.reg .r5)] : List Instr) ++
    (if wide then [.dp .add .r2 .r8 (.imm (BitVec.ofNat 32 fX)), .dp .add .r3 .r8 (.imm (BitVec.ofNat 32 fKb))]
    else [.mov .r2 (.reg .r6), .dp .add .r3 .r8 (.imm (BitVec.ofNat 32 fV))]) ++
    ([.mov .r12 (.reg .r11)] : List Instr)

/-- If `wide`: `V`'s first `D` bytes to the candidate's place. -/
def keepV : List Instr := copyN (c.F.H.D / 4) .r8 fV .r8 fKb

/-- If `wide`: the next four bytes of the candidate from `V`, then the
candidate's `Q` bytes shifted right by `sh` bits. -/
def candTop : List Instr :=
  ([.ldr .r0 .r8 fV, .str .r0 .r8 (fKb + c.F.H.D)] : List Instr) ++ c.conv fKb c.sh

/-- The candidate: `V = HMAC_K(V)`, which is `k`; or, if `wide`, the
leftmost `Q` bytes of `V = HMAC_K(V)` then `V = HMAC_K(V)` again, shifted
right by `sh` bits. -/
def cand : Prog isa :=
  if c.wide then .seq c.hmacV (.seq (.block c.keepV) (.seq c.hmacV (.block c.candTop))) else c.hmacV

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
  (.seq (.block (coreArgs c.wide))
  (.seq (.frame (.push [.r12, .lr]) (.call c.coreN c.coreC) (.pop .r12 8))
  (.seq (.block goOn)
    (.ite .ne (.seq c.rekey (.block again)) (.block stop)))))

/-- The 44 words of `K`, `V` and `h`, each from `r1`. -/
def zeros : List (Reg × Nat) := (List.range 44).map fun j => (.r1, 4 * j)

/-- The words at the frame's top, each from `r1`. -/
def zerosHigh (wide : Bool) : List (Reg × Nat) := (List.range (extra wide)).map fun j => (.r1, fX + 4 * j)

/-- `K`, `V` and `h` cleared, and the words at the frame's top (`r0`, the
result, kept), and our caller's registers back, through `r12` (the frame's
base). -/
def wipe (wide : Bool) : List Instr :=
  ([.mov .r12 (.reg .r8), .mov .r1 (.imm 0)] : List Instr) ++ zeros.map (fun p => .str p.1 .r12 p.2) ++
    (zerosHigh wide).map (fun p => .str p.1 .r12 p.2) ++ epilogue

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block (prologue ++ (if c.wide then c.coreDigest else c.reduce) ++ initKV))
  (.seq (c.rekeyFull 0)
  (.seq (c.rekeyFull 1)
  (.seq (.block c.initCnt)
  (.seq (.loop c.tryOne .ne)
    (.block (wipe c.wide))))))

/-- `vg_ecdsa_<curve>_<hash>_sign`. -/
def sign : Prog isa :=
  .frame (.alloc (frameBytes c.wide)) c.body (.free (frameBytes c.wide))

end Cfg

end VG.Impl.Ecdsa.Rfc6979.Arm
