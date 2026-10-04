import VerifiedGarbage.Impl.Pbkdf2.Md.AArch64
import VerifiedGarbage.Impl.Mont.AArch64

/-!
# Deterministic ECDSA (RFC 6979) on AArch64

`sign R H core (out = x0, d = x1, digest = x2, scratch = x3) -> w0`, as on
x86-64 (`Impl/Ecdsa/Rfc6979/X86_64.lean`): RFC 6979 §3.2 for a curve of
32-byte scalars and a Merkle–Damgård hash function `H` whose output is `D`
bytes, `32 ≤ D ≤ 64`, a multiple of 8, with HMAC computed by calling `H`'s
HMAC `init`, streaming `update` and HMAC `finalize`, and each candidate tried
by calling `core`, the signature with a given `k` (`vg_ecdsa_<curve>_sign`),
which reads the leftmost 32 bytes of `V` and of the digest.

The return address `x30` is pushed (the calls replace it), then a frame of
208 bytes is allocated: from `sp`, `K` and `V` (64 bytes each, of which the
first `D` are used), `h` (32 bytes), the number of candidates left, then
`scratch`, `digest`, `d` and `out`. The calls use only `scratch`, which
`core` overwrites entirely, and the 16 bytes below the frame (HMAC's
functions); `K`, `V` and `h` are cleared before the frame is freed. In
`scratch`, as on x86-64: HMAC's inner and outer streaming states, the working
space of HMAC's and `H`'s functions, and the message of steps d, f and h.3.

1. `h = bits2octets(digest)`: the leftmost 32 bytes, minus `n` if they are
   at least `n` (a conditional subtraction, as `2^256 < 2n`).
2. Steps b to g: `V = 0x01…`, `K = 0x00…`, `K = HMAC_K(V ‖ 0x00 ‖ d ‖ h)`,
   `V = HMAC_K(V)`, `K = HMAC_K(V ‖ 0x01 ‖ d ‖ h)`, `V = HMAC_K(V)`.
3. At most `tries` times: `V = HMAC_K(V)`, the candidate `k = V`, and
   `core(out, d, digest, V, scratch)`; if it failed and candidates are left,
   `K = HMAC_K(V ‖ 0x00)`, `V = HMAC_K(V)` and again. Whether to go on, in
   `x12`, is computed without branches, so that the code branches only on
   it: the number of candidates tried is all it reveals.

`core` writes the signature or zeros to `out`, and its return value is ours.

A block addresses memory only at `sp` (through `x15`, set by `addSp`) or at
a pointer an earlier block loaded from the frame (`digestPtr`, `msgPtrs`),
never one it loads itself, so that the taint analysis of each block knows
its addresses are public.
-/

namespace VG.Impl.Ecdsa.Rfc6979.AArch64

open VG.AArch64 VG.Impl.Pbkdf2.Md.AArch64
open VG.Impl.Mont.AArch64 (const64)

/-! Where things are in the frame. -/
def fK : Nat := 0
def fV : Nat := 64
def fH : Nat := 128
def fCnt : Nat := 160
def fScratch : Nat := 168
def fDigest : Nat := 176
def fD : Nat := 184
def fOut : Nat := 192
/-- The frame's size, a multiple of 16. -/
def frameBytes : Nat := 208

/-! Where things are in `scratch`. -/
def sInner : Nat := 0
def sOuter : Nat := 192
def sWork : Nat := 384
def sMsg : Nat := 2256

/-- What the code needs of a curve and a hash function. -/
structure Cfg where
  /-- The hash function's code and names. -/
  H : Hash
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
  scr .x0 sInner ++ scr .x1 sOuter ++ fr .x2 fK ++ [.movz .x .x3 (BitVec.ofNat 16 D) 0] ++ scr .x4 sWork

/-- The arguments of the streaming `update`: the inner state, the `B` bytes
it holds, the data (at the address `dataA` sets `x2` to) of `len` bytes,
the working space. -/
def hmacArgs₂ (B : Nat) (dataA : List Instr) (len : Nat) : List Instr :=
  scr .x0 sInner ++ [.movz .x .x1 (BitVec.ofNat 16 B) 0] ++ dataA ++
    [.movz .x .x3 (BitVec.ofNat 16 len) 0] ++ scr .x4 sWork

/-- The arguments of HMAC's `finalize`: the states, the `B + len` bytes the
inner one holds, the MAC's place in the frame, the working space. -/
def hmacArgs₃ (B len dst : Nat) : List Instr :=
  scr .x0 sInner ++ scr .x1 sOuter ++ [.movz .x .x2 (BitVec.ofNat 16 (B + len)) 0] ++ fr .x3 dst ++
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

/-- The pointers the messages need: `scratch` in `x9`, `d` in `x10`, and
the frame in `x15` (loaded first, so that every address the message's block
computes is from them). -/
def msgPtrs : List Instr := [.ldrSp .x9 fScratch, .ldrSp .x10 fD, .addSp .x15 0]

/-- The message `V ‖ b` (and `‖ d ‖ h` if `full`) at `scratch + sMsg`, for
`V` of `D` bytes, with `scratch` in `x9`, `d` in `x10` and the frame in
`x15`: `V` and `h` from the frame, `b` a byte; `d ‖ h` through `x12`, which
points after `b`, as an 8-byte store's offset is a multiple of 8. -/
def msg (D b : Nat) (full : Bool) : List Instr :=
  copyN (D / 8) .x15 fV .x9 sMsg ++
    [.movz .x .x11 (BitVec.ofNat 16 b) 0, .strb .x11 .x9 (sMsg + D)] ++
    (if full then .addImm .x .x12 .x9 (sMsg + D + 1) :: (copyN 4 .x10 0 .x12 0 ++ copyN 4 .x15 fH .x12 32)
      else [])

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
def rekeyFull (b : Nat) : Prog isa :=
  .seq (.block msgPtrs) (.seq (.block (msg c.H.D b true))
    (.seq (c.hmac (scr .x2 sMsg) (c.H.D + 65) fK) c.hmacV))

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
def rekey : Prog isa :=
  .seq (.block msgPtrs) (.seq (.block (msg c.H.D 0 false)) (.seq (c.hmac (scr .x2 sMsg) (c.H.D + 1) fK) c.hmacV))

/-- The 64-bit words of `n`, least significant first. -/
def nWord (j : Nat) : BitVec 64 := BitVec.ofNat 64 (c.n >>> (64 * j))

/-- `digest` in `x1`. -/
def digestPtr : List Instr := [.ldrSp .x1 fDigest]

/-- `h`: the 32 bytes at `digest` (in `x1`), as a big-endian number in
`x11:x10:x9:x8`, minus `n` (into `x5:x4:x3:x2`) if that does not borrow
(the mask of the borrow in `x6`), back big-endian into the frame. -/
def reduce : List Instr :=
  [.movz .x .x7 0 0, .addSp .x15 0,
    .ldr .x .x8 .x1 24, .rev .x8 .x8, .ldr .x .x9 .x1 16, .rev .x9 .x9,
    .ldr .x .x10 .x1 8, .rev .x10 .x10, .ldr .x .x11 .x1 0, .rev .x11 .x11] ++
  const64 .x12 (c.nWord 0) ++ [.subs .x .x2 .x8 .x12] ++
  const64 .x12 (c.nWord 1) ++ [.sbcs .x .x3 .x9 .x12] ++
  const64 .x12 (c.nWord 2) ++ [.sbcs .x .x4 .x10 .x12] ++
  const64 .x12 (c.nWord 3) ++ [.sbcs .x .x5 .x11 .x12, .sbc .x .x6 .x7 .x7] ++
  -- `x = d ^ ((x ^ d) & mask)`: `x` if it borrowed, `d` if not.
  ([(.x8, .x2), (.x9, .x3), (.x10, .x4), (.x11, .x5)] : List (Reg × Reg)).flatMap
    (fun (x, d) => [.logic .eor .x x x d, .logic .and .x x x .x6, .logic .eor .x x x d]) ++
  [.rev .x11 .x11, .str .x .x11 .x15 fH, .rev .x10 .x10, .str .x .x10 .x15 (fH + 8),
    .rev .x9 .x9, .str .x .x9 .x15 (fH + 16), .rev .x8 .x8, .str .x .x8 .x15 (fH + 24)]

/-- `V = 0x01…`, `K = 0x00…`, all 64 bytes of each. -/
def initKV : List Instr :=
  const64 .x9 (BitVec.ofNat 64 0x0101010101010101) ++ [.movz .x .x10 0 0, .addSp .x15 0] ++
    (List.range 8).flatMap fun j => [.str .x .x9 .x15 (fV + 8 * j), .str .x .x10 .x15 (fK + 8 * j)]

/-- The candidates left. -/
def initCnt : List Instr :=
  [.movz .x .x9 (BitVec.ofNat 16 c.tries) 0, .addSp .x15 0, .str .x .x9 .x15 fCnt]

/-- `core(out, d, digest, k = V, scratch)`. -/
def coreArgs : List Instr :=
  [.ldrSp .x0 fOut, .ldrSp .x1 fD, .ldrSp .x2 fDigest] ++ fr .x3 fV ++ [.ldrSp .x4 fScratch]

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

/-- One candidate: `V = HMAC_K(V)`, `core` with `k = V`, then, if it failed
and candidates are left, step h.3. -/
def tryOne : Prog isa :=
  .seq c.hmacV
  (.seq (.block coreArgs)
  (.seq (.call c.coreN c.coreC)
  (.seq (.block goOn)
    (.ite (.nonzero .x .x12) (.seq c.rekey (.block again)) (.block stop)))))

/-- `K`, `V` and `h` cleared (`x0`, the result, kept). -/
def wipe : List Instr :=
  [.addSp .x15 0, .movz .x .x14 0 0] ++ (List.range 20).map fun j => .str .x .x14 .x15 (8 * j)

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block saveArgs)
  (.seq (.block digestPtr)
  (.seq (.block (c.reduce ++ initKV))
  (.seq (c.rekeyFull 0)
  (.seq (c.rekeyFull 1)
  (.seq (.block c.initCnt)
  (.seq (.loop c.tryOne (.nonzero .x .x12))
    (.block wipe)))))))

/-- `vg_ecdsa_<curve>_<hash>_sign`. -/
def sign : Prog isa :=
  .frame (.push .x30) (.frame (.alloc frameBytes) c.body (.free frameBytes)) (.pop .x30)

end Cfg

end VG.Impl.Ecdsa.Rfc6979.AArch64
