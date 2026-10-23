module

public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Impl.Mont.PPC64LE

/-!
# Deterministic ECDSA (RFC 6979) on PPC64LE

`sign (out = r3, d = r4, digest = r5, scratch = r6) -> r3`, as on AArch64
(`Impl/Ecdsa/Rfc6979/AArch64.lean`): RFC 6979 §3.2 for a curve of `Q`-byte
scalars, `Q` a multiple of 4, and a Merkle–Damgård hash function `H` whose
output is `D ≥ Q` bytes, a multiple of 4, with HMAC computed by calling `H`'s
HMAC `init` and `finalize` (with their working space as an argument) and
its streaming `update`, and each candidate tried by calling `core`, the
signature with a given `k` (`vg_ecdsa_<curve>_sign`), which reads `Q` bytes
of the digest and of `k`. The order `n` has exactly `8 Q` bits and
`2^(8 Q) < 2n` (P-192, P-224, P-256, P-384, secp256k1, brainpoolP256r1 and
brainpoolP384r1): one `V` makes a candidate, its leftmost `Q` bytes,
`bits2octets` is a conditional subtraction of `n` from the digest's leftmost
`Q` bytes, and `core` reads the digest and `V` in place.

The return address is moved to `r0` and pushed (the calls replace it), then
a frame of 256 bytes is allocated: above its 32-byte header, `K` and `V` (64
bytes each, of which the first `D` are used), `h` (48 bytes, of which `Q`
are used), the number of candidates left, then `scratch`, `digest`, `d` and
`out`. The calls use only `scratch`, which `core` overwrites entirely, and
the stack below the frame; `K`, `V` and `h` are cleared before the frame is
freed. In `scratch`: HMAC's inner and outer streaming states, the working
space of HMAC's and `H`'s functions, and the message of steps d, f and h.3.

1. `h = bits2octets(digest)`: the leftmost `Q` bytes, minus `n` if they are
   at least `n` (a conditional subtraction, as `2^(8 Q) < 2n`), by 32-bit
   digits, as the model has no carry (as in `Impl/Mont/PPC64LE.lean`): the
   digits of the digest to `V`'s place, those of the difference to `K`'s
   (before steps b and c set them), and the one the borrow selects,
   big-endian, to `h`.
2. Steps b to g: `V = 0x01…`, `K = 0x00…`, `K = HMAC_K(V ‖ 0x00 ‖ d ‖ h)`,
   `V = HMAC_K(V)`, `K = HMAC_K(V ‖ 0x01 ‖ d ‖ h)`, `V = HMAC_K(V)`.
3. At most `tries` times: `V = HMAC_K(V)`, which is `k`, and
   `core(out, d, digest, k, scratch)`; if it failed and candidates are left,
   `K = HMAC_K(V ‖ 0x00)`, `V = HMAC_K(V)` and again. Whether to go on, in
   `r12`, is computed without branches from the low bit of `core`'s result
   (the bits its contract determines), so that the code branches only on
   it: the number of candidates tried is all it reveals.

`core` writes the signature or zeros to `out`, and its result is ours.

A block addresses memory only at the frame (through `r11`, set by `addSp`)
or at a pointer it loads from the frame before using it, so that the taint
analysis of each block knows its addresses are public.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Rfc6979.PPC64LE

open VG.PPC64LE
open VG.Impl.Mont.PPC64LE (movImm mask32)

/-! Where things are in the frame. -/
def fK : Nat := 32
def fV : Nat := 96
def fH : Nat := 160
def fCnt : Nat := 208
def fScratch : Nat := 216
def fDigest : Nat := 224
def fD : Nat := 232
def fOut : Nat := 240
/-- The frame's size, a multiple of 16. -/
def frameBytes : Nat := 256

/-! Where things are in `scratch`. -/
def sInner : Nat := 0
def sOuter : Nat := 192
def sWork : Nat := 384
def sMsg : Nat := 2256

/-- HMAC over a hash function, as the code calls it: the block size `B`,
the digest size `D`, HMAC's `init` and `finalize` with their working space
as an argument and the streaming `update`, with their names. -/
structure Hm where
  B : Nat
  D : Nat
  initN : String
  initC : Prog isa
  updN : String
  updC : Prog isa
  finN : String
  finC : Prog isa

/-- What the code needs of a curve and a hash function. -/
structure Cfg where
  /-- The hash function's HMAC. -/
  H : Hm
  /-- The bytes of the curve's scalars, `Q`, a multiple of 4. -/
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

/-- `r12 ← scratch`, with the frame in `r11`. -/
def scrBase : List Instr := [.addSp .r11 0, .load .d .r12 .r11 fScratch]

/-- The arguments of HMAC's `init`: the states, the key `K` of `D` bytes,
the working space. -/
def hmacArgs₁ (D : Nat) : List Instr :=
  scrBase ++ [.addi .r3 .r12 sInner, .addi .r4 .r12 sOuter, .addSp .r5 fK, .li .r6 D, .addi .r7 .r12 sWork]

/-- The arguments of the streaming `update`: the inner state, the `B` bytes
it holds, the data (at the address `dataA` sets `r5` to, from `scratch` in
`r12`) of `len` bytes, the working space. -/
def hmacArgs₂ (B : Nat) (dataA : List Instr) (len : Nat) : List Instr :=
  scrBase ++ [.addi .r3 .r12 sInner, .li .r4 B] ++ dataA ++ [.li .r6 len, .addi .r7 .r12 sWork]

/-- The arguments of HMAC's `finalize`: the states, the `B + len` bytes the
inner one holds, the MAC's place in the frame, the working space. -/
def hmacArgs₃ (B len dst : Nat) : List Instr :=
  scrBase ++ [.addi .r3 .r12 sInner, .addi .r4 .r12 sOuter, .li .r5 (B + len), .addSp .r6 dst,
    .addi .r7 .r12 sWork]

/-- `HMAC_K(data)` into the frame at `dst`, for `len` bytes of `data` at the
address `dataA` sets `r5` to: HMAC's `init` with the key `K`, `update` on
the inner state, and `finalize`. -/
def hmac (dataA : List Instr) (len dst : Nat) : Prog isa :=
  .seq (.block (hmacArgs₁ c.H.D))
  (.seq (.call c.H.initN c.H.initC)
  (.seq (.block (hmacArgs₂ c.H.B dataA len))
  (.seq (.call c.H.updN c.H.updC)
  (.seq (.block (hmacArgs₃ c.H.B len dst))
    (.call c.H.finN c.H.finC)))))

/-- `V = HMAC_K(V)`. -/
def hmacV : Prog isa := c.hmac [.addSp .r5 fV] c.H.D fV

/-- Copying 32-bit word `k` from `so(src)` to `d(dst)`, through `r8`. -/
def cpw (src : Reg) (so : Nat) (dst : Reg) (d k : Nat) : List Instr :=
  [.load .w .r8 src (so + 4 * k), .store .w .r8 dst (d + 4 * k)]

/-- The `4 k` bytes at `so(src)` to `d(dst)`. -/
def copyW (k : Nat) (src : Reg) (so : Nat) (dst : Reg) (d : Nat) : List Instr :=
  (List.range k).flatMap (cpw src so dst d)

/-- The pointers the messages need: the frame in `r11`, `scratch` in `r9`,
`d` in `r10`. -/
def msgPtrs : List Instr := [.addSp .r11 0, .load .d .r9 .r11 fScratch, .load .d .r10 .r11 fD]

/-- The message `V ‖ b` (and `‖ d ‖ h` if `full`, `Q` bytes each) at
`scratch + sMsg`, for `V` of `D` bytes, with the frame in `r11`, `scratch`
in `r9` and `d` in `r10`, a 32-bit word at a time. -/
def msg (Q D b : Nat) (full : Bool) : List Instr :=
  copyW (D / 4) .r11 fV .r9 sMsg ++ ([.li .r8 b, .stb .r8 .r9 (sMsg + D)] : List Instr) ++
    (if full then copyW (Q / 4) .r10 0 .r9 (sMsg + D + 1) ++ copyW (Q / 4) .r11 fH .r9 (sMsg + D + 1 + Q)
    else [])

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
def rekeyFull (b : Nat) : Prog isa :=
  .seq (.block (msgPtrs ++ msg c.len c.H.D b true))
    (.seq (c.hmac [.addi .r5 .r12 sMsg] (c.H.D + 2 * c.len + 1) fK) c.hmacV)

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
def rekey : Prog isa :=
  .seq (.block (msgPtrs ++ msg c.len c.H.D 0 false))
    (.seq (c.hmac [.addi .r5 .r12 sMsg] (c.H.D + 1) fK) c.hmacV)

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
`h + Q - 4 (j + 1)`. -/
def selDigit (j : Nat) : List Instr :=
  [.load .w .r7 .r11 (fV + 4 * j), .load .w .r8 .r11 (fK + 4 * j),
    -- `x = d ^ ((d ^ x) & mask)`: the difference if it did not borrow.
    .logic .xor .r8 .r8 .r7, .logic .and .r8 .r8 .r10, .logic .xor .r7 .r7 .r8,
    .li .r12 (fH + c.len - 4 * (j + 1)), .storeRev .w .r7 .r11 .r12]

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

/-- `core(out, d, digest, k, scratch)`, with `k = V`. -/
def coreArgs : List Instr :=
  [.addSp .r11 0, .load .d .r3 .r11 fOut, .load .d .r4 .r11 fD, .load .d .r5 .r11 fDigest,
    .addSp .r6 fV, .load .d .r7 .r11 fScratch]

/-- One candidate fewer, and `r12 ≠ 0` iff the signature failed (the low bit
of `r3` is 0) and candidates are left: `r12 = ((r3 & 1) - 1) & (count - 1)`. -/
def goOn : List Instr :=
  [.addSp .r11 0, .load .d .r9 .r11 fCnt, .subi .r9 .r9 1, .store .d .r9 .r11 fCnt,
    .li .r10 1, .logic .and .r8 .r3 .r10, .sub .r8 .r8 .r10, .logic .and .r12 .r8 .r9]

/-- Go on. -/
def again : List Instr := [.li .r12 1]

/-- Stop. -/
def stop : List Instr := [.li .r12 0]

/-- One candidate: `V = HMAC_K(V)`, `core` with it, then, if it failed and
candidates are left, step h.3. -/
def tryOne : Prog isa :=
  .seq c.hmacV
  (.seq (.block coreArgs)
  (.seq (.call c.coreN c.coreC)
  (.seq (.block goOn)
    (.ite (.nonzero .d .r12) (.seq c.rekey (.block again)) (.block stop)))))

/-- `K`, `V` and `h` cleared (`r3`, the result, kept). -/
def wipe : List Instr :=
  ([.addSp .r11 0, .li .r12 0] : List Instr) ++ (List.range 22).map fun j => .store .d .r12 .r11 (fK + 8 * j)

/-- `out`, `d`, `digest` and `scratch` into the frame. -/
def saveArgs : List Instr :=
  [.addSp .r11 0, .store .d .r3 .r11 fOut, .store .d .r4 .r11 fD, .store .d .r5 .r11 fDigest,
    .store .d .r6 .r11 fScratch]

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block saveArgs)
  (.seq (.block (c.reduce ++ initKV))
  (.seq (c.rekeyFull 0)
  (.seq (c.rekeyFull 1)
  (.seq (.block c.initCnt)
  (.seq (.loop c.tryOne (.nonzero .d .r12))
    (.block wipe))))))

/-- `vg_ecdsa_<curve>_<hash>_sign`. -/
def sign : Prog isa :=
  .seq (.block [.mflr .r0])
    (.seq (.frame (.push .r0) (.frame (.alloc frameBytes) c.body (.free frameBytes)) (.pop .r0))
      (.block [.mtlr .r0]))

end Cfg

end VG.Impl.Ecdsa.Rfc6979.PPC64LE
