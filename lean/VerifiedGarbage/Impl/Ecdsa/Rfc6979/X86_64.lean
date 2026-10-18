module

public import VerifiedGarbage.Impl.Mgf1.X86_64
public import VerifiedGarbage.Impl.Dispatch.X86_64
public import VerifiedGarbage.Impl.Weierstrass.X86_64

/-!
# Deterministic ECDSA (RFC 6979) on x86-64

`vg_ecdsa_<curve>_rfc6979_sign(out = rdi, d = rsi, digest = rdx,
digest_len = rcx, scratch = r8, hash = r9, hash_fns = [rsp + 8]) -> eax`:
RFC 6979 §3.2 over a curve of `Q`-byte scalars in `w` words, with HMAC over
the hash function `hash` names, whose streaming `init`, `update` and
`finalize` are the three addresses in the table `hash_fns`
(`Spec/HashFns.lean`). `entry` and `entryFns` move `scratch` to `rcx`, the
three addresses to `r9`, `r10` and `r11`, and `hash` to `rax`, and the code
dispatches on `hash` (`Dispatch.X86_64.chain`, a public selector) to `sign`
of the configuration of that hash function (`Cfg.ofCurve`): its output of
`D` bytes and its block of `B`, a multiple of 4 from 20 to 64 and 64 or 128.

`sign` is one stack frame of 48 words, pushed from 18 copies of `rax`, the
three addresses (`r11`, `r10`, `r9`), `rdi`, `rsi`, `rdx`, `rcx` and 23
copies of `rax`: from `rsp`, `K` and `V` (64 bytes each, of which the first
`D` are used), `h` (`bits2octets`, in 48 bytes, unless `hHigh`), the number
of candidates left, then `scratch`, `digest`, `d` and `out`, the addresses
of `init`, `update` and `finalize`, and 18 words above them: the digest for
`core` and the candidate (72 bytes each) if the scalars are longer than the
hash (`wide`), or `h` in 64 bytes if `hHigh` (64-byte scalars, as
brainpoolP512r1's, with a hash at least as long). The calls use the 24
bytes below the frame (a streaming function's return address and the 8
bytes it may use below it; `core`'s return address). In `scratch`: HMAC's
inner and outer streaming states, the working space of `update` and
`finalize` (each at the size SHA-512's need), the block `K ⊕ pad`, the inner
hash, the message of steps d, f and h.3, and the words of a conversion.

Each HMAC (`hmac`) sets the inner state to `init` and `update` with
`K ⊕ ipad` (`keyed`, the key `K` of `D` bytes padded with zeros to a block),
the outer to `K ⊕ opad`, `update`s the inner one with the message, and
`finalize`s it to the inner hash, which the outer one then `update`s with and
`finalize`s to the frame.

1. `h = bits2octets(digest)`. Unless `wide` (`Q ≤ D`): the leftmost `Q`
   bytes, minus `n` if they are at least `n` (a conditional subtraction, as
   `2^(8 Q) < 2n`), a word at a time through memory: the words of the digest
   to `V`'s place, those of the difference to `K`'s (before steps b and c set
   them), and the one the borrow selects, big-endian, to `h` (a top word of
   four bytes by 32-bit loads, and stored ending at `h`'s fourth byte, its
   zero bytes in `V`'s place, which step b then sets). If `wide`, the
   digest's integer is below `n`, so `h` is `Q - D` zero bytes and the
   digest, which the messages take from `digest`; and the digest for `core`
   is made instead (`coreDigest`): the digest's integer shifted left by `sh`
   bits, in `Q` bytes, the digest at `zPre` zero bytes and followed by
   `zPost`, shifted right by `8 zPost - sh` bits if `sh ≠ 0`.
2. Steps b to g: `V = 0x01…`, `K = 0x00…`, `K = HMAC_K(V ‖ 0x00 ‖ d ‖ h)`,
   `V = HMAC_K(V)`, `K = HMAC_K(V ‖ 0x01 ‖ d ‖ h)`, `V = HMAC_K(V)`.
3. At most `tries` times: the candidate `k` (`cand`): `V = HMAC_K(V)`, or,
   if `wide`, `blocks` times `V = HMAC_K(V)`, each `V` after the last in the
   candidate's place, then the candidate's `Q` bytes shifted right by `sh`
   bits if `sh ≠ 0`; then `core(out, d, digest, k, scratch)`; if it failed
   and candidates are left, `K = HMAC_K(V ‖ 0x00)`, `V = HMAC_K(V)` and
   again. Whether to go on is computed without branches, so that the code
   branches only on it: the number of candidates tried is all it reveals.

`core` writes the signature or zeros to `out`, and its return value is ours.

A block addresses memory only at `rsp`, at `rsp` plus a constant, or at a
pointer an earlier block loaded from the frame (`digestPtr`, `msgPtrs`,
`scrPtr`), never one it loads itself, so that the taint analysis of each
block knows its addresses are public. Each call of a streaming function is
an indirect call (`Code.icall`) of the address in its slot, loaded into
`r11` (`Impl.Mgf1.X86_64.initF`, …).
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Rfc6979.X86_64

open VG.X86_64
open VG.Impl.Mgf1.X86_64 (initF updF finF)

/-- `[rsp + d]`, in the frame. -/
def stk (d : Nat) : MemOp := { base := .rsp, disp := d }

/-- `[b + d]`. -/
def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-! Where things are in the frame. -/
def fK : Nat := 0
def fV : Nat := 64
def fH : Nat := 128
def fCnt : Nat := 176
def fScratch : Nat := 184
def fDigest : Nat := 192
def fD : Nat := 200
def fOut : Nat := 208
/-- The addresses of `init`, `update` and `finalize`, in this order. -/
def fFn : Nat := 216
/-- Above the addresses: the digest for `core` if `wide`, or `h` if `hHigh`. -/
def fX : Nat := 240
/-- Above the digest for `core`: the candidate, if `wide`. -/
def fKb : Nat := 312

/-! Where things are in `scratch`. -/
def sInner : Nat := 0
def sOuter : Nat := 192
def sWork : Nat := 384
/-- The block `K ⊕ pad`. -/
def sPad : Nat := 1792
/-- The inner hash. -/
def sTmp : Nat := 1920
def sMsg : Nat := 2256
/-- The words of a conversion. -/
def sSlot : Nat := 2560

/-- `ipad` and `opad` (FIPS 198-1 §3), in each byte of a 32-bit word. -/
def ipadW : BitVec 32 := 0x36363636
def opadW : BitVec 32 := 0x5c5c5c5c

/-- The curve, for the code: `vg_ecdsa_<curve>_sign`, and the sizes of its
scalars. -/
structure Curve where
  /-- The words of the curve's scalars. -/
  w : Nat
  /-- The bytes of the curve's scalars, `Q`. -/
  len : Nat := 8 * w
  /-- The bits of the order of the base point, `qlen`. -/
  nBits : Nat := 8 * len
  /-- The bits `core` shifts its digest right by, `8 Q - qlen`. -/
  sh : Nat := 0
  /-- The order of the curve's base point. -/
  n : Nat
  /-- The most candidates to try. -/
  tries : Nat
  /-- The signature with a given `k`, and its name. -/
  coreN : String
  coreC : Prog isa

/-- What the code needs of a curve and a hash function. -/
structure Cfg where
  /-- The bytes of the hash function's output and of its block. -/
  D : Nat
  B : Nat
  /-- The words of the curve's scalars. -/
  w : Nat
  /-- The bytes of the curve's scalars, `Q`. -/
  len : Nat := 8 * w
  /-- Whether the hash is shorter than the scalars (`blocks` `V`s make a candidate). -/
  wide : Bool := false
  /-- If `wide`, the `V`s that make a candidate: `⌈qlen / (8 D)⌉`. -/
  blocks : Nat := 1
  /-- The bits `core` shifts its digest right by, `8 Q - qlen`. -/
  sh : Nat := 0
  /-- Whether `h` is kept above the frame's addresses: for scalars of 64
  bytes, which the 48 bytes below them do not hold. -/
  hHigh : Bool := false
  /-- The order of the curve's base point. -/
  n : Nat
  /-- The most candidates to try. -/
  tries : Nat
  /-- The signature with a given `k`, and its name. -/
  coreN : String
  coreC : Prog isa

/-- The output and block sizes of the hash function `hash` names
(`Spec.HashId`, SHA-1 and the SHA-2 functions). -/
def sizesOf : Nat → Nat × Nat
  | 1 => (20, 64) | 2 => (28, 64) | 3 => (32, 64) | 4 => (48, 128) | 5 => (64, 128)
  | 6 => (28, 128) | 7 => (32, 128)
  | _ => (32, 64)

/-- The configuration for the curve `E` and the hash function `hash` names. -/
def Cfg.ofCurve (E : Curve) (hash : Nat) : Cfg where
  D := (sizesOf hash).1
  B := (sizesOf hash).2
  w := E.w
  len := E.len
  wide := decide ((sizesOf hash).1 < E.len)
  blocks := (E.nBits + 8 * (sizesOf hash).1 - 1) / (8 * (sizesOf hash).1)
  sh := E.sh
  hHigh := decide (E.len = 64)
  n := E.n
  tries := E.tries
  coreN := E.coreN
  coreC := E.coreC

namespace Cfg

variable (c : Cfg)

/-- Where `h` is in the frame. -/
def fHo : Nat := if c.hHigh then fX else fH

/-- The zero bytes before and after the digest in the digest for `core`, if `wide`. -/
def zPost : Nat := (c.sh + 7) / 8
def zPre : Nat := c.len - c.D - c.zPost

/-- The bytes of `V` number `i` of a candidate kept, if `wide`: all of it,
and enough of the last to make `Q` bytes (at least 8). -/
def chunk (i : Nat) : Nat := if i + 1 < c.blocks then c.D else max 8 (c.len - c.D * (c.blocks - 1))

/-- `d ← [rsp + o] + a`: an address in `scratch`. -/
def scr (d : Reg) (a : Nat) : List Instr :=
  [.mov d (.mem (stk fScratch)), .alu .add d (.imm (BitVec.ofNat 32 a))]

/-- `d ← rsp + o`: an address in the frame. -/
def fr (d : Reg) (o : Nat) : List Instr :=
  [.mov d (.reg .rsp), .alu .add d (.imm (BitVec.ofNat 32 o))]

/-- The 32-bit word `j` of `K ⊕ pad` (`pad` in each byte), `K` of `D` bytes
(a multiple of 4) padded with zeros, to `scratch + sPad` (`scratch` in
`rdi`): `K`'s word XORed with `pad`, or `pad`. -/
def padWord (D : Nat) (pad : BitVec 32) (j : Nat) : List Instr :=
  if 4 * (j + 1) ≤ D then
    [.mov32 .rax (.mem (stk (fK + 4 * j))), .alu32 .xor .rax (.imm pad), .store32 (at_ .rdi (sPad + 4 * j)) .rax]
  else [.mov32 .rax (.imm pad), .store32 (at_ .rdi (sPad + 4 * j)) .rax]

/-- The block `K ⊕ pad` of `B` bytes at `scratch + sPad`, with `scratch` in `rdi`. -/
def padBlock (D B : Nat) (pad : BitVec 32) : List Instr := (List.range (B / 4)).flatMap (padWord D pad)

/-- `scratch` in `rdi`. -/
def scrPtr : List Instr := [.mov .rdi (.mem (stk fScratch))]

/-- The arguments of `update` of the state at `scratch + st`, after `cnt`
bytes, with the `len` bytes at the address `dataA` sets `rdx` to, and the
working space. -/
def updArgs (st cnt : Nat) (dataA : List Instr) (len : Nat) : List Instr :=
  scr .rdi st ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 cnt))] : List Instr) ++ dataA ++
    ([.mov32 .rcx (.imm (BitVec.ofNat 32 len))] : List Instr) ++ scr .r8 sWork

/-- The arguments of `finalize` of the state at `scratch + st`, after `cnt`
bytes, to the address `outA` sets `rdx` to, with the working space. -/
def finArgs (st cnt : Nat) (outA : List Instr) : List Instr :=
  scr .rdi st ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 cnt))] : List Instr) ++ outA ++ scr .rcx sWork

/-- The state at `scratch + st` set to `init`, then `update` with `K ⊕ pad`
(`scratch` loaded into `rdi` by a block of its own, as the block that
writes the pad through it may not load the address it writes). -/
def keyed (st : Nat) (pad : BitVec 32) : Prog isa :=
  .seq (.block (scr .rdi st))
  (.seq (initF fFn)
  (.seq (.block scrPtr)
  (.seq (.block (padBlock c.D c.B pad ++ updArgs st 0 (scr .rdx sPad) c.B))
    (updF fFn))))

/-- `HMAC_K(data)` into the frame at `dst`, for `len` bytes of `data` at the
address `dataA` sets `rdx` to: the keyed inner and outer states, the inner
`update` with the data and `finalize` to the inner hash, and the outer
`update` with it and `finalize` to `dst`. -/
def hmac (dataA : List Instr) (len dst : Nat) : Prog isa :=
  .seq (c.keyed sInner ipadW)
  (.seq (c.keyed sOuter opadW)
  (.seq (.block (updArgs sInner c.B dataA len))
  (.seq (updF fFn)
  (.seq (.block (finArgs sInner (c.B + len) (scr .rdx sTmp)))
  (.seq (finF fFn)
  (.seq (.block (updArgs sOuter c.B (scr .rdx sTmp) c.D))
  (.seq (updF fFn)
  (.seq (.block (finArgs sOuter (c.B + c.D) (fr .rdx dst)))
    (finF fFn)))))))))

/-- `V = HMAC_K(V)`. -/
def hmacV : Prog isa := c.hmac (fr .rdx fV) c.D fV

/-- The `8 k` bytes at `[src + so]` to `[dst + d]`, a word at a time through `rax`. -/
def copyN (k : Nat) (src : Reg) (so : Nat) (dst : Reg) (d : Nat) : List Instr :=
  (List.range k).flatMap fun j =>
    [.mov .rax (.mem (at_ src (so + 8 * j))), .store (at_ dst (d + 8 * j)) .rax]

/-- The `len` bytes at `[src + so]` to `[dst + d]` (`8 ≤ len`), a word at a
time through `rax`: `copyN` for the whole words, then the last eight bytes
again if `len` is not a multiple of 8. -/
def copyBytes (len : Nat) (src : Reg) (so : Nat) (dst : Reg) (d : Nat) : List Instr :=
  copyN (len / 8) src so dst d ++
    (if len % 8 = 0 then [] else
      [.mov .rax (.mem (at_ src (so + len - 8))), .store (at_ dst (d + len - 8)) .rax])

/-- `k` zero words at `[dst + d]`, `rax` zero. -/
def zeroN (k : Nat) (dst : Reg) (d : Nat) : List Instr :=
  (List.range k).map fun j => .store (at_ dst (d + 8 * j)) .rax

/-- The pointers the messages need: `scratch` in `rdi`, `d` in `rsi`, and,
if `wide`, `digest` in `rdx` (loaded first, so that every address the
message's block computes is from them or `rsp`). -/
def msgPtrs (wide : Bool) : List Instr :=
  ([.mov .rdi (.mem (stk fScratch)), .mov .rsi (.mem (stk fD))] : List Instr) ++
    (if wide then [.mov .rdx (.mem (stk fDigest))] else [])

/-- The message `V ‖ b` (and `‖ d ‖ h` if `full`, `Q` bytes each) at
`scratch + sMsg`, for `V` of `D` bytes, with `scratch` in `rdi`, `d` in
`rsi` (and, if `wide`, `digest` in `rdx`): `V` from the frame, `b` a byte,
and `h` from the frame at `ho`, or, if `wide`, `Q - D` zero bytes (zero
words, which the digest's words then overwrite but for them) and the digest. -/
def msg (Q D b : Nat) (full wide : Bool) (ho : Nat := fH) : List Instr :=
  copyBytes D .rsp fV .rdi sMsg ++
    ([.mov32 .rax (.imm (BitVec.ofNat 32 b)), .store8 (at_ .rdi (sMsg + D)) .rax] : List Instr) ++
    (if full then
      (if wide then
        copyBytes Q .rsi 0 .rdi (sMsg + D + 1) ++ ([.alu32 .xor .rax (.reg .rax)] : List Instr) ++
          zeroN ((Q - D + 7) / 8) .rdi (sMsg + D + 1 + Q) ++ copyBytes D .rdx 0 .rdi (sMsg + 1 + 2 * Q)
      else copyBytes Q .rsi 0 .rdi (sMsg + D + 1) ++ copyBytes Q .rsp ho .rdi (sMsg + D + 1 + Q))
    else [])

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
def rekeyFull (b : Nat) : Prog isa :=
  .seq (.block (msgPtrs c.wide)) (.seq (.block (msg c.len c.D b true c.wide c.fHo))
    (.seq (c.hmac (scr .rdx sMsg) (c.D + 2 * c.len + 1) fK) c.hmacV))

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
def rekey : Prog isa :=
  .seq (.block (msgPtrs false)) (.seq (.block (msg c.len c.D 0 false false))
    (.seq (c.hmac (scr .rdx sMsg) (c.D + 1) fK) c.hmacV))

/-- The 64-bit words of `n`, least significant first. -/
def nWord (j : Nat) : BitVec 64 := BitVec.ofNat 64 (c.n >>> (64 * j))

/-- `digest` in `rsi`, and, if `wide`, `scratch` in `rdi`. -/
def digestPtr : List Instr :=
  ([.mov .rsi (.mem (stk fDigest))] : List Instr) ++ (if c.wide then [.mov .rdi (.mem (stk fScratch))] else [])

/-- The `Q` bytes at `rsp + o`, as a big-endian number, shifted right by `s`
bits in place, through the words at `scratch + sSlot` (with `scratch` in
`rdi`). -/
def conv (o s : Nat) : List Instr :=
  fr .rsi o ++ Impl.Weierstrass.X86_64.loadBytes c.len c.w sSlot .rsi ++
    Impl.Weierstrass.X86_64.shrWords c.w sSlot s ++ ([.movImm64 .rcx (BitVec.allOnes 64)] : List Instr) ++
    Impl.Weierstrass.X86_64.storeBytes c.len c.w .rsp o sSlot

/-- If `wide`: the digest for `core`, the digest's integer shifted left by
`sh` bits in `Q` bytes: zero words, the digest (at `rsi`) after `zPre` zero
bytes, and, if `sh ≠ 0`, the `Q` bytes shifted right by `8 zPost - sh` bits. -/
def coreDigest : List Instr :=
  ([.alu32 .xor .rax (.reg .rax)] : List Instr) ++ zeroN ((c.len + 7) / 8) .rsp fX ++
    copyBytes c.D .rsi 0 .rsp (fX + c.zPre) ++ (if c.sh = 0 then [] else c.conv fX (8 * c.zPost - c.sh))

/-- Word `j` of the `Q`-byte number at `digest` (in `rsi`), least
significant first, in `rax`: the byte reversal of the word at
`digest + Q - 8 (j + 1)`, or, for a top word of four bytes (`Q % 8 = 4`),
of the first four, zero-extended. Neither changes the flags, which carry
the borrow from one word to the next. -/
def loadWord (j : Nat) : List Instr :=
  if 8 * (j + 1) ≤ c.len then [.mov .rax (.mem (at_ .rsi (c.len - 8 * (j + 1)))), .bswap .rax]
  else if c.len ≤ 8 * j then [.mov .rax (.imm 0)]
  else [.mov32 .rax (.mem (at_ .rsi 0)), .bswap32 .rax]

/-- Word `j` of the number at `digest` (in `rsi`), least significant first,
to `V`'s place, and word `j` of it minus `n` (with the borrow of the words
before) to `K`'s: `rax` and `rdx` change, and the borrow is the carry flag. -/
def subWord (j : Nat) : List Instr :=
  c.loadWord j ++ ([.store (stk (fV + 8 * j)) .rax,
    .movImm64 .rdx (c.nWord j), .alu (if j = 0 then .sub else .sbb) .rax (.reg .rdx),
    .store (stk (fK + 8 * j)) .rax] : List Instr)

/-- Word `j` of the result, by the mask `rdx` (all ones if subtracting `n`
borrowed): the number's word if so, the difference's if not, big-endian to
`h + Q - 8 (j + 1)`. A top word of fewer bytes is stored below `h`, in `V`'s
place (which `initKV` then sets), its zero bytes there and the rest `h`'s
first bytes. -/
def selWord (j : Nat) : List Instr :=
  [.mov .rax (.mem (stk (fV + 8 * j))), .mov .rcx (.mem (stk (fK + 8 * j))), .alu .xor .rax (.reg .rcx),
    .alu .and .rax (.reg .rdx), .alu .xor .rax (.reg .rcx), .bswap .rax,
    .store (stk (c.fHo + c.len - 8 * (j + 1))) .rax]

/-- `h`: the `Q` bytes at `digest` (in `rsi`), as a big-endian number,
minus `n` if that does not borrow, big-endian into the frame's `Q` bytes at
`h`. -/
def reduce : List Instr :=
  (List.range c.w).flatMap c.subWord ++ ([.alu .sbb .rdx (.reg .rdx)] : List Instr) ++ (List.range c.w).flatMap c.selWord

/-- `V = 0x01…`, `K = 0x00…`, all 64 bytes of each. -/
def initKV : List Instr :=
  ([.movImm64 .rax (BitVec.ofNat 64 0x0101010101010101), .alu32 .xor .rcx (.reg .rcx)] : List Instr) ++
    (List.range 8).flatMap fun j => [.store (stk (fV + 8 * j)) .rax, .store (stk (fK + 8 * j)) .rcx]

/-- The candidates left. -/
def initCnt : List Instr :=
  [.mov32 .rax (.imm (BitVec.ofNat 32 c.tries)), .store (stk fCnt) .rax]

/-- `core(out, d, digest, k, scratch)`: `k = V`, or, if `wide`, the digest
and the candidate above the addresses. -/
def coreArgs : List Instr :=
  ([.mov .rdi (.mem (stk fOut)), .mov .rsi (.mem (stk fD))] : List Instr) ++
    (if c.wide then fr .rdx fX ++ fr .rcx fKb else .mov .rdx (.mem (stk fDigest)) :: fr .rcx fV) ++
    ([.mov .r8 (.mem (stk fScratch))] : List Instr)

/-- If `wide`: `V = HMAC_K(V)`, and its first `chunk i` bytes to the
candidate's place after the `i` `V`s before it. -/
def candStep (i : Nat) : Prog isa :=
  .seq c.hmacV (.block (copyBytes (c.chunk i) .rsp fV .rsp (fKb + c.D * i)))

/-- The steps from `i` of the `k` left. -/
def candSteps : Nat → Nat → Prog isa
  | _, 0 => .block []
  | i, 1 => c.candStep i
  | i, k + 1 => .seq (c.candStep i) (candSteps (i + 1) k)

/-- The candidate: `V = HMAC_K(V)`, which is `k`; or, if `wide`, the
leftmost `Q` bytes of `blocks` successive `V = HMAC_K(V)`, shifted right by
`sh` bits if `sh ≠ 0`. -/
def cand : Prog isa :=
  if c.wide then
    if c.sh = 0 then c.candSteps 0 c.blocks
    else .seq (c.candSteps 0 c.blocks) (.seq (.block scrPtr) (.block (c.conv fKb c.sh)))
  else c.hmacV

/-- One candidate fewer, and `rdx ≠ 0` (and `ZF` clear) iff the signature
failed (`eax = 0`) and candidates are left: `rdx = -(eax < 1) & (count - 1)`. -/
def goOn : List Instr :=
  [.mov .rcx (.mem (stk fCnt)), .alu .sub .rcx (.imm 1), .store (stk fCnt) .rcx,
    .alu32 .cmp .rax (.imm 1), .alu .sbb .rdx (.reg .rdx), .alu .and .rdx (.reg .rcx),
    .alu .test .rdx (.reg .rdx)]

/-- `ZF` clear: go on. -/
def again : List Instr := [.mov32 .rdx (.imm 1), .alu .test .rdx (.reg .rdx)]

/-- `ZF` set: stop. -/
def stop : List Instr := [.alu32 .xor .rdx (.reg .rdx)]

/-- One candidate: `cand`, `core` with it, then, if it failed
and candidates are left, step h.3. -/
def tryOne : Prog isa :=
  .seq c.cand
  (.seq (.block c.coreArgs)
  (.seq (.call c.coreN c.coreC)
  (.seq (.block goOn)
    (.ite .ne (.seq c.rekey (.block again)) (.block stop)))))

/-- The words above the frame's addresses. -/
def extra : Nat := 18

/-- `K`, `V` and `h` cleared, and the words above the addresses (`rax`, the
result, kept). -/
def wipe : List Instr :=
  ([.alu32 .xor .rcx (.reg .rcx)] : List Instr) ++ (List.range 22).map (fun j => .store (stk (8 * j)) .rcx) ++
    (List.range extra).map fun j => .store (stk (fX + 8 * j)) .rcx

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block c.digestPtr)
  (.seq (.block ((if c.wide then c.coreDigest else c.reduce) ++ initKV))
  (.seq (c.rekeyFull 0)
  (.seq (c.rekeyFull 1)
  (.seq (.block c.initCnt)
  (.seq (.loop c.tryOne .ne)
    (.block wipe))))))

/-- The registers the frame's push stores. -/
def pushRs : List Reg := List.replicate extra .rax ++ [.r11, .r10, .r9, .rdi, .rsi, .rdx, .rcx] ++ List.replicate 23 .rax

/-- The signature with this configuration, from `out = rdi`, `d = rsi`,
`digest = rdx`, `scratch = rcx` and the addresses of `init`, `update` and
`finalize` in `r9`, `r10` and `r11`. -/
def sign : Prog isa := .frame (.push pushRs) c.body (.pop .rcx 48)

end Cfg

/-- `scratch` to `rcx`, the table's address (from the stack) to `r10`, and
`hash` to `rax`. -/
def entry : List Instr := [.mov .rcx (.reg .r8), .mov .r10 (.mem (at_ .rsp 8)), .mov .rax (.reg .r9)]

/-- The table's addresses to `r9`, `r10` and `r11`, through `r10` (a block of
its own, as the address it reads at is one the block before loads). -/
def entryFns : List Instr :=
  [.mov .r9 (.mem (at_ .r10 0)), .mov .r11 (.mem (at_ .r10 16)), .mov .r10 (.mem (at_ .r10 8))]

/-- The numbers of the hash functions the signer takes (`Spec.Ecdsa.Rfc6979.hashIds`). -/
def hashIds : List Nat := [1, 2, 3, 4, 5, 6, 7]

/-- `vg_ecdsa_<curve>_rfc6979_sign`: `entry` and `entryFns`, then `sign` of
the configuration of the hash function `hash` names. -/
def signAny (E : Curve) : Prog isa :=
  .seq (.block entry) (.seq (.block entryFns)
    (Dispatch.X86_64.chain (hashIds.map fun k => (k, (Cfg.ofCurve E k).sign))))

end VG.Impl.Ecdsa.Rfc6979.X86_64
