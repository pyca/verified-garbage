import VerifiedGarbage.Impl.Pbkdf2.Md.X86_64
import VerifiedGarbage.Impl.Weierstrass.X86_64

/-!
# Deterministic ECDSA (RFC 6979) on x86-64

`sign R H core (out = rdi, d = rsi, digest = rdx, scratch = rcx) -> eax`, for
a curve of `Q`-byte scalars in `w` words and a Merkle–Damgård hash function
`H` whose output is `D` bytes, a multiple of 8, at most 64: RFC 6979 §3.2,
with HMAC computed by calling `H`'s HMAC `init`, streaming `update` and HMAC
`finalize`, and each candidate tried by calling `core`, the signature with a
given `k` (`vg_ecdsa_<curve>_sign`), which reads `Q` bytes of the digest and
of `k`, and takes the digest's leftmost `qlen` bits (`bits2int`, a right
shift by `sh = 8 Q - qlen` bits).

Two kinds of curve and hash function:

* `Q = 8 w ≤ D` and `qlen = 8 Q` (P-256 and P-384, `wide = false`): one `V`
  makes a candidate, its leftmost `Q` bytes; `bits2octets` is a conditional
  subtraction of `n` from the digest's leftmost `Q` bytes; and `core` reads
  the digest and `V` in place.
* `8 D < qlen ≤ 16 D` and `Q ≤ D + 8` (P-521 with SHA-512, `wide`): two `V`s
  make a candidate, the leftmost `Q` bytes of the second's concatenation with
  the first, shifted right by `sh` bits; the digest's integer is below `n`,
  so `bits2octets` is the digest after `Q - D` zero bytes; and `core` reads
  the digest shifted left by `sh` bits, which it shifts back. The candidate
  and that digest are made in `Q` bytes above the frame's pointers, through
  words at `scratch + sSlot` (`loadBytes`, `shrWords`, `storeBytes`).

Everything runs in one stack frame of 27 words, 45 if `wide`, pushed from
(if `wide`, 18 copies of `rax`), `rdi`, `rsi`, `rdx`, `rcx` and 23 copies of
`rax`: from `rsp`, `K` and `V` (64 bytes each, of which the first `D` are
used), `h` (`bits2octets`, in 48 bytes, unless `wide`), the number of
candidates left, then `scratch`, `digest`, `d` and `out`, and, if `wide`,
the digest for `core` and the candidate (72 bytes each). The layout is the
same for every hash function. The calls use only `scratch`, which `core`
overwrites entirely, and the frame, which they cannot change; `K`, `V`, `h`
and the candidate are cleared before the frame is popped. In `scratch`:
HMAC's inner and outer streaming states, the working space of HMAC's and
`H`'s functions (each at the size SHA-512's need), and the message of steps
d, f and h.3.

1. `h = bits2octets(digest)`: unless `wide`, the leftmost `Q` bytes, minus
   `n` if they are at least `n` (a conditional subtraction, as
   `2^(8 Q) < 2n`), a word at a time through memory: the words of the digest
   to `V`'s place, those of the difference to `K`'s (before steps b and c set
   them), and the one the borrow selects, big-endian, to `h`. If `wide`, the
   digest for `core` instead: the digest then `Q - D` zero bytes, shifted
   right by `8 (Q - D) - sh` bits.
2. Steps b to g: `V = 0x01…`, `K = 0x00…`, `K = HMAC_K(V ‖ 0x00 ‖ d ‖ h)`,
   `V = HMAC_K(V)`, `K = HMAC_K(V ‖ 0x01 ‖ d ‖ h)`, `V = HMAC_K(V)`.
3. At most `tries` times: `V = HMAC_K(V)` (twice if `wide`), the candidate
   `k`, and `core(out, d, digest, k, scratch)`; if it failed and candidates
   are left, `K = HMAC_K(V ‖ 0x00)`, `V = HMAC_K(V)` and again. Whether to
   go on is computed without branches, so that the code branches only on
   it: the number of candidates tried is all it reveals.

`core` writes the signature or zeros to `out`, and its return value is ours.

A block addresses memory only at `rsp`, at `rsp` plus a constant, or at a
pointer an earlier block loaded from the frame (`digestPtr`, `msgPtrs`,
`scrPtr`), never one it loads itself, so that the taint analysis of each
block knows its addresses are public. The blocks that depend on the hash
function depend only on `D` and its block size `B` (`hmacArgs₁`,
`hmacArgs₂`, `hmacArgs₃`, `msg`), so that the taint analysis checks them
for each size.
-/

namespace VG.Impl.Ecdsa.Rfc6979.X86_64

open VG.X86_64 VG.Impl.Pbkdf2.Md.X86_64

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
/-- Above the pointers, if `wide`: the digest for `core`, and the candidate. -/
def fX : Nat := 216
def fKb : Nat := 288

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
  /-- The words of the curve's scalars. -/
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

/-- `d ← [rsp + o] + a`: an address in `scratch`. -/
def scr (d : Reg) (a : Nat) : List Instr :=
  [.mov d (.mem (stk fScratch)), .alu .add d (.imm (BitVec.ofNat 32 a))]

/-- `d ← rsp + o`: an address in the frame. -/
def fr (d : Reg) (o : Nat) : List Instr :=
  [.mov d (.reg .rsp), .alu .add d (.imm (BitVec.ofNat 32 o))]

/-- The arguments of HMAC's `init`: the states, the key `K` of `D` bytes,
the working space. -/
def hmacArgs₁ (D : Nat) : List Instr :=
  scr .rdi sInner ++ scr .rsi sOuter ++ fr .rdx fK ++ [.mov32 .rcx (.imm (BitVec.ofNat 32 D))] ++ scr .r8 sWork

/-- The arguments of the streaming `update`: the inner state, the `B` bytes
it holds, the data (at the address `dataA` sets `rdx` to) of `len` bytes,
the working space. -/
def hmacArgs₂ (B : Nat) (dataA : List Instr) (len : Nat) : List Instr :=
  scr .rdi sInner ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 B))] ++ dataA ++
    [.mov32 .rcx (.imm (BitVec.ofNat 32 len))] ++ scr .r8 sWork

/-- The arguments of HMAC's `finalize`: the states, the `B + len` bytes the
inner one holds, the MAC's place in the frame, the working space. -/
def hmacArgs₃ (B len dst : Nat) : List Instr :=
  scr .rdi sInner ++ scr .rsi sOuter ++ [.mov32 .rdx (.imm (BitVec.ofNat 32 (B + len)))] ++ fr .rcx dst ++
    scr .r8 sWork

/-- `HMAC_K(data)` into the frame at `dst`, for `len` bytes of `data` at the
address `dataA` sets `rdx` to: HMAC's `init` with the key `K`, `update` on
the inner state, and `finalize`. -/
def hmac (dataA : List Instr) (len dst : Nat) : Prog isa :=
  .seq (.block (hmacArgs₁ c.H.D))
  (.seq (.call c.H.hmacInitN c.H.hmacInit)
  (.seq (.block (hmacArgs₂ c.H.P.B dataA len))
  (.seq (.call c.H.updN c.H.updC)
  (.seq (.block (hmacArgs₃ c.H.P.B len dst))
    (.call c.H.hmacFinN c.H.hmacFin)))))

/-- `V = HMAC_K(V)`. -/
def hmacV : Prog isa := c.hmac (fr .rdx fV) c.H.D fV

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

/-- The pointers the messages need: `scratch` in `rdi`, `d` in `rsi`, and,
if `wide`, `digest` in `rdx` (loaded first, so that every address the
message's block computes is from them or `rsp`). -/
def msgPtrs (wide : Bool) : List Instr :=
  [.mov .rdi (.mem (stk fScratch)), .mov .rsi (.mem (stk fD))] ++
    (if wide then [.mov .rdx (.mem (stk fDigest))] else [])

/-- The message `V ‖ b` (and `‖ d ‖ h` if `full`, `Q` bytes each) at
`scratch + sMsg`, for `V` of `D` bytes, with `scratch` in `rdi`, `d` in
`rsi` (and, if `wide`, `digest` in `rdx`): `V` from the frame, `b` a byte,
and `h` from the frame, or, if `wide`, `Q - D` zero bytes (a zero word,
which the digest's words then overwrite but for them) and the digest. -/
def msg (Q D b : Nat) (full wide : Bool) : List Instr :=
  copyN (D / 8) .rsp fV .rdi sMsg ++
    [.mov32 .rax (.imm (BitVec.ofNat 32 b)), .store8 (at_ .rdi (sMsg + D)) .rax] ++
    (if full then
      (if wide then
        copyBytes Q .rsi 0 .rdi (sMsg + D + 1) ++
          [.alu32 .xor .rax (.reg .rax), .store (at_ .rdi (sMsg + D + 1 + Q)) .rax] ++
          copyN (D / 8) .rdx 0 .rdi (sMsg + 1 + 2 * Q)
      else copyN (Q / 8) .rsi 0 .rdi (sMsg + D + 1) ++ copyN (Q / 8) .rsp fH .rdi (sMsg + D + 1 + Q))
    else [])

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
def rekeyFull (b : Nat) : Prog isa :=
  .seq (.block (msgPtrs c.wide)) (.seq (.block (msg c.len c.H.D b true c.wide))
    (.seq (c.hmac (scr .rdx sMsg) (c.H.D + 2 * c.len + 1) fK) c.hmacV))

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
def rekey : Prog isa :=
  .seq (.block (msgPtrs false)) (.seq (.block (msg c.len c.H.D 0 false false))
    (.seq (c.hmac (scr .rdx sMsg) (c.H.D + 1) fK) c.hmacV))

/-- The 64-bit words of `n`, least significant first. -/
def nWord (j : Nat) : BitVec 64 := BitVec.ofNat 64 (c.n >>> (64 * j))

/-- `digest` in `rsi`, and, if `wide`, `scratch` in `rdi`. -/
def digestPtr : List Instr :=
  [.mov .rsi (.mem (stk fDigest))] ++ (if c.wide then [.mov .rdi (.mem (stk fScratch))] else [])

/-- `scratch` in `rdi`. -/
def scrPtr : List Instr := [.mov .rdi (.mem (stk fScratch))]

/-- The `Q` bytes at `rsp + o`, as a big-endian number, shifted right by `s`
bits in place, through the words at `scratch + sSlot` (with `scratch` in
`rdi`). -/
def conv (o s : Nat) : List Instr :=
  fr .rsi o ++ Impl.Weierstrass.X86_64.loadBytes c.len c.w sSlot .rsi ++
    Impl.Weierstrass.X86_64.shrWords c.w sSlot s ++ [.movImm64 .rcx (BitVec.allOnes 64)] ++
    Impl.Weierstrass.X86_64.storeBytes c.len c.w .rsp o sSlot

/-- If `wide`: the digest for `core`, the digest (at `rsi`) then `Q - D`
zero bytes, shifted right by `8 (Q - D) - sh` bits: the digest's integer
shifted left by `sh` bits. -/
def coreDigest : List Instr :=
  [.alu32 .xor .rax (.reg .rax), .store (stk (fX + c.len - 8)) .rax] ++
    copyN (c.H.D / 8) .rsi 0 .rsp fX ++ c.conv fX (8 * (c.len - c.H.D) - c.sh)

/-- Word `j` of the number at `digest` (in `rsi`), least significant first,
to `V`'s place, and word `j` of it minus `n` (with the borrow of the words
before) to `K`'s: `rax` and `rdx` change, and the borrow is the carry flag. -/
def subWord (j : Nat) : List Instr :=
  [.mov .rax (.mem (at_ .rsi (8 * (c.w - 1 - j)))), .bswap .rax, .store (stk (fV + 8 * j)) .rax,
    .movImm64 .rdx (c.nWord j), .alu (if j = 0 then .sub else .sbb) .rax (.reg .rdx),
    .store (stk (fK + 8 * j)) .rax]

/-- Word `j` of the result, by the mask `rdx` (all ones if subtracting `n`
borrowed): the number's word if so, the difference's if not, big-endian to
`h`. -/
def selWord (j : Nat) : List Instr :=
  [.mov .rax (.mem (stk (fV + 8 * j))), .mov .rcx (.mem (stk (fK + 8 * j))), .alu .xor .rax (.reg .rcx),
    .alu .and .rax (.reg .rdx), .alu .xor .rax (.reg .rcx), .bswap .rax,
    .store (stk (fH + 8 * (c.w - 1 - j))) .rax]

/-- `h`: the `Q` bytes at `digest` (in `rsi`), as a big-endian number,
minus `n` if that does not borrow, big-endian into the frame. -/
def reduce : List Instr :=
  (List.range c.w).flatMap c.subWord ++ [.alu .sbb .rdx (.reg .rdx)] ++ (List.range c.w).flatMap c.selWord

/-- `V = 0x01…`, `K = 0x00…`, all 64 bytes of each. -/
def initKV : List Instr :=
  [.movImm64 .rax (BitVec.ofNat 64 0x0101010101010101), .alu32 .xor .rcx (.reg .rcx)] ++
    (List.range 8).flatMap fun j => [.store (stk (fV + 8 * j)) .rax, .store (stk (fK + 8 * j)) .rcx]

/-- The candidates left. -/
def initCnt : List Instr :=
  [.mov32 .rax (.imm (BitVec.ofNat 32 c.tries)), .store (stk fCnt) .rax]

/-- `core(out, d, digest, k, scratch)`: `k = V`, or, if `wide`, the digest
and the candidate above the pointers. -/
def coreArgs : List Instr :=
  [.mov .rdi (.mem (stk fOut)), .mov .rsi (.mem (stk fD))] ++
    (if c.wide then fr .rdx fX ++ fr .rcx fKb else .mov .rdx (.mem (stk fDigest)) :: fr .rcx fV) ++
    [.mov .r8 (.mem (stk fScratch))]

/-- If `wide`: `V`'s first `D` bytes to the candidate's place. -/
def keepV : List Instr := copyN (c.H.D / 8) .rsp fV .rsp fKb

/-- If `wide`: the next eight bytes of the candidate from `V`, then the
candidate's `Q` bytes shifted right by `sh` bits. -/
def candTop : List Instr :=
  [.mov .rax (.mem (stk fV)), .store (stk (fKb + c.H.D)) .rax] ++ c.conv fKb c.sh

/-- The candidate: `V = HMAC_K(V)`, which is `k`; or, if `wide`, the
leftmost `Q` bytes of `V = HMAC_K(V)` then `V = HMAC_K(V)` again, shifted
right by `sh` bits. -/
def cand : Prog isa :=
  if c.wide then
    .seq c.hmacV (.seq (.block c.keepV) (.seq c.hmacV (.seq (.block scrPtr) (.block c.candTop))))
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

/-- The words above the frame's pointers. -/
def extra : Nat := if c.wide then 18 else 0

/-- `K`, `V` and `h` cleared, and the words above the pointers (`rax`, the
result, kept). -/
def wipe : List Instr :=
  [.alu32 .xor .rcx (.reg .rcx)] ++ (List.range 22).map (fun j => .store (stk (8 * j)) .rcx) ++
    (List.range c.extra).map fun j => .store (stk (fX + 8 * j)) .rcx

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block c.digestPtr)
  (.seq (.block ((if c.wide then c.coreDigest else c.reduce) ++ initKV))
  (.seq (c.rekeyFull 0)
  (.seq (c.rekeyFull 1)
  (.seq (.block c.initCnt)
  (.seq (.loop c.tryOne .ne)
    (.block c.wipe))))))

/-- `vg_ecdsa_<curve>_<hash>_sign`. -/
def sign : Prog isa :=
  .frame (.push (List.replicate c.extra .rax ++ [.rdi, .rsi, .rdx, .rcx] ++ List.replicate 23 .rax)) c.body
    (.pop .rcx (27 + c.extra))

end Cfg

end VG.Impl.Ecdsa.Rfc6979.X86_64
