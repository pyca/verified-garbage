module

public import VerifiedGarbage.Impl.Mgf1.X86_64.Table
public import VerifiedGarbage.Impl.Weierstrass.X86_64

/-!
# Deterministic ECDSA (RFC 6979) on x86-64, with the hash function of a table

`vg_ecdsa_<curve>_sign(out = rdi, d = rsi, digest = rdx, digest_len = rcx,
scratch = r8, hash = r9) -> eax` (`signT`), for a curve of `Q`-byte scalars
in `w` words: RFC 6979 §3.2 with HMAC over the hash function of the table
`hash` of the interface `Hash` (`Spec/HashTable.lean`), whose streaming
`init`, `update` and `finalize` (its words 0 to 2) it calls indirectly
(`tcall`), and each candidate tried by calling `core`, the signature with a
given `k` (`vg_ecdsa_<curve>_sign_k`), which reads `Q` bytes of the digest
and of `k`, and takes the digest's leftmost `qlen` bits (`bits2int`, a right
shift by `sh = 8 Q - qlen` bits).

Which table `hash` is, is public (`Abi.withTables`), and so is the hash
function's index in `Mgf1.hashes`, its word 3: `signT` chooses by it
(`byIdx`, comparisons with each index of `idxs`) the code for that hash
function's digest length `D` and block size `B` (`shapeOf`), `sign` of a
`Cfg`, in which both are constants. Everything below is that code.

HMAC (`hmac`) is computed from the table's streaming functions: the key `K`
(`D` bytes, in the frame) padded to a block and XORed with `ipad` (`padBlk`,
a 32-bit word at a time, into `scratch + sPad`), the inner state set by
`init` and updated with it, the same with `opad` for the outer state
(`hinit`); the inner state updated with the data (`hupd`); then the inner
state finalized into `scratch + sTmp`, the outer one updated with that
digest and finalized there too, and its first `D` bytes copied to the MAC's
place in the frame (`hfin`).

Two kinds of curve and hash function:

* `Q ≤ D` (and `qlen = 8 Q`, the scalars' words full or the top one of four
  bytes: P-192, P-224, P-256 and P-384, and brainpoolP512r1 with SHA-512):
  one `V` makes a candidate, its leftmost `Q` bytes; `bits2octets` is a
  conditional subtraction of `n` from the digest's leftmost `Q` bytes
  (`reduce`); and `core` reads the digest and `V` in place.
* `D < Q` (`wide`): `m` `V`s make a candidate `T` (`blocks`), above the
  frame's pointers at `fT`, of which `core` reads the first `Q` bytes,
  shifted right in place by `sh` bits; the digest's integer is below `n`, so
  `h = bits2octets(digest)` is `Q - D` zero bytes then the digest (`hPrep`,
  at `fX`); and `core` reads `h`, or, if `sh ≠ 0` (P-521), the digest's
  integer shifted left by `sh` bits (`xPrep`, at `fXc`: `Q - D - 1` zero
  bytes, the digest and a zero byte, shifted right by `8 - sh` bits). The
  shifts are through the words at `scratch + sSlot` (`conv`).

Everything runs in one stack frame of `28 + extra` words, pushed from `r9`
(the table, `fTab`), `extra` copies of `rax` (34 if `wide`; 8 if `hHigh`),
`rdi`, `rsi`, `rdx`, `rcx` (`scratch`, moved from `r8`) and 23 copies of
`rax`: from `rsp`, `K` and `V` (64 bytes each, of which the first `D` are
used), `h` (`bits2octets`, in 48 bytes, unless `wide` or `hHigh`), the
number of candidates left, then `scratch`, `digest`, `d` and `out`, and, if
`wide`, `h`, the digest for `core` and `T` (72, 72 and 128 bytes), or, if
`hHigh` (64-byte scalars, as brainpoolP512r1's), `h` in 64 bytes; then the
table's address. The calls use only `scratch`, which `core` overwrites
entirely, and the stack below the frame; `K`, `V`, `h` and the words above
the pointers are cleared before the frame is popped. In `scratch`: HMAC's
inner and outer streaming states, the working space of the streaming
functions, the padded key and the inner digest, the message of steps d, f
and h.3, the words of a shift, and a copy of the states for the key `K`.

1. `h = bits2octets(digest)`: unless `wide`, the leftmost `Q` bytes, minus
   `n` if they are at least `n` (a conditional subtraction, as
   `2^(8 Q) < 2n`), a word at a time through memory: the words of the digest
   to `V`'s place, those of the difference to `K`'s (before steps b and c set
   them), and the one the borrow selects, big-endian, to `h` (a top word of
   four bytes by 32-bit loads, and stored ending at `h`'s fourth byte, its
   zero bytes in `V`'s place, which step b then sets). If `wide`, `hPrep`
   and `xPrep`.
2. Steps b to g: `V = 0x01…`, `K = 0x00…`, `K = HMAC_K(V ‖ 0x00 ‖ d ‖ h)`,
   `V = HMAC_K(V)`, `K = HMAC_K(V ‖ 0x01 ‖ d ‖ h)`, `V = HMAC_K(V)`.
3. At most `tries` times: `V = HMAC_K(V)` (`m` times, each copied to `T`, if
   `wide`), the candidate `k`, and `core(out, d, digest, k, scratch)`; if it
   failed and candidates are left, `K = HMAC_K(V ‖ 0x00)`, `V = HMAC_K(V)`
   and again. Whether to go on is computed without branches, so that the
   code branches only on it: the number of candidates tried is all it
   reveals.

`core` writes the signature or zeros to `out`, and its return value is ours.

A block addresses memory only at `rsp`, at `rsp` plus a constant, or at a
pointer an earlier block loaded from the frame (`digestPtr`, `msgPtrs`,
`scrPtr`, the table's address in `tcall`), never one it loads itself, so
that the taint analysis of each block knows its addresses are public. The
blocks that depend on the hash function depend only on `D` and `B`, so that
the taint analysis checks them for each size.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Rfc6979.X86_64

open VG.X86_64
open VG.Impl.Mgf1.X86_64.Table (Fns)

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
/-- Above the pointers: `h`, if `wide` or `hHigh`. -/
def fX : Nat := 216
/-- If `wide`: the digest for `core`, if `sh ≠ 0`. -/
def fXc : Nat := 288
/-- If `wide`: the candidate `T`. -/
def fT : Nat := 360

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
/-- A copy of HMAC's two states just after `hinit`, for the key `K`. -/
def sSave : Nat := 3072

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
  /-- The words of the curve's scalars. -/
  w : Nat
  /-- The bytes of the curve's scalars, `Q`. -/
  len : Nat := 8 * w
  /-- The bits `core` shifts its digest right by, `8 Q - qlen`. -/
  sh : Nat := 0
  /-- Whether `h` is kept above the frame's pointers, in 8 more words: for
  scalars of 64 bytes, which the 48 bytes below them do not hold (and the
  hash is no shorter). -/
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

/-- The words above the frame's pointers. -/
def extra : Nat := if c.wide then 34 else if c.hHigh then 8 else 0

/-- Where `h` is in the frame. -/
def fHo : Nat := if c.wide || c.hHigh then fX else fH

/-- Where the table's address is in the frame: its top word. -/
def fTab : Nat := fX + 8 * c.extra

/-- `d ← [rsp + o] + a`: an address in `scratch`. -/
def scr (d : Reg) (a : Nat) : List Instr :=
  [.mov d (.mem (stk fScratch)), .alu .add d (.imm (BitVec.ofNat 32 a))]

/-- `d ← rsp + o`: an address in the frame. -/
def fr (d : Reg) (o : Nat) : List Instr :=
  [.mov d (.reg .rsp), .alu .add d (.imm (BitVec.ofNat 32 o))]

/-- `scratch` in `rdi`. -/
def scrPtr : List Instr := [.mov .rdi (.mem (stk fScratch))]

/-! ## HMAC through the table -/

/-- The indirect call of the table's function `j`, among `ts`: its address
(the table's word `j`) into `r11`, then `call r11`. -/
def tcall (j : Nat) (ts : List (String × Prog isa)) : Prog isa :=
  .seq (.block [.mov .r11 (.mem (stk c.fTab)), .mov .r11 (.mem (at_ .r11 (8 * j)))])
    (Code.icalls (.callr .r11) ts)

/-- The streaming `init` of the state at `scratch + o`. -/
def initCall (o : Nat) : Prog isa := .seq (.block (scr .rdi o)) (c.tcall 0 c.f.init)

/-- The arguments of the streaming `update` of the state at `scratch + o`,
which holds `cnt` bytes, with the data (at the address `dataA` sets `rdx`
to) of `len` bytes, and the working space. -/
def updArgs (o cnt : Nat) (dataA : List Instr) (len : Nat) : List Instr :=
  scr .rdi o ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 cnt))] : List Instr) ++ dataA ++
    ([.mov32 .rcx (.imm (BitVec.ofNat 32 len))] : List Instr) ++ scr .r8 sWork

def updCall (o cnt : Nat) (dataA : List Instr) (len : Nat) : Prog isa :=
  .seq (.block (updArgs o cnt dataA len)) (c.tcall 1 c.f.upd)

/-- The arguments of the streaming `finalize` of the state at `scratch + o`,
which holds `cnt` bytes, into `scratch + sTmp`, with the working space. -/
def finArgs (o cnt : Nat) : List Instr :=
  scr .rdi o ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 cnt))] : List Instr) ++ scr .rdx sTmp ++ scr .rcx sWork

def finCall (o cnt : Nat) : Prog isa := .seq (.block (finArgs o cnt)) (c.tcall 2 c.f.fin)

/-- Word `k` of the key `K` (the frame's first `D` bytes) padded to `B`
bytes, XORed with the pad in `ecx`, to `scratch + sPad` (`scratch` in
`rdi`). -/
def padW (k : Nat) : List Instr :=
  if k < c.D / 4 then
    [.mov32 .rax (.mem (stk (fK + 4 * k))), .alu32 .xor .rax (.reg .rcx), .store32 (at_ .rdi (sPad + 4 * k)) .rax]
  else [.store32 (at_ .rdi (sPad + 4 * k)) .rcx]

/-- `K₀ ⊕ pad` (a block) at `scratch + sPad`. -/
def padBlk (x : BitVec 32) : List Instr :=
  scrPtr ++ ([.mov32 .rcx (.imm x)] : List Instr) ++ (List.range (c.B / 4)).flatMap c.padW

/-- HMAC's states for the key `K`: each set by `init`, then updated with
the padded key. -/
def hinit : Prog isa :=
  .seq (c.initCall sInner) (.seq (c.initCall sOuter)
  (.seq (.block (c.padBlk ipad32)) (.seq (c.updCall sInner 0 (scr .rdx sPad) c.B)
  (.seq (.block (c.padBlk opad32)) (c.updCall sOuter 0 (scr .rdx sPad) c.B)))))

/-- The inner state updated with `len` bytes of data at the address `dataA`
sets `rdx` to. -/
def hupd (dataA : List Instr) (len : Nat) : Prog isa := c.updCall sInner c.B dataA len

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

/-- The MAC, for `len` bytes of data, to the frame at `dst`: the inner state
finalized, the outer one updated with that digest and finalized, and its
first `D` bytes copied. -/
def hfin (len dst : Nat) : Prog isa :=
  .seq (c.finCall sInner (c.B + len)) (.seq (c.updCall sOuter c.B (scr .rdx sTmp) c.D)
  (.seq (c.finCall sOuter (c.B + c.D)) (.block (scrPtr ++ copyBytes c.D .rdi sTmp .rsp dst))))

/-- `HMAC_K(data)` into the frame at `dst`, for `len` bytes of `data` at the
address `dataA` sets `rdx` to. -/
def hmac (dataA : List Instr) (len dst : Nat) : Prog isa :=
  .seq c.hinit (.seq (c.hupd dataA len) (c.hfin len dst))

/-- The pointers the messages need: `scratch` in `rdi` and `d` in `rsi`. -/
def msgPtrs : List Instr := [.mov .rdi (.mem (stk fScratch)), .mov .rsi (.mem (stk fD))]

/-- The message `V ‖ b` (and `‖ d ‖ h` if `full`, `Q` bytes each) at
`scratch + sMsg`, for `V` of `D` bytes, with `scratch` in `rdi` and `d` in
`rsi`: `V` from the frame, `b` a byte, and `h` from the frame at `ho`. -/
def msg (Q D b : Nat) (full : Bool) (ho : Nat := fH) : List Instr :=
  copyBytes D .rsp fV .rdi sMsg ++
    ([.mov32 .rax (.imm (BitVec.ofNat 32 b)), .store8 (at_ .rdi (sMsg + D)) .rax] : List Instr) ++
    (if full then copyBytes Q .rsi 0 .rdi (sMsg + D + 1) ++ copyBytes Q .rsp ho .rdi (sMsg + D + 1 + Q) else [])

/-- The 64-bit words of `n`, least significant first. -/
def nWord (j : Nat) : BitVec 64 := BitVec.ofNat 64 (c.n >>> (64 * j))

/-- `digest` in `rsi`, and, if `wide`, `scratch` in `rdi`. -/
def digestPtr : List Instr :=
  ([.mov .rsi (.mem (stk fDigest))] : List Instr) ++ (if c.wide then [.mov .rdi (.mem (stk fScratch))] else [])

/-- HMAC's two states (384 bytes) copied from `scratch + sInner` to `scratch + sSave`
(`toSave`) or back, with `scratch` in `rdi`, through `rax`. -/
def copyStates (toSave : Bool) : List Instr :=
  if toSave then copyN 48 .rdi sInner .rdi sSave else copyN 48 .rdi sSave .rdi sInner

/-- `hmac`, its states for `K` saved after `hinit`. -/
def hmacS (dataA : List Instr) (len dst : Nat) : Prog isa :=
  .seq c.hinit (.seq (.block (scrPtr ++ copyStates true)) (.seq (c.hupd dataA len) (c.hfin len dst)))

/-- `hmac`, with the states for `K` restored from the copy rather than made by `hinit`. -/
def hmacR (dataA : List Instr) (len dst : Nat) : Prog isa :=
  .seq (.block (scrPtr ++ copyStates false)) (.seq (c.hupd dataA len) (c.hfin len dst))

/-- `V = HMAC_K(V)`, saving the states for `K`. -/
def hmacVS : Prog isa := c.hmacS (fr .rdx fV) c.D fV

/-- `V = HMAC_K(V)`, from the saved states for `K`. -/
def hmacVR : Prog isa := c.hmacR (fr .rdx fV) c.D fV

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g), the
states for the new `K` saved; for `b = 1` (step f), the states for `K` are
the copy step e saved. -/
def rekeyFull (b : Nat) : Prog isa :=
  .seq (.block msgPtrs) (.seq (.block (msg c.len c.D b true c.fHo))
    (.seq (if b = 0 then c.hmac (scr .rdx sMsg) (c.D + 2 * c.len + 1) fK
      else c.hmacR (scr .rdx sMsg) (c.D + 2 * c.len + 1) fK) c.hmacVS))

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
def rekey : Prog isa :=
  .seq (.block msgPtrs) (.seq (.block (msg c.len c.D 0 false))
    (.seq (c.hmac (scr .rdx sMsg) (c.D + 1) fK) c.hmacVS))

/-- The `Q` bytes at `rsp + o`, as a big-endian number, shifted right by `s`
bits in place, through the words at `scratch + sSlot` (with `scratch` in
`rdi`). -/
def conv (o s : Nat) : List Instr :=
  fr .rsi o ++ Impl.Weierstrass.X86_64.loadBytes c.len c.w sSlot .rsi ++
    Impl.Weierstrass.X86_64.shrWords c.w sSlot s ++ ([.movImm64 .rcx (BitVec.allOnes 64)] : List Instr) ++
    Impl.Weierstrass.X86_64.storeBytes c.len c.w .rsp o sSlot

/-- Nine zero words at `rsp + o`. -/
def zero9 (o : Nat) : List Instr :=
  ([.alu32 .xor .rax (.reg .rax)] : List Instr) ++ (List.range 9).map fun j => .store (stk (o + 8 * j)) .rax

/-- If `wide`: `h`, `Q - D` zero bytes then the digest (at `rsi`), at `fX`. -/
def hPrep : List Instr := zero9 fX ++ copyBytes c.D .rsi 0 .rsp (fX + c.len - c.D)

/-- If `wide` and `sh ≠ 0`: the digest for `core`, `Q - D - 1` zero bytes,
the digest (at `rsi`) and a zero byte, shifted right by `8 - sh` bits: the
digest's integer shifted left by `sh` bits, at `fXc`. -/
def xPrep : List Instr :=
  if c.sh = 0 then [] else
    zero9 fXc ++ copyBytes c.D .rsi 0 .rsp (fXc + c.len - c.D - 1) ++ c.conv fXc (8 - c.sh)

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

/-- Where `core` reads the digest, if `wide`: `h`, or the digest shifted
left by `sh` bits. -/
def fDg : Nat := if c.sh = 0 then fX else fXc

/-- `core(out, d, digest, k, scratch)`: `k = V`, or, if `wide`, the digest
and the candidate above the pointers. -/
def coreArgs : List Instr :=
  ([.mov .rdi (.mem (stk fOut)), .mov .rsi (.mem (stk fD))] : List Instr) ++
    (if c.wide then fr .rdx c.fDg ++ fr .rcx fT else .mov .rdx (.mem (stk fDigest)) :: fr .rcx fV) ++
    ([.mov .r8 (.mem (stk fScratch))] : List Instr)

/-- If `wide`: `V`'s `D` bytes to `T + j D`. -/
def keepV (j : Nat) : List Instr := copyBytes c.D .rsp fV .rsp (fT + j * c.D)

/-- If `wide`: `V = HMAC_K(V)` and its `D` bytes to `T + j D`, for each
`j < k`. -/
def candW : Nat → Prog isa
  | 0 => .block []
  | k + 1 => .seq (candW k) (.seq c.hmacVR (.block (c.keepV k)))

/-- If `wide` and `sh ≠ 0`: `T`'s first `Q` bytes shifted right by `sh` bits. -/
def candTop : List Instr := if c.sh = 0 then [] else scrPtr ++ c.conv fT c.sh

/-- The candidate: `V = HMAC_K(V)`, which is `k`; or, if `wide`, the
leftmost `Q` bytes of `m` successive `V = HMAC_K(V)`, shifted right by `sh`
bits. -/
def cand : Prog isa :=
  if c.wide then .seq (c.candW c.m) (.block c.candTop) else c.hmacVR

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

/-- `K`, `V` and `h` cleared, and the words above the pointers (`rax`, the
result, kept). -/
def wipe : List Instr :=
  ([.alu32 .xor .rcx (.reg .rcx)] : List Instr) ++ (List.range 22).map (fun j => .store (stk (8 * j)) .rcx) ++
    (List.range c.extra).map fun j => .store (stk (fX + 8 * j)) .rcx

/-- `h` (and, if `wide`, the digest for `core`), then `V = 0x01…`, `K = 0x00…`. -/
def prep : List Instr := (if c.wide then c.hPrep ++ c.xPrep else c.reduce) ++ initKV

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block c.digestPtr)
  (.seq (.block c.prep)
  (.seq (c.rekeyFull 0)
  (.seq (c.rekeyFull 1)
  (.seq (.block c.initCnt)
  (.seq (.loop c.tryOne .ne)
    (.block c.wipe))))))

/-- The registers the frame's push stores. -/
def pushRs : List Reg :=
  .r9 :: (List.replicate c.extra .rax ++ [.rdi, .rsi, .rdx, .rcx] ++ List.replicate 23 .rax)

/-- The signature for the hash function of this size, with `scratch` in
`rcx` and the table in `r9`. -/
def sign : Prog isa := .frame (.push c.pushRs) c.body (.pop .rcx (28 + c.extra))

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

/-- `b i` for the index `i` in `r11`, by comparisons with each of `is`: the
last is taken for every other value. -/
def byIdx (b : Nat → Prog isa) : List Nat → Prog isa
  | [] => .block []
  | [i] => b i
  | i :: is => .seq (.block [.alu .cmp .r11 (.imm (BitVec.ofNat 32 i))]) (.ite .e (b i) (byIdx b is))

/-- `scratch` to `rcx`, and the hash function's index (the table's word 3)
to `r11`. -/
def entry : List Instr := [.mov .rcx (.reg .r8), .mov .r11 (.mem (at_ .r9 24))]

/-- `vg_ecdsa_<curve>_sign`: the signature with the code `cfg i` for the
hash function of index `i` of the table `hash`. -/
def signT (cfg : Nat → Cfg) : Prog isa :=
  .seq (.block entry) (byIdx (fun i => (cfg i).sign) idxs)

end VG.Impl.Ecdsa.Rfc6979.X86_64
