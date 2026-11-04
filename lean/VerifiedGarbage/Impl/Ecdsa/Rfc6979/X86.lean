module

public import VerifiedGarbage.Impl.RsaOaep.X86
public import VerifiedGarbage.Impl.Weierstrass.X86

/-!
# Deterministic ECDSA (RFC 6979) on x86 (32-bit), with the hash function of a table

`vg_ecdsa_<curve>_sign(out, d, digest, digest_len, scratch, hash) -> eax`
(`signT`), every argument on the stack (cdecl), as on x86-64
(`Impl/Ecdsa/Rfc6979/X86_64.lean`): for a curve of `Q`-byte scalars, RFC 6979
§3.2 with HMAC over the hash function of the table `hash` of the interface
`Hash` (`Spec/HashTable.lean`), whose streaming `init`, `update` and
`finalize` (its words 0 to 2) it calls indirectly (`tcall`), and each
candidate tried by calling `core`, the signature with a given `k`
(`vg_ecdsa_<curve>_sign_k`), which reads `Q` bytes of the digest and of `k`,
and takes the digest's leftmost `qlen` bits (`bits2int`, a right shift by
`sh = 8 Q - qlen` bits).

Which table `hash` is, is public (`Abi.withTables`), and so is the hash
function's index in `Mgf1.hashes`, its word 3: `signT` chooses by it
(`byIdx`, comparisons with each index of `idxs`) the code for that hash
function's digest length `D` and block size `B` (`shapeOf`), `sign` of a
`Cfg`, in which both are constants. Everything below is that code.

HMAC (`hmac`) is computed from the table's streaming functions, as on
x86-64: the key `K` (`D` bytes, in the frame) padded to a block and XORed
with `ipad` (`padBlk`, a word at a time, into `scratch + sPad`), the inner
state set by `init` and updated with it, the same with `opad` for the outer
state (`hinit`); the inner state updated with the data (`hupd`); then the
inner state finalized into `scratch + sTmp`, the outer one updated with that
digest and finalized there too, and its first `D` bytes copied to the MAC's
place in the frame (`hfin`). Each call passes its arguments in a frame of
their own, pushed last to first (cdecl), from registers: the state in
`ebx`, for `update` the count in `edi` (and `eax` its high word), the data
in `edx` and its length in `ecx`, for `finalize` the count in `eax` (and
`ecx` its high word) and the digest's place in `edx`, and the working space
in `ebp`; the function's address, the table's word, is in `esi`.

Two kinds of curve and hash function, as on x86-64:

* `Q ≤ D` (and `qlen = 8 Q`, a multiple of 32 bits: P-192, P-224, P-256 and
  P-384, and brainpoolP512r1 with SHA-512): one `V` makes a candidate, its
  leftmost `Q` bytes; `bits2octets` is a conditional subtraction of `n` from
  the digest's leftmost `Q` bytes (`reduce`); and `core` reads the digest and
  `V` in place.
* `D < Q` (`wide`): `m` `V`s make a candidate `T` (`candW`), at the frame's
  top at `fT`, of which `core` reads the first `Q` bytes, shifted right in
  place by `sh` bits; the digest's integer is below `n`, so
  `h = bits2octets(digest)` is `Q - D` zero bytes then the digest (`hPrep`,
  at `fX`); and `core` reads `h`, or, if `sh ≠ 0` (P-521), the digest's
  integer shifted left by `sh` bits (`xPrep`, at `fXc`: `Q - D - 1` zero
  bytes, the digest and a zero byte, shifted right by `8 - sh` bits). The
  shifts are through the 32-bit words at `scratch + sSlot` (`conv`).

A frame of `frameBytes` bytes is allocated, 196 and `4 extra` more (68 words
if `wide`, 16 if `hHigh`): from `esp`, `K` and `V` (64 bytes each, of which
the first `D` are used), `h` (48 bytes, unless `wide` or `hHigh`), the number
of candidates left, and our caller's `ebx`, `esi`, `edi` and `ebp`; and, if
`wide`, `h`, the digest for `core` and `T` (72, 72 and 128 bytes), or, if
`hHigh` (64-byte scalars, as brainpoolP512r1's), `h` in 64 bytes. Our
arguments stay where our caller put them, above the frame and the return
address (`argM`). The calls use only `scratch`, which `core` overwrites
entirely, and the stack below the frame; `K`, `V`, `h` and the words at the
frame's top are cleared before the frame is freed. In `scratch`: HMAC's
inner and outer streaming states, the working space of the streaming
functions, the padded key and the inner digest, the message of steps d, f
and h.3, the words of a shift, and a copy of the states for the key `K`.

1. `h = bits2octets(digest)`: unless `wide`, the leftmost `Q` bytes, minus
   `n` if they are at least `n` (a conditional subtraction, as
   `2^(8 Q) < 2n`): the bytes, as `Q / 4` 32-bit words, go to `h`'s place
   and `h - n` to `K`'s, and a mask of the borrow selects between them, word
   by word, big-endian into `h`. If `wide`, `hPrep` and `xPrep`.
2. Steps b to g: `V = 0x01…`, `K = 0x00…`, `K = HMAC_K(V ‖ 0x00 ‖ d ‖ h)`,
   `V = HMAC_K(V)`, `K = HMAC_K(V ‖ 0x01 ‖ d ‖ h)`, `V = HMAC_K(V)`.
3. At most `tries` times: `V = HMAC_K(V)` (`m` times, each copied to `T`, if
   `wide`), the candidate `k`, and `core(out, d, digest, k, scratch)`; if it
   failed and candidates are left, `K = HMAC_K(V ‖ 0x00)`, `V = HMAC_K(V)`
   and again. Whether to go on is computed without branches, so that the
   code branches only on it: the number of candidates tried is all it
   reveals.

`core` writes the signature or zeros to `out`, and its return value is ours.

A block addresses memory only at `esp`, at `esp` plus a constant, or at a
pointer an earlier block loaded from our arguments (`digestPtr`, `msgPtrs`,
`scrPtr`, the table's address in `tcall`), never one it loads itself, so
that the taint analysis of each block knows its addresses are public. The
blocks that depend on the hash function depend only on `D` and `B`, so that
the taint analysis checks them for each size.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Rfc6979.X86

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (at_)
open VG.Impl.RsaOaep.X86 (Fns)

/-- `[esp + d]`, in the frame. -/
def stk (d : Nat) : MemOp := { base := .esp, disp := d }

/-! Where things are in the frame. -/
def fK : Nat := 0
def fV : Nat := 64
def fH : Nat := 128
def fCnt : Nat := 176
def fSave : Nat := 180
/-- At the frame's top: `h`, if `wide` or `hHigh`. -/
def fX : Nat := 196
/-- If `wide`: the digest for `core`, if `sh ≠ 0`. -/
def fXc : Nat := 268
/-- If `wide`: the candidate `T`. -/
def fT : Nat := 340

/-- The 32-bit words at the frame's top. -/
def extra (wide hHigh : Bool) : Nat := if wide then 68 else if hHigh then 16 else 0
/-- The frame's size, a multiple of 4. -/
def frameBytes (wide hHigh : Bool) : Nat := 196 + 4 * extra wide hHigh

/-- Our argument `i` (`out`, `d`, `digest`, `digest_len`, `scratch`,
`hash`), above the frame and the return address. -/
def argM (wide hHigh : Bool) (i : Nat) : Src := .mem (stk (frameBytes wide hHigh + 4 + 4 * i))

/-! Where things are in `scratch`. -/
def sInner : Nat := 0
def sOuter : Nat := 256
def sWork : Nat := 512
/-- The padded key, `K₀ ⊕ ipad` or `K₀ ⊕ opad`. -/
def sPad : Nat := 1024
/-- What the streaming `finalize` writes. -/
def sTmp : Nat := 1152
def sMsg : Nat := 2256
/-- The words of a conversion, if `wide`. -/
def sSlot : Nat := 2560
/-- A copy of HMAC's two states just after `hinit`, for the key `K`. -/
def sSave : Nat := 3072

/-- `ipad` and `opad` (RFC 2104), in each byte of a 32-bit word. -/
def ipad32 : BitVec 32 := 0x36363636
def opad32 : BitVec 32 := 0x5c5c5c5c

/-- Our caller's registers, where the frame keeps them. -/
def saved : List (Reg × Nat) := [(.ebx, fSave), (.esi, fSave + 4), (.edi, fSave + 8), (.ebp, fSave + 12)]

/-- Our caller's registers into the frame. -/
def save : List Instr := saved.map fun (r, d) => .store (stk d) r

/-- Our caller's registers back. -/
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (stk d))

/-- The registers `update`'s frame pushes: the state (`ebx`), the count
(`edi`, and `eax` its high word), the data (`edx`) and its length (`ecx`),
the working space (`ebp`). -/
abbrev upd6 : List Reg := [.ebp, .ecx, .edx, .eax, .edi, .ebx]

/-- The registers `finalize`'s frame pushes: the state (`ebx`), the count
(`eax`, and `ecx` its high word), the digest's place (`edx`), the working
space (`ebp`). -/
abbrev fin5 : List Reg := [.ebp, .edx, .ecx, .eax, .ebx]

/-- What the code needs of a curve and a hash function. -/
structure Cfg where
  /-- The hash function's digest length and block size. -/
  D : Nat
  B : Nat
  /-- The functions an indirect call of a table's functions may reach. -/
  f : Fns
  /-- The 64-bit words of the curve's scalars. -/
  w : Nat
  /-- The bytes of the curve's scalars, `Q`. -/
  len : Nat := 8 * w
  /-- The bits `core` shifts its digest right by, `8 Q - qlen`. -/
  sh : Nat := 0
  /-- Whether `h` is kept at the frame's top, in 16 more words: for scalars
  of 64 bytes, which the 48 bytes below the count do not hold (and the hash
  is no shorter). -/
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

/-- The 32-bit words of the scalars, unless `wide`. -/
def k : Nat := c.len / 4

/-- Where `h` is in the frame. -/
def fHo : Nat := if c.wide || c.hHigh then fX else fH

/-- Our argument `i`. -/
def arg (i : Nat) : Src := argM c.wide c.hHigh i

/-- `d ← scratch + a`: an address in `scratch`. -/
def scr (d : Reg) (a : Nat) : List Instr :=
  [.mov d (c.arg 4), .alu .add d (.imm (BitVec.ofNat 32 a))]

/-- `d ← esp + o`: an address in the frame. -/
def fr (d : Reg) (o : Nat) : List Instr := [.mov d (.reg .esp), .alu .add d (.imm (BitVec.ofNat 32 o))]

/-- `scratch` in `edi`. -/
def scrPtr : List Instr := [.mov .edi (c.arg 4)]

/-! ## HMAC through the table -/

/-- The indirect call of the table's function `j`, among `ts`, in a frame
pushing `rs` (its arguments): the table's address into `esi`, its word `j`
into `esi`, then `call esi`. -/
def tcall (j : Nat) (ts : List (String × Prog isa)) (rs : List Reg) : Prog isa :=
  .seq (.block [.mov .esi (c.arg 5)]) (.seq (.block [.mov .esi (.mem (at_ .esi (4 * j)))])
    (.frame (.push rs) (Code.icalls (.callr .esi) ts) (.pop .eax rs.length)))

/-- The streaming `init` of the state at `scratch + o`. -/
def initCall (o : Nat) : Prog isa := .seq (.block (c.scr .ebx o)) (c.tcall 0 c.f.init [.ebx])

/-- The arguments of the streaming `update` of the state at `scratch + o`,
which holds `cnt` bytes, with the data (at the address `dataA` sets `edx`
to) of `len` bytes, and the working space. -/
def updArgs (o cnt : Nat) (dataA : List Instr) (len : Nat) : List Instr :=
  c.scr .ebx o ++ ([.mov .edi (.imm (BitVec.ofNat 32 cnt)), .mov .eax (.imm 0)] : List Instr) ++ dataA ++
    ([.mov .ecx (.imm (BitVec.ofNat 32 len))] : List Instr) ++ c.scr .ebp sWork

def updCall (o cnt : Nat) (dataA : List Instr) (len : Nat) : Prog isa :=
  .seq (.block (c.updArgs o cnt dataA len)) (c.tcall 1 c.f.upd upd6)

/-- The arguments of the streaming `finalize` of the state at `scratch + o`,
which holds `cnt` bytes, into `scratch + sTmp`, with the working space. -/
def finArgs (o cnt : Nat) : List Instr :=
  c.scr .ebx o ++ ([.mov .eax (.imm (BitVec.ofNat 32 cnt)), .mov .ecx (.imm 0)] : List Instr) ++ c.scr .edx sTmp ++
    c.scr .ebp sWork

def finCall (o cnt : Nat) : Prog isa := .seq (.block (c.finArgs o cnt)) (c.tcall 2 c.f.fin fin5)

/-- Word `k` of the key `K` (the frame's first `D` bytes) padded to `B`
bytes, XORed with the pad in `ecx`, to `scratch + sPad` (`scratch` in
`edi`). -/
def padW (k : Nat) : List Instr :=
  if k < c.D / 4 then
    [.mov .eax (.mem (stk (fK + 4 * k))), .alu .xor .eax (.reg .ecx), .store (at_ .edi (sPad + 4 * k)) .eax]
  else [.store (at_ .edi (sPad + 4 * k)) .ecx]

/-- `K₀ ⊕ pad` (a block) at `scratch + sPad`. -/
def padBlk (x : BitVec 32) : List Instr :=
  c.scrPtr ++ ([.mov .ecx (.imm x)] : List Instr) ++ (List.range (c.B / 4)).flatMap c.padW

/-- HMAC's states for the key `K`: each set by `init`, then updated with
the padded key. -/
def hinit : Prog isa :=
  .seq (c.initCall sInner) (.seq (c.initCall sOuter)
  (.seq (.block (c.padBlk ipad32)) (.seq (c.updCall sInner 0 (c.scr .edx sPad) c.B)
  (.seq (.block (c.padBlk opad32)) (c.updCall sOuter 0 (c.scr .edx sPad) c.B)))))

/-- The inner state updated with `len` bytes of data at the address `dataA`
sets `edx` to. -/
def hupd (dataA : List Instr) (len : Nat) : Prog isa := c.updCall sInner c.B dataA len

/-- The `4 k` bytes at `[src + so]` to `[dst + d]`, a word at a time through `eax`. -/
def copyN (k : Nat) (src : Reg) (so : Nat) (dst : Reg) (d : Nat) : List Instr :=
  (List.range k).flatMap fun j =>
    [.mov .eax (.mem (at_ src (so + 4 * j))), .store (at_ dst (d + 4 * j)) .eax]

/-- The `len` bytes at `[src + so]` to `[dst + d]` (`4 ≤ len`), a word at a
time through `eax`: `copyN` for the whole words, then the last four bytes
again if `len` is not a multiple of 4. -/
def copyBytes (len : Nat) (src : Reg) (so : Nat) (dst : Reg) (d : Nat) : List Instr :=
  copyN (len / 4) src so dst d ++
    (if len % 4 = 0 then [] else
      [.mov .eax (.mem (at_ src (so + len - 4))), .store (at_ dst (d + len - 4)) .eax])

/-- The MAC, for `len` bytes of data, to the frame at `dst`: the inner state
finalized, the outer one updated with that digest and finalized, and its
first `D` bytes copied. -/
def hfin (len dst : Nat) : Prog isa :=
  .seq (c.finCall sInner (c.B + len)) (.seq (c.updCall sOuter c.B (c.scr .edx sTmp) c.D)
  (.seq (c.finCall sOuter (c.B + c.D)) (.block (c.scrPtr ++ copyBytes c.D .edi sTmp .esp dst))))

/-- `HMAC_K(data)` into the frame at `dst`, for `len` bytes of `data` at the
address `dataA` sets `edx` to. -/
def hmac (dataA : List Instr) (len dst : Nat) : Prog isa :=
  .seq c.hinit (.seq (c.hupd dataA len) (c.hfin len dst))

/-- The pointers the messages need: `scratch` in `edi` and `d` in `esi`. -/
def msgPtrs : List Instr := [.mov .edi (c.arg 4), .mov .esi (c.arg 1)]

/-- The message `V ‖ b` (and `‖ d ‖ h` if `full`, `Q` bytes each) at
`scratch + sMsg`, for `V` of `D` bytes, with `scratch` in `edi` and `d` in
`esi`: `V` from the frame, `b` a byte, and `h` from the frame at `ho`. -/
def msg (Q D b : Nat) (full : Bool) (ho : Nat := fH) : List Instr :=
  copyBytes D .esp fV .edi sMsg ++
    ([.mov .eax (.imm (BitVec.ofNat 32 b)), .store8 (at_ .edi (sMsg + D)) .al] : List Instr) ++
    (if full then copyBytes Q .esi 0 .edi (sMsg + D + 1) ++ copyBytes Q .esp ho .edi (sMsg + D + 1 + Q) else [])

/-- The 32-bit words of `n`, least significant first. -/
def nWord (j : Nat) : BitVec 32 := BitVec.ofNat 32 (c.n >>> (32 * j))

/-- `digest` in `esi`, and, if `wide`, `scratch` in `edi`. -/
def digestPtr : List Instr :=
  ([.mov .esi (c.arg 2)] : List Instr) ++ (if c.wide then [.mov .edi (c.arg 4)] else [])

/-- HMAC's two states (512 bytes) copied from `scratch + sInner` to
`scratch + sSave` (`toSave`) or back, with `scratch` in `edi`, through `eax`. -/
def copyStates (toSave : Bool) : List Instr :=
  if toSave then copyN 128 .edi sInner .edi sSave else copyN 128 .edi sSave .edi sInner

/-- `hmac`, its states for `K` saved after `hinit`. -/
def hmacS (dataA : List Instr) (len dst : Nat) : Prog isa :=
  .seq c.hinit (.seq (.block (c.scrPtr ++ copyStates true)) (.seq (c.hupd dataA len) (c.hfin len dst)))

/-- `hmac`, with the states for `K` restored from the copy rather than made by `hinit`. -/
def hmacR (dataA : List Instr) (len dst : Nat) : Prog isa :=
  .seq (.block (c.scrPtr ++ copyStates false)) (.seq (c.hupd dataA len) (c.hfin len dst))

/-- `V = HMAC_K(V)`, saving the states for `K`. -/
def hmacVS : Prog isa := c.hmacS (fr .edx fV) c.D fV

/-- `V = HMAC_K(V)`, from the saved states for `K`. -/
def hmacVR : Prog isa := c.hmacR (fr .edx fV) c.D fV

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g), the
states for the new `K` saved; for `b = 1` (step f), the states for `K` are
the copy step e saved. -/
def rekeyFull (b : Nat) : Prog isa :=
  .seq (.block c.msgPtrs) (.seq (.block (msg c.len c.D b true c.fHo))
    (.seq (if b = 0 then c.hmac (c.scr .edx sMsg) (c.D + 2 * c.len + 1) fK
      else c.hmacR (c.scr .edx sMsg) (c.D + 2 * c.len + 1) fK) c.hmacVS))

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
def rekey : Prog isa :=
  .seq (.block c.msgPtrs) (.seq (.block (msg c.len c.D 0 false))
    (.seq (c.hmac (c.scr .edx sMsg) (c.D + 1) fK) c.hmacVS))

/-- The `Q` bytes at `esp + o`, as a big-endian number, shifted right by `s`
bits in place (`0 < s < 32`), through the words at `scratch + sSlot` (with
`scratch` in `edi`). -/
def conv (o s : Nat) : List Instr :=
  fr .esi o ++ Impl.Weierstrass.X86.loadBytes c.len c.w sSlot .esi ++
    Impl.Weierstrass.X86.shrWords c.w sSlot s ++ ([.mov .ecx (.imm (BitVec.allOnes 32))] : List Instr) ++
    Impl.Weierstrass.X86.storeBytes c.len c.w .esp o sSlot

/-- Eighteen zero words at `esp + o`. -/
def zero18 (o : Nat) : List Instr :=
  ([.mov .eax (.imm 0)] : List Instr) ++ (List.range 18).map fun j => .store (stk (o + 4 * j)) .eax

/-- If `wide`: `h`, `Q - D` zero bytes then the digest (at `esi`), at `fX`. -/
def hPrep : List Instr := zero18 fX ++ copyBytes c.D .esi 0 .esp (fX + c.len - c.D)

/-- If `wide` and `sh ≠ 0`: the digest for `core`, `Q - D - 1` zero bytes,
the digest (at `esi`) and a zero byte, shifted right by `8 - sh` bits: the
digest's integer shifted left by `sh` bits, at `fXc`. -/
def xPrep : List Instr :=
  if c.sh = 0 then [] else
    zero18 fXc ++ copyBytes c.D .esi 0 .esp (fXc + c.len - c.D - 1) ++ c.conv fXc (8 - c.sh)

/-- Word `j` (least significant first) of the `Q` bytes at `digest` (in
`esi`), as a big-endian number, to `h`'s place, and that word of the
difference with `n` (`sub` for the first, `sbb` for the others) to `K`'s:
both at the offset of the word's bytes. -/
def subWord (j : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .esi (4 * (c.k - 1 - j)))), .bswap .eax, .store (stk (c.fHo + 4 * (c.k - 1 - j))) .eax,
    .alu (if j = 0 then .sub else .sbb) .eax (.imm (c.nWord j)), .store (stk (fK + 4 * (c.k - 1 - j))) .eax]

/-- Word `j` of `h`: of the digest's number if subtracting `n` borrowed
(the mask in `edx`), of the difference if not, big-endian into `h`. -/
def selWord (j : Nat) : List Instr :=
  [.mov .eax (.mem (stk (c.fHo + 4 * (c.k - 1 - j)))), .mov .ecx (.mem (stk (fK + 4 * (c.k - 1 - j)))),
    -- `x = d ^ ((x ^ d) & mask)`: `x` if it borrowed, `d` if not.
    .alu .xor .eax (.reg .ecx), .alu .and .eax (.reg .edx), .alu .xor .eax (.reg .ecx),
    .bswap .eax, .store (stk (c.fHo + 4 * (c.k - 1 - j))) .eax]

/-- `h`: the `Q` bytes at `digest` (in `esi`), minus `n` if that does not borrow. -/
def reduce : List Instr :=
  (List.range c.k).flatMap c.subWord ++ ([.alu .sbb .edx (.reg .edx)] : List Instr) ++ (List.range c.k).flatMap c.selWord

/-- `V = 0x01…`, `K = 0x00…`, all 64 bytes of each. -/
def initKV : List Instr :=
  ([.mov .eax (.imm 0x01010101), .mov .ecx (.imm 0)] : List Instr) ++
    (List.range 16).flatMap fun j => [.store (stk (fV + 4 * j)) .eax, .store (stk (fK + 4 * j)) .ecx]

/-- The candidates left. -/
def initCnt : List Instr :=
  [.mov .eax (.imm (BitVec.ofNat 32 c.tries)), .store (stk fCnt) .eax]

/-- Where `core` reads the digest, if `wide`: `h`, or the digest shifted
left by `sh` bits. -/
def fDg : Nat := if c.sh = 0 then fX else fXc

/-- `core(out, d, digest, k, scratch)`'s arguments: `edi`, `esi`, `edx`,
`ecx`, `ebp`, with `k = V`, or, if `wide`, the digest and the candidate at
the frame's top. -/
def coreArgs : List Instr :=
  ([.mov .edi (c.arg 0), .mov .esi (c.arg 1)] : List Instr) ++
    (if c.wide then fr .edx c.fDg ++ fr .ecx fT else .mov .edx (c.arg 2) :: fr .ecx fV) ++
    ([.mov .ebp (c.arg 4)] : List Instr)

/-- If `wide`: `V`'s `D` bytes to `T + j D`. -/
def keepV (j : Nat) : List Instr := copyBytes c.D .esp fV .esp (fT + j * c.D)

/-- If `wide`: `V = HMAC_K(V)` and its `D` bytes to `T + j D`, for each
`j < k`. -/
def candW : Nat → Prog isa
  | 0 => .block []
  | k + 1 => .seq (candW k) (.seq c.hmacVR (.block (c.keepV k)))

/-- If `wide` and `sh ≠ 0`: `T`'s first `Q` bytes shifted right by `sh` bits. -/
def candTop : List Instr := if c.sh = 0 then [] else c.scrPtr ++ c.conv fT c.sh

/-- The candidate: `V = HMAC_K(V)`, which is `k`; or, if `wide`, the
leftmost `Q` bytes of `m` successive `V = HMAC_K(V)`, shifted right by `sh`
bits. -/
def cand : Prog isa :=
  if c.wide then .seq (c.candW c.m) (.block c.candTop) else c.hmacVR

/-- One candidate fewer, and `edx ≠ 0` (and `ZF` clear) iff the signature
failed (`eax = 0`) and candidates are left: `edx = -(eax < 1) & (count - 1)`. -/
def goOn : List Instr :=
  [.mov .ecx (.mem (stk fCnt)), .alu .sub .ecx (.imm 1), .store (stk fCnt) .ecx,
    .alu .cmp .eax (.imm 1), .alu .sbb .edx (.reg .edx), .alu .and .edx (.reg .ecx),
    .alu .test .edx (.reg .edx)]

/-- `ZF` clear: go on. -/
def again : List Instr := [.mov .edx (.imm 1), .alu .test .edx (.reg .edx)]

/-- `ZF` set: stop. -/
def stop : List Instr := [.mov .edx (.imm 0), .alu .test .edx (.reg .edx)]

/-- One candidate: `cand`, `core` with it, then, if it failed and candidates
are left, step h.3. -/
def tryOne : Prog isa :=
  .seq c.cand
  (.seq (.block c.coreArgs)
  (.seq (.frame (.push [.ebp, .ecx, .edx, .esi, .edi]) (.call c.coreN c.coreC) (.pop .ecx 5))
  (.seq (.block goOn)
    (.ite .ne (.seq c.rekey (.block again)) (.block stop)))))

/-- `K`, `V` and `h` cleared, and the words at the frame's top (`eax`, the
result, kept), and our caller's registers back. -/
def wipe : List Instr :=
  ([.mov .ecx (.imm 0)] : List Instr) ++ (List.range 44).map (fun j => .store (stk (4 * j)) .ecx) ++
    (List.range (extra c.wide c.hHigh)).map (fun j => .store (stk (fX + 4 * j)) .ecx) ++ restore

/-- `h` (and, if `wide`, the digest for `core`), then `V = 0x01…`, `K = 0x00…`. -/
def prep : List Instr := (if c.wide then c.hPrep ++ c.xPrep else c.reduce) ++ initKV

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block (save ++ c.digestPtr))
  (.seq (.block c.prep)
  (.seq (c.rekeyFull 0)
  (.seq (c.rekeyFull 1)
  (.seq (.block c.initCnt)
  (.seq (.loop c.tryOne .ne)
    (.block c.wipe))))))

/-- The signature for the hash function of this size. -/
def sign : Prog isa :=
  .frame (.alloc (frameBytes c.wide c.hHigh)) c.body (.free (frameBytes c.wide c.hHigh))

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

/-- `b i` for the index `i` in `ecx`, by comparisons with each of `is`: the
last is taken for every other value. -/
def byIdx (b : Nat → Prog isa) : List Nat → Prog isa
  | [] => .block []
  | [i] => b i
  | i :: is => .seq (.block [.alu .cmp .ecx (.imm (BitVec.ofNat 32 i))]) (.ite .e (b i) (byIdx b is))

/-- The table's address (our argument 5) to `ecx`. -/
def entry₁ : List Instr := [.mov .ecx (.mem (stk 24))]

/-- The hash function's index (the table's word 3) to `ecx`. -/
def entry₂ : List Instr := [.mov .ecx (.mem (at_ .ecx 12))]

/-- `vg_ecdsa_<curve>_sign`: the signature with the code `cfg i` for the
hash function of index `i` of the table `hash`. -/
def signT (cfg : Nat → Cfg) : Prog isa :=
  .seq (.block entry₁) (.seq (.block entry₂) (byIdx (fun i => (cfg i).sign) idxs))

end VG.Impl.Ecdsa.Rfc6979.X86
