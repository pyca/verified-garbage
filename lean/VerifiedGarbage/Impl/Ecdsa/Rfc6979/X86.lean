module

public import VerifiedGarbage.Impl.Bignum.X86.CopyBytes
public import VerifiedGarbage.Impl.Pbkdf2.Stream.X86
public import VerifiedGarbage.Impl.Weierstrass.X86
public import VerifiedGarbage.Impl.ICall

/-!
# Deterministic ECDSA (RFC 6979) on x86 (32-bit), with HMAC through a table

`vg_ecdsa_<curve>_sign(out, d, digest, digest_len, scratch, hmac) -> eax`,
every argument on the stack (cdecl), as on x86-64
(`Impl/Ecdsa/Rfc6979/X86_64.lean`), for a curve of `Q`-byte scalars in `w`
32-bit words: RFC 6979 §3.2 with HMAC over the hash function of the table
`hmac` of the interface `Hmac` (`Spec/HmacTable.lean`), whose functions it
calls indirectly (`tcall`): HMAC's `init` (word 0), the streaming `update`
(word 1), on the inner state, and HMAC's `finalize` (word 2), each in a
frame of its arguments, pushed last to first; and each candidate tried by
calling `core`, the signature with a given `k`
(`vg_ecdsa_<curve>_sign_k`), which reads `Q` bytes of the digest and of
`k`, and takes their leftmost `qlen` bits (`bits2int`, a right shift by
`sh = 8 Q - qlen` bits).

One body serves every hash function: the digest length `D` and HMAC's block
size `B` are the table's words of data 4 and 5, which the code copies to the
frame on entry (`entry`) and reads wherever it needs them, as the lengths
and counts it passes (all public). Nothing in the code depends on the hash
function but those two words and the table's functions.

Each HMAC is `init` with the key `K` (`D` bytes, in the frame) or the states
for `K` restored (`restore`, from a copy `save` made after an earlier
`init` with the same `K`), the inner state updated with `V` (`D` bytes, in
the frame), then with the message `b ‖ d ‖ h` or `b` (`msg`, in `scratch`,
its length the curve's), and `finalize`, which writes the MAC to `K` or `V`
in the frame, with the count `B + D + len`. The copies of the states are a
byte loop (`cpLoop`, `Impl.Bignum.X86.copyBytes`).

The digest's leftmost `min(D, Q)` bytes, after `Q - min(D, Q)` zero bytes,
are `X` (`prepX`, by the byte loop; the minimum by the borrow of `D - Q`, a
mask), a `Q`-byte number: the digest's `bits2int` if `sh = 0`. Then:

* unless `big` (all but P-521): `h = bits2octets(digest)` is `X` minus `n` if
  it is at least `n` (a conditional subtraction, `reduce`, as
  `2^(8 Q) < 2 n`), and `core` reads `X` as its digest;
* if `big` (P-521, whose scalars are longer than every digest, with
  `sh ≠ 0`): `X`'s integer is below `n`, so `h` is `X` itself, and `core`
  reads the digest's integer shifted left by `sh` bits (`prepC`, at `fXc`:
  `Q - 1 - D` zero bytes, the digest and a zero byte, shifted right by
  `8 - sh` bits through the words at `scratch + sSlot`, `conv`).

The candidate `k` is the leftmost `Q` bytes of `T`, the `V`s of successive
`V = HMAC_K(V)` while `T` is shorter than `Q` bytes (`cand`: a loop whose
count is public, each `V` appended to `T` by the byte loop), shifted right
by `sh` bits in place if `big` (`candTop`).

A frame of `frameBytes` (512) bytes is allocated: from `esp`, `K` and `V`
(64 bytes each, of which the first `D` are used), our caller's `ebx`, `esi`,
`edi` and `ebp`, `D` and `B`, the length of `T`, the number of candidates
left, `h`, `X` and `core`'s digest if `big` (72 bytes each), and `T` (136
bytes). Our arguments stay where our caller put them, above the frame and
the return address (`argM`). The calls use only `scratch`, which `core`
overwrites entirely, and the stack below the frame (48 bytes for HMAC's
functions, besides their arguments and return address); `K`, `V` and the
frame above `B` are cleared before the frame is freed. In `scratch`: HMAC's
inner and outer streaming states (192 bytes each), the working space of the
table's functions, the message, the words of a shift, and the copy of the
states for `K`.

1. `X`; `h` (`reduce`, or `prepC`); `V = 0x01…`, `K = 0x00…`.
2. Steps d to g: `K = HMAC_K(V ‖ 0x00 ‖ d ‖ h)`, `V = HMAC_K(V)`,
   `K = HMAC_K(V ‖ 0x01 ‖ d ‖ h)`, `V = HMAC_K(V)`.
3. At most `tries` times: the candidate `k` (`cand`) and
   `core(out, d, digest, k, scratch)`; if it failed and candidates are left,
   `K = HMAC_K(V ‖ 0x00)`, `V = HMAC_K(V)` and again. Whether to go on is
   computed without branches, so that the code branches only on it: the
   number of candidates tried is all it reveals.

`core` writes the signature or zeros to `out`, and its return value is ours.

A block addresses memory only at `esp`, at `esp` plus a constant, or at a
pointer it or an earlier block loaded from our arguments (`msgPtrs`,
`scrPtr`, the table's address in `entry` and `tcall`), plus public offsets:
the taint analysis of each block, once for each curve, knows its addresses
are public.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Rfc6979.X86

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (at_)

/-- `[esp + d]`, in the frame. -/
def stk (d : Nat) : MemOp := { base := .esp, disp := d }

/-! Where things are in the frame. -/
def fK : Nat := 0
def fV : Nat := 64
/-- Our caller's `ebx`, `esi`, `edi` and `ebp`. -/
def fSave : Nat := 128
/-- The digest length `D` and HMAC's block size `B`. -/
def fDl : Nat := 144
def fBl : Nat := 148
/-- The length of `T`. -/
def fTlen : Nat := 152
def fCnt : Nat := 156
/-- `h` (72 bytes), unless `big`. -/
def fH : Nat := 160
/-- `X` (72 bytes): the digest's leftmost bytes, as a `Q`-byte number; `h` if `big`. -/
def fX : Nat := 232
/-- If `big`: the digest for `core` (72 bytes). -/
def fXc : Nat := 304
/-- The candidate `T` (136 bytes). -/
def fT : Nat := 376
/-- The frame's size, a multiple of 4. -/
def frameBytes : Nat := 512

/-- Our argument `i` (`out`, `d`, `digest`, `digest_len`, `scratch`,
`hmac`), above the frame and the return address. -/
def argM (i : Nat) : Src := .mem (stk (frameBytes + 4 + 4 * i))

/-! Where things are in `scratch`. -/
def sInner : Nat := 0
def sOuter : Nat := 192
def sWork : Nat := 384
def sMsg : Nat := 2256
/-- The words of a conversion, if `big`. -/
def sSlot : Nat := 2560
/-- A copy of HMAC's two states just after `init`, for the key `K`. -/
def sSave : Nat := 3072

/-- Our caller's registers, where the frame keeps them. -/
def saved : List (Reg × Nat) := [(.ebx, fSave), (.esi, fSave + 4), (.edi, fSave + 8), (.ebp, fSave + 12)]

/-- The functions an indirect call of each of a table's functions may
reach: for each of `init`, `update` and `finalize`, that function of every
table of the interface, by name. -/
structure Fns where
  init : List (String × Prog isa)
  upd : List (String × Prog isa)
  fin : List (String × Prog isa)

/-- The registers the frames of HMAC's `init`, the streaming `update` and
HMAC's `finalize` push, last argument first. -/
abbrev init5 : List Reg := [.ebp, .ecx, .edx, .esi, .edi]
abbrev upd6 : List Reg := [.ebp, .ecx, .edx, .eax, .esi, .edi]
abbrev fin6 : List Reg := [.ebp, .edi, .ecx, .eax, .esi, .edx]

/-- What the code needs of a curve. -/
structure Cfg where
  /-- The functions an indirect call of a table's functions may reach. -/
  f : Fns
  /-- The 32-bit words of the curve's scalars. -/
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

/-- `d ← scratch + a`: an address in `scratch`. -/
def scr (d : Reg) (a : Nat) : List Instr := [.mov d (argM 4), .alu .add d (.imm (BitVec.ofNat 32 a))]

/-- `d ← esp + o`: an address in the frame. -/
def fr (d : Reg) (o : Nat) : List Instr := [.mov d (.reg .esp), .alu .add d (.imm (BitVec.ofNat 32 o))]

/-- `scratch` in `edi`. -/
def scrPtr : List Instr := [.mov .edi (argM 4)]

/-- Our caller's registers into the frame, and `D` and `B`, the table's
words of data 4 and 5, from it. -/
def entry : List Instr :=
  saved.map (fun (r, d) => .store (stk d) r) ++
    [.mov .eax (argM 5), .mov .ecx (.mem (at_ .eax 16)), .store (stk fDl) .ecx, .mov .ecx (.mem (at_ .eax 20)),
      .store (stk fBl) .ecx]

/-- Our caller's registers back. -/
def restoreRegs : List Instr := saved.map fun (r, d) => .mov r (.mem (stk d))

/-! ## HMAC through the table -/

/-- The indirect call of the table's function `j`, among `ts`, in a frame
pushing `rs` (its arguments): the table's address into `ebx`, its word `j`
into `ebx`, then `call ebx`. -/
def tcall (j : Nat) (ts : List (String × Prog isa)) (rs : List Reg) : Prog isa :=
  .seq (.block [.mov .ebx (argM 5), .mov .ebx (.mem (at_ .ebx (4 * j)))])
    (.frame (.push rs) (Code.icalls (.callr .ebx) ts) (.pop .eax rs.length))

/-- The arguments of HMAC's `init`: the states (`edi`, `esi`), the key `K`
of `D` bytes (`edx`, `ecx`), the working space (`ebp`). -/
def initArgs : List Instr :=
  scr .edi sInner ++ scr .esi sOuter ++ fr .edx fK ++ ([.mov .ecx (.mem (stk fDl))] : List Instr) ++
    scr .ebp sWork

/-- The arguments of the streaming `update` with `V`: the inner state
(`edi`), the `B` bytes it holds (`esi`, and `eax` the high word), `V`'s `D`
bytes (`edx`, `ecx`), the working space (`ebp`). -/
def updVArgs : List Instr :=
  scr .edi sInner ++ ([.mov .esi (.mem (stk fBl)), .mov .eax (.imm 0)] : List Instr) ++ fr .edx fV ++
    ([.mov .ecx (.mem (stk fDl))] : List Instr) ++ scr .ebp sWork

/-- The arguments of the streaming `update` with the message: the inner
state, the `B + D` bytes it holds, the message's `len` bytes, the working
space. -/
def updMArgs (len : Nat) : List Instr :=
  scr .edi sInner ++ ([.mov .esi (.mem (stk fBl)), .alu .add .esi (.mem (stk fDl)), .mov .eax (.imm 0)] :
    List Instr) ++ scr .edx sMsg ++ ([.mov .ecx (.imm (BitVec.ofNat 32 len))] : List Instr) ++ scr .ebp sWork

/-- The arguments of HMAC's `finalize`: the states (`edx`, `esi`), the
`B + D + len` bytes the inner one holds (`eax`, and `ecx` the high word),
the MAC's place in the frame (`edi`), the working space (`ebp`). -/
def finArgs (len dst : Nat) : List Instr :=
  scr .edx sInner ++ scr .esi sOuter ++
    ([.mov .eax (.mem (stk fBl)), .alu .add .eax (.mem (stk fDl)),
      .alu .add .eax (.imm (BitVec.ofNat 32 len)), .mov .ecx (.imm 0)] : List Instr) ++ fr .edi dst ++
    scr .ebp sWork

/-- HMAC's states for `K`, by `init`. -/
def initK : Prog isa := .seq (.block initArgs) (tcall 0 c.f.init init5)

/-- The inner state updated with `V`. -/
def updV : Prog isa := .seq (.block updVArgs) (tcall 1 c.f.upd upd6)

/-- The inner state updated with the message's `len` bytes. -/
def updM (len : Nat) : Prog isa := .seq (.block (updMArgs len)) (tcall 1 c.f.upd upd6)

/-- The MAC, of `D + len` bytes of text, to the frame at `dst`. -/
def fin (len dst : Nat) : Prog isa := .seq (.block (finArgs len dst)) (tcall 2 c.f.fin fin6)

/-- The `ecx` bytes at `esi` to `ebx` (`ecx > 0`), a byte at a time. -/
def cpLoop : Prog isa := Impl.Bignum.X86.copyBytes

/-- The arguments of the copy of HMAC's two states (384 bytes) from
`scratch + sInner` to `scratch + sSave` (`toSave`) or back. -/
def copyArgs (toSave : Bool) : List Instr :=
  (if toSave then scr .esi sInner ++ scr .ebx sSave else scr .esi sSave ++ scr .ebx sInner) ++
    ([.mov .ecx (.imm 384)] : List Instr)

/-- The states for `K` saved. -/
def save : Prog isa := .seq (.block (copyArgs true)) cpLoop

/-- The states for `K` restored from the copy. -/
def restore : Prog isa := .seq (.block (copyArgs false)) cpLoop

/-- `V = HMAC_K(V)`, saving the states for `K`. -/
def hmacVS : Prog isa := .seq c.initK (.seq save (.seq c.updV (c.fin 0 fV)))

/-- `V = HMAC_K(V)`, from the saved states for `K`. -/
def hmacVR : Prog isa := .seq restore (.seq c.updV (c.fin 0 fV))

/-- `K = HMAC_K(V ‖ msg)`, for the message's `len` bytes, from the states
for `K` by `init` (`fresh`) or restored. -/
def hmacK (fresh : Bool) (len : Nat) : Prog isa :=
  .seq (if fresh then c.initK else restore) (.seq c.updV (.seq (c.updM len) (c.fin len fK)))

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

/-- The pointers the messages need: `scratch` in `edi`, `d` in `esi`. -/
def msgPtrs : List Instr := [.mov .edi (argM 4), .mov .esi (argM 1)]

/-- The message `b` (and `‖ d ‖ h` if `full`, `Q` bytes each) at
`scratch + sMsg`, with `scratch` in `edi` and `d` in `esi`: `b` a byte, then
the private key and `h` from the frame. -/
def msg (b : Nat) (full : Bool) : List Instr :=
  ([.mov .eax (.imm (BitVec.ofNat 32 b)), .store8 (at_ .edi sMsg) .al] : List Instr) ++
    (if full then copyBytes c.len .esi 0 .edi (sMsg + 1) ++ copyBytes c.len .esp c.fHo .edi (sMsg + 1 + c.len)
    else [])

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g), the
states for the new `K` saved; for `b = 1` (step f), the states for `K` are
the copy step e saved. -/
def rekeyFull (b : Nat) : Prog isa :=
  .seq (.block msgPtrs) (.seq (.block (c.msg b true)) (.seq (c.hmacK (b = 0) (1 + 2 * c.len)) c.hmacVS))

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
def rekey : Prog isa :=
  .seq (.block msgPtrs) (.seq (.block (c.msg 0 false)) (.seq (c.hmacK true 1) c.hmacVS))

/-! ## Bytes, numbers and `h` -/

/-- Eighteen zero words at `esp + o`. -/
def zero18 (o : Nat) : List Instr :=
  ([.mov .eax (.imm 0)] : List Instr) ++ (List.range 18).map fun j => .store (stk (o + 4 * j)) .eax

/-- The arguments of `X`'s copy: `X` cleared; then `ecx = min(D, Q)` (`Q`
plus `D - Q` under the mask of its borrow), the digest in `esi` and
`X + Q - ecx` in `ebx`. -/
def xArgs : List Instr :=
  zero18 fX ++
    ([.mov .ecx (.mem (stk fDl)), .alu .sub .ecx (.imm (BitVec.ofNat 32 c.len)), .alu .sbb .edx (.reg .edx),
      .alu .and .ecx (.reg .edx), .alu .add .ecx (.imm (BitVec.ofNat 32 c.len)), .mov .ebx (.reg .esp),
      .alu .add .ebx (.imm (BitVec.ofNat 32 (fX + c.len))), .alu .sub .ebx (.reg .ecx), .mov .esi (argM 2)] :
      List Instr)

/-- `X`: `Q - min(D, Q)` zero bytes, then the digest's leftmost `min(D, Q)`. -/
def prepX : Prog isa := .seq (.block c.xArgs) cpLoop

/-- The 32-bit words of `n`, least significant first. -/
def nWord (j : Nat) : BitVec 32 := BitVec.ofNat 32 (c.n >>> (32 * j))

/-- Word `j` (least significant first) of `X` (at `esi`), as a big-endian
number, to `h`'s place, and that word of the difference with `n` (`sub` for
the first, `sbb` for the others) to `K`'s: both at the offset of the word's
bytes. -/
def subWord (j : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .esi (4 * (c.w - 1 - j)))), .bswap .eax, .store (stk (fH + 4 * (c.w - 1 - j))) .eax,
    .alu (if j = 0 then .sub else .sbb) .eax (.imm (c.nWord j)), .store (stk (fK + 4 * (c.w - 1 - j))) .eax]

/-- Word `j` of `h`: of `X`'s number if subtracting `n` borrowed (the mask
in `edx`), of the difference if not, big-endian into `h`. -/
def selWord (j : Nat) : List Instr :=
  [.mov .eax (.mem (stk (fH + 4 * (c.w - 1 - j)))), .mov .ecx (.mem (stk (fK + 4 * (c.w - 1 - j)))),
    -- `x = d ^ ((x ^ d) & mask)`: `x` if it borrowed, `d` if not.
    .alu .xor .eax (.reg .ecx), .alu .and .eax (.reg .edx), .alu .xor .eax (.reg .ecx),
    .bswap .eax, .store (stk (fH + 4 * (c.w - 1 - j))) .eax]

/-- `h`, unless `big`: `X` (at `esi`), minus `n` if that does not borrow,
big-endian into the frame's `Q` bytes at `h`. -/
def reduce : List Instr :=
  fr .esi fX ++ (List.range c.w).flatMap c.subWord ++ ([.alu .sbb .edx (.reg .edx)] : List Instr) ++
    (List.range c.w).flatMap c.selWord

/-- The `Q` bytes at `esp + o`, as a big-endian number, shifted right by `s`
bits in place (`0 < s < 32`), through the words at `scratch + sSlot` (with
`scratch` in `edi`). -/
def conv (o s : Nat) : List Instr :=
  fr .esi o ++ Impl.Weierstrass.X86.loadBytes c.len (c.w / 2) sSlot .esi ++
    Impl.Weierstrass.X86.shrWords (c.w / 2) sSlot s ++ ([.mov .ecx (.imm (BitVec.allOnes 32))] : List Instr) ++
    Impl.Weierstrass.X86.storeBytes c.len (c.w / 2) .esp o sSlot

/-- The arguments of the copy of `core`'s digest, if `big`: it cleared;
then `ecx = D`, the digest in `esi` and `fXc + Q - 1 - D` in `ebx`. -/
def xcArgs : List Instr :=
  zero18 fXc ++
    ([.mov .ecx (.mem (stk fDl)), .mov .ebx (.reg .esp),
      .alu .add .ebx (.imm (BitVec.ofNat 32 (fXc + c.len - 1))), .alu .sub .ebx (.reg .ecx),
      .mov .esi (argM 2)] : List Instr)

/-- If `big`: `core`'s digest, `Q - 1 - D` zero bytes, the digest and a zero
byte, shifted right by `8 - sh` bits: the digest's integer shifted left by
`sh` bits. -/
def prepC : Prog isa := .seq (.block c.xcArgs) (.seq cpLoop (.block (scrPtr ++ c.conv fXc (8 - c.sh))))

/-- `h`: `reduce`, or, if `big`, `X` itself, with `core`'s digest. -/
def prepH : Prog isa := if c.big then c.prepC else .block c.reduce

/-- `V = 0x01…`, `K = 0x00…`, all 64 bytes of each. -/
def initKV : List Instr :=
  ([.mov .eax (.imm 0x01010101), .mov .ecx (.imm 0)] : List Instr) ++
    (List.range 16).flatMap fun j => [.store (stk (fV + 4 * j)) .eax, .store (stk (fK + 4 * j)) .ecx]

/-- The candidates left. -/
def initCnt : List Instr :=
  [.mov .eax (.imm (BitVec.ofNat 32 c.tries)), .store (stk fCnt) .eax]

/-! ## The candidates -/

/-- `T` empty. -/
def tInit : List Instr := [.mov .eax (.imm 0), .store (stk fTlen) .eax]

/-- The arguments of `V`'s copy to the end of `T`: `V` in `esi`, `T + |T|`
in `ebx` and `ecx = D`. -/
def keepArgs : List Instr :=
  fr .esi fV ++ fr .ebx fT ++ ([.alu .add .ebx (.mem (stk fTlen)), .mov .ecx (.mem (stk fDl))] : List Instr)

/-- `T` longer by `D` bytes, and the carry flag set iff it is still shorter
than `Q`. -/
def tStep : List Instr :=
  [.mov .eax (.mem (stk fTlen)), .alu .add .eax (.mem (stk fDl)), .store (stk fTlen) .eax,
    .alu .cmp .eax (.imm (BitVec.ofNat 32 c.len))]

/-- One `V` of the candidate: `V = HMAC_K(V)`, appended to `T`. -/
def candStep : Prog isa := .seq c.hmacVR (.seq (.block keepArgs) (.seq cpLoop (.block c.tStep)))

/-- If `big`: `T`'s first `Q` bytes shifted right by `sh` bits. -/
def candTop : List Instr := if c.big then scrPtr ++ c.conv fT c.sh else []

/-- The candidate: `T`, the `V`s of successive `V = HMAC_K(V)` while it is
shorter than `Q` bytes, its leftmost `Q` bytes shifted right by `sh` bits if
`big`. -/
def cand : Prog isa := .seq (.block tInit) (.seq (.loop c.candStep .b) (.block c.candTop))

/-- `core(out, d, digest, k, scratch)`'s arguments: `edi`, `esi`, `edx`,
`ecx`, `ebp`, with the digest `X` (or, if `big`, the one at `fXc`) and
`k = T`. -/
def coreArgs : List Instr :=
  ([.mov .edi (argM 0), .mov .esi (argM 1)] : List Instr) ++ fr .edx c.fDg ++ fr .ecx fT ++
    ([.mov .ebp (argM 4)] : List Instr)

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
  (.seq (.frame (.push init5) (.call c.coreN c.coreC) (.pop .ecx 5))
  (.seq (.block goOn)
    (.ite .ne (.seq c.rekey (.block again)) (.block stop)))))

/-- The words of the frame above `B`. -/
def high : Nat := (frameBytes - fTlen) / 4

/-- `K`, `V` and the frame above `B` cleared (`eax`, the result, kept), and
our caller's registers back. -/
def wipe : List Instr :=
  ([.mov .ecx (.imm 0)] : List Instr) ++ (List.range 32).map (fun j => .store (stk (4 * j)) .ecx) ++
    (List.range high).map (fun j => .store (stk (fTlen + 4 * j)) .ecx) ++ restoreRegs

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block entry)
  (.seq c.prepX
  (.seq c.prepH
  (.seq (.block initKV)
  (.seq (c.rekeyFull 0)
  (.seq (c.rekeyFull 1)
  (.seq (.block c.initCnt)
  (.seq (.loop c.tryOne .ne)
    (.block wipe))))))))

/-- `vg_ecdsa_<curve>_sign`. -/
def sign : Prog isa := .frame (.alloc frameBytes) c.body (.free frameBytes)

end Cfg

/-- `vg_ecdsa_<curve>_sign`. -/
def signCode (c : Cfg) : Prog isa := c.sign

end VG.Impl.Ecdsa.Rfc6979.X86
