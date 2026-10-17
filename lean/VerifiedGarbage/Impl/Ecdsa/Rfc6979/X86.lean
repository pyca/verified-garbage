module

public import VerifiedGarbage.Impl.Pbkdf2.Whole.X86
public import VerifiedGarbage.Impl.Weierstrass.X86
public import VerifiedGarbage.Impl.Dispatch.X86

/-!
# Deterministic ECDSA (RFC 6979) on x86 (32-bit), with the hash function as an argument

`sign R fns core (out, d, digest, digest_len, scratch, hash) -> eax`, every
argument on the stack (cdecl): RFC 6979 §3.2 for a curve of `Q`-byte
scalars (`w` 32-bit words, unless `sh ≠ 0`) and `qlen = 8 Q - sh` bits, and
the Merkle–Damgård hash function numbered `hash` (`Spec/HashId.lean`), one
of the keys of `fns`, whose output is `D` bytes (a multiple of 4, at most
64) and blocks `B` bytes. HMAC is computed by calling that hash function's
HMAC `init`, streaming `update` and HMAC `finalize`, each through a dispatch
on `hash` (`Impl/Dispatch/X86.lean`, with `hash` in `ebx`, which none of
the calls takes); each candidate is tried by calling `core`, the signature
with a given `k` (`vg_ecdsa_<curve>_sign`), which reads `Q` bytes of the
digest and of `k`, and takes the digest's leftmost `qlen` bits (`bits2int`,
a right shift by `sh` bits).

What depends on the hash function is computed once, by a dispatch on
`hash` (`setup`): its sizes (`D`, `B`, the lengths of HMAC's messages, and
`nb`, the number of `V`s that make a candidate), stored in the frame, from
which the code loads them, and the digest for `core`, `X` (`Q` bytes in the
frame): the digest's leftmost `Q` bytes if `Q ≤ D` (then `sh = 0`),
otherwise the digest after `Q - D` zero bytes, shifted left by `sh` bits
(which, for `sh ≠ 0`, is the digest after `Q - D - 1` zero bytes and before
one, shifted right by `8 - sh` bits), whose integer is `bits2int` of the
digest. Then `h = bits2octets(digest)` is `X` modulo `n` (a conditional
subtraction, as `2^(8 Q) < 2n`) if `sh = 0`; otherwise (the digest is
shorter than `n`) the digest after `Q - D` zero bytes, which `setup` writes.

A frame of 460 bytes is allocated: from `esp`, `K` and `V` (64 bytes each,
of which the first `D` are used), the hash function's sizes (eight words),
the offset and count of the candidate's `V`s, the number of candidates left,
our caller's `ebx`, `esi`, `edi` and `ebp`, which the calls' arguments use;
then `h`, `X` (68 bytes each) and the candidate (128 bytes). Our arguments
stay where our caller put them, above the frame and the return address
(`argM`). Each call passes its arguments in a frame of their own, pushed
last to first (cdecl), which its pop loads into a register (`ecx` for
`core`, whose result is `eax`). The calls use only `scratch`, which `core`
overwrites entirely, and the stack below the frame (48 bytes for HMAC's
functions, besides their arguments and return address); `K`, `V`, `h`, `X`
and the candidate are cleared before the frame is freed. In `scratch`: HMAC's
inner and outer streaming states, the working space of HMAC's and the hash
function's functions, the message of steps d, f and h.3, and the words of the
conversions.

1. `setup` (the sizes, and `X`; and `h` if `sh ≠ 0`), then, if `sh = 0`,
   `h`: `X`, as `w` 32-bit words, to `h`'s place and `X - n` to `K`'s, and
   a mask of the borrow selects between them, word by word, big-endian into
   `h`; if `sh ≠ 0`, `X` shifted right by `8 - sh` bits.
2. Steps b to g: `V = 0x01…`, `K = 0x00…`, `K = HMAC_K(V ‖ 0x00 ‖ d ‖ h)`,
   `V = HMAC_K(V)`, `K = HMAC_K(V ‖ 0x01 ‖ d ‖ h)`, `V = HMAC_K(V)`.
3. At most `tries` times: `nb` times `V = HMAC_K(V)`, each copied after the
   previous ones (64 bytes at a time, at an offset that grows by `D`); the
   candidate `k` is their first `Q` bytes, shifted right by `sh` bits; and
   `core(out, d, X, k, scratch)`; if it failed and candidates are left,
   `K = HMAC_K(V ‖ 0x00)`, `V = HMAC_K(V)` and again. Whether to go on is
   computed without branches, so that the code branches only on it, on the
   number of `V`s and on `hash`: the number of candidates tried and the hash
   function are all it reveals.

`core` writes the signature or zeros to `out`, and its return value is ours.

A block addresses memory only at `esp`, at `esp` plus a constant, or at a
pointer an earlier block loaded or computed (`digestPtr`, `msgPtrs`,
`vAt`, `candAt`, `scrPtr`), never one it loads itself, so that the taint
analysis of each block knows its addresses are public.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Rfc6979.X86

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (at_)
open VG.Impl.Pbkdf2.Whole.X86 (Fns)

/-- `[esp + d]`, in the frame. -/
def stk (d : Nat) : MemOp := { base := .esp, disp := d }

/-! Where things are in the frame. -/
def fK : Nat := 0
def fV : Nat := 64
/-- The hash function's sizes: `D`, `B`, `D + 1`, `D + 1 + 2 Q`, `B + D`,
`B + D + 1`, `B + D + 1 + 2 Q` and `nb`. -/
def pD : Nat := 128
def pB : Nat := 132
def pL1 : Nat := 136
def pLF : Nat := 140
def pF0 : Nat := 144
def pF1 : Nat := 148
def pFF : Nat := 152
def pNb : Nat := 156
/-- The offset of the next `V` in the candidate, and the `V`s left. -/
def pOff : Nat := 160
def pCnt2 : Nat := 164
def fCnt : Nat := 176
def fSave : Nat := 180
def fH : Nat := 196
def fX : Nat := 264
def fC : Nat := 332
/-- The frame's size. -/
def frameBytes : Nat := 460

/-- Our argument `i` (`out`, `d`, `digest`, `digest_len`, `scratch`,
`hash`), above the frame and the return address. -/
def argM (i : Nat) : Src := .mem (stk (frameBytes + 4 + 4 * i))

/-! Where things are in `scratch`. -/
def sInner : Nat := 0
def sOuter : Nat := 192
def sWork : Nat := 384
def sMsg : Nat := 2256
/-- The words of a conversion, if `sh ≠ 0`. -/
def sSlot : Nat := 2560

/-- Our caller's registers, where the frame keeps them. -/
def saved : List (Reg × Nat) := [(.ebx, fSave), (.esi, fSave + 4), (.edi, fSave + 8), (.ebp, fSave + 12)]

/-- What the code needs of a curve and of the hash functions. -/
structure Cfg where
  /-- For each hash function, by its number: its streaming `update`, and
  HMAC's `init` and `finalize` with their working space as an argument (the
  functions PBKDF2's code calls). -/
  fns : List (Nat × Fns)
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

/-- `d ← esp + o`: an address in the frame. -/
def fr (d : Reg) (o : Nat) : List Instr := [.mov d (.reg .esp), .alu .add d (.imm (BitVec.ofNat 32 o))]

/-- `d ← scratch + a`: an address in `scratch`. -/
def scr (d : Reg) (a : Nat) : List Instr := [.mov d (argM 4), .alu .add d (.imm (BitVec.ofNat 32 a))]

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

/-- `k` zero words at `esp + o`. -/
def zeroN (k o : Nat) : List Instr :=
  .mov .eax (.imm 0) :: (List.range k).map fun j => .store (stk (o + 4 * j)) .eax

/-- Our caller's registers into the frame. -/
def save : List Instr := saved.map fun (r, d) => .store (stk d) r

/-- Our caller's registers back. -/
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (stk d))

/-- `hash` in `ebx`, for a dispatch. -/
def selArg : List Instr := [.mov .ebx (argM 5)]

/-- The arguments of HMAC's `init`: the states (`edi`, `esi`), the key `K`
of `D` bytes (`edx`, `ecx`), the working space (`ebp`); and `hash`. -/
def hmacArgs₁ : List Instr :=
  scr .edi sInner ++ scr .esi sOuter ++ fr .edx fK ++ ([.mov .ecx (.mem (stk pD))] : List Instr) ++
    scr .ebp sWork ++ selArg

/-- The arguments of the streaming `update`: the inner state (`edi`), the
`B` bytes it holds (`esi`, and `eax` the high word), the data (at the
address `dataA` sets `edx` to), of the length at `[esp + lenS]` (`ecx`), the
working space (`ebp`); and `hash`. -/
def hmacArgs₂ (dataA : List Instr) (lenS : Nat) : List Instr :=
  scr .edi sInner ++ ([.mov .esi (.mem (stk pB)), .mov .eax (.imm 0)] : List Instr) ++ dataA ++
    ([.mov .ecx (.mem (stk lenS))] : List Instr) ++ scr .ebp sWork ++ selArg

/-- The arguments of HMAC's `finalize`: the states (`edx`, `esi`), the bytes
the inner one holds, at `[esp + totS]` (`eax`, and `ecx` the high word), the
MAC's place in the frame (`edi`), the working space (`ebp`); and `hash`. -/
def hmacArgs₃ (totS dst : Nat) : List Instr :=
  scr .edx sInner ++ scr .esi sOuter ++
    ([.mov .eax (.mem (stk totS)), .mov .ecx (.imm 0)] : List Instr) ++ fr .edi dst ++ scr .ebp sWork ++ selArg

/-- The arguments of HMAC's `init`, `update` and `finalize`, pushed last
to first, once around the dispatch (`Cfg.framed`). -/
abbrev hiPush : List Reg := [.ebp, .ecx, .edx, .esi, .edi]
abbrev updPush : List Reg := [.ebp, .ecx, .edx, .eax, .esi, .edi]
abbrev hfPush : List Reg := [.ebp, .edi, .ecx, .eax, .esi, .edx]

/-- The calls of HMAC's `init`, `update` and `finalize` of a hash function. -/
def hiCall (F : Fns) : Prog isa := .call F.hiN F.hiC
def updCall (F : Fns) : Prog isa := .call F.H.updN F.H.updC
def hfCall (F : Fns) : Prog isa := .call F.hfN F.hfC

/-- `V` copied at `esp + o`, 64 bytes, from the frame, with `dst` its base. -/
def copyV (dst : Reg) (d : Nat) : List Instr := copyN 16 .esp fV dst d

/-- The message `V ‖ b` (and `‖ d ‖ h` if `full`, `Q` bytes each) at
`scratch + sMsg`, with `scratch + D` in `edi` and `d` in `esi`: the byte
`b`, then the private key and `h` copied from the frame. (`V` is copied
before, `msgV`.) -/
def msgTail (Q b : Nat) (full : Bool) : List Instr :=
  ([.mov .eax (.imm (BitVec.ofNat 32 b)), .store8 (at_ .edi sMsg) .al] : List Instr) ++
    (if full then copyBytes Q .esi 0 .edi (sMsg + 1) ++ copyBytes Q .esp fH .edi (sMsg + 1 + Q) else [])

/-- `V`'s 64 bytes to `scratch + sMsg`, with `scratch` in `edi`, then
`edi ← scratch + D`. -/
def msgV : List Instr := copyV .edi sMsg ++ [.alu .add .edi (.mem (stk pD))]

/-- The pointers the messages need: `scratch` in `edi`, and `d` in `esi`. -/
def msgPtrs : List Instr := [.mov .edi (argM 4), .mov .esi (argM 1)]

/-- `edi ← esp + fC + off`: where the next `V` of the candidate goes. -/
def candAt : List Instr := fr .edi fC ++ [.alu .add .edi (.mem (stk pOff))]

/-- `V` after the candidate's previous ones, the offset of the next one, and
one `V` fewer: `ZF` clear iff more are left. -/
def candStep : List Instr :=
  copyV .edi 0 ++
    [.mov .eax (.mem (stk pOff)), .alu .add .eax (.mem (stk pD)), .store (stk pOff) .eax,
      .mov .ecx (.mem (stk pCnt2)), .alu .sub .ecx (.imm 1), .store (stk pCnt2) .ecx,
      .alu .test .ecx (.reg .ecx)]

/-- The offset 0 and the count `nb` of the candidate's `V`s. -/
def candInit : List Instr :=
  [.mov .eax (.imm 0), .store (stk pOff) .eax, .mov .eax (.mem (stk pNb)), .store (stk pCnt2) .eax]

/-- `scratch` in `edi`. -/
def scrPtr : List Instr := [.mov .edi (argM 4)]

/-- `digest` in `esi`. -/
def digestPtr : List Instr := [.mov .esi (argM 2)]

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

/-- `V = 0x01…`, `K = 0x00…`, all 64 bytes of each. -/
def initKV : List Instr :=
  ([.mov .eax (.imm 0x01010101), .mov .ecx (.imm 0)] : List Instr) ++
    (List.range 16).flatMap fun j => [.store (stk (fV + 4 * j)) .eax, .store (stk (fK + 4 * j)) .ecx]

/-- `core(out, d, X, k, scratch)`'s arguments: `edi`, `esi`, `edx`, `ecx`,
`ebp`, with `X` and the candidate `k` in the frame. -/
def coreArgs : List Instr :=
  ([.mov .edi (argM 0), .mov .esi (argM 1)] : List Instr) ++ fr .edx fX ++ fr .ecx fC ++
    ([.mov .ebp (argM 4)] : List Instr)

/-- `K`, `V`, `h`, `X` and the candidate cleared (`eax`, the result, kept),
and our caller's registers back. -/
def wipe : List Instr :=
  ([.mov .ecx (.imm 0)] : List Instr) ++ (List.range 32).map (fun j => .store (stk (4 * j)) .ecx) ++
    (List.range 66).map (fun j => .store (stk (fH + 4 * j)) .ecx) ++ restore

namespace Cfg

variable (c : Cfg)

/-- The case of `fns` of the hash function in `ebx`, each made by `mk`. -/
def calls (mk : Fns → Prog isa) : Prog isa := Dispatch.X86.chain .ebx (c.fns.map fun p => (p.1, mk p.2))

/-- The call of the hash function in `ebx` that `mk` makes, in one frame of
the arguments `rs` around the dispatch, whose cases are bare calls. -/
def framed (rs : List Reg) (mk : Fns → Prog isa) : Prog isa := .frame (.push rs) (c.calls mk) (.pop .eax rs.length)

/-- `HMAC_K(data)` into the frame at `dst`, for the data at the address
`dataA` sets `edx` to, of the length at `[esp + lenS]` (the bytes the inner
state then holds at `[esp + totS]`): HMAC's `init` with the key `K`,
`update` on the inner state, and `finalize`. -/
def hmac (dataA : List Instr) (lenS totS dst : Nat) : Prog isa :=
  .seq (.block hmacArgs₁) (.seq (c.framed hiPush hiCall)
  (.seq (.block (hmacArgs₂ dataA lenS)) (.seq (c.framed updPush updCall)
  (.seq (.block (hmacArgs₃ totS dst)) (c.framed hfPush hfCall)))))

/-- `V = HMAC_K(V)`. -/
def hmacV : Prog isa := c.hmac (fr .edx fV) pD pF0 fV

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
def rekeyFull (b : Nat) : Prog isa :=
  .seq (.block msgPtrs) (.seq (.block msgV) (.seq (.block (msgTail c.len b true))
    (.seq (c.hmac (scr .edx sMsg) pLF pFF fK) c.hmacV)))

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
def rekey : Prog isa :=
  .seq (.block msgPtrs) (.seq (.block msgV) (.seq (.block (msgTail c.len 0 false))
    (.seq (c.hmac (scr .edx sMsg) pL1 pF1 fK) c.hmacV)))

/-- The 32-bit words of `n`, least significant first. -/
def nWord (j : Nat) : BitVec 32 := BitVec.ofNat 32 (c.n >>> (32 * j))

/-- The `Q` bytes at `esp + o`, as a big-endian number, shifted right by `s`
bits in place (`0 < s < 32`), through the words at `scratch + sSlot` (with
`scratch` in `edi`). -/
def conv (o s : Nat) : List Instr :=
  fr .esi o ++ Impl.Weierstrass.X86.loadBytes c.len ((c.len + 7) / 8) sSlot .esi ++
    Impl.Weierstrass.X86.shrWords ((c.len + 7) / 8) sSlot s ++ ([.mov .ecx (.imm (BitVec.allOnes 32))] : List Instr) ++
    Impl.Weierstrass.X86.storeBytes c.len ((c.len + 7) / 8) .esp o sSlot

/-- The number of `V`s that make a candidate, for a hash function of `D`-byte
values: the least `nb` with `8 D nb ≥ qlen`. -/
def nb (D : Nat) : Nat := (8 * c.len - c.sh + 8 * D - 1) / (8 * D)

/-- The hash function's sizes, for its functions `F`. -/
def sizes (F : Fns) : List (Nat × Nat) :=
  [(pD, F.H.D), (pB, F.H.B), (pL1, F.H.D + 1), (pLF, F.H.D + 1 + 2 * c.len), (pF0, F.H.B + F.H.D),
    (pF1, F.H.B + F.H.D + 1), (pFF, F.H.B + F.H.D + 1 + 2 * c.len), (pNb, c.nb F.H.D)]

/-- The sizes into the frame. -/
def storeSizes (F : Fns) : List Instr :=
  (c.sizes F).flatMap fun p => [.mov .eax (.imm (BitVec.ofNat 32 p.2)), .store (stk p.1) .eax]

/-- The digest (at `esi`), for a hash function of `D`-byte values: `X`, its
leftmost `Q` bytes if `Q ≤ D`; otherwise the digest after `Q - D` zero bytes,
or, if `sh ≠ 0`, after `Q - D - 1` and before one, and `h`, the digest after
`Q - D` zero bytes. -/
def digestX (D : Nat) : List Instr :=
  if c.len ≤ D then copyN (c.len / 4) .esi 0 .esp fX
  else if c.sh = 0 then zeroN 17 fX ++ copyN (D / 4) .esi 0 .esp (fX + c.len - D)
  else zeroN 17 fH ++ copyN (D / 4) .esi 0 .esp (fH + c.len - D) ++
    zeroN 17 fX ++ copyN (D / 4) .esi 0 .esp (fX + c.len - D - 1)

/-- What depends on the hash function in `ebx`: its sizes, and `X` (and `h`
if `sh ≠ 0`), from the digest at `esi`. -/
def setup : Prog isa := c.calls fun F => .block (c.storeSizes F ++ c.digestX F.H.D)

/-- Word `j` (least significant first) of `X`, as a big-endian number, to
`h`'s place, and that word of the difference with `n` (`sub` for the first,
`sbb` for the others) to `K`'s: both at the offset of the word's bytes. -/
def subWord (j : Nat) : List Instr :=
  [.mov .eax (.mem (stk (fX + 4 * (c.w - 1 - j)))), .bswap .eax, .store (stk (fH + 4 * (c.w - 1 - j))) .eax,
    .alu (if j = 0 then .sub else .sbb) .eax (.imm (c.nWord j)), .store (stk (fK + 4 * (c.w - 1 - j))) .eax]

/-- Word `j` of `h`: of `X`'s number if subtracting `n` borrowed (the mask
in `edx`), of the difference if not, big-endian into `h`. -/
def selWord (j : Nat) : List Instr :=
  [.mov .eax (.mem (stk (fH + 4 * (c.w - 1 - j)))), .mov .ecx (.mem (stk (fK + 4 * (c.w - 1 - j)))),
    -- `x = d ^ ((x ^ d) & mask)`: `x` if it borrowed, `d` if not.
    .alu .xor .eax (.reg .ecx), .alu .and .eax (.reg .edx), .alu .xor .eax (.reg .ecx),
    .bswap .eax, .store (stk (fH + 4 * (c.w - 1 - j))) .eax]

/-- `h`: `X`, minus `n` if that does not borrow. -/
def reduce : List Instr :=
  (List.range c.w).flatMap c.subWord ++ ([.alu .sbb .edx (.reg .edx)] : List Instr) ++ (List.range c.w).flatMap c.selWord

/-- `h` and `X`, after `setup`, and `V` and `K`: `h = X mod n` if `sh = 0`;
otherwise `X` shifted right by `8 - sh` bits, with `scratch` in `edi`. -/
def prep : Prog isa :=
  if c.sh = 0 then .block (c.reduce ++ initKV)
  else .seq (.block scrPtr) (.block (c.conv fX (8 - c.sh) ++ initKV))

/-- The candidates left. -/
def initCnt : List Instr :=
  [.mov .eax (.imm (BitVec.ofNat 32 c.tries)), .store (stk fCnt) .eax]

/-- The candidate: `nb` times `V = HMAC_K(V)`, each after the previous ones;
then, if `sh ≠ 0`, their first `Q` bytes shifted right by `sh` bits. -/
def cand : Prog isa :=
  .seq (.block candInit)
  (.seq (.loop (.seq c.hmacV (.seq (.block candAt) (.block candStep))) .ne)
    (if c.sh = 0 then .block [] else .seq (.block scrPtr) (.block (c.conv fC c.sh))))

/-- One candidate: `cand`, `core` with it, then, if it failed and candidates
are left, step h.3. -/
def tryOne : Prog isa :=
  .seq c.cand
  (.seq (.block coreArgs)
  (.seq (.frame (.push [.ebp, .ecx, .edx, .esi, .edi]) (.call c.coreN c.coreC) (.pop .ecx 5))
  (.seq (.block goOn)
    (.ite .ne (.seq c.rekey (.block again)) (.block stop)))))

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block (save ++ selArg ++ digestPtr))
  (.seq c.setup
  (.seq c.prep
  (.seq (c.rekeyFull 0)
  (.seq (c.rekeyFull 1)
  (.seq (.block c.initCnt)
  (.seq (.loop c.tryOne .ne)
    (.block wipe)))))))

/-- `vg_ecdsa_<curve>_rfc6979_sign`. -/
def sign : Prog isa :=
  .frame (.alloc frameBytes) c.body (.free frameBytes)

end Cfg

end VG.Impl.Ecdsa.Rfc6979.X86
