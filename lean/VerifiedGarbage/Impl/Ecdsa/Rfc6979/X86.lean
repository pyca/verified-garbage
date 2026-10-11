module

public import VerifiedGarbage.Impl.Pbkdf2.Whole.X86
public import VerifiedGarbage.Impl.Weierstrass.X86

/-!
# Deterministic ECDSA (RFC 6979) on x86 (32-bit)

`sign R H core (out, d, digest, scratch) -> eax`, every argument on the
stack (cdecl), as on x86-64 and AArch64 (`Impl/Ecdsa/Rfc6979/X86_64.lean`):
RFC 6979 §3.2 for a curve of `Q`-byte scalars in `w` 32-bit words and a
Merkle–Damgård hash function `H` whose output is `D` bytes, a multiple of 8,
at most 64, with HMAC computed by calling `H`'s HMAC `init`, streaming
`update` and HMAC `finalize`, and each candidate tried by calling `core`,
the signature with a given `k` (`vg_ecdsa_<curve>_sign`), which reads `Q`
bytes of the digest and of `k`, and takes the digest's leftmost `qlen` bits
(`bits2int`, a right shift by `sh = 8 Q - qlen` bits).

Two kinds of curve and hash function, as on x86-64:

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
  32-bit words at `scratch + sSlot` (`loadBytes`, `shrWords`, `storeBytes`).

A frame of 196 bytes is allocated, 340 if `wide`: from `esp`, `K` and `V`
(64 bytes each, of which the first `D` are used), `h` (48 bytes, unless
`wide`), the number of candidates left, and our caller's `ebx`, `esi`,
`edi` and `ebp`, which the calls' arguments use; and, if `wide`, the digest
for `core` and the candidate (72 bytes each). Our arguments stay where our
caller put them, above the frame and the return address (`argM`). Each call
passes its arguments in a frame of their own, pushed last to first (cdecl),
which its pop loads into a register (`ecx` for `core`, whose result is
`eax`). The calls use only `scratch`, which `core` overwrites entirely, and
the stack below the frame (48 bytes for HMAC's functions, besides their
arguments and return address); `K`, `V`, `h` and, if `wide`, the digest for
`core` and the candidate are cleared before the frame is freed. In
`scratch`, as on x86-64: HMAC's inner and outer streaming states, the
working space of HMAC's and `H`'s functions, the message of steps d, f and
h.3, and the words of the conversions.

1. `h = bits2octets(digest)`: unless `wide`, the leftmost `Q` bytes, minus
   `n` if they are at least `n` (a conditional subtraction, as
   `2^(8 Q) < 2n`): the bytes, as `w` 32-bit words, go to `h`'s place and
   `h - n` to `K`'s, and a mask of the borrow selects between them, word by
   word, big-endian into `h`. If `wide`, the digest for `core` instead: the
   digest then `Q - D` zero bytes, shifted right by `8 (Q - D) - sh` bits.
2. Steps b to g: `V = 0x01…`, `K = 0x00…`, `K = HMAC_K(V ‖ 0x00 ‖ d ‖ h)`,
   `V = HMAC_K(V)`, `K = HMAC_K(V ‖ 0x01 ‖ d ‖ h)`, `V = HMAC_K(V)`.
3. At most `tries` times: `V = HMAC_K(V)` (twice if `wide`), the candidate
   `k`, and `core(out, d, digest, k, scratch)`; if it failed and candidates
   are left, `K = HMAC_K(V ‖ 0x00)`, `V = HMAC_K(V)` and again. Whether to
   go on is computed without branches, so that the code branches only on
   it: the number of candidates tried is all it reveals.

`core` writes the signature or zeros to `out`, and its return value is ours.

A block addresses memory only at `esp`, at `esp` plus a constant, or at a
pointer an earlier block loaded from our arguments (`digestPtr`, `msgPtrs`,
`scrPtr`), never one it loads itself, so that the taint analysis of each
block knows its addresses are public.
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
def fH : Nat := 128
def fCnt : Nat := 176
def fSave : Nat := 180
/-- If `wide`: the digest for `core`, and the candidate. -/
def fX : Nat := 196
def fKb : Nat := 268
/-- The words at the frame's top: the digest for `core` and the candidate,
if `wide`. -/
def extra (wide : Bool) : Nat := if wide then 36 else 0
/-- The frame's size, a multiple of 4. -/
def frameBytes (wide : Bool) : Nat := 196 + 4 * extra wide

/-- Our argument `i` (`out`, `d`, `digest`, `scratch`), above the frame and
the return address. -/
def argM (wide : Bool) (i : Nat) : Src := .mem (stk (frameBytes wide + 4 + 4 * i))

/-! Where things are in `scratch`. -/
def sInner : Nat := 0
def sOuter : Nat := 192
def sWork : Nat := 384
def sMsg : Nat := 2256
/-- The words of a conversion, if `wide`. -/
def sSlot : Nat := 2560

/-- Our caller's registers, where the frame keeps them. -/
def saved : List (Reg × Nat) := [(.ebx, fSave), (.esi, fSave + 4), (.edi, fSave + 8), (.ebp, fSave + 12)]

/-- What the code needs of a curve and a hash function. -/
structure Cfg where
  /-- The hash function's streaming `update`, and HMAC's `init` and
  `finalize` with their working space as an argument (the functions
  PBKDF2's code calls). -/
  F : Impl.Pbkdf2.Whole.X86.Fns
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

/-- `d ← scratch + a`: an address in `scratch`. -/
def scr (wide : Bool) (d : Reg) (a : Nat) : List Instr :=
  [.mov d (argM wide 3), .alu .add d (.imm (BitVec.ofNat 32 a))]

/-- `d ← esp + o`: an address in the frame. -/
def fr (d : Reg) (o : Nat) : List Instr := [.mov d (.reg .esp), .alu .add d (.imm (BitVec.ofNat 32 o))]

/-- Our caller's registers into the frame. -/
def save : List Instr := saved.map fun (r, d) => .store (stk d) r

/-- Our caller's registers back. -/
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (stk d))

/-- The arguments of HMAC's `init`: the states (`edi`, `esi`), the key `K`
of `D` bytes (`edx`, `ecx`), the working space (`ebp`). -/
def hmacArgs₁ (wide : Bool) (D : Nat) : List Instr :=
  scr wide .edi sInner ++ scr wide .esi sOuter ++ fr .edx fK ++ ([.mov .ecx (.imm (BitVec.ofNat 32 D))] : List Instr) ++
    scr wide .ebp sWork

/-- The arguments of the streaming `update`: the inner state (`edi`), the
`B` bytes it holds (`esi`, and `eax` the high word), the data (at the
address `dataA` sets `edx` to) of `len` bytes (`ecx`), the working space
(`ebp`). -/
def hmacArgs₂ (wide : Bool) (B : Nat) (dataA : List Instr) (len : Nat) : List Instr :=
  scr wide .edi sInner ++ ([.mov .esi (.imm (BitVec.ofNat 32 B)), .mov .eax (.imm 0)] : List Instr) ++ dataA ++
    ([.mov .ecx (.imm (BitVec.ofNat 32 len))] : List Instr) ++ scr wide .ebp sWork

/-- The arguments of HMAC's `finalize`: the states (`edx`, `esi`), the
`B + len` bytes the inner one holds (`eax`, and `ecx` the high word), the
MAC's place in the frame (`edi`), the working space (`ebp`). -/
def hmacArgs₃ (wide : Bool) (B len dst : Nat) : List Instr :=
  scr wide .edx sInner ++ scr wide .esi sOuter ++
    ([.mov .eax (.imm (BitVec.ofNat 32 (B + len))), .mov .ecx (.imm 0)] : List Instr) ++ fr .edi dst ++ scr wide .ebp sWork

/-- `HMAC_K(data)` into the frame at `dst`, for `len` bytes of `data` at the
address `dataA` sets `edx` to: HMAC's `init` with the key `K`, `update` on
the inner state, and `finalize`. -/
def hmac (dataA : List Instr) (len dst : Nat) : Prog isa :=
  .seq (.block (hmacArgs₁ c.wide c.F.H.D))
  (.seq (.frame (.push [.ebp, .ecx, .edx, .esi, .edi]) (.call c.F.hiN c.F.hiC) (.pop .eax 5))
  (.seq (.block (hmacArgs₂ c.wide c.F.H.B dataA len))
  (.seq (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call c.F.H.updN c.F.H.updC) (.pop .eax 6))
  (.seq (.block (hmacArgs₃ c.wide c.F.H.B len dst))
    (.frame (.push [.ebp, .edi, .ecx, .eax, .esi, .edx]) (.call c.F.hfN c.F.hfC) (.pop .eax 6))))))

/-- `V = HMAC_K(V)`. -/
def hmacV : Prog isa := c.hmac (fr .edx fV) c.F.H.D fV

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

/-- The pointers the messages need: `scratch` in `edi`, `d` in `esi`, and,
if `full` and `wide`, `digest` in `edx` (loaded first, so that every address
the message's block computes is from them or `esp`). -/
def msgPtrs (wide full : Bool) : List Instr :=
  ([.mov .edi (argM wide 3), .mov .esi (argM wide 1)] : List Instr) ++
    (if wide && full then [.mov .edx (argM wide 2)] else [])

/-- The message `V ‖ b` (and `‖ d ‖ h` if `full`, `Q` bytes each) at
`scratch + sMsg`, for `V` of `D` bytes, with `scratch` in `edi`, `d` in
`esi` (and, if `wide`, `digest` in `edx`): `V` from the frame, `b` a byte,
and `h` from the frame, or, if `wide`, `Q - D` zero bytes (a zero word,
which the digest's words then overwrite but for them) and the digest. -/
def msg (Q D b : Nat) (full wide : Bool) : List Instr :=
  copyN (D / 4) .esp fV .edi sMsg ++
    ([.mov .eax (.imm (BitVec.ofNat 32 b)), .store8 (at_ .edi (sMsg + D)) .al] : List Instr) ++
    (if full then
      (if wide then
        copyBytes Q .esi 0 .edi (sMsg + D + 1) ++
          ([.mov .eax (.imm 0), .store (at_ .edi (sMsg + D + 1 + Q)) .eax] : List Instr) ++
          copyN (D / 4) .edx 0 .edi (sMsg + 1 + 2 * Q)
      else copyN (Q / 4) .esi 0 .edi (sMsg + D + 1) ++ copyN (Q / 4) .esp fH .edi (sMsg + D + 1 + Q))
    else [])

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
def rekeyFull (b : Nat) : Prog isa :=
  .seq (.block (msgPtrs c.wide true)) (.seq (.block (msg c.len c.F.H.D b true c.wide))
    (.seq (c.hmac (scr c.wide .edx sMsg) (c.F.H.D + 2 * c.len + 1) fK) c.hmacV))

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
def rekey : Prog isa :=
  .seq (.block (msgPtrs c.wide false)) (.seq (.block (msg c.len c.F.H.D 0 false false))
    (.seq (c.hmac (scr c.wide .edx sMsg) (c.F.H.D + 1) fK) c.hmacV))

/-- The 32-bit words of `n`, least significant first. -/
def nWord (j : Nat) : BitVec 32 := BitVec.ofNat 32 (c.n >>> (32 * j))

/-- `digest` in `esi`, and, if `wide`, `scratch` in `edi`. -/
def digestPtr (wide : Bool) : List Instr :=
  ([.mov .esi (argM wide 2)] : List Instr) ++ (if wide then [.mov .edi (argM wide 3)] else [])

/-- `scratch` in `edi`. -/
def scrPtr (wide : Bool) : List Instr := [.mov .edi (argM wide 3)]

/-- The `Q` bytes at `esp + o`, as a big-endian number, shifted right by `s`
bits in place (`0 < s < 32`), through the words at `scratch + sSlot` (with
`scratch` in `edi`). -/
def conv (o s : Nat) : List Instr :=
  fr .esi o ++ Impl.Weierstrass.X86.loadBytes c.len (c.w / 2) sSlot .esi ++
    Impl.Weierstrass.X86.shrWords (c.w / 2) sSlot s ++ ([.mov .ecx (.imm (BitVec.allOnes 32))] : List Instr) ++
    Impl.Weierstrass.X86.storeBytes c.len (c.w / 2) .esp o sSlot

/-- If `wide`: the digest for `core`, the digest (at `esi`) then `Q - D`
zero bytes, shifted right by `8 (Q - D) - sh` bits: the digest's integer
shifted left by `sh` bits. -/
def coreDigest : List Instr :=
  ([.mov .eax (.imm 0), .store (stk (fX + c.len - 4)) .eax] : List Instr) ++
    copyN (c.F.H.D / 4) .esi 0 .esp fX ++ c.conv fX (8 * (c.len - c.F.H.D) - c.sh)

/-- Word `j` (least significant first) of the `Q` bytes at `digest` (in
`esi`), as a big-endian number, to `h`'s place, and that word of the
difference with `n` (`sub` for the first, `sbb` for the others) to `K`'s:
both at the offset of the word's bytes. -/
def subWord (j : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .esi (4 * (c.w - 1 - j)))), .bswap .eax, .store (stk (fH + 4 * (c.w - 1 - j))) .eax,
    .alu (if j = 0 then .sub else .sbb) .eax (.imm (c.nWord j)), .store (stk (fK + 4 * (c.w - 1 - j))) .eax]

/-- Word `j` of `h`: of the digest's number if subtracting `n` borrowed
(the mask in `edx`), of the difference if not, big-endian into `h`. -/
def selWord (j : Nat) : List Instr :=
  [.mov .eax (.mem (stk (fH + 4 * (c.w - 1 - j)))), .mov .ecx (.mem (stk (fK + 4 * (c.w - 1 - j)))),
    -- `x = d ^ ((x ^ d) & mask)`: `x` if it borrowed, `d` if not.
    .alu .xor .eax (.reg .ecx), .alu .and .eax (.reg .edx), .alu .xor .eax (.reg .ecx),
    .bswap .eax, .store (stk (fH + 4 * (c.w - 1 - j))) .eax]

/-- `h`: the `Q` bytes at `digest` (in `esi`), minus `n` if that does not borrow. -/
def reduce : List Instr :=
  (List.range c.w).flatMap c.subWord ++ ([.alu .sbb .edx (.reg .edx)] : List Instr) ++ (List.range c.w).flatMap c.selWord

/-- `V = 0x01…`, `K = 0x00…`, all 64 bytes of each. -/
def initKV : List Instr :=
  ([.mov .eax (.imm 0x01010101), .mov .ecx (.imm 0)] : List Instr) ++
    (List.range 16).flatMap fun j => [.store (stk (fV + 4 * j)) .eax, .store (stk (fK + 4 * j)) .ecx]

/-- The candidates left. -/
def initCnt : List Instr :=
  [.mov .eax (.imm (BitVec.ofNat 32 c.tries)), .store (stk fCnt) .eax]

/-- `core(out, d, digest, k, scratch)`'s arguments: `edi`, `esi`, `edx`,
`ecx`, `ebp`, with `k = V`, or, if `wide`, the digest and the candidate at
the frame's top. -/
def coreArgs (wide : Bool) : List Instr :=
  ([.mov .edi (argM wide 0), .mov .esi (argM wide 1)] : List Instr) ++
    (if wide then fr .edx fX ++ fr .ecx fKb else .mov .edx (argM wide 2) :: fr .ecx fV) ++
    ([.mov .ebp (argM wide 3)] : List Instr)

/-- If `wide`: `V`'s first `D` bytes to the candidate's place. -/
def keepV : List Instr := copyN (c.F.H.D / 4) .esp fV .esp fKb

/-- If `wide`: the next four bytes of the candidate from `V`, then the
candidate's `Q` bytes shifted right by `sh` bits. -/
def candTop : List Instr :=
  ([.mov .eax (.mem (stk fV)), .store (stk (fKb + c.F.H.D)) .eax] : List Instr) ++ c.conv fKb c.sh

/-- The candidate: `V = HMAC_K(V)`, which is `k`; or, if `wide`, the
leftmost `Q` bytes of `V = HMAC_K(V)` then `V = HMAC_K(V)` again, shifted
right by `sh` bits. -/
def cand : Prog isa :=
  if c.wide then
    .seq c.hmacV (.seq (.block c.keepV) (.seq c.hmacV (.seq (.block (scrPtr true)) (.block c.candTop))))
  else c.hmacV

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
  (.seq (.block (coreArgs c.wide))
  (.seq (.frame (.push [.ebp, .ecx, .edx, .esi, .edi]) (.call c.coreN c.coreC) (.pop .ecx 5))
  (.seq (.block goOn)
    (.ite .ne (.seq c.rekey (.block again)) (.block stop)))))

/-- `K`, `V` and `h` cleared, and the words at the frame's top (`eax`, the
result, kept), and our caller's registers back. -/
def wipe (wide : Bool) : List Instr :=
  ([.mov .ecx (.imm 0)] : List Instr) ++ (List.range 44).map (fun j => .store (stk (4 * j)) .ecx) ++
    (List.range (extra wide)).map (fun j => .store (stk (fX + 4 * j)) .ecx) ++ restore

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block (save ++ digestPtr c.wide))
  (.seq (.block ((if c.wide then c.coreDigest else c.reduce) ++ initKV))
  (.seq (c.rekeyFull 0)
  (.seq (c.rekeyFull 1)
  (.seq (.block c.initCnt)
  (.seq (.loop c.tryOne .ne)
    (.block (wipe c.wide)))))))

/-- `vg_ecdsa_<curve>_<hash>_sign`. -/
def sign : Prog isa :=
  .frame (.alloc (frameBytes c.wide)) c.body (.free (frameBytes c.wide))

end Cfg

end VG.Impl.Ecdsa.Rfc6979.X86
