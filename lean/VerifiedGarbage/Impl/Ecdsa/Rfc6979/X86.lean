import VerifiedGarbage.Impl.Pbkdf2.Whole.X86

/-!
# Deterministic ECDSA (RFC 6979) on x86 (32-bit)

`sign R H core (out, d, digest, scratch) -> eax`, every argument on the
stack (cdecl), as on x86-64 and AArch64 (`Impl/Ecdsa/Rfc6979/X86_64.lean`):
RFC 6979 §3.2 for a curve of `Q = 4 w` byte scalars (`w ≤ 12` words: 8 for
P-256, 12 for P-384) and a Merkle–Damgård hash function `H` whose output is
`D` bytes, `Q ≤ D ≤ 64`, a multiple of 8, with HMAC computed by calling
`H`'s HMAC `init`, streaming `update` and HMAC `finalize`, and each
candidate tried by calling `core`, the signature with a given `k`
(`vg_ecdsa_<curve>_sign`), which reads the leftmost `Q` bytes of `V` and of
the digest.

A frame of 196 bytes is allocated: from `esp`, `K` and `V` (64 bytes each,
of which the first `D` are used), `h` (48 bytes), the number of candidates
left, and our caller's `ebx`, `esi`, `edi` and `ebp`, which the calls'
arguments use. Our arguments stay where our caller put them, above the
frame and the return address (`argM`). Each call passes its arguments in a
frame of their own, pushed last to first (cdecl), which its pop loads into a
register (`ecx` for `core`, whose result is `eax`). The calls use only
`scratch`, which `core` overwrites entirely, and the stack below the frame
(48 bytes for HMAC's functions, besides their arguments and return
address); `K`, `V` and `h` are cleared before the frame is freed. In
`scratch`, as on x86-64: HMAC's inner and outer streaming states, the
working space of HMAC's and `H`'s functions, and the message of steps d, f
and h.3.

1. `h = bits2octets(digest)`: the leftmost `Q` bytes, minus `n` if they are
   at least `n` (a conditional subtraction, as `2^(8 Q) < 2n`): the bytes, as
   `w` 32-bit words, go to `h`'s place and `h - n` to `K`'s, and a mask
   of the borrow selects between them, word by word, big-endian into `h`.
2. Steps b to g: `V = 0x01…`, `K = 0x00…`, `K = HMAC_K(V ‖ 0x00 ‖ d ‖ h)`,
   `V = HMAC_K(V)`, `K = HMAC_K(V ‖ 0x01 ‖ d ‖ h)`, `V = HMAC_K(V)`.
3. At most `tries` times: `V = HMAC_K(V)`, the candidate `k = V`, and
   `core(out, d, digest, V, scratch)`; if it failed and candidates are left,
   `K = HMAC_K(V ‖ 0x00)`, `V = HMAC_K(V)` and again. Whether to go on is
   computed without branches, so that the code branches only on it: the
   number of candidates tried is all it reveals.

`core` writes the signature or zeros to `out`, and its return value is ours.

A block addresses memory only at `esp` or at a pointer an earlier block
loaded from our arguments (`digestPtr`, `msgPtrs`), never one it loads
itself, so that the taint analysis of each block knows its addresses are
public.
-/

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
/-- The frame's size, a multiple of 4. -/
def frameBytes : Nat := 196

/-- Our argument `i` (`out`, `d`, `digest`, `scratch`), above the frame and
the return address. -/
def argM (i : Nat) : Src := .mem (stk (frameBytes + 4 + 4 * i))

/-! Where things are in `scratch`. -/
def sInner : Nat := 0
def sOuter : Nat := 192
def sWork : Nat := 384
def sMsg : Nat := 2256

/-- Our caller's registers, where the frame keeps them. -/
def saved : List (Reg × Nat) := [(.ebx, fSave), (.esi, fSave + 4), (.edi, fSave + 8), (.ebp, fSave + 12)]

/-- What the code needs of a curve and a hash function. -/
structure Cfg where
  /-- The hash function's streaming `update`, and HMAC's `init` and
  `finalize` with their working space as an argument (the functions
  PBKDF2's code calls). -/
  F : Impl.Pbkdf2.Whole.X86.Fns
  /-- The 32-bit words of the curve's scalars. -/
  w : Nat
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
def scr (d : Reg) (a : Nat) : List Instr := [.mov d (argM 3), .alu .add d (.imm (BitVec.ofNat 32 a))]

/-- `d ← esp + o`: an address in the frame. -/
def fr (d : Reg) (o : Nat) : List Instr := [.mov d (.reg .esp), .alu .add d (.imm (BitVec.ofNat 32 o))]

/-- Our caller's registers into the frame. -/
def save : List Instr := saved.map fun (r, d) => .store (stk d) r

/-- Our caller's registers back. -/
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (stk d))

/-- The arguments of HMAC's `init`: the states (`edi`, `esi`), the key `K`
of `D` bytes (`edx`, `ecx`), the working space (`ebp`). -/
def hmacArgs₁ (D : Nat) : List Instr :=
  scr .edi sInner ++ scr .esi sOuter ++ fr .edx fK ++ [.mov .ecx (.imm (BitVec.ofNat 32 D))] ++ scr .ebp sWork

/-- The arguments of the streaming `update`: the inner state (`edi`), the
`B` bytes it holds (`esi`, and `eax` the high word), the data (at the
address `dataA` sets `edx` to) of `len` bytes (`ecx`), the working space
(`ebp`). -/
def hmacArgs₂ (B : Nat) (dataA : List Instr) (len : Nat) : List Instr :=
  scr .edi sInner ++ [.mov .esi (.imm (BitVec.ofNat 32 B)), .mov .eax (.imm 0)] ++ dataA ++
    [.mov .ecx (.imm (BitVec.ofNat 32 len))] ++ scr .ebp sWork

/-- The arguments of HMAC's `finalize`: the states (`edx`, `esi`), the
`B + len` bytes the inner one holds (`eax`, and `ecx` the high word), the
MAC's place in the frame (`edi`), the working space (`ebp`). -/
def hmacArgs₃ (B len dst : Nat) : List Instr :=
  scr .edx sInner ++ scr .esi sOuter ++ [.mov .eax (.imm (BitVec.ofNat 32 (B + len))), .mov .ecx (.imm 0)] ++
    fr .edi dst ++ scr .ebp sWork

/-- `HMAC_K(data)` into the frame at `dst`, for `len` bytes of `data` at the
address `dataA` sets `edx` to: HMAC's `init` with the key `K`, `update` on
the inner state, and `finalize`. -/
def hmac (dataA : List Instr) (len dst : Nat) : Prog isa :=
  .seq (.block (hmacArgs₁ c.F.H.D))
  (.seq (.frame (.push [.ebp, .ecx, .edx, .esi, .edi]) (.call c.F.hiN c.F.hiC) (.pop .eax 5))
  (.seq (.block (hmacArgs₂ c.F.H.B dataA len))
  (.seq (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call c.F.H.updN c.F.H.updC) (.pop .eax 6))
  (.seq (.block (hmacArgs₃ c.F.H.B len dst))
    (.frame (.push [.ebp, .edi, .ecx, .eax, .esi, .edx]) (.call c.F.hfN c.F.hfC) (.pop .eax 6))))))

/-- `V = HMAC_K(V)`. -/
def hmacV : Prog isa := c.hmac (fr .edx fV) c.F.H.D fV

/-- The `4 k` bytes at `[src + so]` to `[dst + d]`, a word at a time through `eax`. -/
def copyN (k : Nat) (src : Reg) (so : Nat) (dst : Reg) (d : Nat) : List Instr :=
  (List.range k).flatMap fun j =>
    [.mov .eax (.mem (at_ src (so + 4 * j))), .store (at_ dst (d + 4 * j)) .eax]

/-- The pointers the messages need: `scratch` in `edi`, `d` in `esi` (loaded
first, so that every address the message's block computes is from them or
`esp`). -/
def msgPtrs : List Instr := [.mov .edi (argM 3), .mov .esi (argM 1)]

/-- The message `V ‖ b` (and `‖ d ‖ h` if `full`, `w` words each) at
`scratch + sMsg`, for `V` of `D` bytes, with `scratch` in `edi` and `d` in
`esi`: `V` and `h` from the frame, `b` a byte. -/
def msg (w D b : Nat) (full : Bool) : List Instr :=
  copyN (D / 4) .esp fV .edi sMsg ++
    [.mov .eax (.imm (BitVec.ofNat 32 b)), .store8 (at_ .edi (sMsg + D)) .al] ++
    (if full then copyN w .esi 0 .edi (sMsg + D + 1) ++ copyN w .esp fH .edi (sMsg + D + 1 + 4 * w)
    else [])

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
def rekeyFull (b : Nat) : Prog isa :=
  .seq (.block msgPtrs) (.seq (.block (msg c.w c.F.H.D b true))
    (.seq (c.hmac (scr .edx sMsg) (c.F.H.D + 8 * c.w + 1) fK) c.hmacV))

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
def rekey : Prog isa :=
  .seq (.block msgPtrs) (.seq (.block (msg c.w c.F.H.D 0 false))
    (.seq (c.hmac (scr .edx sMsg) (c.F.H.D + 1) fK) c.hmacV))

/-- The 32-bit words of `n`, least significant first. -/
def nWord (j : Nat) : BitVec 32 := BitVec.ofNat 32 (c.n >>> (32 * j))

/-- `digest` in `esi`. -/
def digestPtr : List Instr := [.mov .esi (argM 2)]

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
  (List.range c.w).flatMap c.subWord ++ [.alu .sbb .edx (.reg .edx)] ++ (List.range c.w).flatMap c.selWord

/-- `V = 0x01…`, `K = 0x00…`, all 64 bytes of each. -/
def initKV : List Instr :=
  [.mov .eax (.imm 0x01010101), .mov .ecx (.imm 0)] ++
    (List.range 16).flatMap fun j => [.store (stk (fV + 4 * j)) .eax, .store (stk (fK + 4 * j)) .ecx]

/-- The candidates left. -/
def initCnt : List Instr :=
  [.mov .eax (.imm (BitVec.ofNat 32 c.tries)), .store (stk fCnt) .eax]

/-- `core(out, d, digest, k = V, scratch)`'s arguments: `edi`, `esi`,
`edx`, `ecx`, `ebp`. -/
def coreArgs : List Instr :=
  [.mov .edi (argM 0), .mov .esi (argM 1), .mov .edx (argM 2)] ++ fr .ecx fV ++ [.mov .ebp (argM 3)]

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

/-- One candidate: `V = HMAC_K(V)`, `core` with `k = V`, then, if it failed
and candidates are left, step h.3. -/
def tryOne : Prog isa :=
  .seq c.hmacV
  (.seq (.block coreArgs)
  (.seq (.frame (.push [.ebp, .ecx, .edx, .esi, .edi]) (.call c.coreN c.coreC) (.pop .ecx 5))
  (.seq (.block goOn)
    (.ite .ne (.seq c.rekey (.block again)) (.block stop)))))

/-- `K`, `V` and `h` cleared (`eax`, the result, kept), and our caller's
registers back. -/
def wipe : List Instr :=
  [.mov .ecx (.imm 0)] ++ (List.range 44).map (fun j => .store (stk (4 * j)) .ecx) ++ restore

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block (save ++ digestPtr))
  (.seq (.block (c.reduce ++ initKV))
  (.seq (c.rekeyFull 0)
  (.seq (c.rekeyFull 1)
  (.seq (.block c.initCnt)
  (.seq (.loop c.tryOne .ne)
    (.block wipe))))))

/-- `vg_ecdsa_<curve>_<hash>_sign`. -/
def sign : Prog isa :=
  .frame (.alloc frameBytes) c.body (.free frameBytes)

end Cfg

end VG.Impl.Ecdsa.Rfc6979.X86
