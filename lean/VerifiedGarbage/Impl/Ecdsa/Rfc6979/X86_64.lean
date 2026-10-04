import VerifiedGarbage.Impl.Pbkdf2.Md.X86_64

/-!
# Deterministic ECDSA (RFC 6979) on x86-64

`sign R H core (out = rdi, d = rsi, digest = rdx, scratch = rcx) -> eax`, for
a curve of `Q = 8 w` byte scalars (`w ≤ 6` words: 4 for P-256, 6 for P-384)
and a Merkle–Damgård hash function `H` whose output is `D` bytes,
`Q ≤ D ≤ 64`, a multiple of 8 (one `V` makes a candidate: `blocks = 1`):
RFC 6979 §3.2, with HMAC computed by calling `H`'s HMAC `init`, streaming
`update` and HMAC `finalize`, and each candidate tried by calling `core`, the
signature with a given `k` (`vg_ecdsa_<curve>_sign`), which reads the
leftmost `Q` bytes of `V` and of the digest (their leftmost `8 Q` bits,
`bits2int`).

Everything runs in one stack frame of 27 words, pushed from `rdi`, `rsi`,
`rdx`, `rcx` and 23 copies of `rax`: from `rsp`, `K` and `V` (64 bytes each,
of which the first `D` are used), `h` (the hash's leftmost `Q` bytes reduced
modulo `n`, `bits2octets`, in 48 bytes), the number of candidates left, then
`scratch`, `digest`, `d` and `out`. The layout is the same for every hash
function. The calls use only `scratch`, which `core` overwrites entirely,
and the frame, which they cannot change; `K`, `V` and `h` are cleared before
the frame is popped. In `scratch`: HMAC's inner and outer streaming states,
the working space of HMAC's and `H`'s functions (each at the size SHA-512's
need), and the message of steps d, f and h.3.

1. `h = bits2octets(digest)`: the leftmost `Q` bytes, minus `n` if they are
   at least `n` (a conditional subtraction, as `2^(8 Q) < 2n`), a word at a
   time through memory: the words of the digest to `V`'s place, those of
   the difference to `K`'s (before steps b and c set them), and the one
   the borrow selects, big-endian, to `h`.
2. Steps b to g: `V = 0x01…`, `K = 0x00…`, `K = HMAC_K(V ‖ 0x00 ‖ d ‖ h)`,
   `V = HMAC_K(V)`, `K = HMAC_K(V ‖ 0x01 ‖ d ‖ h)`, `V = HMAC_K(V)`.
3. At most `tries` times: `V = HMAC_K(V)`, the candidate `k = V`, and
   `core(out, d, digest, V, scratch)`; if it failed and candidates are left,
   `K = HMAC_K(V ‖ 0x00)`, `V = HMAC_K(V)` and again. Whether to go on is
   computed without branches, so that the code branches only on it: the
   number of candidates tried is all it reveals.

`core` writes the signature or zeros to `out`, and its return value is ours.

A block addresses memory only at `rsp` or at a pointer an earlier block
loaded from the frame (`digestPtr`, `msgPtrs`), never one it loads itself,
so that the taint analysis of each block knows its addresses are public.
The blocks that depend on the hash function depend only on `D` and its block
size `B` (`hmacArgs₁`, `hmacArgs₂`, `hmacArgs₃`, `msg`), so that the taint
analysis checks them for each size.
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

/-! Where things are in `scratch`. -/
def sInner : Nat := 0
def sOuter : Nat := 192
def sWork : Nat := 384
def sMsg : Nat := 2256

/-- What the code needs of a curve and a hash function. -/
structure Cfg where
  /-- The hash function's code and names. -/
  H : Hash
  /-- The words of the curve's scalars. -/
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

/-- The pointers the messages need: `scratch` in `rdi`, `d` in `rsi` (loaded
first, so that every address the message's block computes is from them or
`rsp`). -/
def msgPtrs : List Instr := [.mov .rdi (.mem (stk fScratch)), .mov .rsi (.mem (stk fD))]

/-- The message `V ‖ b` (and `‖ d ‖ h` if `full`, `w` words each) at
`scratch + sMsg`, for `V` of `D` bytes, with `scratch` in `rdi` and `d` in
`rsi`: `V` and `h` from the frame, `b` a byte. -/
def msg (w D b : Nat) (full : Bool) : List Instr :=
  copyN (D / 8) .rsp fV .rdi sMsg ++
    [.mov32 .rax (.imm (BitVec.ofNat 32 b)), .store8 (at_ .rdi (sMsg + D)) .rax] ++
    (if full then copyN w .rsi 0 .rdi (sMsg + D + 1) ++ copyN w .rsp fH .rdi (sMsg + D + 1 + 8 * w)
    else [])

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
def rekeyFull (b : Nat) : Prog isa :=
  .seq (.block msgPtrs) (.seq (.block (msg c.w c.H.D b true))
    (.seq (c.hmac (scr .rdx sMsg) (c.H.D + 16 * c.w + 1) fK) c.hmacV))

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
def rekey : Prog isa :=
  .seq (.block msgPtrs) (.seq (.block (msg c.w c.H.D 0 false))
    (.seq (c.hmac (scr .rdx sMsg) (c.H.D + 1) fK) c.hmacV))

/-- The 64-bit words of `n`, least significant first. -/
def nWord (j : Nat) : BitVec 64 := BitVec.ofNat 64 (c.n >>> (64 * j))

/-- `digest` in `rsi`. -/
def digestPtr : List Instr := [.mov .rsi (.mem (stk fDigest))]

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

/-- `core(out, d, digest, k = V, scratch)`. -/
def coreArgs : List Instr :=
  [.mov .rdi (.mem (stk fOut)), .mov .rsi (.mem (stk fD)), .mov .rdx (.mem (stk fDigest))] ++
    fr .rcx fV ++ [.mov .r8 (.mem (stk fScratch))]

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

/-- One candidate: `V = HMAC_K(V)`, `core` with `k = V`, then, if it failed
and candidates are left, step h.3. -/
def tryOne : Prog isa :=
  .seq c.hmacV
  (.seq (.block coreArgs)
  (.seq (.call c.coreN c.coreC)
  (.seq (.block goOn)
    (.ite .ne (.seq c.rekey (.block again)) (.block stop)))))

/-- `K`, `V` and `h` cleared (`rax`, the result, kept). -/
def wipe : List Instr :=
  [.alu32 .xor .rcx (.reg .rcx)] ++ (List.range 22).map fun j => .store (stk (8 * j)) .rcx

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block digestPtr)
  (.seq (.block (c.reduce ++ initKV))
  (.seq (c.rekeyFull 0)
  (.seq (c.rekeyFull 1)
  (.seq (.block c.initCnt)
  (.seq (.loop c.tryOne .ne)
    (.block wipe))))))

/-- `vg_ecdsa_<curve>_<hash>_sign`. -/
def sign : Prog isa :=
  .frame (.push ([.rdi, .rsi, .rdx, .rcx] ++ List.replicate 23 .rax)) c.body (.pop .rcx 27)

end Cfg

end VG.Impl.Ecdsa.Rfc6979.X86_64
