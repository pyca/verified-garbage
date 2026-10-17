module

public import VerifiedGarbage.Impl.Pbkdf2.Md.X86_64
public import VerifiedGarbage.Impl.Weierstrass.X86_64
public import VerifiedGarbage.Impl.Dispatch.X86_64

/-!
# Deterministic ECDSA (RFC 6979) on x86-64, with the hash function as an argument

`sign (out = rdi, d = rsi, digest = rdx, digest_len = rcx, scratch = r8,
hash = r9) -> eax`, for a curve of `Q`-byte scalars in `w` words and the
Merkle–Damgård hash functions `hs` (each with its number, `HashId.hmac`):
RFC 6979 §3.2, with HMAC computed by calling the HMAC `init`, streaming
`update` and HMAC `finalize` of the hash function that `hash` names, and each
candidate tried by calling `core`, the signature with a given `k`
(`vg_ecdsa_<curve>_sign`), which reads `Q` bytes of its digest and of `k`,
and takes its digest's leftmost `qlen` bits (`bits2int`, a right shift by
`sh = 8 Q - qlen` bits). `digest_len` is the hash function's output length
`D` (a precondition), which the code takes from `hash` instead.

The hash function is public. Each call of one of its functions is a dispatch
on `hash` (`Dispatch.X86_64.chain`), each case a direct call; its output
length `D` and block size `B` are chosen once, by a dispatch before the
frame is pushed, and kept in the frame, from which every length that depends
on them is computed. The only other code that depends on the hash function
is the digest's conversion (`prepCase`), whose copies depend on `D`, which
is a dispatch of its own.

* `h = bits2octets(digest)` (RFC 6979 §2.3.4): with `X` the digest's `Q`
  leftmost bytes, or the digest after `Q - D` zero bytes if it is shorter,
  `bits2int(digest)` is `X`'s integer for every curve but P-521's (`wide`,
  whose digest is always shorter), so `h` is `X`, minus `n` if it is at least
  `n` (a conditional subtraction, as `2^(8 Q) < 2n`). `core`'s digest is `X`.
  If `wide`, `X`'s integer is below `n`, so `h` is `X`; and `core`'s digest
  is `X` shifted left by `sh` bits, made from the digest after
  `Q - D - 1` zero bytes and before one (`X` shifted left by 8), shifted right
  by `8 - sh` bits.
* Each candidate is the leftmost `Q` bytes of `T`, the concatenation of
  enough successive `V = HMAC_K(V)` (`ceil(Q / D)`, which is RFC 6979's
  `ceil(qlen / 8 D)`), shifted right by `sh` bits: a loop appends each `V` to
  the candidate (all 64 bytes of `V`'s place, of which the next `V` then
  overwrites what follows its first `D`), at the offset `off`, until
  `off ≥ Q`.

Everything runs in one stack frame of 65 words, pushed from `rax` (`hash`),
`r10` (`D`), `r11` (`B`), 35 copies of `rax`, `rdi`, `rsi`, `rdx`, `rcx`
(`scratch`) and 23 copies of `rax`: from `rsp`, `K` and `V` (64 bytes each,
of which the first `D` are used), the candidate's offset, the number of
candidates left, then `scratch`, `digest`, `d` and `out`, `core`'s digest
(`Y`, 72 bytes), `h` (72), the candidate (`C`, 136), and `B`, `D` and
`hash`. The calls use only `scratch`, which `core` overwrites entirely, and
the 24 bytes below the frame; `K`, `V`, `h`, `Y` and the candidate are
cleared before the frame is popped. In `scratch`: HMAC's inner and outer
streaming states (256 bytes each), the working space of HMAC's and the hash
function's functions (2048 bytes), the message of steps d, f and h.3, and the
words of a shift (if `wide`).

1. `h` and `core`'s digest, as above.
2. Steps b to g: `V = 0x01…`, `K = 0x00…`, `K = HMAC_K(V ‖ 0x00 ‖ d ‖ h)`,
   `V = HMAC_K(V)`, `K = HMAC_K(V ‖ 0x01 ‖ d ‖ h)`, `V = HMAC_K(V)`.
3. At most `tries` times: the candidate `k`, and
   `core(out, d, Y, k, scratch)`; if it failed and candidates are left,
   `K = HMAC_K(V ‖ 0x00)`, `V = HMAC_K(V)` and again. Whether to go on is
   computed without branches, so that the code branches only on it: the
   number of candidates tried is all it reveals.

`core` writes the signature or zeros to `out`, and its return value is ours.

A block addresses memory only at `rsp`, at `rsp` plus a constant, or at a
pointer or offset an earlier block loaded from the frame (`digestPtr`,
`msgPtrs`, `scrPtr`, `offLd`), never one it loads itself, so that the taint
analysis of each block knows its addresses are public.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Rfc6979.X86_64

open VG.X86_64 VG.Impl.Pbkdf2.Md.X86_64

/-- `[rsp + d]`, in the frame. -/
def stk (d : Nat) : MemOp := { base := .rsp, disp := d }

/-- `[b + d]`. -/
def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-! Where things are in the frame. -/
def fK : Nat := 0
def fV : Nat := 64
/-- The candidate's offset: the bytes of `T` made so far. -/
def fOff : Nat := 128
def fCnt : Nat := 176
def fScratch : Nat := 184
def fDigest : Nat := 192
def fD : Nat := 200
def fOut : Nat := 208
/-- Above the pointers: `core`'s digest, `h`, the candidate. -/
def fY : Nat := 216
def fH : Nat := 288
def fC : Nat := 360
/-- The hash function's block size, output length and number. -/
def fBS : Nat := 496
def fHL : Nat := 504
def fSel : Nat := 512

/-! Where things are in `scratch`. -/
def sInner : Nat := 0
def sOuter : Nat := 256
def sWork : Nat := 512
def sMsg : Nat := 2560
/-- The words of a shift, if `wide`. -/
def sSlot : Nat := 2816

/-- The words of the frame above its pointers, but for `B`, `D` and `hash`. -/
def extra : Nat := 35

/-- What the code needs of a curve and the hash functions. -/
structure Cfg where
  /-- The hash functions' code and names, each with its number. -/
  hs : List (Nat × Hash)
  /-- The words of the curve's scalars. -/
  w : Nat
  /-- The bytes of the curve's scalars, `Q`. -/
  len : Nat := 8 * w
  /-- Whether the scalars are longer than any hash function's output, and
  `nBits` is not `8 Q` (P-521's). -/
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

/-- `rax ← hash`, for a dispatch. -/
def selLd : List Instr := [.mov .rax (.mem (stk fSel))]

/-- The call of the function `f` gives of the hash function `hash` names. -/
def callH (f : Hash → String × Prog isa) : Prog isa :=
  Dispatch.X86_64.chain (c.hs.map fun p => (p.1, .call (f p.2).1 (f p.2).2))

/-- `d ← [rsp + o] + a`: an address in `scratch`. -/
def scr (d : Reg) (a : Nat) : List Instr :=
  [.mov d (.mem (stk fScratch)), .alu .add d (.imm (BitVec.ofNat 32 a))]

/-- `d ← rsp + o`: an address in the frame. -/
def fr (d : Reg) (o : Nat) : List Instr :=
  [.mov d (.reg .rsp), .alu .add d (.imm (BitVec.ofNat 32 o))]

/-- The arguments of HMAC's `init`: the states, the key `K` of `D` bytes,
the working space; and `hash`. -/
def hmacArgs₁ : List Instr :=
  scr .rdi sInner ++ scr .rsi sOuter ++ fr .rdx fK ++ ([.mov .rcx (.mem (stk fHL))] : List Instr) ++
    scr .r8 sWork ++ selLd

/-- The arguments of the streaming `update`: the inner state, the `B` bytes
it holds, the data (at the address `dataA` sets `rdx` to) of `D + e` bytes,
the working space; and `hash`. -/
def hmacArgs₂ (dataA : List Instr) (e : Nat) : List Instr :=
  scr .rdi sInner ++ ([.mov .rsi (.mem (stk fBS))] : List Instr) ++ dataA ++
    ([.mov .rcx (.mem (stk fHL)), .alu .add .rcx (.imm (BitVec.ofNat 32 e))] : List Instr) ++
    scr .r8 sWork ++ selLd

/-- The arguments of HMAC's `finalize`: the states, the `B + D + e` bytes
the inner one holds, the MAC's place in the frame, the working space; and
`hash`. -/
def hmacArgs₃ (e dst : Nat) : List Instr :=
  scr .rdi sInner ++ scr .rsi sOuter ++
    ([.mov .rdx (.mem (stk fBS)), .alu .add .rdx (.mem (stk fHL)), .alu .add .rdx (.imm (BitVec.ofNat 32 e))] :
      List Instr) ++ fr .rcx dst ++ scr .r8 sWork ++ selLd

/-- `HMAC_K(data)` into the frame at `dst`, for `D + e` bytes of `data` at
the address `dataA` sets `rdx` to: HMAC's `init` with the key `K`, `update`
on the inner state, and `finalize`, each of the hash function `hash` names. -/
def hmac (dataA : List Instr) (e dst : Nat) : Prog isa :=
  .seq (.block hmacArgs₁)
  (.seq (c.callH fun H => (H.hmacInitN, H.hmacInit))
  (.seq (.block (hmacArgs₂ dataA e))
  (.seq (c.callH fun H => (H.updN, H.updC))
  (.seq (.block (hmacArgs₃ e dst))
    (c.callH fun H => (H.hmacFinN, H.hmacFin))))))

/-- `V = HMAC_K(V)`. -/
def hmacV : Prog isa := c.hmac (fr .rdx fV) 0 fV

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

/-- The pointers the messages need: `scratch` in `rdi`, `d` in `rsi`, and
`D` in `rdx` (loaded first, so that every address the message's block
computes is from them or `rsp`). -/
def msgPtrs : List Instr :=
  [.mov .rdi (.mem (stk fScratch)), .mov .rsi (.mem (stk fD)), .mov .rdx (.mem (stk fHL))]

/-- The message `V ‖ b` (and `‖ d ‖ h` if `full`, `Q` bytes each) at
`scratch + sMsg`, for `V` of `D` bytes, with `scratch` in `rdi`, `d` in
`rsi` and `D` in `rdx`: all 64 bytes of `V`'s place (the rest of which `b`,
`d` and `h` overwrite, or follow the message), then `b` at `scratch + sMsg +
D` (`rdx`, from then on), `d` and `h` from the frame. -/
def msg (Q b : Nat) (full : Bool) : List Instr :=
  copyN 8 .rsp fV .rdi sMsg ++
    ([.alu .add .rdx (.reg .rdi), .mov32 .rax (.imm (BitVec.ofNat 32 b)), .store8 (at_ .rdx sMsg) .rax] :
      List Instr) ++
    (if full then copyBytes Q .rsi 0 .rdx (sMsg + 1) ++ copyBytes Q .rsp fH .rdx (sMsg + 1 + Q) else [])

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
def rekeyFull (b : Nat) : Prog isa :=
  .seq (.block msgPtrs) (.seq (.block (msg c.len b true))
    (.seq (c.hmac (scr .rdx sMsg) (2 * c.len + 1) fK) c.hmacV))

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
def rekey : Prog isa :=
  .seq (.block msgPtrs) (.seq (.block (msg c.len 0 false))
    (.seq (c.hmac (scr .rdx sMsg) 1 fK) c.hmacV))

/-- The 64-bit words of `n`, least significant first. -/
def nWord (j : Nat) : BitVec 64 := BitVec.ofNat 64 (c.n >>> (64 * j))

/-- `digest` in `rsi`, `scratch` in `rdi`. -/
def digestPtr : List Instr := [.mov .rsi (.mem (stk fDigest)), .mov .rdi (.mem (stk fScratch))]

/-- `scratch` in `rdi`. -/
def scrPtr : List Instr := [.mov .rdi (.mem (stk fScratch))]

/-- The `Q` bytes at `rsp + o`, as a big-endian number, shifted right by `s`
bits in place, through the words at `scratch + sSlot` (with `scratch` in
`rdi`). -/
def conv (o s : Nat) : List Instr :=
  fr .rsi o ++ Impl.Weierstrass.X86_64.loadBytes c.len c.w sSlot .rsi ++
    Impl.Weierstrass.X86_64.shrWords c.w sSlot s ++ ([.movImm64 .rcx (BitVec.allOnes 64)] : List Instr) ++
    Impl.Weierstrass.X86_64.storeBytes c.len c.w .rsp o sSlot

/-- `core`'s digest (and, if `wide`, `h`) cleared, and `hash` in `rax`. -/
def prepZero : List Instr :=
  ([.alu32 .xor .rcx (.reg .rcx)] : List Instr) ++
    (List.range (if c.wide then 18 else 9)).map (fun j => .store (stk (fY + 8 * j)) .rcx) ++ selLd

/-- The digest (at `rsi`) to `core`'s digest (and `h`), for a hash function
of `D`-byte output: if `wide`, after `Q - D - 1` zero bytes (and `Q - D` in
`h`); otherwise its `min D Q` leftmost bytes, after `Q - min D Q`. -/
def prepCase (D : Nat) : List Instr :=
  if c.wide then copyBytes D .rsi 0 .rsp (fY + (c.len - D - 1)) ++ copyBytes D .rsi 0 .rsp (fH + (c.len - D))
  else copyBytes (min D c.len) .rsi 0 .rsp (fY + (c.len - min D c.len))

/-- Word `j` of the `Q`-byte number at `rsi`, least significant first, in
`rax`: the byte reversal of the word at `rsi + Q - 8 (j + 1)`, or, for a top
word of four bytes (`Q % 8 = 4`), of the first four, zero-extended, or zero
beyond the number. None changes the flags, which carry the borrow from one
word to the next. -/
def loadWord (j : Nat) : List Instr :=
  if 8 * (j + 1) ≤ c.len then [.mov .rax (.mem (at_ .rsi (c.len - 8 * (j + 1)))), .bswap .rax]
  else if c.len ≤ 8 * j then [.mov .rax (.imm 0)]
  else [.mov32 .rax (.mem (at_ .rsi 0)), .bswap32 .rax]

/-- Word `j` of the number at `rsi`, least significant first, to `V`'s place,
and word `j` of it minus `n` (with the borrow of the words before) to
`K`'s: `rax` and `rdx` change, and the borrow is the carry flag. -/
def subWord (j : Nat) : List Instr :=
  c.loadWord j ++ ([.store (stk (fV + 8 * j)) .rax,
    .movImm64 .rdx (c.nWord j), .alu (if j = 0 then .sub else .sbb) .rax (.reg .rdx),
    .store (stk (fK + 8 * j)) .rax] : List Instr)

/-- Word `j` of the result, by the mask `rdx` (all ones if subtracting `n`
borrowed): the number's word if so, the difference's if not, big-endian to
`h + Q - 8 (j + 1)`. A top word of fewer bytes is stored below `h`, in the
last bytes of `core`'s digest's place (beyond its `Q`), its zero bytes there
and the rest `h`'s first bytes. -/
def selWord (j : Nat) : List Instr :=
  [.mov .rax (.mem (stk (fV + 8 * j))), .mov .rcx (.mem (stk (fK + 8 * j))), .alu .xor .rax (.reg .rcx),
    .alu .and .rax (.reg .rdx), .alu .xor .rax (.reg .rcx), .bswap .rax,
    .store (stk (fH + c.len - 8 * (j + 1))) .rax]

/-- `h`: the `Q` bytes at `rsi`, as a big-endian number, minus `n` if that
does not borrow, big-endian into the frame's `Q` bytes at `h`. -/
def reduce : List Instr :=
  (List.range c.w).flatMap c.subWord ++ ([.alu .sbb .rdx (.reg .rdx)] : List Instr) ++ (List.range c.w).flatMap c.selWord

/-- After the digest's copies: unless `wide`, `h` from `core`'s digest; if
`wide`, `core`'s digest shifted right by `8 - sh` bits. -/
def prepPost : List Instr :=
  if c.wide then c.conv fY (8 - c.sh) else fr .rsi fY ++ c.reduce

/-- `h` and `core`'s digest, from the digest (at `rsi`, with `scratch` in `rdi`). -/
def prep : Prog isa :=
  .seq (.block c.prepZero)
  (.seq (Dispatch.X86_64.chain (c.hs.map fun p => (p.1, .block (c.prepCase p.2.D))))
    (.block c.prepPost))

/-- `V = 0x01…`, `K = 0x00…`, all 64 bytes of each. -/
def initKV : List Instr :=
  ([.movImm64 .rax (BitVec.ofNat 64 0x0101010101010101), .alu32 .xor .rcx (.reg .rcx)] : List Instr) ++
    (List.range 8).flatMap fun j => [.store (stk (fV + 8 * j)) .rax, .store (stk (fK + 8 * j)) .rcx]

/-- The candidates left. -/
def initCnt : List Instr :=
  [.mov32 .rax (.imm (BitVec.ofNat 32 c.tries)), .store (stk fCnt) .rax]

/-- The candidate's offset, 0. -/
def offInit : List Instr := [.alu32 .xor .rax (.reg .rax), .store (stk fOff) .rax]

/-- The candidate's offset in `rdx`. -/
def offLd : List Instr := [.mov .rdx (.mem (stk fOff))]

/-- `V`'s 64 bytes to the candidate at the offset (in `rdx`), and the offset
`D` more; the carry flag set iff it is still below `Q`. -/
def appendV : List Instr :=
  ([.alu .add .rdx (.reg .rsp)] : List Instr) ++ copyN 8 .rsp fV .rdx fC ++
    [.mov .rcx (.mem (stk fOff)), .alu .add .rcx (.mem (stk fHL)), .store (stk fOff) .rcx,
      .alu .cmp .rcx (.imm (BitVec.ofNat 32 c.len))]

/-- One `V` of the candidate: `V = HMAC_K(V)`, appended. -/
def candStep : Prog isa := .seq c.hmacV (.seq (.block offLd) (.block c.appendV))

/-- The candidate `k`: the leftmost `Q` bytes of the successive
`V = HMAC_K(V)`, until there are `Q`, shifted right by `sh` bits. -/
def cand : Prog isa :=
  .seq (.block offInit)
    (if c.sh = 0 then .loop c.candStep .b
    else .seq (.loop c.candStep .b) (.seq (.block scrPtr) (.block (c.conv fC c.sh))))

/-- `core(out, d, Y, k, scratch)`. -/
def coreArgs : List Instr :=
  ([.mov .rdi (.mem (stk fOut)), .mov .rsi (.mem (stk fD))] : List Instr) ++ fr .rdx fY ++ fr .rcx fC ++
    ([.mov .r8 (.mem (stk fScratch))] : List Instr)

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
  (.seq (.block coreArgs)
  (.seq (.call c.coreN c.coreC)
  (.seq (.block goOn)
    (.ite .ne (.seq c.rekey (.block again)) (.block stop)))))

/-- `K`, `V`, the offset and the count cleared, and the words above the
pointers but for `B`, `D` and `hash` (`rax`, the result, kept). -/
def wipe : List Instr :=
  ([.alu32 .xor .rcx (.reg .rcx)] : List Instr) ++ (List.range 22).map (fun j => .store (stk (8 * j)) .rcx) ++
    (List.range extra).map fun j => .store (stk (fY + 8 * j)) .rcx

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block digestPtr)
  (.seq c.prep
  (.seq (.block initKV)
  (.seq (c.rekeyFull 0)
  (.seq (c.rekeyFull 1)
  (.seq (.block c.initCnt)
  (.seq (.loop c.tryOne .ne)
    (.block wipe)))))))

/-- The registers the frame is pushed from. -/
def pushRs : List Reg :=
  [.rax, .r10, .r11] ++ List.replicate extra .rax ++ [.rdi, .rsi, .rdx, .rcx] ++ List.replicate 23 .rax

/-- `scratch` in `rcx`, `hash` (zero-extended from 32 bits) in `rax`. -/
def entry : List Instr := [.mov .rcx (.reg .r8), .mov32 .rax (.reg .r9)]

/-- `D` in `r10` and `B` in `r11`, for a hash function of output length `D`
and block size `B`. -/
def sizes (D B : Nat) : List Instr :=
  [.mov32 .r10 (.imm (BitVec.ofNat 32 D)), .mov32 .r11 (.imm (BitVec.ofNat 32 B))]

/-- `vg_ecdsa_<curve>_rfc6979_sign`. -/
def sign : Prog isa :=
  .seq (.block entry)
  (.seq (Dispatch.X86_64.chain (c.hs.map fun p => (p.1, .block (sizes p.2.D p.2.P.B))))
    (.frame (.push pushRs) c.body (.pop .rcx 65)))

end Cfg

end VG.Impl.Ecdsa.Rfc6979.X86_64
