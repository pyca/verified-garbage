import VerifiedGarbage.Impl.Pbkdf2.Md.X86_64

/-!
# RSASSA-PSS (RFC 8017 §8.1, EMSA-PSS §9.1) on x86-64

`sign` and `verify`, for a Merkle–Damgård hash function `H` (an
`Impl.Pbkdf2.Md.X86_64.Hash`: MD5, SHA-1, SHA-224, SHA-256 or the SHA-512
family) as both the hash function and MGF1's, calling `H`'s compression
function and streaming `init`, and the RSA operation: the private-key
operation checked against `e` (`vg_rsa_private_checked`) when signing, the
public-key operation within BoringSSL's limits (`vg_rsa_public_checked`) when
verifying.

Everything runs in a frame of `frameBytes` bytes: at `rsp`, the stack
arguments of the RSA operation; then the slots, which hold the arguments,
the values computed from the public key and the counters of the loops (the
callees keep no caller-saved register), and our caller's `rbx`, `rbp` and
`r12`, which the hash function's length field and digest code (`P.len`,
`P.out`) use. The first 8192 bytes of `scratch` are ours (`oCW`, …); the
RSA operation gets the rest.

## Hashing a message of secret length (`ctHash`)

The message is the first `ℓ` bytes (`ℓ` in the slot `sL`) of the buffer
`Y` (`scratch + oY`), whose bytes after it are zero up to `nbm` blocks
(`nbm` in `sNb`), with `ℓ + 1 + L ≤ nbm B`. The code depends only on `nbm`,
never on `ℓ`, which verification computes from the signature:

1. `init` sets the hash value to the initial one;
2. `0x80` is ORed into byte `i` of `Y` under the mask of `i = ℓ`, for every
   `i < nbm B`;
3. `P.len` writes the length field of `ℓ` to `scratch + oLen`, and it is
   ORed into the last `L` bytes of block `b` under the mask of
   `b = ⌊(ℓ + L) / B⌋`, the last block of the padded message, for every
   `b < nbm`;
4. every block `b < nbm` is compressed, and the hash value is copied to
   `scratch + oSel` under the mask of `b = ⌊(ℓ + L) / B⌋`;
5. `P.out` writes the digest of that hash value to `scratch + oDig`.

## MGF1 (`mgfXor`)

With `DB` at `scratch + oEm + lo` (`sEb`), `dbLen` bytes (`sDb`), and `H`
after it: for each counter `c`, `Y` is cleared (`mgfNb` blocks: one for every
hash function here), `H ‖ I2OSP(c, 4)` written to it and hashed (`mgfHash`),
and the first
`min(hLen, dbLen - c hLen)` bytes of the digest XORed into `DB` at
`c hLen`.

## The encoding's parameters (`params`)

From `n`'s first byte `n₀`: `n₀ = 0` makes the modulus invalid (both
operations refuse it); otherwise `v = smear(n₀ >> 1)` (every bit below the
top one of `n₀ >> 1`, by three shifts and ORs) is `0xFF >> z` for
`z = 8 emLen - emBits`, unless it is zero (`n₀ = 1`), in which case
`emLen = k - 1` (`lo = 1`) and the mask is `0xFF`.

## Signing

The checks (`n₀ ≠ 0`, `emLen ≥ hLen + 2`, `emLen - hLen - 2 ≥ sLen`) fail
with zeros to `out` and 0. Then `Y = 0⁸ ‖ mHash ‖ salt` is hashed into
`H`; `EM = 0^lo ‖ 0…0 ‖ 0x01 ‖ salt ‖ H ‖ 0xbc` is written to
`scratch + oEm`; MGF1 masks `DB`; its top bits are cleared; and
`vg_rsa_private_checked` is called on it, whose result is ours.

## Verifying

The public checks return 0. Then `vg_rsa_public_checked` writes the
signature's RSAVP1 (or zeros) to `scratch + oEm`, and everything after
depends only on public data: an accumulator `acc` ORs together every
byte or value that is nonzero exactly when a check fails (the leading
zero byte, `0xbc`, the top bits of `maskedDB`); MGF1 unmasks `DB`; the first
nonzero byte of `DB` is found by masks over all of it (`posScan`), and must
be `0x01`, with the salt after it of the expected length if one is; `Y =
0⁸ ‖ mHash ‖ DB` is shifted left by `pos + 1` bytes after its first
`8 + hLen` (`shift`: ten passes, pass `j` moving every byte `2^j` bytes
under the mask of bit `j` of `pos + 1`), leaving `0⁸ ‖ mHash ‖ salt` and
zeros; it is hashed (`ctHash`), and the digest compared with `H`. The
result is 1 if `acc = 0`, computed without a branch.
-/

namespace VG.Impl.RsaPss.X86_64

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

/-- `c₁; c₂; …`. -/
def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-- `[rsp + d]`. -/
def sp (d : Nat) : MemOp := { base := .rsp, disp := (d : Int) }

/-- `[b + i + d]`. -/
def ix (b i : Reg) (d : Nat := 0) : MemOp := { base := b, index := some i, disp := (d : Int) }

/-- `[b + d]`. -/
def at_ (b : Reg) (d : Nat := 0) : MemOp := { base := b, disp := (d : Int) }

/-! ## The frame -/

/-- The frame: the RSA operation's stack arguments (14 words) at `rsp`,
then the slots. `≡ 8 (mod 16)`, so that `rsp` is a multiple of 16 at the
calls. -/
def frameBytes : Nat := 392

def sOut : Nat := 128
def sK : Nat := 136
def sN : Nat := 144
def sE : Nat := 152
def sEl : Nat := 160
def sScr : Nat := 168
def sScrLen : Nat := 176
def sEb : Nat := 184
def sDb : Nat := 192
def sC : Nat := 200
def sLo : Nat := 208
def sL : Nat := 216
def sNb : Nat := 224
def sB : Nat := 232
def sFb : Nat := 240
def sCtr : Nat := 248
def sDone : Nat := 256
def sAcc : Nat := 264
def sPos : Nat := 272
def sAny : Nat := 280
def sSlen : Nat := 288
def sDig : Nat := 296
def sSig : Nat := 304
def sSalt : Nat := 312
def sSaltLen : Nat := 320
def sRbx : Nat := 328
def sRbp : Nat := 336
def sR12 : Nat := 344
def sJ : Nat := 352
def sA : Nat := 360
def sD : Nat := 368

/-- The function's stack argument `j`. -/
def arg (j : Nat) : MemOp := sp (frameBytes + 8 + 8 * j)

/-! ## Our part of `scratch` -/

/-- The compression function's working space (`so` bytes, less than 2048). -/
def oCW : Nat := 0
/-- The streaming state `init` sets: its first `N` bytes are the hash value. -/
def oSt : Nat := 2048
/-- The hash value selected after the last block. -/
def oSel : Nat := 2240
/-- The digest. -/
def oDig : Nat := 2304
/-- The length field. -/
def oLen : Nat := 2368
/-- `EM` (signing), or the signature's RSAVP1 (verifying): `k` bytes. -/
def oEm : Nat := 2560
/-- The message hashed by `ctHash`, and its padding: 2048 bytes. -/
def oY : Nat := 3584
/-- Where the RSA operation's working space starts. -/
def oRsa : Nat := 8192

variable (H : Hash)

/-- `log₂ B`. -/
def lgB : Nat := Nat.log2 H.P.B

/-- `d ← [scratch] + o`. -/
def scr (d : Reg) (o : Nat) : List Instr :=
  [.mov d (.mem (sp sScr)), .alu .add d (.imm (BitVec.ofNat 32 o))]

/-- `d ← -(a = b)`, from `a` (`rax` is used): all ones if `a = b`, zero
otherwise. -/
def eqMask (d a : Reg) (b : Src) : List Instr :=
  [.mov d (.reg a), .alu .xor d b, .alu .cmp d (.imm 1), .alu .sbb d (.reg d)]

/-- `add r8, 1; cmp r8, n`: the counter of a byte loop. -/
def step (n : Src) : List Instr := [.alu .add .r8 (.imm 1), .alu .cmp .r8 n]

/-- A loop over `r8` while it differs from `n` after the step. -/
def byteLoop (body : List Instr) (n : Src) : Prog isa := .loop (.block (body ++ step n)) .ne

/-! ## `ctHash`: hashing a message of secret length -/

/-- `init` on the state at `scratch + oSt`. -/
def ctInit : Prog isa := .seq (.block (scr .rdi oSt)) (.call H.initN H.initC)

/-- `0x80` ORed into byte `ℓ` of `Y`, a mask for each of its `nbm B` bytes. -/
def pad80 : Prog isa :=
  .seq (.block (scr .rcx oY ++ [.mov .rdx (.mem (sp sL)), .mov .r10 (.mem (sp sNb)),
      .shift .ror .r10 (64 - lgB H), .mov32 .r8 (.imm 0)]))
    (byteLoop ([.mov .rax (.reg .r8), .alu .xor .rax (.reg .rdx), .alu .cmp .rax (.imm 1),
      .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 0x80), .movzx8 .r9 (ix .rcx .r8),
      .alu .or .r9 (.reg .rax), .store8 (ix .rcx .r8) .r9]) (.reg .r10))

/-- The length field of `ℓ` to `scratch + oLen` (`P.len` with `rbx` placed
so that it writes there), and the last block's index `⌊(ℓ + L) / B⌋` to
`sFb`. -/
def lenField : List Instr :=
  scr .rbx (oLen - (H.P.N + H.P.B - H.P.L)) ++ [.mov .r12 (.mem (sp sL))] ++ H.P.len ++
    [.mov .rax (.mem (sp sL)), .alu .add .rax (.imm (BitVec.ofNat 32 H.P.L)), .shift .shr .rax (lgB H),
      .store (sp sFb) .rax]

/-- The length field ORed into the last `L` bytes of block `b` (`r8`, the
counter, at `rcx`) under the mask of `b = ⌊(ℓ + L) / B⌋`, for every block. -/
def lenLoop : Prog isa :=
  .seq (.block (scr .rcx (oY + H.P.B - H.P.L) ++ scr .rsi oLen ++
      [.mov .rdx (.mem (sp sFb)), .mov .r10 (.mem (sp sNb)), .mov32 .r8 (.imm 0)]))
    (.loop (.seq (.block (eqMask .r11 .r8 (.reg .rdx) ++ [.mov32 .r9 (.imm 0)]))
      (.seq (.loop (.block [.movzx8 .rax (ix .rsi .r9), .alu .and .rax (.reg .r11), .movzx8 .rdi (ix .rcx .r9),
          .alu .or .rdi (.reg .rax), .store8 (ix .rcx .r9) .rdi, .alu .add .r9 (.imm 1),
          .alu .cmp .r9 (.imm (BitVec.ofNat 32 H.P.L))]) .ne)
        (.block [.alu .add .rcx (.imm (BitVec.ofNat 32 H.P.B)), .alu .add .r8 (.imm 1), .alu .cmp .r8 (.reg .r10)])))
      .ne)

/-- The arguments of the compression function: the hash value at
`scratch + oSt`, block `b` (`sB`) of `Y`, one block, the working space. -/
def compArgs : List Instr :=
  scr .rdi oSt ++ [.mov .rcx (.mem (sp sScr)), .mov .rsi (.mem (sp sB)), .shift .ror .rsi (64 - lgB H),
    .alu .add .rsi (.reg .rcx), .alu .add .rsi (.imm (BitVec.ofNat 32 oY)), .mov32 .rdx (.imm 1)]

/-- The hash value copied to `scratch + oSel` under the mask of
`b = ⌊(ℓ + L) / B⌋`. -/
def select : Prog isa :=
  .seq (.block ([.mov .rcx (.mem (sp sScr)), .mov .rax (.mem (sp sB)), .alu .xor .rax (.mem (sp sFb)),
      .alu .cmp .rax (.imm 1), .alu .sbb .r11 (.reg .r11), .mov32 .r8 (.imm 0)]))
    (byteLoop [.movzx8 .rax (ix .rcx .r8 oSt), .movzx8 .rdx (ix .rcx .r8 oSel), .alu .xor .rax (.reg .rdx),
      .alu .and .rax (.reg .r11), .alu .xor .rdx (.reg .rax), .store8 (ix .rcx .r8 oSel) .rdx]
      (.imm (BitVec.ofNat 32 H.P.N)))

/-- The next block, and ZF set after the last. -/
def nextBlock : List Instr :=
  [.mov .rax (.mem (sp sB)), .alu .add .rax (.imm 1), .store (sp sB) .rax, .mov .rdx (.mem (sp sNb)),
    .alu .cmp .rax (.reg .rdx)]

/-- Every block compressed, the last one's hash value selected. -/
def compLoop : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0), .store (sp sB) .rax])
    (.loop (seqs [.block (compArgs H), .call H.compN H.compC, select H, .block nextBlock]) .ne)

/-- The digest of the selected hash value to `scratch + oDig`. -/
def digestAt (o : Nat) : List Instr := scr .rbx o ++ scr .rbp oDig ++ H.P.out

def digestOut : List Instr := digestAt H oSel

/-- The shared hash computation, with its padding step supplied by the caller. -/
def ctHashWith (padding : Prog isa) : Prog isa :=
  seqs [ctInit H, padding, .block (lenField H), lenLoop H, compLoop H, .block (digestOut H)]

/-- The digest of the first `ℓ` bytes of `Y` (`sL`), padded in `nbm`
blocks (`sNb`), to `scratch + oDig`, without revealing `ℓ`. -/
def ctHash : Prog isa := ctHashWith H (pad80 H)

/-- A fixed-length message needs one padding write, at a public offset. -/
def fixedPad80 (ℓ : Nat) : Prog isa :=
  .seq (.block (scr .rcx oY))
    (.block [.movzx8 .rax (at_ .rcx ℓ), .alu .or .rax (.imm 0x80), .store8 (at_ .rcx ℓ) .rax])

/-- For an MGF1 input whose padding fits one block, use the compression
state directly instead of copying it under a last-block mask. -/
def mgfDirectHash : Prog isa := seqs [ctInit H, fixedPad80 (H.D + 4),
  .block (lenField H), lenLoop H,
  .block [.mov32 .rax (.imm 0), .store (sp sB) .rax],
  .seq (.block (compArgs H)) (.call H.compN H.compC), .block (digestAt H oSt)]

/-- MGF1's message length is fixed by the hash function. -/
def mgfGenericHash : Prog isa := ctHashWith H (fixedPad80 (H.D + 4))

/-- The one-block case is selected at generation time from the hash dimensions. -/
def mgfHash : Prog isa :=
  if H.D + 4 + H.P.L < H.P.B then mgfDirectHash H else mgfGenericHash H

/-! ## MGF1 -/

/-- The blocks MGF1 hashes `H ‖ C` in: `⌊(hLen + 4 + L) / B⌋ + 1`, one for
every hash function here. -/
def mgfNb : Nat := (H.D + 4 + H.P.L) / H.P.B + 1

/-- `Y`'s first `mgfNb` blocks cleared, and `rcx` = `Y`. -/
def clearBlock : Prog isa :=
  .seq (.block (scr .rcx oY ++ [.mov32 .rax (.imm 0), .mov32 .r8 (.imm 0)]))
    (.loop (.block [.store (ix .rcx .r8) .rax, .alu .add .r8 (.imm 8),
      .alu .cmp .r8 (.imm (BitVec.ofNat 32 (mgfNb H * H.P.B)))]) .ne)

/-- `H` (at `DB + dbLen`) to `Y` (in `rcx`). -/
def copyH : Prog isa :=
  .seq (.block [.mov .rsi (.mem (sp sEb)), .mov .r8 (.mem (sp sDb)), .alu .add .rsi (.reg .r8), .mov32 .r8 (.imm 0)])
    (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rcx .r8) .rax] (.imm (BitVec.ofNat 32 H.D)))

/-- The counter, big-endian, after `H` in `Y` (in `rcx`); the message's
length, `hLen + 4`, and its `mgfNb` blocks, for `mgfHash`. -/
def counter : List Instr :=
  [.mov .rax (.mem (sp sCtr)), .store8 (at_ .rcx (H.D + 3)) .rax, .shift .shr .rax 8,
    .store8 (at_ .rcx (H.D + 2)) .rax, .shift .shr .rax 8, .store8 (at_ .rcx (H.D + 1)) .rax,
    .shift .shr .rax 8, .store8 (at_ .rcx H.D) .rax,
    .mov32 .rax (.imm (BitVec.ofNat 32 (H.D + 4))), .store (sp sL) .rax,
    .mov32 .rax (.imm (BitVec.ofNat 32 (mgfNb H))), .store (sp sNb) .rax]

/-- The first `min(hLen, dbLen - done)` bytes of the digest XORed into `DB`
at `done`. -/
def xorOut : Prog isa :=
  seqs [.block (scr .rcx oDig ++ [.mov .rdx (.mem (sp sDone)), .mov .rdi (.mem (sp sEb)), .alu .add .rdi (.reg .rdx),
      .mov .rax (.mem (sp sDb)), .alu .sub .rax (.reg .rdx), .mov32 .r10 (.imm (BitVec.ofNat 32 H.D)),
      .alu .cmp .rax (.reg .r10)]),
    .ite .b (.block [.mov .r10 (.reg .rax)]) (.block []),
    .block [.mov32 .r8 (.imm 0)],
    byteLoop [.movzx8 .rax (ix .rcx .r8), .movzx8 .rdx (ix .rdi .r8), .alu .xor .rdx (.reg .rax),
      .store8 (ix .rdi .r8) .rdx] (.reg .r10)]

/-- The next counter, and CF set while `done < dbLen`. -/
def nextCtr : List Instr :=
  [.mov .rax (.mem (sp sCtr)), .alu .add .rax (.imm 1), .store (sp sCtr) .rax, .mov .rax (.mem (sp sDone)),
    .alu .add .rax (.imm (BitVec.ofNat 32 H.D)), .store (sp sDone) .rax, .mov .rdx (.mem (sp sDb)),
    .alu .cmp .rax (.reg .rdx)]

/-- `DB ⊕= MGF1(H, dbLen)`. -/
def mgfXor : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0), .store (sp sCtr) .rax, .store (sp sDone) .rax])
    (.loop (seqs [clearBlock H, copyH H, .block (counter H), mgfHash H, xorOut H, .block (nextCtr H)]) .b)

/-- `DB`'s first byte ANDed with the mask `0xFF >> z` (`sC`). -/
def clearTop : List Instr :=
  [.mov .rdi (.mem (sp sEb)), .movzx8 .rax (at_ .rdi), .alu .and .rax (.mem (sp sC)), .store8 (at_ .rdi) .rax]

/-! ## The encoding's parameters -/

/-- `n₀`, and ZF set if it is zero. -/
def n0 : List Instr := [.mov .rsi (.mem (sp sN)), .movzx8 .rax (at_ .rsi), .alu .test .rax (.reg .rax)]

/-- `rdx := smear(n₀ >> 1)`, ZF set if zero. -/
def smear : List Instr :=
  [.mov .rdx (.reg .rax), .shift .shr .rdx 1, .mov .rax (.reg .rdx), .shift .shr .rax 1, .alu .or .rdx (.reg .rax),
    .mov .rax (.reg .rdx), .shift .shr .rax 2, .alu .or .rdx (.reg .rax), .mov .rax (.reg .rdx),
    .shift .shr .rax 4, .alu .or .rdx (.reg .rax), .alu .test .rdx (.reg .rdx)]

/-- The mask `sC` and `lo` (`sLo`); `rax := emLen = k - lo`, and CF set
if `emLen < hLen + 2`. -/
def emLen : Prog isa :=
  .seq (.ite .e (.block [.mov32 .rdx (.imm 0xFF), .mov32 .r8 (.imm 1)]) (.block [.mov32 .r8 (.imm 0)]))
    (.block [.store (sp sC) .rdx, .store (sp sLo) .r8, .mov .rax (.mem (sp sK)), .alu .sub .rax (.reg .r8),
      .alu .cmp .rax (.imm (BitVec.ofNat 32 (H.D + 2)))])

/-- `rax := emLen - hLen - 2`, the longest salt, and CF set if it is less
than the salt's length in `rdx`. -/
def saltFits : List Instr :=
  [.alu .sub .rax (.imm (BitVec.ofNat 32 (H.D + 2))), .alu .cmp .rax (.reg .rdx)]

/-- `dbLen = emLen - hLen - 1` (from `rax = emLen - hLen - 2`) and
`DB = scratch + oEm + lo` into their slots. -/
def dbSlots : List Instr :=
  [.alu .add .rax (.imm 1), .store (sp sDb) .rax] ++ scr .rax oEm ++
    [.mov .rdx (.mem (sp sLo)), .alu .add .rax (.reg .rdx), .store (sp sEb) .rax]

/-! ## Common pieces -/

/-- `Y` cleared (2048 bytes, a word at a time), and `rcx` = `Y`. -/
def clearY : Prog isa :=
  .seq (.block (scr .rcx oY ++ [.mov32 .rax (.imm 0), .mov32 .r8 (.imm 0)]))
    (.loop (.block [.store (ix .rcx .r8) .rax, .alu .add .r8 (.imm 8), .alu .cmp .r8 (.imm 2048)]) .ne)

/-- The digest `mHash` after the 8 zero bytes of `Y` (in `rcx`). -/
def copyDigest : Prog isa :=
  .seq (.block [.mov .rsi (.mem (sp sDig)), .mov32 .r8 (.imm 0)])
    (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rcx .r8 8) .rax] (.imm (BitVec.ofNat 32 H.D)))

/-- Our caller's `rbx`, `rbp` and `r12`, saved. -/
def saveRegs : List Instr := [.store (sp sRbx) .rbx, .store (sp sRbp) .rbp, .store (sp sR12) .r12]

/-- And restored. -/
def restoreRegs : List Instr :=
  [.mov .rbx (.mem (sp sRbx)), .mov .rbp (.mem (sp sRbp)), .mov .r12 (.mem (sp sR12))]

/-! ## Signing

`sign(out = rdi, out_len = rsi, n = rdx, n_len = rcx, e = r8, e_len = r9,
p, p_len, q, q_len, dp, dp_len, dq, dq_len, qinv, qinv_len, digest, salt,
salt_len, scratch, scratch_len)`, the last fifteen on the stack. -/

/-- The arguments into their slots. -/
def signPrologue : List Instr :=
  saveRegs ++ [.store (sp sOut) .rdi, .store (sp sN) .rdx, .store (sp sK) .rcx, .store (sp sE) .r8,
    .store (sp sEl) .r9, .mov .rax (.mem (arg 10)), .store (sp sDig) .rax, .mov .rax (.mem (arg 11)),
    .store (sp sSalt) .rax, .mov .rax (.mem (arg 12)), .store (sp sSaltLen) .rax, .mov .rax (.mem (arg 13)),
    .store (sp sScr) .rax, .mov .rax (.mem (arg 14)), .store (sp sScrLen) .rax]

/-- Zeros to `out` and 0 returned. -/
def signFail : Prog isa :=
  .seq (.block [.mov .rdi (.mem (sp sOut)), .mov .r10 (.mem (sp sK)), .mov32 .rax (.imm 0), .mov32 .r8 (.imm 0)])
    (byteLoop [.store8 (ix .rdi .r8) .rax] (.reg .r10))

/-- The salt after `mHash` in `Y` (in `rcx`), if it is not empty. -/
def copySaltY : Prog isa :=
  .seq (.block [.mov .rsi (.mem (sp sSalt)), .mov .r10 (.mem (sp sSaltLen)), .mov32 .r8 (.imm 0),
      .alu .test .r10 (.reg .r10)])
    (.ite .e (.block []) (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rcx .r8 (8 + H.D)) .rax] (.reg .r10)))

/-- `ℓ = 8 + hLen + sLen` and `nbm = ⌊(ℓ + L) / B⌋ + 1`. -/
def hashSaltLen (k : Nat) : List Instr :=
  [.mov .rax (.mem (sp (8 * k))), .alu .add .rax (.imm (BitVec.ofNat 32 (8 + H.D))), .store (sp sL) .rax,
    .alu .add .rax (.imm (BitVec.ofNat 32 H.P.L)), .shift .shr .rax (lgB H), .alu .add .rax (.imm 1),
    .store (sp sNb) .rax]

/-- Signing supplies its salt length in slot 40. -/
def signLen : List Instr := hashSaltLen H 40

/-- `EM`'s `k` bytes cleared. -/
def clearEm : Prog isa :=
  .seq (.block (scr .rcx oEm ++ [.mov .r10 (.mem (sp sK)), .mov32 .rax (.imm 0), .mov32 .r8 (.imm 0)]))
    (byteLoop [.store8 (ix .rcx .r8) .rax] (.reg .r10))

/-- `0x01` at `DB + dbLen - sLen - 1`, and the salt after it. -/
def putSalt : Prog isa :=
  .seq (.block [.mov .rdi (.mem (sp sEb)), .mov .rax (.mem (sp sDb)), .alu .add .rdi (.reg .rax),
      .mov .rax (.mem (sp sSaltLen)), .alu .sub .rdi (.reg .rax), .alu .sub .rdi (.imm 1), .mov32 .rax (.imm 1),
      .store8 (at_ .rdi) .rax])
    (.seq (.block [.mov .rsi (.mem (sp sSalt)), .mov .r10 (.mem (sp sSaltLen)), .mov32 .r8 (.imm 0),
        .alu .test .r10 (.reg .r10)])
      (.ite .e (.block []) (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rdi .r8 1) .rax] (.reg .r10))))

/-- `H` (the digest) at `DB + dbLen`, and `0xbc` at `EM`'s last byte. -/
def putH : Prog isa :=
  .seq (.block ([.mov .rdi (.mem (sp sEb)), .mov .rax (.mem (sp sDb)), .alu .add .rdi (.reg .rax)] ++ scr .rsi oDig ++
      [.mov32 .r8 (.imm 0)]))
    (.seq (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rdi .r8) .rax] (.imm (BitVec.ofNat 32 H.D)))
      (.block (scr .rdi oEm ++ [.mov .rax (.mem (sp sK)), .alu .add .rdi (.reg .rax), .alu .sub .rdi (.imm 1),
        .mov32 .rax (.imm 0xbc),
        .store8 (at_ .rdi) .rax])))

/-- The arguments of `vg_rsa_private_checked`: `out`, `n` (`k` bytes), `e`,
`EM` as the input (`k` bytes), the private key, and the rest of `scratch`. -/
def privArgs : List Instr :=
  (List.range 10).flatMap (fun j => [.mov .rax (.mem (arg j)), .store (sp (16 + 8 * j)) .rax]) ++
  scr .rax oEm ++ [.store (sp 0) .rax, .mov .rax (.mem (sp sK)), .store (sp 8) .rax] ++
  scr .rax oRsa ++ [.store (sp 96) .rax, .mov .rax (.mem (sp sScrLen)), .alu .sub .rax (.imm 1024),
    .store (sp 104) .rax] ++
  [.mov .rdi (.mem (sp sOut)), .mov .rsi (.mem (sp sK)), .mov .rdx (.mem (sp sN)), .mov .rcx (.mem (sp sK)),
    .mov .r8 (.mem (sp sE)), .mov .r9 (.mem (sp sEl))]

variable (privN : String) (privC : Prog isa)

/-- After the checks: `EM` at `scratch + oEm`. -/
def signEnc : Prog isa :=
  seqs [.block dbSlots, clearY, copyDigest H, copySaltY H, .block (signLen H), ctHash H, clearEm,
    putSalt, putH H, mgfXor H, .block clearTop]

/-- After the checks: the encoding, and the private-key operation. -/
def signMain : Prog isa := seqs [signEnc H, .block privArgs, .call privN privC]

/-- The checks, then `signMain`. -/
def signBody : Prog isa :=
  seqs [.block (signPrologue ++ n0),
    .ite .e signFail (seqs [.block smear, emLen H,
      .ite .b signFail (seqs [.block ([.mov .rdx (.mem (sp sSaltLen))] ++ saltFits H),
        .ite .b signFail (signMain H privN privC)])]),
    .block restoreRegs]

/-- `vg_rsa_pss_<H>_mgf1_<H>_sign`. -/
def sign : Prog isa := .frame (.alloc frameBytes) (signBody H privN privC) (.free frameBytes)

/-! ## Verifying

`verify(n = rdi, n_len = rsi, e = rdx, e_len = rcx, digest = r8, sig = r9,
sig_len, salt_len, any_salt_len, scratch, scratch_len)`, the last five on
the stack. -/

def verifyPrologue : List Instr :=
  saveRegs ++ [.store (sp sN) .rdi, .store (sp sK) .rsi, .store (sp sE) .rdx, .store (sp sEl) .rcx,
    .store (sp sDig) .r8, .store (sp sSig) .r9, .mov .rax (.mem (arg 3)), .store (sp sScr) .rax,
    .mov .rax (.mem (arg 4)), .store (sp sScrLen) .rax]

/-- `sAny := any_salt_len ≠ 0` and `sSlen := salt_len`; `rdx` the expected
length for the check, 0 if any. -/
def anyArgs : Prog isa :=
  .seq (.block [.mov .rax (.mem (arg 1)), .store (sp sSlen) .rax, .mov32 .rax (.mem (arg 2)),
      .alu .test .rax (.reg .rax)])
    (.ite .e (.block [.mov32 .rax (.imm 0), .store (sp sAny) .rax, .mov .rdx (.mem (sp sSlen))])
      (.block [.mov32 .rax (.imm 1), .store (sp sAny) .rax, .mov32 .rdx (.imm 0)]))

/-- 0 returned. -/
def verifyFail : Prog isa := .block [.mov32 .rax (.imm 0)]

/-- The arguments of `vg_rsa_public_checked`: `EM`'s place (`k` bytes),
`n`, `e`, the signature (`k` bytes), and the rest of `scratch`. -/
def pubArgs : List Instr :=
  [.mov .rax (.mem (sp sSig)), .store (sp 0) .rax, .mov .rax (.mem (sp sK)), .store (sp 8) .rax] ++
  scr .rax oRsa ++ [.store (sp 16) .rax, .mov .rax (.mem (sp sScrLen)), .alu .sub .rax (.imm 1024),
    .store (sp 24) .rax] ++ scr .rdi oEm ++
  [.mov .rsi (.mem (sp sK)), .mov .rdx (.mem (sp sN)), .mov .rcx (.mem (sp sK)), .mov .r8 (.mem (sp sE)),
    .mov .r9 (.mem (sp sEl))]

/-- `acc :=` the leading byte if `lo = 1`, `EM`'s last byte `⊕ 0xbc`, and the
top bits of `maskedDB`'s first byte. -/
def acc0 : List Instr :=
  scr .rcx oEm ++ [.mov .rdi (.mem (sp sK)), .alu .add .rdi (.reg .rcx), .alu .sub .rdi (.imm 1),
    .movzx8 .rax (at_ .rdi), .alu .xor .rax (.imm 0xbc),
    .movzx8 .r9 (at_ .rcx), .mov .r10 (.mem (sp sLo)), .mov32 .r11 (.imm 0), .alu .sub .r11 (.reg .r10),
    .alu .and .r9 (.reg .r11),
    .alu .or .rax (.reg .r9),
    .mov .rdi (.mem (sp sEb)), .movzx8 .r9 (at_ .rdi), .mov .r11 (.mem (sp sC)), .alu .xor .r11 (.imm 0xFF),
    .alu .and .r9 (.reg .r11), .alu .or .rax (.reg .r9), .store (sp sAcc) .rax]

/-- The first nonzero byte of `DB`: its index into `rsi`, its value into
`r11`, and `rdx` all ones if there is one. -/
def posScan : Prog isa :=
  .seq (.block [.mov .rdi (.mem (sp sEb)), .mov .r10 (.mem (sp sDb)), .mov32 .r8 (.imm 0), .mov32 .rdx (.imm 0),
      .mov32 .rsi (.imm 0), .mov32 .r11 (.imm 0)])
    (byteLoop [.movzx8 .rax (ix .rdi .r8), .mov .r9 (.reg .rax), .alu .cmp .r9 (.imm 1), .alu .sbb .r9 (.reg .r9),
      .alu .xor .r9 (.imm 0xFFFFFFFF), .mov .rcx (.reg .rdx), .alu .xor .rcx (.imm 0xFFFFFFFF),
      .alu .and .r9 (.reg .rcx), .mov .rcx (.reg .r8), .alu .and .rcx (.reg .r9), .alu .or .rsi (.reg .rcx),
      .alu .and .rax (.reg .r9), .alu .or .r11 (.reg .rax), .alu .or .rdx (.reg .r9)] (.reg .r10))

/-- `acc |= (val ⊕ 1) | ¬found`, the salt's length `dbLen - pos - 1`
compared with the expected one if there is one, `pos` and `ℓ` into their
slots. -/
def posCheck : Prog isa :=
  .seq (.block [.alu .xor .r11 (.imm 1), .alu .xor .rdx (.imm 0xFFFFFFFF), .alu .or .r11 (.reg .rdx),
      .mov .rax (.mem (sp sAcc)), .alu .or .rax (.reg .r11), .store (sp sPos) .rsi,
      .mov .rcx (.mem (sp sDb)), .alu .sub .rcx (.reg .rsi), .alu .sub .rcx (.imm 1),
      .mov .r9 (.mem (sp sAny)), .alu .test .r9 (.reg .r9)])
    (.seq (.ite .e (.block [.mov .r9 (.reg .rcx), .alu .xor .r9 (.mem (sp sSlen)), .alu .or .rax (.reg .r9)])
        (.block []))
      (.block [.store (sp sAcc) .rax, .alu .add .rcx (.imm (BitVec.ofNat 32 (8 + H.D))), .store (sp sL) .rcx]))

/-- `DB` after `mHash` in `Y` (in `rcx`). -/
def copyDb : Prog isa :=
  .seq (.block [.mov .rsi (.mem (sp sEb)), .mov .r10 (.mem (sp sDb)), .mov32 .r8 (.imm 0)])
    (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rcx .r8 (8 + H.D)) .rax] (.reg .r10))

/-- One pass of the shift: every byte of `DB`'s place in `Y` replaced by
the one `d` (`sD`) bytes after it if bit 0 of `a` (`sA`) is set. -/
def shiftPass : Prog isa :=
  .seq (.block (scr .rcx (oY + 8 + H.D) ++ [.mov .rsi (.mem (sp sD)), .alu .add .rsi (.reg .rcx),
      .mov .r11 (.mem (sp sA)), .alu .and .r11 (.imm 1), .mov32 .r9 (.imm 0), .alu .sub .r9 (.reg .r11),
      .mov .r10 (.mem (sp sDb)), .mov32 .r8 (.imm 0)]))
    (byteLoop [.movzx8 .rax (ix .rcx .r8), .movzx8 .rdi (ix .rsi .r8), .alu .xor .rdi (.reg .rax),
      .alu .and .rdi (.reg .r9), .alu .xor .rax (.reg .rdi), .store8 (ix .rcx .r8) .rax] (.reg .r10))

/-- The next pass: `a >>= 1`, `d *= 2`, ZF set after the tenth. -/
def nextPass : List Instr :=
  [.mov .rax (.mem (sp sA)), .shift .shr .rax 1, .store (sp sA) .rax, .mov .rax (.mem (sp sD)),
    .alu .add .rax (.reg .rax), .store (sp sD) .rax, .mov .rax (.mem (sp sJ)), .alu .sub .rax (.imm 1),
    .store (sp sJ) .rax]

/-- `DB`'s place in `Y` shifted left by `pos + 1` bytes. -/
def shift : Prog isa :=
  .seq (.block [.mov .rax (.mem (sp sPos)), .alu .add .rax (.imm 1), .store (sp sA) .rax, .mov32 .rax (.imm 1),
      .store (sp sD) .rax, .mov32 .rax (.imm 10), .store (sp sJ) .rax])
    (.loop (.seq (shiftPass H) (.block nextPass)) .ne)

/-- `nbm = ⌊(8 + hLen + dbLen - 1 + L) / B⌋ + 1`, enough for the longest
salt. -/
def verifyNb : List Instr :=
  [.mov .rax (.mem (sp sDb)), .alu .add .rax (.imm (BitVec.ofNat 32 (7 + H.D + H.P.L))), .shift .shr .rax (lgB H),
    .alu .add .rax (.imm 1), .store (sp sNb) .rax]

/-- `acc` ORed with the digest `⊕ H`, and the result: 1 if `acc = 0`. -/
def cmpH : Prog isa :=
  .seq (.block (scr .rcx oDig ++ [.mov .rdi (.mem (sp sEb)), .mov .rdx (.mem (sp sDb)), .alu .add .rdi (.reg .rdx),
      .mov .rdx (.mem (sp sAcc)), .mov32 .r8 (.imm 0)]))
    (.seq (byteLoop [.movzx8 .rax (ix .rcx .r8), .movzx8 .r9 (ix .rdi .r8), .alu .xor .rax (.reg .r9),
        .alu .or .rdx (.reg .rax)] (.imm (BitVec.ofNat 32 H.D)))
      (.block [.alu .cmp .rdx (.imm 1), .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 1)]))

variable (pubN : String) (pubC : Prog isa)

/-- Copy a fixed-length salt from the end of `DB`; both the address and
count depend only on the public requested salt length. -/
def copyFixedSalt : Prog isa :=
  .seq (.block [.mov .rsi (.mem (sp sEb)), .mov .rax (.mem (sp sDb)),
    .alu .add .rsi (.reg .rax), .mov .r10 (.mem (sp sSlen)), .alu .sub .rsi (.reg .r10),
    .mov32 .r8 (.imm 0), .alu .test .r10 (.reg .r10)])
    (.ite .e (.block []) (byteLoop [.movzx8 .rax (ix .rsi .r8),
      .store8 (ix .rcx .r8 (8 + H.D)) .rax] (.reg .r10)))

/-- Build only the requested salt's hash input, avoiding the masked shift. -/
def fixedSaltPrefix : Prog isa := seqs [clearY, copyDigest H, copyFixedSalt H,
  .block (hashSaltLen H 36)]

/-- Hash and compare the fixed-length verification input. -/
def fixedSaltBack : Prog isa := .seq (fixedSaltPrefix H) (.seq (ctHash H) (cmpH H))

/-- Verification with an inferred salt length keeps the masked shift. -/
def genericSaltBack : Prog isa := seqs [clearY, copyDigest H, copyDb H,
  shift H, .block (verifyNb H), ctHash H, cmpH H]

/-- The fast path's length check also makes this tail safe independently
of the outer verification entry checks. -/
def saltBack : Prog isa :=
  .seq (.block [.mov .rax (.mem (sp sAny)), .alu .test .rax (.reg .rax)])
    (.ite .e (.seq (.block [.mov .rax (.mem (sp sSlen)), .alu .cmp .rax (.mem (sp sDb))])
      (.ite .b (fixedSaltBack H) (genericSaltBack H))) (genericSaltBack H))

/-- After the public checks. -/
def verifyMain : Prog isa :=
  seqs [.block dbSlots, .block pubArgs, .call pubN pubC, .block acc0, mgfXor H, .block clearTop,
    posScan, posCheck H, saltBack H]

def verifyBody : Prog isa :=
  seqs [.block (verifyPrologue ++ n0),
    .ite .e verifyFail (seqs [.block smear, emLen H,
      .ite .b verifyFail (seqs [anyArgs, .block ([.mov .rax (.mem (sp sK)), .mov .r8 (.mem (sp sLo)),
          .alu .sub .rax (.reg .r8)] ++
          saltFits H),
        .ite .b verifyFail (verifyMain H pubN pubC)])]),
    .block restoreRegs]

/-- `vg_rsa_pss_<H>_mgf1_<H>_verify`. -/
def verify : Prog isa := .frame (.alloc frameBytes) (verifyBody H pubN pubC) (.free frameBytes)

end VG.Impl.RsaPss.X86_64
