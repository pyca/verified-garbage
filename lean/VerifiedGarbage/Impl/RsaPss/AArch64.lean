module

public import VerifiedGarbage.Impl.Pbkdf2.Md.AArch64
public import VerifiedGarbage.Impl.RsaPkcs1Sig.AArch64.Encode

/-!
# RSASSA-PSS (RFC 8017 §8.1, EMSA-PSS §9.1) on AArch64

`sign` and `verifyPrecomputed`, for a Merkle–Damgård hash function `H` (an
`Impl.Pbkdf2.Md.AArch64.Hash`) as both the hash function and MGF1's, as on
x86-64 (`Impl/RsaPss/X86_64.lean`), whose design this follows: `H`'s
compression function and streaming `init`, and the RSA operation
(`vg_rsa_private_checked` when signing, a precomputed public operation when
verifying).

The first 8192 bytes of `scratch` are ours (`oCW`, …); the RSA operation
gets the rest. The callees preserve `x19`–`x28`, which hold our variables:

* `x19`: the hash value the compression function updates (`scratch + oSt`),
  and, around `H`'s length field and digest code, the address they need;
* `x20`: `scratch`, whose first bytes are the compression function's
  working space;
* `x21`: the digest (`scratch + oDig`), where `H`'s digest code writes;
* `x22`: the length `ℓ` of the message hashed (`H`'s length field code reads
  it there), or the passes left of the shift;
* `x23`: `k`; `x24`: `DB` (`scratch + oEm + lo`); `x25`: `dbLen`;
* `x26`: the accumulator of failed checks (verifying);
* `x27`: the block hashed, or the shift's `a`;
* `x28`: MGF1's counter, or the shift's distance.

The frame (`frameBytes`) holds, at `sp`, the stack arguments of the RSA
operation; then our caller's `x19`–`x28` and our return address (`saved`);
then the slots of the values used less often. Every comparison is a
subtraction whose borrow is taken by a shift (`(a - b) >> 63`, for
`a, b < 2^63`), and every selection a mask: only the public key, the
lengths and `salt_len` decide a branch or an address.

## Hashing a message of secret length (`ctHash`)

The message is the first `ℓ` bytes of `Y` (`scratch + oY`), whose bytes
after it are zero up to `nbm` blocks (`nbm` in the slot `sNb`), with
`ℓ + 1 + L ≤ nbm B`. As on x86-64: `init`; `0x80` ORed into byte `i` under
the mask of `i = ℓ`, for every `i < nbm B` (`pad80`); the length field
written to `scratch + oLen` and ORed into the end of block `b` under the
mask of `b = ⌊(ℓ + L) / B⌋` (`lenLoop`); every block compressed, the hash
value copied to `scratch + oSel` under the same mask (`compLoop`); the
digest of that hash value written (`digestOut`).
-/

@[expose] public section

namespace VG.Impl.RsaPss.AArch64

open VG.AArch64
open VG.Impl.MdStream.AArch64 (mov compressAt)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Impl.RsaPkcs1Sig.AArch64 (psLoop copyLoop)

/-- `c₁; c₂; …`. -/
def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-! ## The frame -/

/-- The callee-saved registers we use, and our return address, and their
slots. -/
def saved : List (Reg × Nat) :=
  [(.x19, 96), (.x20, 104), (.x21, 112), (.x22, 120), (.x23, 128), (.x24, 136), (.x25, 144),
    (.x26, 152), (.x27, 160), (.x28, 168), (.x30, 176)]

/-- The slots. -/
def sN : Nat := 184
def sE : Nat := 192
def sEl : Nat := 200
def sDig : Nat := 208
/-- `out` (signing) or the signature (verifying). -/
def sOut : Nat := 216
def sSalt : Nat := 224
def sSaltLen : Nat := 232
def sScrLen : Nat := 240
def sC : Nat := 248
def sLo : Nat := 256
def sAny : Nat := 264
def sDone : Nat := 272
def sNb : Nat := 280
def sP : Nat := 288
def sPl : Nat := 296
def sPos : Nat := 304
def sPre : Nat := 312
def sPreLen : Nat := 320

/-- The size of the frame. -/
def frameBytes : Nat := 336

/-- `x16 := sp`, and the registers of `saved` stored. -/
def save : List Instr := .addSp .x16 0 :: saved.map fun (r, d) => .str .x r .x16 d

/-- The registers of `saved` restored. -/
def restore : List Instr := .addSp .x16 0 :: saved.map fun (r, d) => .ldr .x r .x16 d

/-- A slot into `r`. -/
def ld (r : Reg) (o : Nat) : Instr := .ldrSp r o

/-- `r` into a slot, through `x16`. -/
def st (r : Reg) (o : Nat) : List Instr := [.addSp .x16 0, .str .x r .x16 o]

/-- `d := n` for `n < 2^16`. -/
def movi (d : Reg) (n : Nat) : Instr := .movz .x d (BitVec.ofNat 16 n) 0

/-! ## Our part of `scratch` -/

/-- The compression function's working space (less than 2048 bytes). -/
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

/-- `d := (a = b)`, 1 or 0, for `a, b < 2^63` (`t` is used). -/
def eq1 (d a b : Reg) : List Instr := [.logic .eor .x d a b, .subImm .x d d 1, .lsr .x d d 63]

/-- `d := -(a = b)`, all ones or zero, for `a, b < 2^63` (`x9` is used). -/
def eqMask (d a b : Reg) : List Instr := eq1 d a b ++ [movi .x9 0, .sub .x d .x9 d]

/-- `d := ⌊(ℓ + L) / B⌋`, the last block of the padded message. -/
def lastBlk (d : Reg) : List Instr := [.addImm .x d .x22 H.P.L, .lsr .x d d (lgB H)]

/-! ## `ctHash`: hashing a message of secret length -/

/-- `init` on the state at `x19`. -/
def ctInit : Prog isa := .seq (.block [mov .x0 .x19]) (.call H.initN H.initC)

/-- `0x80` ORed into byte `ℓ` of `Y`, a mask for each of its `nbm B` bytes:
`x10` the byte, `x11` its index, `x12` the bytes left. -/
def pad80 : Prog isa :=
  .seq (.block [.addImm .x .x10 .x20 oY, movi .x11 0, ld .x12 sNb, .lsl .x .x12 .x12 (lgB H)])
    (.loop (.block (.ldrb .x13 .x10 0 :: eq1 .x14 .x11 .x22 ++
      ([.lsl .x .x14 .x14 7, .logic .orr .x .x13 .x13 .x14, .strb .x13 .x10 0, .addImm .x .x10 .x10 1,
        .addImm .x .x11 .x11 1, .subImm .x .x12 .x12 1] : List Instr))) (.nonzero .x .x12))

/-- The length field of `ℓ` to `scratch + oLen` (`P.len`, with `x19` placed
so that it writes there). -/
def lenField : List Instr :=
  ([.addImm .x .x19 .x20 (oLen - (H.P.N + H.P.B - H.P.L))] : List Instr) ++ H.P.len ++ ([.addImm .x .x19 .x20 oSt] : List Instr)

/-- The length field ORed into the last `L` bytes of block `b` (`x11`, at
`x10`) under the mask of `b = ⌊(ℓ + L) / B⌋` (`x15`), for every block. -/
def lenLoop : Prog isa :=
  .seq (.block (([.addImm .x .x10 .x20 (oY + H.P.B - H.P.L), movi .x11 0, ld .x12 sNb] : List Instr) ++ lastBlk H .x15))
    (.loop (.seq (.block (eqMask .x13 .x11 .x15 ++ ([.addImm .x .x14 .x20 oLen, mov .x16 .x10, movi .x17 H.P.L] : List Instr)))
      (.seq (.loop (.block [.ldrb .x9 .x14 0, .logic .and .x .x9 .x9 .x13, .ldrb .x8 .x16 0,
          .logic .orr .x .x8 .x8 .x9, .strb .x8 .x16 0, .addImm .x .x14 .x14 1, .addImm .x .x16 .x16 1,
          .subImm .x .x17 .x17 1]) (.nonzero .x .x17))
        (.block [.addImm .x .x10 .x10 H.P.B, .addImm .x .x11 .x11 1, .subImm .x .x12 .x12 1])))
      (.nonzero .x .x12))

/-- The block `b` (`x27`) of `Y` into `x1`. -/
def compArgs : List Instr := [.lsl .x .x1 .x27 (lgB H), .add .x .x1 .x1 .x20, .addImm .x .x1 .x1 oY]

/-- The hash value copied to `scratch + oSel` under the mask of
`b = ⌊(ℓ + L) / B⌋`. -/
def select : Prog isa :=
  .seq (.block (lastBlk H .x15 ++ eqMask .x13 .x27 .x15 ++
      ([.addImm .x .x10 .x20 oSt, .addImm .x .x11 .x20 oSel, movi .x12 H.P.N] : List Instr)))
    (.loop (.block [.ldrb .x14 .x10 0, .ldrb .x15 .x11 0, .logic .eor .x .x14 .x14 .x15,
      .logic .and .x .x14 .x14 .x13, .logic .eor .x .x15 .x15 .x14, .strb .x15 .x11 0, .addImm .x .x10 .x10 1,
      .addImm .x .x11 .x11 1, .subImm .x .x12 .x12 1]) (.nonzero .x .x12))

/-- The next block, and `x9` nonzero while blocks are left. -/
def nextBlock : List Instr := [.addImm .x .x27 .x27 1, ld .x9 sNb, .sub .x .x9 .x9 .x27]

/-- Every block compressed, the last one's hash value selected. -/
def compLoop : Prog isa :=
  .seq (.block [movi .x27 0])
    (.loop (seqs [.block (compArgs H), compressAt H.compN H.compC, select H, .block nextBlock])
      (.nonzero .x .x9))

/-- The digest of the selected hash value to `scratch + oDig` (`x21`). -/
def digestOut : List Instr := ([.addImm .x .x19 .x20 oSel] : List Instr) ++ H.P.out ++ ([.addImm .x .x19 .x20 oSt] : List Instr)

/-- The hash computation, with its padding step. -/
def ctHashWith (padding : Prog isa) : Prog isa :=
  seqs [ctInit H, padding, .block (lenField H), lenLoop H, compLoop H, .block (digestOut H)]

/-- The digest of the first `ℓ` bytes of `Y`, padded in `nbm` blocks, to
`scratch + oDig`, without revealing `ℓ`. -/
def ctHash : Prog isa := ctHashWith H (pad80 H)

/-- A message of public length `ℓ` (less than 2048) needs one padding
write. -/
def fixedPad80 (ℓ : Nat) : Prog isa :=
  .block [.addImm .x .x10 .x20 (oY + ℓ), .ldrb .x9 .x10 0, movi .x13 0x80, .logic .orr .x .x9 .x9 .x13,
    .strb .x9 .x10 0]

/-- MGF1's message, `H ‖ C`, of a length fixed by the hash function. -/
def mgfHash : Prog isa := ctHashWith H (fixedPad80 (H.D + 4))

/-! ## MGF1 -/

/-- The blocks MGF1 hashes `H ‖ C` in: `⌊(hLen + 4 + L) / B⌋ + 1`. -/
def mgfNb : Nat := (H.D + 4 + H.P.L) / H.P.B + 1

/-- `Y`'s first `mgfNb` blocks cleared, eight bytes at a time. -/
def clearBlock : Prog isa :=
  .seq (.block [.addImm .x .x10 .x20 oY, movi .x9 0, movi .x12 (mgfNb H * H.P.B / 8)])
    (.loop (.block [.str .x .x9 .x10 0, .addImm .x .x10 .x10 8, .subImm .x .x12 .x12 1]) (.nonzero .x .x12))

/-- `H` (at `DB + dbLen`) to `Y`. -/
def copyH : Prog isa :=
  .seq (.block [.add .x .x11 .x24 .x25, .addImm .x .x14 .x20 oY, movi .x12 H.D]) copyLoop

/-- The counter (`x28`), big-endian, after `H` in `Y`; the message's length,
`hLen + 4`, and its `mgfNb` blocks, for `mgfHash`. -/
def counter : List Instr :=
  ([.addImm .x .x10 .x20 (oY + H.D), .lsr .x .x9 .x28 24, .strb .x9 .x10 0, .lsr .x .x9 .x28 16,
    .strb .x9 .x10 1, .lsr .x .x9 .x28 8, .strb .x9 .x10 2, .strb .x28 .x10 3, movi .x22 (H.D + 4),
    movi .x9 (mgfNb H)] : List Instr) ++ st .x9 sNb

/-- The first `min(hLen, dbLen - done)` bytes of the digest XORed into `DB`
at `done`. -/
def xorOut : Prog isa :=
  seqs [.block [ld .x9 sDone, .add .x .x10 .x24 .x9, mov .x11 .x21, .sub .x .x12 .x25 .x9, movi .x13 H.D,
      .sub .x .x14 .x12 .x13, .lsr .x .x14 .x14 63],
    .ite (.zero .x .x14) (.block [mov .x12 .x13]) (.block []),
    .loop (.block [.ldrb .x9 .x11 0, .ldrb .x15 .x10 0, .logic .eor .x .x15 .x15 .x9, .strb .x15 .x10 0,
      .addImm .x .x11 .x11 1, .addImm .x .x10 .x10 1, .subImm .x .x12 .x12 1]) (.nonzero .x .x12)]

/-- The next counter, and `x10` nonzero while `done < dbLen`. -/
def nextCtr : List Instr :=
  ([.addImm .x .x28 .x28 1, ld .x9 sDone, .addImm .x .x9 .x9 H.D] : List Instr) ++ st .x9 sDone ++
    ([.sub .x .x10 .x9 .x25, .lsr .x .x10 .x10 63] : List Instr)

/-- `DB ⊕= MGF1(H, dbLen)`. -/
def mgfXor : Prog isa :=
  .seq (.block ([movi .x28 0, movi .x9 0] ++ st .x9 sDone))
    (.loop (seqs [clearBlock H, copyH H, .block (counter H), mgfHash H, xorOut H, .block (nextCtr H)])
      (.nonzero .x .x10))

/-- `DB`'s first byte ANDed with the mask `0xFF >> z` (`sC`). -/
def clearTop : List Instr :=
  [.ldrb .x9 .x24 0, ld .x10 sC, .logic .and .x .x9 .x9 .x10, .strb .x9 .x24 0]

/-! ## The encoding's parameters -/

/-- `n₀` into `x10`, from `n` in `r`. -/
def n0 (r : Reg) : List Instr := [.ldrb .x10 r 0]

/-- `x11 := smear(n₀ >> 1)`. -/
def smear : List Instr :=
  [.lsr .x .x11 .x10 1, .lsr .x .x12 .x11 1, .logic .orr .x .x11 .x11 .x12, .lsr .x .x12 .x11 2,
    .logic .orr .x .x11 .x11 .x12, .lsr .x .x12 .x11 4, .logic .orr .x .x11 .x11 .x12]

/-- The mask `sC` and `lo` (`sLo`); `x9 := emLen = k - lo`, and `x10`
nonzero if `emLen < hLen + 2`. -/
def emLen : Prog isa :=
  .seq (.ite (.zero .x .x11) (.block [movi .x11 0xFF, movi .x12 1]) (.block [movi .x12 0]))
    (.block (st .x11 sC ++ st .x12 sLo ++
      ([.sub .x .x9 .x23 .x12, .subImm .x .x10 .x9 (H.D + 2), .lsr .x .x10 .x10 63] : List Instr)))

/-- `x9 := emLen - hLen - 2`, the longest salt, and `x10` nonzero if it is
less than the salt's length in `x12` (any 64-bit value: its top bit is
ORed in, since the borrow of `x9 - x12` is the comparison only below
`2^63`). -/
def saltFits : List Instr :=
  [.subImm .x .x9 .x9 (H.D + 2), .sub .x .x10 .x9 .x12, .lsr .x .x10 .x10 63, .lsr .x .x13 .x12 63,
    .logic .orr .x .x10 .x10 .x13]

/-- `dbLen = emLen - hLen - 1` (from `x9 = emLen - hLen - 2`) and
`DB = scratch + oEm + lo`. -/
def dbRegs : List Instr :=
  [.addImm .x .x25 .x9 1, ld .x9 sLo, .addImm .x .x24 .x20 oEm, .add .x .x24 .x24 .x9]

/-! ## Common pieces -/

/-- `Y` cleared (2048 bytes, eight at a time). -/
def clearY : Prog isa :=
  .seq (.block [.addImm .x .x10 .x20 oY, movi .x9 0, movi .x12 256])
    (.loop (.block [.str .x .x9 .x10 0, .addImm .x .x10 .x10 8, .subImm .x .x12 .x12 1]) (.nonzero .x .x12))

/-- The digest `mHash` after the 8 zero bytes of `Y`. -/
def copyDigest : Prog isa :=
  .seq (.block [ld .x11 sDig, .addImm .x .x14 .x20 (oY + 8), movi .x12 H.D]) copyLoop

/-- The callee-saved registers saved, `scratch` into `x20`, and `x19`,
`x21` set. -/
def regsUp : List Instr := [.addImm .x .x19 .x20 oSt, .addImm .x .x21 .x20 oDig]

/-! ## Signing

`sign(out = x0, out_len = x1, n = x2, n_len = x3, e = x4, e_len = x5,
p = x6, p_len = x7, q, q_len, dp, dp_len, dq, dq_len, qinv, qinv_len, digest,
salt, salt_len, scratch, scratch_len)`, the last thirteen on the stack. -/

/-- The stack argument `j` of the function into `r`. -/
def arg (r : Reg) (j : Nat) : Instr := .ldrSp r (frameBytes + 8 * j)

/-- The registers saved, and the arguments into their places. -/
def signPrologue : List Instr :=
  save ++ ([.str .x .x0 .x16 sOut, .str .x .x2 .x16 sN, .str .x .x4 .x16 sE, .str .x .x5 .x16 sEl,
    .str .x .x6 .x16 sP, .str .x .x7 .x16 sPl, mov .x23 .x3, arg .x9 8, .str .x .x9 .x16 sDig,
    arg .x9 9, .str .x .x9 .x16 sSalt, arg .x9 10, .str .x .x9 .x16 sSaltLen, arg .x20 11, arg .x9 12,
    .str .x .x9 .x16 sScrLen] : List Instr) ++ regsUp

/-- Zeros to `out` and 0 returned. -/
def signFail : Prog isa :=
  .seq (.block [ld .x14 sOut, mov .x13 .x23, movi .x15 0]) (.seq psLoop (.block [movi .x0 0]))

/-- The salt after `mHash` in `Y`, if it is not empty. -/
def copySaltY : Prog isa :=
  .seq (.block [ld .x11 sSalt, .addImm .x .x14 .x20 (oY + 8 + H.D), ld .x12 sSaltLen])
    (.ite (.zero .x .x12) (.block []) copyLoop)

/-- `ℓ = 8 + hLen + sLen` and `nbm = ⌊(ℓ + L) / B⌋ + 1`. -/
def signLen : List Instr :=
  [ld .x9 sSaltLen, .addImm .x .x22 .x9 (8 + H.D)] ++ lastBlk H .x9 ++ ([.addImm .x .x9 .x9 1] : List Instr) ++ st .x9 sNb

/-- `EM`'s `k` bytes cleared. -/
def clearEm : Prog isa := .seq (.block [.addImm .x .x14 .x20 oEm, mov .x13 .x23, movi .x15 0]) psLoop

/-- `0x01` at `DB + dbLen - sLen - 1`, and the salt after it. -/
def putSalt : Prog isa :=
  .seq (.block [.add .x .x14 .x24 .x25, ld .x12 sSaltLen, .sub .x .x14 .x14 .x12, .subImm .x .x14 .x14 1,
      movi .x9 1, .strb .x9 .x14 0, .addImm .x .x14 .x14 1, ld .x11 sSalt])
    (.ite (.zero .x .x12) (.block []) copyLoop)

/-- `H` (the digest) at `DB + dbLen`, and `0xbc` at `EM`'s last byte. -/
def putH : Prog isa :=
  .seq (.seq (.block [.add .x .x14 .x24 .x25, mov .x11 .x21, movi .x12 H.D]) copyLoop)
    (.block [.addImm .x .x9 .x20 oEm, .add .x .x9 .x9 .x23, .subImm .x .x9 .x9 1, movi .x10 0xbc,
      .strb .x10 .x9 0])

/-- The arguments of `vg_rsa_private_checked`: `out`, `n` (`k` bytes), `e`,
`EM` as the input (`k` bytes), the private key, and the rest of `scratch`. -/
def privArgs : List Instr :=
  ([.addSp .x16 0, ld .x9 sP, .str .x .x9 .x16 0, ld .x9 sPl, .str .x .x9 .x16 8] : List Instr) ++
    (List.range 8).flatMap (fun j => [arg .x9 j, .str .x .x9 .x16 (16 + 8 * j)]) ++
    [movi .x9 oRsa, .add .x .x9 .x20 .x9, .str .x .x9 .x16 80, ld .x9 sScrLen, .subImm .x .x9 .x9 1024,
      .str .x .x9 .x16 88, ld .x0 sOut, mov .x1 .x23, ld .x2 sN, mov .x3 .x23, ld .x4 sE, ld .x5 sEl,
      .addImm .x .x6 .x20 oEm, mov .x7 .x23]

variable (privN : String) (privC : Prog isa)

/-- After the checks: `EM` at `scratch + oEm`. -/
def signEnc : Prog isa :=
  seqs [.block dbRegs, clearY, copyDigest H, copySaltY H, .block (signLen H), ctHash H, clearEm,
    putSalt, putH H, mgfXor H, .block clearTop]

/-- After the checks: the encoding, and the private-key operation. -/
def signMain : Prog isa := seqs [signEnc H, .block privArgs, .call privN privC]

/-- The checks, then `signMain`. -/
def signBody : Prog isa :=
  seqs [.block (signPrologue ++ n0 .x2),
    .ite (.zero .x .x10) signFail (seqs [.block smear, emLen H,
      .ite (.nonzero .x .x10) signFail (seqs [.block ([ld .x12 sSaltLen] ++ saltFits H),
        .ite (.nonzero .x .x10) signFail (signMain H privN privC)])]),
    .block restore]

/-- `vg_rsa_pss_<H>_mgf1_<H>_sign`. -/
def sign : Prog isa := .frame (.alloc frameBytes) (signBody H privN privC) (.free frameBytes)

/-! ## Verifying

`verifyPrecomputed(n = x0, n_len = x1, e = x2, e_len = x3, digest = x4,
sig = x5, sig_len = x6, salt_len = x7, any_salt_len, scratch, scratch_len,
pre, pre_len)`, the last five on the stack. -/

/-- The registers saved, and the arguments into their places; `sAny` is
`any_salt_len`'s 32 bits, and `sSaltLen` is `salt_len`. -/
def verifyPrologue : List Instr :=
  save ++ ([.str .x .x0 .x16 sN, .str .x .x2 .x16 sE, .str .x .x3 .x16 sEl, .str .x .x4 .x16 sDig,
    .str .x .x5 .x16 sOut, .str .x .x7 .x16 sSaltLen, mov .x23 .x1, arg .x9 0,
    .addImm .w .x9 .x9 0, .str .x .x9 .x16 sAny, arg .x20 1, arg .x9 2, .str .x .x9 .x16 sScrLen,
    arg .x9 3, .str .x .x9 .x16 sPre, arg .x9 4, .str .x .x9 .x16 sPreLen] : List Instr) ++ regsUp

/-- `x12 :=` the expected salt length for the check, 0 if any. -/
def expLen : Prog isa :=
  .seq (.block [ld .x13 sAny]) (.ite (.zero .x .x13) (.block [ld .x12 sSaltLen]) (.block [movi .x12 0]))

/-- 0 returned. -/
def verifyFail : Prog isa := .block [movi .x0 0]

/-- The arguments of the precomputed public operation: `EM`'s place (`k`
bytes), `pre` (`pre_len` words), `e`, the signature (`k` bytes), and the rest
of `scratch`. -/
def pubArgs : List Instr :=
  [.addSp .x16 0, movi .x9 oRsa, .add .x .x9 .x20 .x9, .str .x .x9 .x16 0, ld .x9 sScrLen,
    .subImm .x .x9 .x9 1024, .str .x .x9 .x16 8, .addImm .x .x0 .x20 oEm, mov .x1 .x23, ld .x2 sPre,
    ld .x3 sPreLen, ld .x4 sE, ld .x5 sEl, ld .x6 sOut, mov .x7 .x23]

/-- `acc :=` the leading byte if `lo = 1`, `EM`'s last byte `⊕ 0xbc`, and the
top bits of `maskedDB`'s first byte. -/
def acc0 : List Instr :=
  [.addImm .x .x10 .x20 oEm, .add .x .x9 .x10 .x23, .subImm .x .x9 .x9 1, .ldrb .x26 .x9 0, movi .x9 0xbc,
    .logic .eor .x .x26 .x26 .x9,
    .ldrb .x11 .x10 0, ld .x12 sLo, movi .x9 0, .sub .x .x12 .x9 .x12, .logic .and .x .x11 .x11 .x12,
    .logic .orr .x .x26 .x26 .x11,
    .ldrb .x11 .x24 0, ld .x12 sC, movi .x9 0xFF, .logic .eor .x .x12 .x12 .x9, .logic .and .x .x11 .x11 .x12,
    .logic .orr .x .x26 .x26 .x11]

/-- The first nonzero byte of `DB`: its index into `x14`, its value into
`x15`, and `x13` all ones if there is none (zero if there is). -/
def posScan : Prog isa :=
  .seq (.block [mov .x10 .x24, movi .x11 0, mov .x12 .x25, movi .x13 0, .subImm .x .x13 .x13 1, movi .x14 0,
      movi .x15 0])
    (.loop (.block [.ldrb .x9 .x10 0, .subImm .x .x8 .x9 1, .lsr .x .x8 .x8 63, .subImm .x .x16 .x8 1,
      .logic .and .x .x16 .x16 .x13, .logic .and .x .x17 .x11 .x16, .logic .orr .x .x14 .x14 .x17,
      .logic .and .x .x17 .x9 .x16, .logic .orr .x .x15 .x15 .x17, movi .x17 0, .sub .x .x17 .x17 .x8,
      .logic .and .x .x13 .x13 .x17, .addImm .x .x10 .x10 1, .addImm .x .x11 .x11 1, .subImm .x .x12 .x12 1])
      (.nonzero .x .x12))

/-- `acc |= (val ⊕ 1) | notFound` (its top bit), `pos` into `sPos`, and the
salt's length `dbLen - pos - 1` compared with the expected one if there is
one. -/
def posCheck : Prog isa :=
  .seq (.block ([movi .x9 1, .logic .eor .x .x15 .x15 .x9, .lsr .x .x13 .x13 63, .logic .orr .x .x15 .x15 .x13,
      .logic .orr .x .x26 .x26 .x15] ++ st .x14 sPos ++
      ([.sub .x .x11 .x25 .x14, .subImm .x .x11 .x11 1, ld .x9 sAny] : List Instr)))
    (.ite (.zero .x .x9) (.block [ld .x12 sSaltLen, .logic .eor .x .x12 .x12 .x11,
      .logic .orr .x .x26 .x26 .x12]) (.block []))

/-- `DB` after `mHash` in `Y`. -/
def copyDb : Prog isa :=
  .seq (.block [mov .x11 .x24, .addImm .x .x14 .x20 (oY + 8 + H.D), mov .x12 .x25]) copyLoop

/-- One pass of the shift: every byte of `DB`'s place in `Y` replaced by the
one `d` (`x28`) bytes after it if bit 0 of `a` (`x27`) is set. -/
def shiftPass : Prog isa :=
  .seq (.block [.addImm .x .x10 .x20 (oY + 8 + H.D), .add .x .x11 .x10 .x28, .lsr .x .x14 .x27 1,
      .lsl .x .x14 .x14 1, .sub .x .x14 .x27 .x14, movi .x9 0, .sub .x .x14 .x9 .x14, mov .x12 .x25])
    (.loop (.block [.ldrb .x15 .x10 0, .ldrb .x9 .x11 0, .logic .eor .x .x9 .x9 .x15, .logic .and .x .x9 .x9 .x14,
      .logic .eor .x .x15 .x15 .x9, .strb .x15 .x10 0, .addImm .x .x10 .x10 1, .addImm .x .x11 .x11 1,
      .subImm .x .x12 .x12 1]) (.nonzero .x .x12))

/-- The next pass: `a >>= 1`, `d *= 2`. -/
def nextPass : List Instr :=
  [.lsr .x .x27 .x27 1, .add .x .x28 .x28 .x28, .subImm .x .x22 .x22 1]

/-- `DB`'s place in `Y` shifted left by `pos + 1` bytes, in ten passes; then
`ℓ = 8 + hLen + dbLen - pos - 1` into `x22`. -/
def shift : Prog isa :=
  .seq (.block [ld .x27 sPos, .addImm .x .x27 .x27 1, movi .x28 1, movi .x22 10])
    (.seq (.loop (.seq (shiftPass H) (.block nextPass)) (.nonzero .x .x22))
      (.block [ld .x9 sPos, .sub .x .x9 .x25 .x9, .subImm .x .x9 .x9 1, .addImm .x .x22 .x9 (8 + H.D)]))

/-- `nbm = ⌊(8 + hLen + dbLen - 1 + L) / B⌋ + 1`, enough for the longest
salt. -/
def verifyNb : List Instr :=
  ([.addImm .x .x9 .x25 (7 + H.D + H.P.L), .lsr .x .x9 .x9 (lgB H), .addImm .x .x9 .x9 1] : List Instr) ++ st .x9 sNb

/-- `acc` ORed with the digest `⊕ H`, and the result: 1 if `acc = 0`. -/
def cmpH : Prog isa :=
  .seq (.block [mov .x11 .x21, .add .x .x10 .x24 .x25, movi .x12 H.D])
    (.seq (.loop (.block [.ldrb .x9 .x11 0, .ldrb .x15 .x10 0, .logic .eor .x .x9 .x9 .x15,
        .logic .orr .x .x26 .x26 .x9, .addImm .x .x11 .x11 1, .addImm .x .x10 .x10 1, .subImm .x .x12 .x12 1])
        (.nonzero .x .x12))
      (.block [.subImm .x .x0 .x26 1, .lsr .x .x0 .x0 63]))

variable (pubN : String) (pubC : Prog isa)

/-- After the public checks. -/
def verifyMain : Prog isa :=
  seqs [.block dbRegs, .block pubArgs, .call pubN pubC, .block acc0, mgfXor H, .block clearTop, posScan,
    posCheck, clearY, copyDigest H, copyDb H, shift H, .block (verifyNb H), ctHash H, cmpH H]

/-- The checks, then `verifyMain`. -/
def verifyBody : Prog isa :=
  seqs [.block (verifyPrologue ++ n0 .x0),
    .ite (.zero .x .x10) verifyFail (seqs [.block smear, emLen H,
      .ite (.nonzero .x .x10) verifyFail (seqs [expLen, .block (saltFits H),
        .ite (.nonzero .x .x10) verifyFail (verifyMain H pubN pubC)])]),
    .block restore]

/-- `vg_rsa_pss_<H>_mgf1_<H>_verify_precomputed`, calling a precomputed
public operation (`pubN`, `pubC`). -/
def verifyPrecomputed : Prog isa :=
  .frame (.alloc frameBytes) (verifyBody H pubN pubC) (.free frameBytes)

end VG.Impl.RsaPss.AArch64
