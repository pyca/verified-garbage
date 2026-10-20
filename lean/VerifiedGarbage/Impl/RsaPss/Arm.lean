module

public import VerifiedGarbage.Impl.Pbkdf2.Md.Arm
public import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Wrap
public import VerifiedGarbage.Impl.Bignum.Arm.MaskBytes
public import VerifiedGarbage.Impl.Bignum.Arm.CompareBytes

/-!
# RSASSA-PSS (RFC 8017 §8.1, EMSA-PSS §9.1) on ARMv7

`sign` and `verifyPrecomputed`, for a Merkle–Damgård hash function `H` as
both the hash function and MGF1's, as on AArch64
(`Impl/RsaPss/AArch64.lean`), whose design this follows: every hash is
computed by `ctHash`, from `H`'s streaming `init`, length field and digest
code and its compression function, without revealing the length of the
message; the RSA operation is `vg_rsa_private_checked` when signing and the
precomputed public operation when verifying, called as the ARMv7 PKCS #1
v1.5 functions call them (`Impl/RsaPkcs1Sig/Arm/`).

Each function runs in the frames of `wrap` (`Impl/RsaPkcs1Sig/Arm/Wrap.lean`):
a push of every register, and a frame of `frameBytes` bytes whose first 64
hold the RSA operation's stack arguments and the rest the slots (`sS`, …).
The first 8192 bytes of `scratch` are ours (`oCW`, …); the RSA operation
gets the rest. Every value lives in a slot between the pieces of code, and
each piece loads what it needs: the blocks that only address the stack
(through `sp` and `r12 = sp`) set up the registers of the byte loops, which
address our buffers through pointers alone. ARMv7 has no conditional select
or subtraction with borrow: every comparison of a secret is the top bit of
a difference of numbers below `2^31`, and every selection a mask. Only the
public key, the lengths, `salt_len` and `any_salt_len` decide a branch or an
address.

## Hashing a message of secret length (`ctHash`)

The message is the first `ℓ` bytes (slot `sL`) of `Y` (`scratch + oY`),
whose bytes after it are zero up to `nbm` blocks (slot `sNb`), with
`ℓ + 1 + L ≤ nbm B`. The streaming `init` sets the hash value at `oSt`;
the length field of `ℓ` is written at the end of a block of `B` bytes at
`oLen` whose other bytes are zero; then each byte `i` of `Y`'s `nbm` blocks
gets `0x80` ORed in under the mask of `i = ℓ`, and byte `i mod B` of that
block under the mask of `⌊i / B⌋ = ⌊(ℓ + L) / B⌋` (`padLoop`); every block
is compressed, and the hash value copied to `oSel` under the mask of being
the last block of the padded message (`compLoop`); and the digest of `oSel`
is written to `oDig`.
-/

@[expose] public section

namespace VG.Impl.RsaPss.Arm

open VG.Arm
open VG.Impl.RsaPkcs1Sig.Arm (wrap argOff)
open VG.Impl.Bignum.Arm (copyBytes maskBytes compareBytes)

/-- What the code needs of a hash function: its code as HMAC and PBKDF2 call
it (`md`: its streaming `init`, digest code and compression function), and
its streaming code's length field (`len`: the length field of the byte count
in `r4:r5` at `r0 + N + B - L`, writing only `r9`). -/
structure Hash where
  md : Impl.Pbkdf2.Md.Arm.Hash
  len : List Instr

/-- `c₁; c₂; …`. -/
def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-! ## The frame -/

/-- The size of the inner frame: the RSA operation's stack arguments (64
bytes), then the slots. -/
def frameBytes : Nat := 128

/-- `scratch`. -/
def sS : Nat := 64
/-- `lo = k - emLen`, 0 or 1. -/
def sLo : Nat := 68
/-- The mask `0xFF >> (8 emLen - emBits)` of `maskedDB`'s first byte. -/
def sC : Nat := 72
/-- `dbLen = emLen - hLen - 1`. -/
def sDb : Nat := 76
/-- The length `ℓ` of the message `ctHash` hashes. -/
def sL : Nat := 80
/-- The number of its blocks `nbm`. -/
def sNb : Nat := 84
/-- The block `ctHash` compresses. -/
def sBi : Nat := 88
/-- MGF1's counter. -/
def sCtr : Nat := 92
/-- The bytes of `DB` masked so far. -/
def sDone : Nat := 96
/-- The accumulator of failed checks (verifying). -/
def sAcc : Nat := 100
/-- Where the padding of `DB` ends (verifying). -/
def sPos : Nat := 104
/-- The shift's distance left (verifying). -/
def sA : Nat := 108
/-- The shift's distance of this pass (verifying). -/
def sD : Nat := 112
/-- The shift's passes left (verifying). -/
def sPc : Nat := 116
/-- 1 if `any_salt_len` is not zero (verifying). -/
def sAny : Nat := 120

/-! ## Our part of `scratch` -/

/-- The compression function's working space. -/
def oCW : Nat := 0
/-- The streaming state `init` sets: its first `N` bytes are the hash value. -/
def oSt : Nat := 512
/-- The hash value selected after the last block. -/
def oSel : Nat := 768
/-- The digest. -/
def oDig : Nat := 832
/-- A block whose last `L` bytes are the length field, the others zero. -/
def oLen : Nat := 896
/-- `EM` (signing), or the signature's RSAVP1 (verifying): `k` bytes. -/
def oEm : Nat := 1024
/-- The message hashed by `ctHash`, and its padding: 2048 bytes. -/
def oY : Nat := 2048
/-- Where the RSA operation's working space starts. -/
def oRsa : Nat := 8192

/-! ## Instructions -/

/-- `d := v`, for `v < 2^16`. -/
def mw (d : Reg) (v : Nat) : Instr := .movw d (BitVec.ofNat 16 v)

/-- `r12 := sp`. -/
def sp0 : Instr := .addSp .r12 0

/-- `r` into a slot, through `r12 = sp`. -/
def st (r : Reg) (o : Nat) : Instr := .str r .r12 o

/-- A slot into `r`. -/
def ld (r : Reg) (o : Nat) : Instr := .ldrSp r o

/-- `d := scratch + o` (`lr` is used). -/
def atS (d : Reg) (o : Nat) : List Instr := [ld d sS, mw .lr o, .dp .add d d (.reg .lr)]

/-- `d := d + slot o` (`lr` is used). -/
def addSlot (d : Reg) (o : Nat) : List Instr := [ld .lr o, .dp .add d d (.reg .lr)]

/-- `d := DB = scratch + oEm + lo` (`lr` is used). -/
def atDb (d : Reg) : List Instr := atS d oEm ++ addSlot d sLo

/-- The loop of `n > 0` iterations of a block ending with `subs lr, lr, #1`. -/
def countLoop (body : List Instr) : Prog isa := .loop (.block body) .ne

variable (H : Hash)

/-- The block size, the digest size, the size of the hash value and of the
length field. -/
abbrev blk : Nat := H.md.st.B
abbrev dig : Nat := H.md.st.D
abbrev hvN : Nat := H.md.N
abbrev lenL : Nat := H.md.L

/-- `log₂ B`. -/
def lgB : Nat := Nat.log2 (blk H)

/-! ## `ctHash` -/

/-- `r0 := scratch + oSt`, for `init`. -/
def initArgs : List Instr := sp0 :: atS .r0 oSt

/-- The block at `oLen`, for `maskBytes` with a zero mask. -/
def lenClr : List Instr := sp0 :: (atS .r0 oLen ++ [mw .r2 0, mw .lr (blk H)])

/-- `r0 := scratch + oLen - N` and `r5:r4 := ℓ`, for the length field. -/
def lenArgs : List Instr := sp0 :: (atS .r0 (oLen - hvN H) ++ [ld .r4 sL, mw .r5 0])

/-- The padding loop's registers: `r0` the byte of `Y`, `r1` its index,
`lr` the bytes left (`nbm B`), `r4 = ℓ`, `r5` the last block of the padded
message, `r6` the block at `oLen`, `r7 = 0` and `r9 = B - 1`. -/
def padArgs : List Instr :=
  sp0 :: (atS .r0 oY ++ atS .r6 oLen ++
    [mw .r1 0, ld .r4 sL, mw .r5 (lenL H), .dp .add .r5 .r4 (.reg .r5), .mov .r5 (.shifted .r5 .lsr (lgB H)),
      mw .r7 0, mw .r9 (blk H - 1), ld .lr sNb, .mov .lr (.shifted .lr .lsl (lgB H))])

/-- Byte `i`: `0x80` under the mask of `i = ℓ`, and byte `i mod B` of the
block at `oLen` under the mask of `⌊i / B⌋` being the last block. -/
def padBody : List Instr :=
  [.ldrb .r2 .r0 0,
    .dp .eor .r3 .r1 (.reg .r4), .dp .sub .r3 .r3 (.imm 1), .mov .r3 (.shifted .r3 .lsr 31),
    .dp .orr .r2 .r2 (.shifted .r3 .lsl 7),
    .mov .r3 (.shifted .r1 .lsr (lgB H)), .dp .eor .r3 .r3 (.reg .r5), .dp .sub .r3 .r3 (.imm 1),
    .mov .r3 (.shifted .r3 .lsr 31), .dp .sub .r3 .r7 (.reg .r3),
    .dp .and .r8 .r1 (.reg .r9), .dp .add .r8 .r8 (.reg .r6), .ldrb .r8 .r8 0, .dp .and .r8 .r8 (.reg .r3),
    .dp .orr .r2 .r2 (.reg .r8),
    .strb .r2 .r0 0, .dp .add .r0 .r0 (.imm 1), .dp .add .r1 .r1 (.imm 1), .subs .lr .lr (.imm 1)]

/-- The first block. -/
def compInit : List Instr := [sp0, mw .r0 0, st .r0 sBi]

/-- The compression's registers: the hash value `r0`, the working space
`r3` and the block `r6`. -/
def compSet : List Instr :=
  sp0 :: (atS .r0 oSt ++ atS .r3 oCW ++ atS .r6 oY ++
    [ld .r1 sBi, .mov .r1 (.shifted .r1 .lsl (lgB H)), .dp .add .r6 .r6 (.reg .r1)])

/-- The selection's registers: the hash value `r0`, the selected one `r1`,
`lr = N` and the mask `r2` of this block being the last of the padded
message. -/
def selSet : List Instr :=
  sp0 :: (atS .r0 oSt ++ atS .r1 oSel ++
    [ld .r2 sBi, .mov .r2 (.shifted .r2 .lsl (lgB H)), ld .r3 sL, mw .r4 (lenL H), .dp .add .r3 .r3 (.reg .r4),
      .mov .r3 (.shifted .r3 .lsr (lgB H)), .mov .r3 (.shifted .r3 .lsl (lgB H)), .dp .eor .r2 .r2 (.reg .r3),
      .dp .sub .r2 .r2 (.imm 1), .mov .r2 (.shifted .r2 .lsr 31), mw .r3 0, .dp .sub .r2 .r3 (.reg .r2),
      mw .lr (hvN H)])

/-- A byte of the selected hash value, under the mask. -/
def selBody : List Instr :=
  [.ldrb .r3 .r0 0, .ldrb .r4 .r1 0, .dp .eor .r3 .r3 (.reg .r4), .dp .and .r3 .r3 (.reg .r2),
    .dp .eor .r4 .r4 (.reg .r3), .strb .r4 .r1 0, .dp .add .r0 .r0 (.imm 1), .dp .add .r1 .r1 (.imm 1),
    .subs .lr .lr (.imm 1)]

/-- The next block, and the flags of whether it was the last. -/
def compNext : List Instr := [sp0, ld .r0 sBi, .dp .add .r0 .r0 (.imm 1), st .r0 sBi, ld .r1 sNb, .cmp .r0 (.reg .r1)]

def compBody : Prog isa :=
  seqs [.block (compSet H), H.md.compressBlock, .block (selSet H),
    countLoop selBody, .block compNext]

/-- Every block compressed, the last one's hash value selected. -/
def compLoop : Prog isa := .seq (.block compInit) (.loop (compBody H) .ne)

/-- The digest code's registers: the selected hash value `r0`, the digest `r6`. -/
def outSet : List Instr := sp0 :: (atS .r0 oSel ++ atS .r6 oDig)

/-- The hash value set to the initial one. -/
def initPart : Prog isa := .seq (.block initArgs) (.call H.md.st.initN H.md.st.initC)

/-- The block at `oLen`: zeros, then the length field. -/
def lenPart : Prog isa :=
  .seq (.block (lenClr H)) (.seq maskBytes (.seq (.block (lenArgs H)) (.block H.len)))

/-- The padding of `Y`. -/
def padPart : Prog isa := .seq (.block (padArgs H)) (countLoop (padBody H))

/-- The digest of the selected hash value. -/
def outPart : Prog isa := .seq (.block outSet) (.block H.md.out)

/-- The digest of the first `ℓ` bytes of `Y`, padded in `nbm` blocks, to
`scratch + oDig`, without revealing `ℓ`. -/
def ctHash : Prog isa := seqs [initPart H, lenPart H, padPart H, compLoop H, outPart H]

/-! ## MGF1 -/

/-- The counter and the bytes masked, zero. -/
def mgfInit : List Instr := [sp0, mw .r0 0, st .r0 sCtr, st .r0 sDone]

/-- `Y`'s first block, for `maskBytes` with a zero mask. -/
def mgfClr : List Instr := sp0 :: (atS .r0 oY ++ [mw .r2 0, mw .lr (blk H)])

/-- `H` (at `DB + dbLen`) to `Y`, for `copyBytes`. -/
def mgfSeed : List Instr := sp0 :: (atS .r0 oY ++ atDb .r1 ++ addSlot .r1 sDb ++ [mw .lr (dig H)])

/-- The counter's place after `H` in `Y` (`r0`) and the counter (`r1`); the
message's length `hLen + 4` and its one block, for `ctHash`. -/
def ctrSet : List Instr :=
  sp0 :: (atS .r0 (oY + dig H) ++ [ld .r1 sCtr, mw .r2 (dig H + 4), st .r2 sL, mw .r2 1, st .r2 sNb])

/-- The counter, big-endian. -/
def ctrPut : List Instr :=
  [.mov .r2 (.shifted .r1 .lsr 24), .strb .r2 .r0 0, .mov .r2 (.shifted .r1 .lsr 16), .strb .r2 .r0 1,
    .mov .r2 (.shifted .r1 .lsr 8), .strb .r2 .r0 2, .strb .r1 .r0 3]

/-- `DB + done` (`r0`), the digest (`r1`) and `min(hLen, dbLen - done)`
(`lr`), for `xorBody`. -/
def xorSet : List Instr :=
  sp0 :: (atDb .r0 ++ addSlot .r0 sDone ++ atS .r1 oDig ++
    [ld .r2 sDone, ld .r3 sDb, .dp .sub .r3 .r3 (.reg .r2), mw .r4 (dig H), .dp .sub .r5 .r3 (.reg .r4),
      .mov .r5 (.shifted .r5 .lsr 31), mw .r6 0, .dp .sub .r5 .r6 (.reg .r5), .dp .eor .r6 .r3 (.reg .r4),
      .dp .and .r6 .r6 (.reg .r5), .dp .eor .lr .r4 (.reg .r6)])

/-- A byte of the digest XORed into `DB`. -/
def xorBody : List Instr :=
  [.ldrb .r2 .r0 0, .ldrb .r3 .r1 0, .dp .eor .r2 .r2 (.reg .r3), .strb .r2 .r0 0, .dp .add .r0 .r0 (.imm 1),
    .dp .add .r1 .r1 (.imm 1), .subs .lr .lr (.imm 1)]

/-- The next counter, and the flags of `done ≥ dbLen`. -/
def mgfNext : List Instr :=
  [sp0, ld .r0 sCtr, .dp .add .r0 .r0 (.imm 1), st .r0 sCtr, ld .r0 sDone, mw .r1 (dig H), .dp .add .r0 .r0 (.reg .r1),
    st .r0 sDone, ld .r1 sDb, .dp .sub .r0 .r0 (.reg .r1), .mov .r0 (.shifted .r0 .lsr 31), .cmp .r0 (.imm 0)]

def mgfBody : Prog isa :=
  seqs [.block (mgfClr H), maskBytes, .block (mgfSeed H), copyBytes, .block (ctrSet H), .block ctrPut, ctHash H,
    .block (xorSet H), countLoop xorBody, .block (mgfNext H)]

/-- `DB ⊕= MGF1(H, dbLen)`. -/
def mgfXor : Prog isa := .seq (.block mgfInit) (.loop (mgfBody H) .ne)

/-- `DB`'s first byte, and the mask `sC`. -/
def topSet : List Instr := sp0 :: (atDb .r0 ++ [ld .r1 sC])

/-- `DB`'s first byte ANDed with the mask. -/
def topAnd : List Instr := [.ldrb .r2 .r0 0, .dp .and .r2 .r2 (.reg .r1), .strb .r2 .r0 0]

/-! ## The encoding's parameters

From `n` (`r0`), `k` (`r1`), `salt_len` or the expected salt length (`r2`)
and `hLen + 1` (`r11`): `c`, `lo` and `dbLen` to their slots, `r9 :=
dbLen - 1`, the longest salt, and `r8` nonzero if `n₀ = 0` or
`emLen < hLen + 2`. -/
def params : List Instr :=
  [.ldrb .r3 .r0 0,
    .mov .r4 (.shifted .r3 .lsr 1), .dp .orr .r4 .r4 (.shifted .r4 .lsr 1), .dp .orr .r4 .r4 (.shifted .r4 .lsr 2),
    .dp .orr .r4 .r4 (.shifted .r4 .lsr 4),
    .dp .sub .r5 .r4 (.imm 1), .mov .r5 (.shifted .r5 .lsr 31),
    mw .r6 0, .dp .sub .r6 .r6 (.reg .r5), .dp .and .r6 .r6 (.imm 0xFF), .dp .orr .r4 .r4 (.reg .r6),
    .dp .sub .r6 .r1 (.reg .r5), .dp .sub .r7 .r6 (.reg .r11),
    st .r4 sC, st .r5 sLo, st .r7 sDb,
    .dp .sub .r8 .r3 (.imm 1), .mov .r8 (.shifted .r8 .lsr 31),
    .dp .sub .r9 .r7 (.imm 1), .dp .orr .r8 .r8 (.shifted .r9 .lsr 31)]

/-- `r8` also nonzero if the salt length `r2` is more than `r9`; the flags
of `r8 = 0`. -/
def saltFits : List Instr :=
  [.dp .sub .r9 .r9 (.reg .r2), .dp .orr .r8 .r8 (.shifted .r9 .lsr 31), .dp .orr .r8 .r8 (.shifted .r2 .lsr 31),
    .cmp .r8 (.imm 0)]

/-! ## Common pieces -/

/-- `Y` (2048 bytes), for `maskBytes` with a zero mask. -/
def clrY : List Instr := sp0 :: (atS .r0 oY ++ [mw .r2 0, mw .lr 2048])

/-- The digest `mHash` (argument `j`) after the 8 zero bytes of `Y`, for
`copyBytes`. -/
def cpDig (j : Nat) : List Instr := sp0 :: (atS .r0 (oY + 8) ++ [ld .r1 (argOff frameBytes j), mw .lr (dig H)])

/-- `ℓ = 8 + hLen + sLen` (`sLen` the argument `j`) and
`nbm = ⌊(ℓ + L) / B⌋ + 1`. -/
def lenSet (j : Nat) : List Instr :=
  [sp0, ld .r0 (argOff frameBytes j), mw .r1 (8 + dig H), .dp .add .r0 .r0 (.reg .r1), st .r0 sL, mw .r1 (lenL H),
    .dp .add .r0 .r0 (.reg .r1), .mov .r0 (.shifted .r0 .lsr (lgB H)), .dp .add .r0 .r0 (.imm 1), st .r0 sNb]

/-- `Y` cleared and the digest after its 8 zero bytes. -/
def yDig (j : Nat) : Prog isa := seqs [.block clrY, maskBytes, .block (cpDig H j), copyBytes]

/-! ## Signing

`sign(out = r0, out_len = r1, n = r2, n_len = r3, e, e_len, p, p_len, q,
q_len, dp, dp_len, dq, dq_len, qinv, qinv_len, digest, salt, salt_len,
scratch, scratch_len)`, the last seventeen on the stack: argument `j` is at
`argOff frameBytes j` in the inner frame. -/

/-- Argument `j`'s place. -/
abbrev arg (j : Nat) : Nat := argOff frameBytes j

/-- `scratch` to its slot; `n`, `k`, `salt_len` and `hLen + 1` for `params`. -/
def signChk : List Instr :=
  [sp0, ld .r0 (arg 19), st .r0 sS, ld .r0 (arg 2), ld .r1 (arg 3), ld .r2 (arg 18), mw .r11 (dig H + 1)]

/-- Zeros to `out`, for `maskBytes`, and 0 returned. -/
def signFail : Prog isa :=
  seqs [.block [sp0, ld .r0 (arg 0), ld .lr (arg 3), mw .r2 0], maskBytes, .block [mw .r0 0]]

/-- The salt after `mHash` in `Y`, if it is not empty. -/
def cpSalt : List Instr := sp0 :: (atS .r0 (oY + 8 + dig H) ++ [ld .r1 (arg 17), ld .lr (arg 18), .cmp .lr (.imm 0)])

/-- `EM`'s `k` bytes, for `maskBytes` with a zero mask. -/
def clrEm : List Instr := sp0 :: (atS .r0 oEm ++ [mw .r2 0, ld .lr (arg 3)])

/-- `DB + dbLen - sLen - 1` (`r0`), the salt (`r1`) and its length (`lr`). -/
def saltPos : List Instr :=
  sp0 :: (atDb .r0 ++ addSlot .r0 sDb ++
    [ld .r1 (arg 18), .dp .sub .r0 .r0 (.reg .r1), .dp .sub .r0 .r0 (.imm 1), ld .r1 (arg 17), ld .lr (arg 18)])

/-- `0x01`, then `r0` after it; the flags of an empty salt. -/
def put1 : List Instr := [mw .r2 1, .strb .r2 .r0 0, .dp .add .r0 .r0 (.imm 1), .cmp .lr (.imm 0)]

/-- `H` (the digest) to `DB + dbLen`, for `copyBytes`. -/
def putH : List Instr := sp0 :: (atDb .r0 ++ addSlot .r0 sDb ++ atS .r1 oDig ++ [mw .lr (dig H)])

/-- `EM`'s last byte. -/
def bcSet : List Instr := sp0 :: (atS .r0 oEm ++ [ld .r1 (arg 3), .dp .add .r0 .r0 (.reg .r1), .dp .sub .r0 .r0 (.imm 1)])

def bcPut : List Instr := [mw .r1 0xbc, .strb .r1 .r0 0]

/-- Argument `j` to the call's stack argument `i`. -/
def copyArg (j i : Nat) : List Instr := [ld .r0 (arg j), st .r0 (4 * i)]

/-- The arguments of `vg_rsa_private_checked`: `out`, `n` (`k` bytes), `e`,
`EM` as the input (`k` bytes), the private key, and the rest of
`scratch`. -/
def privArgs : List Instr :=
  [sp0] ++ copyArg 4 0 ++ copyArg 5 1 ++ atS .r0 oEm ++ [st .r0 8] ++ copyArg 3 3 ++ copyArg 6 4 ++
    copyArg 7 5 ++ copyArg 8 6 ++ copyArg 9 7 ++ copyArg 10 8 ++ copyArg 7 9 ++ copyArg 12 10 ++
    copyArg 9 11 ++ copyArg 14 12 ++ copyArg 7 13 ++ atS .r0 oRsa ++ [st .r0 56, ld .r0 (arg 20), mw .r1 1024,
    .dp .sub .r0 .r0 (.reg .r1), st .r0 60, ld .r0 (arg 0), ld .r1 (arg 3), ld .r2 (arg 2), ld .r3 (arg 3)]

/-- After the checks: `EM` at `scratch + oEm`. -/
def signEnc : Prog isa :=
  seqs [yDig H 16, .block (cpSalt H), .ite .eq (.block []) copyBytes, .block (lenSet H 18), ctHash H,
    .block clrEm, maskBytes, .block saltPos, .block put1, .ite .eq (.block []) copyBytes, .block (putH H), copyBytes,
    .block bcSet, .block bcPut, mgfXor H, .block topSet, .block topAnd]

variable (privN : String) (privC : Prog isa)

/-- The inner frame's body. -/
def signBody : Prog isa :=
  seqs [.block (signChk H), .block (params ++ saltFits),
    .ite .ne signFail (seqs [signEnc H, .block privArgs, .call privN privC])]

/-- `vg_rsa_pss_<H>_mgf1_<H>_sign`, calling a checked private operation by
its name. -/
def sign : Prog isa := wrap frameBytes (signBody H privN privC)

/-! ## Verifying

`verifyPrecomputed(n = r0, n_len = r1, e = r2, e_len = r3, digest, sig,
sig_len, salt_len, any_salt_len, scratch, scratch_len, pre, pre_len)`, the
last nine on the stack. -/

/-- `scratch` to its slot; `n`, `k`, `salt_len`, `any_salt_len` and
`hLen + 1` for the checks. -/
def verifyChk : List Instr :=
  [sp0, ld .r0 (arg 9), st .r0 sS, ld .r0 (arg 0), ld .r1 (arg 1), ld .r2 (arg 7), ld .r10 (arg 8),
    mw .r11 (dig H + 1)]

/-- `sAny := [any_salt_len ≠ 0]` and `r2 :=` the expected salt length,
`salt_len` or 0 if any. -/
def expLen : List Instr :=
  [mw .r3 0, .dp .sub .r3 .r3 (.reg .r10), .dp .orr .r3 .r3 (.reg .r10), .mov .r3 (.shifted .r3 .lsr 31),
    st .r3 sAny, .dp .sub .r10 .r3 (.imm 1), .dp .and .r2 .r2 (.reg .r10)]

/-- The arguments of the precomputed public operation: `EM`'s place (`k`
bytes), `pre` (`pre_len` words), `e`, the signature (`k` bytes), and the rest
of `scratch`. -/
def pubArgs : List Instr :=
  [sp0] ++ copyArg 2 0 ++ copyArg 3 1 ++ copyArg 5 2 ++ copyArg 1 3 ++ atS .r0 oRsa ++
    [st .r0 16, ld .r0 (arg 10), mw .r1 1024, .dp .sub .r0 .r0 (.reg .r1), st .r0 20] ++ atS .r0 oEm ++
    [ld .r1 (arg 1), ld .r2 (arg 11), ld .r3 (arg 12)]

/-- `EM` (`r0`), its last byte (`r7`), `DB` (`r6`), `lo` (`r4`) and `c` (`r5`). -/
def accSet : List Instr :=
  sp0 :: (atS .r0 oEm ++ [ld .r1 (arg 1), .dp .add .r7 .r0 (.reg .r1), .dp .sub .r7 .r7 (.imm 1), ld .r4 sLo,
    .dp .add .r6 .r0 (.reg .r4), ld .r5 sC])

/-- `acc :=` `EM`'s last byte `⊕ 0xbc`, the leading byte if `lo = 1`, and the
top bits of `maskedDB`'s first byte, to its slot. -/
def acc0 : List Instr :=
  [.ldrb .r8 .r7 0, .dp .eor .r8 .r8 (.imm 0xbc),
    .ldrb .r9 .r0 0, mw .r10 0, .dp .sub .r10 .r10 (.reg .r4), .dp .and .r9 .r9 (.reg .r10), .dp .orr .r8 .r8 (.reg .r9),
    .ldrb .r9 .r6 0, .dp .eor .r10 .r5 (.imm 0xFF), .dp .and .r9 .r9 (.reg .r10), .dp .orr .r8 .r8 (.reg .r9),
    st .r8 sAcc]

/-- The scan's registers: `DB` (`r0`), the index (`r1`), the bytes left
(`lr`), the first nonzero byte's index (`r4`) and value (`r5`), all ones
while none is found (`r6`), and 0 (`r7`). -/
def scanSet : List Instr :=
  sp0 :: (atDb .r0 ++ [ld .lr sDb, mw .r1 0, mw .r4 0, mw .r5 0, mw .r7 0, .dp .sub .r6 .r7 (.imm 1)])

/-- Byte `i`: if it is the first nonzero byte, its index and value. -/
def scanBody : List Instr :=
  [.ldrb .r2 .r0 0, .dp .sub .r3 .r2 (.imm 1), .mov .r3 (.shifted .r3 .lsr 31), .dp .sub .r8 .r3 (.imm 1),
    .dp .and .r8 .r8 (.reg .r6), .dp .and .r9 .r1 (.reg .r8), .dp .orr .r4 .r4 (.reg .r9), .dp .and .r9 .r2 (.reg .r8),
    .dp .orr .r5 .r5 (.reg .r9), .dp .sub .r9 .r7 (.reg .r3), .dp .and .r6 .r6 (.reg .r9),
    .dp .add .r0 .r0 (.imm 1), .dp .add .r1 .r1 (.imm 1), .subs .lr .lr (.imm 1)]

/-- `acc` (`r1`), `dbLen` (`r2`), `salt_len` (`r3`) and `[any_salt_len ≠ 0]` (`r8`). -/
def posSet : List Instr := [sp0, ld .r1 sAcc, ld .r2 sDb, ld .r3 (arg 7), ld .r8 sAny]

/-- `acc |= (val ⊕ 1) | notFound`, `pos` to its slot, and, if a salt length
is expected, `acc |= sLen ⊕ (dbLen - pos - 1)`. -/
def posChk : List Instr :=
  [.dp .eor .r5 .r5 (.imm 1), .dp .orr .r5 .r5 (.shifted .r6 .lsr 31), .dp .orr .r1 .r1 (.reg .r5), st .r4 sPos,
    .dp .sub .r2 .r2 (.reg .r4), .dp .sub .r2 .r2 (.imm 1), .dp .eor .r2 .r2 (.reg .r3), .dp .sub .r8 .r8 (.imm 1),
    .dp .and .r2 .r2 (.reg .r8), .dp .orr .r1 .r1 (.reg .r2), st .r1 sAcc]

/-- The flags of `any_salt_len = 0`. -/
def anySet : List Instr := [sp0, ld .r0 sAny, .cmp .r0 (.imm 0)]

/-- The last `salt_len` bytes of `DB` after `mHash` in `Y`, if there are any. -/
def fxSalt : List Instr :=
  sp0 :: (atS .r0 (oY + 8 + dig H) ++ atDb .r1 ++ addSlot .r1 sDb ++
    [ld .r2 (arg 7), .dp .sub .r1 .r1 (.reg .r2), ld .lr (arg 7), .cmp .lr (.imm 0)])

/-- `DB` after `mHash` in `Y`, for `copyBytes`. -/
def cpDb : List Instr := sp0 :: (atS .r0 (oY + 8 + dig H) ++ atDb .r1 ++ [ld .lr sDb])

/-- The shift by `pos + 1`: its distance, its first pass's, and its ten passes. -/
def shInit : List Instr :=
  [sp0, ld .r0 sPos, .dp .add .r0 .r0 (.imm 1), st .r0 sA, mw .r0 1, st .r0 sD, mw .r0 10, st .r0 sPc]

/-- A pass's registers: `DB`'s place in `Y` (`r0`), the byte `d` after it
(`r1`), the bytes (`lr = dbLen`) and the mask of bit 0 of the distance left
(`r2`). -/
def passSet : List Instr :=
  sp0 :: (atS .r0 (oY + 8 + dig H) ++
    [ld .r1 sD, .dp .add .r1 .r0 (.reg .r1), ld .r2 sA, .dp .and .r2 .r2 (.imm 1), mw .r3 0,
      .dp .sub .r2 .r3 (.reg .r2), ld .lr sDb])

/-- Byte `j` replaced by byte `j + d` under the mask. -/
def passBody : List Instr :=
  [.ldrb .r3 .r0 0, .ldrb .r4 .r1 0, .dp .eor .r4 .r4 (.reg .r3), .dp .and .r4 .r4 (.reg .r2),
    .dp .eor .r3 .r3 (.reg .r4), .strb .r3 .r0 0, .dp .add .r0 .r0 (.imm 1), .dp .add .r1 .r1 (.imm 1),
    .subs .lr .lr (.imm 1)]

/-- The next pass, and the flags of whether it was the last. -/
def passNext : List Instr :=
  [sp0, ld .r0 sA, .mov .r0 (.shifted .r0 .lsr 1), st .r0 sA, ld .r0 sD, .dp .add .r0 .r0 (.reg .r0), st .r0 sD,
    ld .r0 sPc, .dp .sub .r0 .r0 (.imm 1), st .r0 sPc, .cmp .r0 (.imm 0)]

def passOne : Prog isa := seqs [.block (passSet H), countLoop passBody, .block passNext]

/-- `DB`'s place in `Y` shifted left by `pos + 1` bytes, in ten passes. -/
def shift : Prog isa := .seq (.block shInit) (.loop (passOne H) .ne)

/-- `ℓ = 8 + hLen + dbLen - pos - 1` and the blocks of the longest salt,
`nbm = ⌊(8 + hLen + dbLen - 1 + L) / B⌋ + 1`. -/
def anyLen : List Instr :=
  [sp0, ld .r0 sDb, ld .r1 sPos, .dp .sub .r0 .r0 (.reg .r1), mw .r1 (7 + dig H), .dp .add .r0 .r0 (.reg .r1),
    st .r0 sL, ld .r0 sDb, mw .r1 (7 + dig H + lenL H), .dp .add .r0 .r0 (.reg .r1),
    .mov .r0 (.shifted .r0 .lsr (lgB H)), .dp .add .r0 .r0 (.imm 1), st .r0 sNb]

/-- The digest and `H` (at `DB + dbLen`), for `compareBytes`. -/
def cmpSet : List Instr :=
  sp0 :: (atS .r0 oDig ++ atDb .r1 ++ addSlot .r1 sDb ++ [mw .r2 0, mw .lr (dig H)])

/-- 1 if neither `acc` nor the comparison found a difference, 0 otherwise: the top bit
of `x | -x` is whether `x` is not zero. -/
def result : List Instr :=
  [sp0, ld .r0 sAcc, .dp .orr .r0 .r0 (.reg .r2), mw .r1 0, .dp .sub .r1 .r1 (.reg .r0), .dp .orr .r0 .r0 (.reg .r1),
    .mov .r0 (.shifted .r0 .lsr 31), .dp .eor .r0 .r0 (.imm 1)]

/-- The hash of `M'` compared with `H`, and the result. -/
def cmpH : Prog isa := seqs [.block (cmpSet H), compareBytes, .block result]

/-- A salt of the expected length: copied from the end of `DB`. -/
def fixedPath : Prog isa :=
  seqs [yDig H 4, .block (fxSalt H), .ite .eq (.block []) copyBytes, .block (lenSet H 7), ctHash H, cmpH H]

/-- A salt of any length: `DB` shifted into place, hashed over the blocks of
the longest salt. -/
def anyPath : Prog isa :=
  seqs [yDig H 4, .block (cpDb H), copyBytes, shift H, .block (anyLen H), ctHash H, cmpH H]

variable (pubN : String) (pubC : Prog isa)

/-- After the public checks. -/
def verifyMain : Prog isa :=
  seqs [.block pubArgs, .call pubN pubC, .block accSet, .block acc0, mgfXor H, .block topSet, .block topAnd,
    .block scanSet, countLoop scanBody, .block posSet, .block posChk, .block anySet,
    .ite .eq (fixedPath H) (anyPath H)]

/-- The inner frame's body. -/
def verifyBody : Prog isa :=
  seqs [.block (verifyChk H), .block (params ++ expLen ++ saltFits),
    .ite .ne (.block [mw .r0 0]) (verifyMain H pubN pubC)]

/-- `vg_rsa_pss_<H>_mgf1_<H>_verify_precomputed`, calling a precomputed
public operation by its name. -/
def verifyPrecomputed : Prog isa := wrap frameBytes (verifyBody H pubN pubC)

end VG.Impl.RsaPss.Arm
