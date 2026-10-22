module

public import VerifiedGarbage.Impl.Pbkdf2.Md.X86
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Wrap
public import VerifiedGarbage.Impl.Bignum.X86.CopyBytes
public import VerifiedGarbage.Impl.Bignum.X86.PublicFn

/-!
# RSASSA-PSS (RFC 8017 §8.1, EMSA-PSS §9.1) on x86 (32-bit)

`sign` and `verifyPrecomputed`, for a Merkle–Damgård hash function `H` as
both the hash function and MGF1's, with the design of ARMv7
(`Impl/RsaPss/Arm.lean`): every hash is computed by `ctHash`, from `H`'s
streaming `init`, its compression function and its digest code, without
revealing the length of the message; the RSA operation is
`vg_rsa_private_checked` when signing and the precomputed public operation
when verifying, called as the x86 PKCS #1 v1.5 functions call them.

Each function runs in the frames of `wrap` (`Impl/RsaPkcs1Sig/X86/Wrap.lean`):
a push of `ebx`, `ebp`, `esi` and `edi`, and a frame of `frameBytes` bytes
whose first 80 hold the RSA operation's arguments and the rest the slots
(`sLo`, …). `ebp` holds `scratch` throughout (every function we call keeps
it), so our part of it, its first 8192 bytes (`oCW`, …), is addressed from
`ebp`; the RSA operation gets the rest. Every other value lives in a slot
between the pieces of code, and each piece loads what it needs. Every
comparison of a secret is the borrow of a subtraction (`sub`, then `sbb` of
a register with itself), and every selection a mask. Only the public key,
the lengths, `salt_len` and `any_salt_len` decide a branch or an address.

## Hashing a message of secret length (`ctHash`)

The message is the first `ℓ` bytes (slot `sL`) of `Y` (`scratch + oY`),
whose bytes after it are zero up to `nbm` blocks (slot `sNb`), with
`ℓ + 1 + L ≤ nbm B`. The streaming `init` sets the hash value at `oSt`; the
block at `oLen` gets zeros and the length field of `ℓ`
(`Impl.MdStream.X86.len64Of`, in its last 8 bytes); each byte `i` of `Y`'s
`nbm` blocks gets `0x80` ORed in under the mask of `i = ℓ`, and byte
`i mod B` of the block at `oLen` under the mask of `⌊i / B⌋` being
`⌊(ℓ + L) / B⌋` (slot `sLb`, `padLoop`); every block is copied after the
hash value at `oSt` and compressed into it, and the hash value copied to
`oSel` under the mask of being the last block of the padded message
(`compLoop`); and the digest of `oSel` is written to `oDig`.
-/

@[expose] public section

namespace VG.Impl.RsaPss.X86

open VG.X86
open VG.Impl.RsaPkcs1Sig.X86 (wrap argOff stk at_)
open VG.Impl.Bignum.X86 (copyBytes)
open VG.Impl.Pbkdf2.Md.X86 (Hash)

/-- `c₁; c₂; …`. -/
def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-! ## The frame -/

/-- The size of the inner frame: the RSA operation's arguments (80 bytes),
then the slots. -/
def frameBytes : Nat := 144

/-- `lo = k - emLen`, 0 or 1. -/
def sLo : Nat := 80
/-- The mask `0xFF >> (8 emLen - emBits)` of `maskedDB`'s first byte. -/
def sC : Nat := 84
/-- `dbLen = emLen - hLen - 1`. -/
def sDb : Nat := 88
/-- The length `ℓ` of the message `ctHash` hashes. -/
def sL : Nat := 92
/-- The number of its blocks `nbm`. -/
def sNb : Nat := 96
/-- The block `ctHash` compresses. -/
def sBi : Nat := 100
/-- MGF1's counter. -/
def sCtr : Nat := 104
/-- The bytes of `DB` masked so far. -/
def sDone : Nat := 108
/-- The accumulator of failed checks (verifying). -/
def sAcc : Nat := 112
/-- Where the padding of `DB` ends (verifying). -/
def sPos : Nat := 116
/-- The shift's distance left (verifying). -/
def sA : Nat := 120
/-- The shift's distance of this pass (verifying). -/
def sD : Nat := 124
/-- The shift's passes left (verifying). -/
def sPc : Nat := 128
/-- 1 if `any_salt_len` is not zero (verifying). -/
def sAny : Nat := 132
/-- The last block of the padded message `ctHash` hashes. -/
def sLb : Nat := 136
/-- The value of the first nonzero byte of `DB`'s padding (verifying). -/
def sVal : Nat := 140

/-! ## Our part of `scratch` -/

/-- The compression function's working space. -/
def oCW : Nat := 0
/-- The streaming state `init` sets: its first `N` bytes are the hash value,
and the block compressed is copied after it. -/
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

/-- A slot (or an argument) into `r`. -/
def ld (r : Reg) (d : Nat) : Instr := .mov r (.mem (stk d))

/-- `r` into a slot. -/
def st (r : Reg) (d : Nat) : Instr := .store (stk d) r

/-- `r := v`. -/
def mi (r : Reg) (v : Nat) : Instr := .mov r (.imm (BitVec.ofNat 32 v))

/-- `r := r + v`. -/
def addi (r : Reg) (v : Nat) : Instr := .alu .add r (.imm (BitVec.ofNat 32 v))

/-- `d := scratch + o`. -/
def atS (d : Reg) (o : Nat) : List Instr := [.mov d (.reg .ebp), addi d o]

/-- `d := d + slot o`. -/
def addSlot (d : Reg) (o : Nat) : Instr := .alu .add d (.mem (stk o))

/-- `d := DB = scratch + oEm + lo`. -/
def atDb (d : Reg) : List Instr := atS d oEm ++ [addSlot d sLo]

/-- `r := r · 2^k`. -/
def shl (r : Reg) (k : Nat) : List Instr := List.replicate k (.alu .add r (.reg r))

/-- `r :=` all ones if `r = 0`, else 0 (`r` is clobbered through the borrow
of `r - 1`). -/
def isZero (r : Reg) : List Instr := [.alu .sub r (.imm 1), .alu .sbb r (.reg r)]

/-- The loop of `n > 0` iterations of a block ending with `sub` of the count. -/
def countLoop (body : List Instr) : Prog isa := .loop (.block body) .ne

/-- `ecx > 0` zero bytes from `esi` (with `eax = 0`). -/
def zeroLoop : Prog isa := .loop (.block Impl.Bignum.X86.PublicFn.clearStep) .ne

/-- `n` zero bytes from `scratch + o`, for `zeroLoop`. -/
def clrArgs (o n : Nat) : List Instr := atS .esi o ++ [mi .ecx n, mi .eax 0]

variable (H : Hash)

/-- `log₂ B`. -/
def lgB : Nat := Nat.log2 H.B

/-! ## `ctHash` -/

/-- `ebx := scratch + oSt`, for `init`. -/
def initArgs : List Instr := atS .ebx oSt

/-- The hash value set to the initial one. -/
def initPart : Prog isa := .seq (.block initArgs) (H.st.callInit .ebx)

/-- The length field of `ℓ` bytes, in the last 8 bytes of the block at
`oLen` (the others zero), and the last block of the padded message. -/
def lenSet : List Instr :=
  atS .ebx oLen ++ [ld .eax sL, mi .ecx 0] ++ Impl.MdStream.X86.len64Of (H.B - 8) H.be ++
    [ld .eax sL, addi .eax H.L, .shift .shr .eax (lgB H), st .eax sLb]

/-- The block at `oLen`: zeros, then the length field. -/
def lenPart : Prog isa := .seq (.block (clrArgs oLen H.B)) (.seq zeroLoop (.block (lenSet H)))

/-- The padding loop's registers: `esi` the byte of `Y`, `edi` its index and
`ebx` the bytes left (`nbm B`). -/
def padArgs : List Instr := atS .esi oY ++ [mi .edi 0, ld .ebx sNb] ++ shl .ebx (lgB H)

/-- Byte `i`: `0x80` under the mask of `i = ℓ`, and byte `i mod B` of the
block at `oLen` under the mask of `⌊i / B⌋` being the last block. -/
def padBody : List Instr :=
  [.movzx8 .eax (at_ .esi 0),
    .mov .edx (.reg .edi), .alu .xor .edx (.mem (stk sL))] ++ isZero .edx ++
  [.alu .and .edx (.imm 0x80), .alu .or .eax (.reg .edx),
    .mov .edx (.reg .edi), .shift .shr .edx (lgB H), .alu .xor .edx (.mem (stk sLb))] ++ isZero .edx ++
  [.mov .ecx (.reg .edi), .alu .and .ecx (.imm (BitVec.ofNat 32 (H.B - 1))), .alu .add .ecx (.reg .ebp),
    .movzx8 .ecx (at_ .ecx oLen), .alu .and .ecx (.reg .edx), .alu .or .eax (.reg .ecx),
    .store8 (at_ .esi 0) .al, addi .esi 1, addi .edi 1, .alu .sub .ebx (.imm 1)]

/-- The padding of `Y`. -/
def padPart : Prog isa := .seq (.block (padArgs H)) (countLoop (padBody H))

/-- The first block. -/
def compInit : List Instr := [mi .eax 0, st .eax sBi]

/-- The block to compress, after the hash value at `oSt`, for `copyBytes`. -/
def blkSet : List Instr :=
  [ld .esi sBi] ++ shl .esi (lgB H) ++ [.alu .add .esi (.reg .ebp), addi .esi oY] ++ atS .ebx (oSt + H.N) ++
    [mi .ecx H.B]

/-- The compression's registers: the hash value `ebx` and the block `eax`
after it. -/
def cmpSet : List Instr := atS .ebx oSt ++ atS .eax (oSt + H.N)

/-- The selection's registers: the hash value `esi`, the selected one `edi`,
`ecx = N` and the mask `edx` of this block being the last of the padded
message. -/
def selSet : List Instr :=
  atS .esi oSt ++ atS .edi oSel ++ [ld .edx sBi, .alu .xor .edx (.mem (stk sLb))] ++ isZero .edx ++ [mi .ecx H.N]

/-- A byte of the selected hash value, under the mask. -/
def selBody : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .movzx8 .ebx (at_ .edi 0), .alu .xor .eax (.reg .ebx), .alu .and .eax (.reg .edx),
    .alu .xor .ebx (.reg .eax), .store8 (at_ .edi 0) .bl, addi .esi 1, addi .edi 1, .alu .sub .ecx (.imm 1)]

/-- The next block, and the flags of whether it was the last. -/
def compNext : List Instr := [ld .eax sBi, addi .eax 1, st .eax sBi, .alu .cmp .eax (.mem (stk sNb))]

def compBody : Prog isa :=
  seqs [.block (blkSet H), copyBytes, .block (cmpSet H), H.cmp, .block (selSet H), countLoop selBody,
    .block compNext]

/-- Every block compressed, the last one's hash value selected. -/
def compLoop : Prog isa := .seq (.block compInit) (.loop (compBody H) .ne)

/-- The digest code's registers: the selected hash value `ebx`, the digest `eax`. -/
def outSet : List Instr := atS .ebx oSel ++ atS .eax oDig

/-- The digest of the selected hash value. -/
def outPart : Prog isa := .block (outSet ++ H.out)

/-- The digest of the first `ℓ` bytes of `Y`, padded in `nbm` blocks, to
`scratch + oDig`, without revealing `ℓ`. -/
def ctHash : Prog isa := seqs [initPart H, lenPart H, padPart H, compLoop H, outPart H]

/-! ## MGF1 -/

/-- The counter and the bytes masked, zero. -/
def mgfInit : List Instr := [mi .eax 0, st .eax sCtr, st .eax sDone]

/-- `H` (at `DB + dbLen`) to `Y`, for `copyBytes`. -/
def mgfSeed : List Instr := atDb .esi ++ [addSlot .esi sDb] ++ atS .ebx oY ++ [mi .ecx H.D]

/-- The counter, big-endian, after `H` in `Y`; the message's length
`hLen + 4` and its one block, for `ctHash`. -/
def ctrSet : List Instr :=
  [ld .eax sCtr, .bswap .eax, .store (at_ .ebp (oY + H.D)) .eax, mi .eax (H.D + 4), st .eax sL, mi .eax 1,
    st .eax sNb]

/-- `DB + done` (`edi`), the digest (`esi`) and `min(hLen, dbLen - done)`
(`ecx`), for `xorBody`. -/
def xorSet : List Instr :=
  atDb .edi ++ [addSlot .edi sDone] ++ atS .esi oDig ++
    [ld .ecx sDb, .alu .sub .ecx (.mem (stk sDone)), .mov .eax (.reg .ecx),
      .alu .sub .eax (.imm (BitVec.ofNat 32 H.D)), .alu .sbb .edx (.reg .edx), .alu .and .eax (.reg .edx),
      addi .eax H.D, .mov .ecx (.reg .eax)]

/-- A byte of the digest XORed into `DB`. -/
def xorBody : List Instr :=
  [.movzx8 .eax (at_ .edi 0), .movzx8 .edx (at_ .esi 0), .alu .xor .eax (.reg .edx), .store8 (at_ .edi 0) .al,
    addi .edi 1, addi .esi 1, .alu .sub .ecx (.imm 1)]

/-- The next counter, and the flags of `done < dbLen`. -/
def mgfNext : List Instr :=
  [ld .eax sCtr, addi .eax 1, st .eax sCtr, ld .eax sDone, addi .eax H.D, st .eax sDone,
    .alu .cmp .eax (.mem (stk sDb))]

def mgfBody : Prog isa :=
  seqs [.block (clrArgs oY H.B), zeroLoop, .block (mgfSeed H), copyBytes, .block (ctrSet H), ctHash H,
    .block (xorSet H), countLoop xorBody, .block (mgfNext H)]

/-- `DB ⊕= MGF1(H, dbLen)`. -/
def mgfXor : Prog isa := .seq (.block mgfInit) (.loop (mgfBody H) .b)

/-- `DB`'s first byte (`esi`). -/
def topSet : List Instr := atDb .esi

/-- `DB`'s first byte ANDed with the mask `sC`. -/
def topAnd : List Instr := [.movzx8 .eax (at_ .esi 0), .alu .and .eax (.mem (stk sC)), .store8 (at_ .esi 0) .al]

/-! ## The encoding's parameters

From `n` (`esi`), `k` (`ecx`) and `salt_len` or the expected salt length
(`edx`): `c`, `lo` and `dbLen` to their slots, and `ebx` nonzero if
`n₀ = 0`, `emLen < hLen + 2` or the salt does not fit, with the flags of
`ebx = 0`. -/
def params : List Instr :=
  [.movzx8 .eax (at_ .esi 0),
    .mov .ebx (.reg .eax), .shift .shr .ebx 1,
    .mov .edi (.reg .ebx), .shift .shr .edi 1, .alu .or .ebx (.reg .edi),
    .mov .edi (.reg .ebx), .shift .shr .edi 2, .alu .or .ebx (.reg .edi),
    .mov .edi (.reg .ebx), .shift .shr .edi 4, .alu .or .ebx (.reg .edi),
    .mov .edi (.reg .ebx), .alu .sub .edi (.imm 1), .shift .shr .edi 31, st .edi sLo,
    mi .esi 0, .alu .sub .esi (.reg .edi), .alu .and .esi (.imm 0xFF), .alu .or .ebx (.reg .esi), st .ebx sC,
    .mov .esi (.reg .ecx), .alu .sub .esi (.reg .edi), .alu .sub .esi (.imm (BitVec.ofNat 32 (H.D + 1))),
    st .esi sDb,
    .mov .ebx (.reg .eax), .alu .sub .ebx (.imm 1), .shift .shr .ebx 31,
    .mov .edi (.reg .esi), .alu .sub .edi (.imm 1), .shift .shr .edi 31, .alu .or .ebx (.reg .edi),
    .alu .sub .esi (.imm 1), .alu .sub .esi (.reg .edx), .shift .shr .esi 31, .alu .or .ebx (.reg .esi),
    .mov .esi (.reg .edx), .shift .shr .esi 31, .alu .or .ebx (.reg .esi), .alu .test .ebx (.reg .ebx)]

/-! ## Common pieces -/

/-- The digest `mHash` (argument `j`) after the 8 zero bytes of `Y`, for
`copyBytes`. -/
def cpDig (j : Nat) : List Instr := [ld .esi (argOff frameBytes j)] ++ atS .ebx (oY + 8) ++ [mi .ecx H.D]

/-- `ℓ = 8 + hLen + sLen` (`sLen` the argument `j`) and
`nbm = ⌊(ℓ + L) / B⌋ + 1`. -/
def lenArgs (j : Nat) : List Instr :=
  [ld .eax (argOff frameBytes j), addi .eax (8 + H.D), st .eax sL, addi .eax H.L, .shift .shr .eax (lgB H),
    addi .eax 1, st .eax sNb]

/-- `Y` cleared and the digest after its 8 zero bytes. -/
def yDig (j : Nat) : Prog isa := seqs [.block (clrArgs oY 2048), zeroLoop, .block (cpDig H j), copyBytes]

/-! ## Signing

`sign(out, out_len, n, n_len, e, e_len, p, p_len, q, q_len, dp, dp_len, dq,
dq_len, qinv, qinv_len, digest, salt, salt_len, scratch, scratch_len)`, all
on the stack: argument `j` is at `argOff frameBytes j` in the inner frame. -/

/-- Argument `j`'s place. -/
abbrev arg (j : Nat) : Nat := argOff frameBytes j

/-- `scratch` into `ebp`; `n`, `k` and `salt_len` for `params`. -/
def signChk : List Instr := [ld .ebp (arg 19), ld .esi (arg 2), ld .ecx (arg 3), ld .edx (arg 18)]

/-- Zeros to `out`, and 0 returned. -/
def signFail : Prog isa := seqs [.block [ld .esi (arg 0), ld .ecx (arg 3), mi .eax 0], zeroLoop, .block [mi .eax 0]]

/-- The salt after `mHash` in `Y`, if it is not empty. -/
def cpSalt : List Instr :=
  [ld .esi (arg 17)] ++ atS .ebx (oY + 8 + H.D) ++ [ld .ecx (arg 18), .alu .test .ecx (.reg .ecx)]

/-- `EM`'s `k` bytes, for `zeroLoop`. -/
def clrEm : List Instr := atS .esi oEm ++ [ld .ecx (arg 3), mi .eax 0]

/-- `DB + dbLen - sLen - 1` (`ebx`). -/
def oneSet : List Instr :=
  atDb .ebx ++ [addSlot .ebx sDb, .alu .sub .ebx (.mem (stk (arg 18))), .alu .sub .ebx (.imm 1)]

/-- `0x01` there, `ebx` after it, the salt (`esi`) and its length (`ecx`),
and the flags of an empty salt. -/
def put1 : List Instr :=
  [mi .eax 1, .store8 (at_ .ebx 0) .al, addi .ebx 1, ld .esi (arg 17), ld .ecx (arg 18), .alu .test .ecx (.reg .ecx)]

/-- `H` (the digest) to `DB + dbLen`, for `copyBytes`. -/
def putH : List Instr := atS .esi oDig ++ atDb .ebx ++ [addSlot .ebx sDb, mi .ecx H.D]

/-- `EM`'s last byte (`esi`). -/
def bcSet : List Instr := atS .esi oEm ++ [addSlot .esi (arg 3), .alu .sub .esi (.imm 1)]

/-- `0xbc` there. -/
def putBc : List Instr := [mi .eax 0xbc, .store8 (at_ .esi 0) .al]

/-- Argument `j` to the call's argument `i`. -/
def copyArg (j i : Nat) : List Instr := [ld .eax (arg j), st .eax (4 * i)]

/-- The arguments of `vg_rsa_private_checked`: `out`, `n` (`k` bytes), `e`,
`EM` as the input (`k` bytes), the private key, and the rest of
`scratch`. -/
def privArgs : List Instr :=
  copyArg 0 0 ++ copyArg 3 1 ++ copyArg 2 2 ++ copyArg 3 3 ++ copyArg 4 4 ++ copyArg 5 5 ++
    atS .eax oEm ++ [st .eax 24] ++ copyArg 3 7 ++ copyArg 6 8 ++ copyArg 7 9 ++ copyArg 8 10 ++
    copyArg 9 11 ++ copyArg 10 12 ++ copyArg 7 13 ++ copyArg 12 14 ++ copyArg 9 15 ++ copyArg 14 16 ++
    copyArg 7 17 ++ atS .eax oRsa ++ [st .eax 72, ld .eax (arg 20), .alu .sub .eax (.imm 1024), st .eax 76]

/-- After the checks: `EM` at `scratch + oEm`. -/
def signEnc : Prog isa :=
  seqs [yDig H 16, .block (cpSalt H), .ite .e (.block []) copyBytes, .block (lenArgs H 18), ctHash H,
    .block clrEm, zeroLoop, .block oneSet, .block put1, .ite .e (.block []) copyBytes, .block (putH H), copyBytes,
    .block bcSet, .block putBc, mgfXor H, .block topSet, .block topAnd]

variable (privN : String) (privC : Prog isa)

/-- The inner frame's body. -/
def signBody : Prog isa :=
  seqs [.block (signChk ++ params H),
    .ite .ne (signFail) (seqs [signEnc H, .block privArgs, .call privN privC])]

/-- `vg_rsa_pss_<H>_mgf1_<H>_sign`, calling a checked private operation by
its name. -/
def sign : Prog isa := wrap frameBytes (signBody H privN privC)

/-! ## Verifying

`verifyPrecomputed(n, n_len, e, e_len, digest, sig, sig_len, salt_len,
any_salt_len, scratch, scratch_len, pre, pre_len)`, all on the stack. -/

/-- `scratch` into `ebp`; `sAny := [any_salt_len ≠ 0]`; `n`, `k` and the
expected salt length, `salt_len` or 0 if any, for `params`. -/
def verifyChk : List Instr :=
  [ld .ebp (arg 9), ld .edx (arg 7), ld .edi (arg 8), mi .eax 0, .alu .cmp .eax (.reg .edi),
    .alu .sbb .eax (.reg .eax), .mov .ebx (.reg .eax), .alu .and .ebx (.imm 1), st .ebx sAny,
    .alu .xor .eax (.imm (BitVec.allOnes 32)), .alu .and .edx (.reg .eax), ld .esi (arg 0), ld .ecx (arg 1)]

/-- The arguments of the precomputed public operation: `EM`'s place (`k`
bytes), `pre` (`pre_len` words), `e`, the signature (`k` bytes), and the rest
of `scratch`. -/
def pubArgs : List Instr :=
  atS .eax oEm ++ [st .eax 0] ++ copyArg 1 1 ++ copyArg 11 2 ++ copyArg 12 3 ++ copyArg 2 4 ++
    copyArg 3 5 ++ copyArg 5 6 ++ copyArg 1 7 ++ atS .eax oRsa ++
    [st .eax 32, ld .eax (arg 10), .alu .sub .eax (.imm 1024), st .eax 36]

/-- `EM` (`esi`), its last byte (`edi`) and `DB` (`ebx`). -/
def accSet : List Instr :=
  atS .esi oEm ++ [.mov .edi (.reg .esi), addSlot .edi (arg 1), .alu .sub .edi (.imm 1), .mov .ebx (.reg .esi),
    addSlot .ebx sLo]

/-- `acc :=` `EM`'s last byte `⊕ 0xbc`, the leading byte if `lo = 1`, and the
top bits of `maskedDB`'s first byte, to its slot. -/
def acc0 : List Instr :=
  [.movzx8 .eax (at_ .edi 0), .alu .xor .eax (.imm 0xbc),
    .movzx8 .edx (at_ .esi 0), mi .ecx 0, .alu .sub .ecx (.mem (stk sLo)), .alu .and .edx (.reg .ecx),
    .alu .or .eax (.reg .edx),
    .movzx8 .edx (at_ .ebx 0), ld .ecx sC, .alu .xor .ecx (.imm 0xFF), .alu .and .edx (.reg .ecx),
    .alu .or .eax (.reg .edx), st .eax sAcc]

/-- The scan's registers: `DB` (`esi`), the index (`edi`), the bytes left
(`ecx`), all ones while no nonzero byte is found (`ebx`), and the first
nonzero byte's index and value, zero in their slots. -/
def scanSet : List Instr :=
  atDb .esi ++ [ld .ecx sDb, mi .edi 0, mi .eax 0, st .eax sPos, st .eax sVal, mi .ebx 0,
    .alu .sub .ebx (.imm 1)]

/-- Byte `i`: if it is the first nonzero byte, its index and value into
their slots (through `ebp`, which `scratch` is loaded into again after the
loop). -/
def scanBody : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .mov .edx (.reg .eax)] ++ isZero .edx ++
  [.alu .xor .edx (.imm (BitVec.allOnes 32)), .alu .and .edx (.reg .ebx),
    .alu .and .eax (.reg .edx), ld .ebp sVal, .alu .or .ebp (.reg .eax), st .ebp sVal,
    .mov .eax (.reg .edi), .alu .and .eax (.reg .edx), ld .ebp sPos, .alu .or .ebp (.reg .eax), st .ebp sPos,
    .alu .xor .edx (.imm (BitVec.allOnes 32)), .alu .and .ebx (.reg .edx),
    addi .esi 1, addi .edi 1, .alu .sub .ecx (.imm 1)]

/-- `scratch` into `ebp` again; `acc |= (val ⊕ 1) | notFound`, and, if a
salt length is expected, `acc |= sLen ⊕ (dbLen - pos - 1)`; the flags of
`any_salt_len = 0`. -/
def posChk : List Instr :=
  [ld .ebp (arg 9), ld .eax sAcc, ld .edx sVal, .alu .xor .edx (.imm 1), .alu .or .eax (.reg .edx),
    .shift .shr .ebx 31, .alu .or .eax (.reg .ebx),
    ld .edx sDb, .alu .sub .edx (.mem (stk sPos)), .alu .sub .edx (.imm 1), .alu .xor .edx (.mem (stk (arg 7))),
    ld .ecx sAny, .alu .sub .ecx (.imm 1), .alu .and .edx (.reg .ecx), .alu .or .eax (.reg .edx), st .eax sAcc,
    ld .eax sAny, .alu .test .eax (.reg .eax)]

/-- The last `salt_len` bytes of `DB` after `mHash` in `Y`, if there are any. -/
def fxSalt : List Instr :=
  atDb .esi ++ [addSlot .esi sDb, .alu .sub .esi (.mem (stk (arg 7)))] ++ atS .ebx (oY + 8 + H.D) ++
    [ld .ecx (arg 7), .alu .test .ecx (.reg .ecx)]

/-- `DB` after `mHash` in `Y`, for `copyBytes`. -/
def cpDb : List Instr := atDb .esi ++ atS .ebx (oY + 8 + H.D) ++ [ld .ecx sDb]

/-- The shift by `pos + 1`: its distance, its first pass's, and its ten passes. -/
def shInit : List Instr := [ld .eax sPos, addi .eax 1, st .eax sA, mi .eax 1, st .eax sD, mi .eax 10, st .eax sPc]

/-- A pass's registers: `DB`'s place in `Y` (`esi`), the byte `d` after it
(`edi`), the bytes (`ecx = dbLen`) and the mask of bit 0 of the distance left
(`edx`). -/
def passSet : List Instr :=
  atS .esi (oY + 8 + H.D) ++
    [.mov .edi (.reg .esi), addSlot .edi sD, ld .eax sA, .alu .and .eax (.imm 1), mi .edx 0,
      .alu .sub .edx (.reg .eax), ld .ecx sDb]

/-- Byte `j` replaced by byte `j + d` under the mask. -/
def passBody : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .movzx8 .ebx (at_ .edi 0), .alu .xor .ebx (.reg .eax), .alu .and .ebx (.reg .edx),
    .alu .xor .eax (.reg .ebx), .store8 (at_ .esi 0) .al, addi .esi 1, addi .edi 1, .alu .sub .ecx (.imm 1)]

/-- The next pass, and the flags of whether it was the last. -/
def passNext : List Instr :=
  [ld .eax sA, .shift .shr .eax 1, st .eax sA, ld .eax sD, .alu .add .eax (.reg .eax), st .eax sD,
    ld .eax sPc, .alu .sub .eax (.imm 1), st .eax sPc]

def passOne : Prog isa := seqs [.block (passSet H), countLoop passBody, .block passNext]

/-- `DB`'s place in `Y` shifted left by `pos + 1` bytes, in ten passes. -/
def shift : Prog isa := .seq (.block shInit) (.loop (passOne H) .ne)

/-- `ℓ = 8 + hLen + dbLen - pos - 1` and the blocks of the longest salt,
`nbm = ⌊(8 + hLen + dbLen - 1 + L) / B⌋ + 1`. -/
def anyLen : List Instr :=
  [ld .eax sDb, .alu .sub .eax (.mem (stk sPos)), addi .eax (7 + H.D), st .eax sL,
    ld .eax sDb, addi .eax (7 + H.D + H.L), .shift .shr .eax (lgB H), addi .eax 1, st .eax sNb]

/-- The digest (`esi`) and `H` at `DB + dbLen` (`edi`), the differences
(`edx`), and the bytes (`ecx`). -/
def cmpArgs : List Instr := atS .esi oDig ++ atDb .edi ++ [addSlot .edi sDb, mi .edx 0, mi .ecx H.D]

/-- A byte's difference ORed into `edx`. -/
def cmpBody : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .movzx8 .ebx (at_ .edi 0), .alu .xor .eax (.reg .ebx), .alu .or .edx (.reg .eax),
    addi .esi 1, addi .edi 1, .alu .sub .ecx (.imm 1)]

/-- 1 if neither `acc` nor the comparison found a difference, 0 otherwise:
the borrow of `x - 1` is whether `x` is zero. -/
def result : List Instr :=
  [ld .eax sAcc, .alu .or .eax (.reg .edx), .alu .cmp .eax (.imm 1), .alu .sbb .eax (.reg .eax),
    .alu .and .eax (.imm 1)]

/-- The hash of `M'` compared with `H`, and the result. -/
def cmpH : Prog isa := seqs [.block (cmpArgs H), countLoop cmpBody, .block result]

/-- A salt of the expected length: copied from the end of `DB`. -/
def fixedPath : Prog isa :=
  seqs [yDig H 4, .block (fxSalt H), .ite .e (.block []) copyBytes, .block (lenArgs H 7), ctHash H, cmpH H]

/-- A salt of any length: `DB` shifted into place, hashed over the blocks of
the longest salt. -/
def anyPath : Prog isa :=
  seqs [yDig H 4, .block (cpDb H), copyBytes, shift H, .block (anyLen H), ctHash H, cmpH H]

variable (pubN : String) (pubC : Prog isa)

/-- After the public checks. -/
def verifyMain : Prog isa :=
  seqs [.block pubArgs, .call pubN pubC, .block accSet, .block acc0, mgfXor H, .block topSet, .block topAnd,
    .block scanSet,
    countLoop scanBody, .block posChk, .ite .e (fixedPath H) (anyPath H)]

/-- The inner frame's body. -/
def verifyBody : Prog isa :=
  seqs [.block (verifyChk ++ params H), .ite .ne (.block [mi .eax 0]) (verifyMain H pubN pubC)]

/-- `vg_rsa_pss_<H>_mgf1_<H>_verify_precomputed`, calling a precomputed
public operation by its name. -/
def verifyPrecomputed : Prog isa := wrap frameBytes (verifyBody H pubN pubC)

end VG.Impl.RsaPss.X86
