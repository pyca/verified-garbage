module

public import VerifiedGarbage.Impl.RsaPss.Arm

/-!
# RSAES-OAEP (RFC 8017 §7.1) on ARMv7

`encryptPrecomputed` and `decrypt`, for a hash function `H` (the label's)
and MGF1's hash function `G`, each a streaming hash function
(`Impl.Pbkdf2.Stream.Arm.Hash`: its `init`, `update` and `finalize`), with
the steps of AArch64 (`Impl/RsaOaep/AArch64.lean`) and the frames, slots,
byte loops and RSA calls of the ARMv7 RSASSA-PSS functions
(`Impl/RsaPss/Arm.lean`), whose definitions this file reuses: the public-key
operation with the precomputed modulus (`vg_rsa_public_precomputed_checked`)
when encrypting, the private-key operation checked against `e`
(`vg_rsa_private_checked`) when decrypting.

Each function runs in the frames of `wrap`: a push of every register, and a
frame of `frameBytes` bytes whose first 64 hold the RSA operation's stack
arguments and the rest the slots. The first 8192 bytes of `scratch` are
ours (`oEm`, …); the RSA operation gets the rest. Every value lives in a
slot between the pieces of code: the blocks that only address the stack
(through `sp` and `r12 = sp`) set up the registers of the byte loops and of
the calls, which address our buffers through pointers alone. `update` and
`finalize` take some of their arguments on the stack: each call of them is
in a frame that pushes those (`Impl/Pbkdf2/Stream/Arm.lean`), below our
frame.

## MGF1

`mgfXor`: `dst ⊕= MGF1(src, dstLen)` with `G`, the addresses and lengths
in the slots `sSrc`, `sSrcLen`, `sDst`, `sDstLen`, as on AArch64
(`Impl/RsaOaep/AArch64/Mgf1.lean`): for each counter `c` from 0, while
`done = c hLen` is below `dstLen`, the state at `scratch + oSt` is set by
`init`, `update` absorbs `src` and `I2OSP(c, 4)` (at `scratch + oCtr`),
`finalize` writes the digest to `scratch + oDig`, and its first
`min(hLen, dstLen - done)` bytes are XORed into `dst + done`
(`Impl.RsaPss.Arm.xorBody`). Every length is public.

## Encryption

`encryptPrecomputed(out = r0, out_len = r1, n = r2, n_len = r3, e, e_len,
label, label_len, msg, msg_len, seed, scratch, scratch_len, pre, pre_len)`,
the last eleven on the stack. If `k < 2 hLen + 2` or
`msg_len > k - 2 hLen - 2` (public), it writes zeros to `out` and returns 0.
Otherwise it writes `EM = 0x00 ‖ seed ‖ DB` to `scratch` (`DB = lHash ‖ 0… ‖
0x01 ‖ M`, the label hashed with `H`), masks `DB` with MGF1 of the seed and
then the seed with MGF1 of `maskedDB` (`G`), and returns the precomputed
public operation of `EM` into `out`.

## Decryption

`decrypt(out = r0, out_len = r1, msg_len = r2, n = r3, n_len, e, e_len, p,
p_len, q, q_len, dp, dp_len, dq, dq_len, qinv, qinv_len, label, label_len,
ct, ct_len, scratch, scratch_len)`, the last nineteen on the stack.
`vg_rsa_private_checked` writes `EM` (or zeros) to `scratch` and returns `r`
(1, 0 or 2), which only selects values without a branch. If
`k < 2 hLen + 2` (public), the result is `r = 2 ? 2 : 0`, with zeros to
`out` and `*msg_len`. Otherwise, without a branch on anything secret: the
label is hashed (`H`) to `scratch + oLh`, the seed and `DB` unmasked in
place (`G`); the accumulator `acc` ORs `EM`'s first byte into the
comparison of `lHash'` with `lHash` (`Bignum.Arm.compareBytes`); the scan of
`T = DB[hLen..]` (`t = k - 2 hLen - 1` bytes, `Impl.RsaPss.Arm.scanBody`)
finds the index `idx` and the value of its first byte that is not zero, if
any, and `acc` takes in that this byte is `0x01`; `T` is copied into the
2048-byte buffer `scratch + oBuf`, zeros after it, and shifted left by
`idx + 1` bytes in ten passes (`Impl.RsaPss.Arm.passBody`), pass `j` moving
each of its first 1024 bytes `2^j` bytes under the mask of bit `j` of
`idx + 1`: the message, then zeros. With `ok` all ones exactly when `r = 1`
and `acc = 0`, `out` receives the buffer's first `k` bytes ANDed with `ok`,
`*msg_len` receives `(t - idx - 1) ∧ ok`, and the result is
`(ok ∧ 1) ∨ (r = 2 ? 2 : 0)`.

ARMv7 has no conditional select or subtraction with borrow: every
comparison of a secret is the top bit of a difference of numbers below
`2^31`, and every selection a mask.
-/

@[expose] public section

namespace VG.Impl.RsaOaep.Arm

open VG VG.Arm
open VG.Impl.RsaPkcs1Sig.Arm (wrap)
open VG.Impl.RsaPss.Arm (seqs mw sp0 st ld atS countLoop copyArg arg frameBytes sS sCtr sDone sAcc sPos sA sD
  sPc oRsa)
open VG.Impl.Pbkdf2.Stream.Arm (Hash)

/-! ## The slots

Besides those of `Impl/RsaPss/Arm.lean` that we use as it does (`sS`,
`sCtr`, `sDone`, `sAcc`, and `sPos` for `idx`, `sA`, `sD`, `sPc` for the
shift). -/

/-- MGF1's source and destination: their addresses and lengths. -/
def sSrc : Nat := 68
def sSrcLen : Nat := 72
def sDst : Nat := 76
def sDstLen : Nat := 80
/-- The private-key operation's result. -/
def sRes : Nat := 84
/-- The mask `ok`. -/
def sOk : Nat := 88

/-! ## Our part of `scratch` -/

/-- `EM`: `k` bytes. -/
def oEm : Nat := 0
/-- The buffer in which decryption shifts `T`: 2048 bytes. -/
def oBuf : Nat := 1024
/-- The streaming state (at most 256 bytes). -/
def oSt : Nat := 3072
/-- The digest `finalize` writes (at most 64 bytes). -/
def oDig : Nat := 3328
/-- `lHash`, when decrypting (at most 64 bytes). -/
def oLh : Nat := 3392
/-- MGF1's counter. -/
def oCtr : Nat := 3456
/-- The working space of `update` and `finalize` (at most 512 bytes). -/
def oW : Nat := 3520

/-! ## Calls of the streaming functions -/

/-- `update`'s stack arguments pushed around its call (the data, its
length and the working space, in `r1`, `r7` and `r10`). -/
def updCall (G : Hash) : Prog isa := .frame (.push [.r1, .r7, .r10, .r12]) (.call G.updN G.updC) (.pop .r1 16)

/-- `finalize`'s stack arguments pushed around its call (`out` and the
working space, in `r1` and `r12`). -/
def finCall (G : Hash) : Prog isa := .frame (.push [.r1, .r12]) (.call G.finN G.finC) (.pop .r1 8)

/-- `r12 := r10`, the working space for `finalize`. -/
def toR12 : List Instr := [.mov .r12 (.reg .r10)]

/-! ## MGF1 -/

section Mgf

variable (G : Hash)

/-- `init(state)`. -/
def initArgs : List Instr := sp0 :: atS .r0 oSt

/-- `update(state, 0, src, srcLen, work)`. -/
def updSrcArgs : List Instr :=
  sp0 :: (atS .r0 oSt ++ [ld .r1 sSrc, ld .r7 sSrcLen] ++ atS .r10 oW ++ [mw .r2 0, mw .r3 0])

/-- The counter's place (`r0`) and the counter (`r1`), for `ctrPut`. -/
def ctrSet : List Instr := sp0 :: (atS .r0 oCtr ++ [ld .r1 sCtr])

/-- `update(state, srcLen, scratch + oCtr, 4, work)`. -/
def updCtrArgs : List Instr :=
  sp0 :: (atS .r0 oSt ++ atS .r1 oCtr ++ [mw .r7 4] ++ atS .r10 oW ++ [ld .r2 sSrcLen, mw .r3 0])

/-- `finalize(state, srcLen + 4, scratch + oDig, work)`, the working space in
`r10` until `toR12`. -/
def finArgs : List Instr :=
  sp0 :: (atS .r0 oSt ++ atS .r1 oDig ++ atS .r10 oW ++ [ld .r2 sSrcLen, .dp .add .r2 .r2 (.imm 4), mw .r3 0])

/-- `dst + done` (`r0`), the digest (`r1`) and `min(hLen, dstLen - done)`
(`lr`), for `xorBody`: `hLen` unless `dstLen - done < hLen`, the top bit of
the difference, both below `2^31`. -/
def xorSet : List Instr :=
  sp0 :: ([ld .r0 sDst, ld .r2 sDone, .dp .add .r0 .r0 (.reg .r2)] ++ atS .r1 oDig ++
    [ld .r3 sDstLen, .dp .sub .r3 .r3 (.reg .r2), mw .r4 G.D, .dp .sub .r5 .r3 (.reg .r4),
      .mov .r5 (.shifted .r5 .lsr 31), mw .r6 0, .dp .sub .r5 .r6 (.reg .r5), .dp .eor .r6 .r3 (.reg .r4),
      .dp .and .r6 .r6 (.reg .r5), .dp .eor .lr .r4 (.reg .r6)])

/-- The next counter, and the flags of `done ≥ dstLen`. -/
def mgfNext : List Instr :=
  [sp0, ld .r0 sCtr, .dp .add .r0 .r0 (.imm 1), st .r0 sCtr, ld .r0 sDone, mw .r1 G.D, .dp .add .r0 .r0 (.reg .r1),
    st .r0 sDone, ld .r1 sDstLen, .dp .sub .r0 .r0 (.reg .r1), .mov .r0 (.shifted .r0 .lsr 31), .cmp .r0 (.imm 0)]

/-- One block of the mask: the digest of `src ‖ I2OSP(c, 4)`, XORed into
`dst`. -/
def mgfRound : Prog isa :=
  seqs [.block initArgs, .call G.initN G.initC, .block updSrcArgs, updCall G, .block ctrSet,
    .block Impl.RsaPss.Arm.ctrPut, .block updCtrArgs, updCall G, .block finArgs, .block toR12, finCall G,
    .block (xorSet G), countLoop Impl.RsaPss.Arm.xorBody, .block (mgfNext G)]

/-- `dst ⊕= MGF1(src, dstLen)`, for `dstLen > 0`. -/
def mgfXor : Prog isa := .seq (.block Impl.RsaPss.Arm.mgfInit) (.loop (mgfRound G) .ne)

end Mgf

/-! ## Common pieces -/

section Common

variable (H : Hash)

/-- `update(state, 0, label, label_len, work)`, with the label argument `j`
and its length `j + 1`. -/
def updLabArgs (j : Nat) : List Instr :=
  sp0 :: (atS .r0 oSt ++ [ld .r1 (arg j), ld .r7 (arg (j + 1))] ++ atS .r10 oW ++ [mw .r2 0, mw .r3 0])

/-- `finalize(state, label_len, scratch + o, work)`. -/
def finLabArgs (j o : Nat) : List Instr :=
  sp0 :: (atS .r0 oSt ++ atS .r1 o ++ atS .r10 oW ++ [ld .r2 (arg (j + 1)), mw .r3 0])

/-- The label's hash, `H(label)`, to `scratch + o`, the label being
argument `j`. -/
def hashLabel (j o : Nat) : Prog isa :=
  seqs [.block initArgs, .call H.initN H.initC, .block (updLabArgs j), updCall H, .block (finLabArgs j o),
    .block toR12, finCall H]

/-- MGF1's slots for masking `DB` (`k - hLen - 1` bytes at `EM + 1 + hLen`)
with the seed (`hLen` bytes at `EM + 1`), `k` being argument `j`. -/
def dbArgs (j : Nat) : List Instr :=
  sp0 :: (atS .r0 (oEm + 1 + H.D) ++ [ld .r1 (arg j), mw .r2 (H.D + 1), .dp .sub .r1 .r1 (.reg .r2)] ++
    atS .r2 (oEm + 1) ++ [mw .r3 H.D, st .r0 sDst, st .r1 sDstLen, st .r2 sSrc, st .r3 sSrcLen])

/-- MGF1's slots for masking the seed with `DB`. -/
def seedArgs (j : Nat) : List Instr :=
  sp0 :: (atS .r0 (oEm + 1) ++ [mw .r1 H.D] ++ atS .r2 (oEm + 1 + H.D) ++
    [ld .r3 (arg j), mw .r4 (H.D + 1), .dp .sub .r3 .r3 (.reg .r4), st .r0 sDst, st .r1 sDstLen, st .r2 sSrc,
      st .r3 sSrcLen])

end Common

/-! ## Encryption -/

section Enc

variable (H G : Hash)

/-- `scratch` to its slot; the flags of `k < 2 hLen + 2` or
`msg_len > k - 2 hLen - 2`: the top bit of `k - 2 hLen - 2`, `msg_len ≥ 1024`,
or the top bit of `k - 2 hLen - 2 - msg_len`, all three of numbers below
`2^31` once the first two are clear. -/
def encChk : List Instr :=
  [sp0, ld .r0 (arg 11), st .r0 sS, ld .r0 (arg 3), mw .r1 (2 * H.D + 2), .dp .sub .r0 .r0 (.reg .r1),
    .mov .r1 (.shifted .r0 .lsr 31), ld .r2 (arg 9), .dp .orr .r1 .r1 (.shifted .r2 .lsr 10),
    .dp .sub .r3 .r0 (.reg .r2), .dp .orr .r1 .r1 (.shifted .r3 .lsr 31), .cmp .r1 (.imm 0)]

/-- Zeros to `out`, for `maskBytes`, and 0 returned. -/
def encFail : Prog isa :=
  seqs [.block [sp0, ld .r0 (arg 0), ld .lr (arg 3), mw .r2 0], Bignum.Arm.maskBytes, .block [mw .r0 0]]

/-- `EM`'s `k` bytes, for `maskBytes` with a zero mask. -/
def clrEm : List Instr := sp0 :: (atS .r0 oEm ++ [mw .r2 0, ld .lr (arg 3)])

/-- The seed to `EM + 1`, for `copyBytes`. -/
def seedSet : List Instr := sp0 :: (atS .r0 (oEm + 1) ++ [ld .r1 (arg 10), mw .lr H.D])

/-- `lHash` (the digest at `scratch + oDig`) to `EM + 1 + hLen`, for
`copyBytes`. -/
def lhSet : List Instr := sp0 :: (atS .r0 (oEm + 1 + H.D) ++ atS .r1 oDig ++ [mw .lr H.D])

/-- `EM + k - mLen - 1` (`r0`), the message (`r1`) and its length (`lr`). -/
def msgPos : List Instr :=
  sp0 :: (atS .r0 oEm ++ [ld .r1 (arg 3), .dp .add .r0 .r0 (.reg .r1), ld .lr (arg 9), .dp .sub .r0 .r0 (.reg .lr),
    .dp .sub .r0 .r0 (.imm 1), ld .r1 (arg 8)])

/-- `EM`, before masking: zeros, the seed, `lHash`, `0x01` and the message. -/
def encEm : Prog isa :=
  seqs [.block clrEm, Bignum.Arm.maskBytes, .block (seedSet H), Bignum.Arm.copyBytes, hashLabel H 6 oDig,
    .block (lhSet H), Bignum.Arm.copyBytes, .block msgPos, .block Impl.RsaPss.Arm.put1,
    .ite .eq (.block []) Bignum.Arm.copyBytes]

/-- The arguments of the precomputed public operation: `out` (`k` bytes),
`pre` (`pre_len` words), `e`, `EM` as the input (`k` bytes), and the rest
of `scratch`. -/
def pubArgs : List Instr :=
  [sp0] ++ copyArg 4 0 ++ copyArg 5 1 ++ atS .r0 oEm ++ [st .r0 8] ++ copyArg 3 3 ++ atS .r0 oRsa ++
    [st .r0 16, ld .r0 (arg 12), mw .r1 1024, .dp .sub .r0 .r0 (.reg .r1), st .r0 20, ld .r0 (arg 0),
      ld .r1 (arg 3), ld .r2 (arg 13), ld .r3 (arg 14)]

variable (pubN : String) (pubC : Prog isa)

/-- After the checks. -/
def encMain : Prog isa :=
  seqs [encEm H, .block (dbArgs H 3), mgfXor G, .block (seedArgs H 3), mgfXor G, .block pubArgs, .call pubN pubC]

/-- The inner frame's body. -/
def encBody : Prog isa := seqs [.block (encChk H), .ite .ne (encFail) (encMain H G pubN pubC)]

/-- `vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed`, calling a precomputed
public operation by its name. -/
def encryptPrecomputed : Prog isa := wrap frameBytes (encBody H G pubN pubC)

end Enc

/-! ## Decryption -/

section Dec

variable (H G : Hash)

/-- `scratch` to its slot. -/
def decStart : List Instr := [sp0, ld .r0 (arg 21), st .r0 sS]

/-- The arguments of `vg_rsa_private_checked`: `EM`'s place (`k` bytes), `n`,
`e`, the ciphertext as the input (`k` bytes), the private key, and the rest
of `scratch`. -/
def privArgs : List Instr :=
  [sp0] ++ copyArg 5 0 ++ copyArg 6 1 ++ copyArg 19 2 ++ copyArg 4 3 ++ copyArg 7 4 ++ copyArg 8 5 ++
    copyArg 9 6 ++ copyArg 10 7 ++ copyArg 11 8 ++ copyArg 8 9 ++ copyArg 13 10 ++ copyArg 10 11 ++
    copyArg 15 12 ++ copyArg 8 13 ++ atS .r0 oRsa ++ [st .r0 56, ld .r0 (arg 22), mw .r1 1024,
    .dp .sub .r0 .r0 (.reg .r1), st .r0 60] ++ atS .r0 oEm ++ [ld .r1 (arg 4), ld .r2 (arg 3), ld .r3 (arg 4)]

/-- The result to its slot; the flags of `k < 2 hLen + 2`. -/
def decChk : List Instr :=
  [sp0, st .r0 sRes, ld .r0 (arg 4), mw .r1 (2 * H.D + 2), .dp .sub .r0 .r0 (.reg .r1), .mov .r0 (.shifted .r0 .lsr 31),
    .cmp .r0 (.imm 0)]

/-- `r0 := (r = 2) ? 2 : 0`, for `r` (in its slot) 0, 1 or 2: the top bit of
`(r ⊕ 2) - 1`, doubled. -/
def faultBit : List Instr :=
  [ld .r1 sRes, .dp .eor .r1 .r1 (.imm 2), .dp .sub .r1 .r1 (.imm 1), .mov .r1 (.shifted .r1 .lsr 31),
    .mov .r0 (.shifted .r1 .lsl 1)]

/-- `msg_len` (`r1`), and the length `r3` and zero (`r2`) to store there. -/
def mlFail : List Instr := [sp0, ld .r1 (arg 2), mw .r3 0, mw .r2 0]

/-- `*msg_len := r3`, as two words. -/
def mlStore : List Instr := [.str .r3 .r1 0, .str .r2 .r1 4]

/-- Zeros to `out` and `*msg_len`, and the result `(r = 2) ? 2 : 0`. -/
def decFail : Prog isa :=
  seqs [.block [sp0, ld .r0 (arg 0), ld .lr (arg 4), mw .r2 0], Bignum.Arm.maskBytes, .block mlFail, .block mlStore,
    .block (sp0 :: faultBit)]

/-- `lHash'` (`EM + 1 + hLen`) and `lHash`, for `compareBytes`. -/
def cmpSet : List Instr := sp0 :: (atS .r0 (oEm + 1 + H.D) ++ atS .r1 oLh ++ [mw .r2 0, mw .lr H.D])

/-- `EM` (`r0`), with the comparison in `r2`. -/
def accSet : List Instr := sp0 :: atS .r0 oEm

/-- `r2 := EM[0] ∨ r2`. -/
def accPut : List Instr := [.ldrb .r3 .r0 0, .dp .orr .r2 .r2 (.reg .r3)]

/-- `acc := r2`, to its slot. -/
def accSave : List Instr := [sp0, st .r2 sAcc]

/-- The scan's registers: `T` (`r0`), the index (`r1`), the bytes left
(`lr = t`), the first nonzero byte's index (`r4`) and value (`r5`), all ones
while none is found (`r6`), and 0 (`r7`). -/
def scanSet : List Instr :=
  sp0 :: (atS .r0 (oEm + 1 + 2 * H.D) ++ [ld .lr (arg 4), mw .r1 (2 * H.D + 1), .dp .sub .lr .lr (.reg .r1),
    mw .r1 0, mw .r4 0, mw .r5 0, mw .r7 0, .dp .sub .r6 .r7 (.imm 1)])

/-- `acc |= (val ⊕ 1) | notFound`, and `idx` to its slot. -/
def scanEnd : List Instr :=
  [sp0, ld .r1 sAcc, .dp .eor .r5 .r5 (.imm 1), .dp .orr .r5 .r5 (.shifted .r6 .lsr 31), .dp .orr .r1 .r1 (.reg .r5),
    st .r1 sAcc, st .r4 sPos]

/-- The buffer's 2048 bytes, for `maskBytes` with a zero mask. -/
def clrBuf : List Instr := sp0 :: (atS .r0 oBuf ++ [mw .r2 0, mw .lr 2048])

/-- `T` to the buffer, for `copyBytes`. -/
def tSet : List Instr :=
  sp0 :: (atS .r0 oBuf ++ atS .r1 (oEm + 1 + 2 * H.D) ++ [ld .lr (arg 4), mw .r2 (2 * H.D + 1),
    .dp .sub .lr .lr (.reg .r2)])

/-- A pass's registers: the buffer (`r0`), the byte `d` after it (`r1`), its
first 1024 bytes (`lr`) and the mask of bit 0 of the distance left (`r2`). -/
def passSet : List Instr :=
  sp0 :: (atS .r0 oBuf ++ [ld .r1 sD, .dp .add .r1 .r0 (.reg .r1), ld .r2 sA, .dp .and .r2 .r2 (.imm 1), mw .r3 0,
    .dp .sub .r2 .r3 (.reg .r2), mw .lr 1024])

def passOne : Prog isa := seqs [.block passSet, countLoop Impl.RsaPss.Arm.passBody, .block Impl.RsaPss.Arm.passNext]

/-- The buffer shifted left by `idx + 1` bytes, in ten passes. -/
def shift : Prog isa := .seq (.block Impl.RsaPss.Arm.shInit) (.loop passOne .ne)

/-- `ok`: all ones exactly when `r = 1` and `acc = 0` (each below `2^31`), to
its slot. -/
def okMask : List Instr :=
  [sp0, ld .r0 sRes, .dp .eor .r0 .r0 (.imm 1), .dp .sub .r0 .r0 (.imm 1), .mov .r0 (.shifted .r0 .lsr 31), ld .r1 sAcc,
    .dp .sub .r1 .r1 (.imm 1), .mov .r1 (.shifted .r1 .lsr 31), .dp .and .r0 .r0 (.reg .r1), mw .r1 0,
    .dp .sub .r0 .r1 (.reg .r0), st .r0 sOk]

/-- The buffer's first `k` bytes to `out`, for `copyBytes`. -/
def outSet : List Instr := sp0 :: (atS .r1 oBuf ++ [ld .r0 (arg 0), ld .lr (arg 4)])

/-- `out` ANDed with `ok`, for `maskBytes`. -/
def outMask : List Instr := [sp0, ld .r0 (arg 0), ld .lr (arg 4), ld .r2 sOk]

/-- `msg_len` (`r1`), its length `(t - idx - 1) ∧ ok` (`r3`) and zero (`r2`). -/
def mlSet : List Instr :=
  [sp0, ld .r3 (arg 4), mw .r1 (2 * H.D + 2), .dp .sub .r3 .r3 (.reg .r1), ld .r1 sPos, .dp .sub .r3 .r3 (.reg .r1),
    ld .r1 sOk, .dp .and .r3 .r3 (.reg .r1), ld .r1 (arg 2), mw .r2 0]

/-- The result `(ok ∧ 1) ∨ ((r = 2) ? 2 : 0)`. -/
def decRet : List Instr := sp0 :: (faultBit ++ [ld .r1 sOk, .dp .and .r1 .r1 (.imm 1), .dp .orr .r0 .r0 (.reg .r1)])

/-- After the private operation and the check of `k`: the decoding. -/
def decMain : Prog isa :=
  seqs [hashLabel H 17 oLh, .block (seedArgs H 4), mgfXor G, .block (dbArgs H 4), mgfXor G, .block (cmpSet H),
    Bignum.Arm.compareBytes, .block accSet, .block accPut, .block accSave, .block (scanSet H), countLoop Impl.RsaPss.Arm.scanBody,
    .block scanEnd, .block clrBuf, Bignum.Arm.maskBytes, .block (tSet H), Bignum.Arm.copyBytes, shift,
    .block okMask, .block outSet, Bignum.Arm.copyBytes, .block outMask, Bignum.Arm.maskBytes, .block (mlSet H),
    .block mlStore, .block decRet]

variable (privN : String) (privC : Prog isa)

/-- The inner frame's body. -/
def decBody : Prog isa :=
  seqs [.block decStart, .block privArgs, .call privN privC, .block (decChk H), .ite .ne decFail (decMain H G)]

/-- `vg_rsa_oaep_<H>_mgf1_<G>_decrypt`, calling a checked private operation
by its name. -/
def decrypt : Prog isa := wrap frameBytes (decBody H G privN privC)

end Dec

end VG.Impl.RsaOaep.Arm
