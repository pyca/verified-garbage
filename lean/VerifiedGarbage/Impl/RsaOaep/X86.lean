module

public import VerifiedGarbage.Impl.RsaPss.X86
public import VerifiedGarbage.Impl.Pbkdf2.Stream.X86

/-!
# RSAES-OAEP (RFC 8017 §7.1) on x86 (32-bit)

`encryptPrecomputed` and `decrypt`, for a hash function `H` (the label's)
and MGF1's hash function `G`, each a streaming hash function
(`Impl.Pbkdf2.Stream.X86.Hash`: its `init`, `update` and `finalize`), with
the steps of ARMv7 (`Impl/RsaOaep/Arm.lean`) and the frame, slots, byte loops
and RSA calls of the x86 RSASSA-PSS functions (`Impl/RsaPss/X86.lean`),
whose definitions this file reuses: the public-key operation with the
precomputed modulus (`vg_rsa_public_precomputed_checked`) when encrypting,
the private-key operation checked against `e` (`vg_rsa_private_checked`)
when decrypting.

Each function runs in the frames of `wrap`: a push of `ebx`, `ebp`, `esi`
and `edi`, and a frame of `frameBytes` bytes whose first 80 hold the RSA
operation's arguments and the rest the slots. `ebp` holds `scratch`
throughout (every function we call keeps it), so our part of it, its first
8192 bytes (`oW`, …), is addressed from `ebp`; the RSA operation gets the
rest. Every other value lives in a slot between the pieces of code, and each
piece loads what it needs. The streaming functions take their arguments on
the stack: each call of them is in a frame that pushes those, from
registers (`callInit`, `callUpd`, `callFin`), below our frame, and their
working space is the first 512 bytes of `scratch`, at `ebp`.

## MGF1

`mgfXor`: `dst ⊕= MGF1(src, dstLen)` with `G`, the addresses and lengths in
the slots `sSrc`, `sSrcLen`, `sDst`, `sDstLen`, as on ARMv7: for each counter
`c` from 0, while `done = c hLen` is below `dstLen`, the state at
`scratch + oSt` is set by `init`, `update` absorbs `src` and `I2OSP(c, 4)` (at
`scratch + oCtr`), `finalize` writes the digest to `scratch + oDig`, and its
first `min(hLen, dstLen - done)` bytes are XORed into `dst + done`
(`Impl.RsaPss.X86.xorBody`). Every length is public.

## Encryption

`encryptPrecomputed(out, out_len, n, n_len, e, e_len, label, label_len, msg,
msg_len, seed, scratch, scratch_len, pre, pre_len)`, all on the stack. If
`k < 2 hLen + 2` or `msg_len > k - 2 hLen - 2` (public), it writes zeros to
`out` and returns 0. Otherwise it writes `EM = 0x00 ‖ seed ‖ DB` to
`scratch` (`DB = lHash ‖ 0… ‖ 0x01 ‖ M`, the label hashed with `H`), masks
`DB` with MGF1 of the seed and then the seed with MGF1 of `maskedDB` (`G`),
and returns the precomputed public operation of `EM` into `out`.

## Decryption

`decrypt(out, out_len, msg_len, n, n_len, e, e_len, p, p_len, q, q_len, dp,
dp_len, dq, dq_len, qinv, qinv_len, label, label_len, ct, ct_len, scratch,
scratch_len)`, all on the stack, as on ARMv7: `vg_rsa_private_checked`
writes `EM` (or zeros) to `scratch` and returns `r` (1, 0 or 2), which only
selects values without a branch. If `k < 2 hLen + 2` (public), the result is
`r = 2 ? 2 : 0`, with zeros to `out` and `*msg_len`. Otherwise, without a
branch on anything secret: the label is hashed (`H`) to `scratch + oLh`, the
seed and `DB` unmasked in place (`G`); the accumulator `acc` ORs `EM`'s
first byte into the comparison of `lHash'` with `lHash`
(`Impl.RsaPss.X86.cmpBody`); the scan of `T = DB[hLen..]`
(`t = k - 2 hLen - 1` bytes, `Impl.RsaPss.X86.scanBody`) finds the index
`idx` and the value of its first byte that is not zero, if any, and `acc`
takes in that this byte is `0x01`; `T` is copied into the 2048-byte buffer
`scratch + oBuf`, zeros after it, and shifted left by `idx + 1` bytes in ten
passes (`Impl.RsaPss.X86.passBody`), pass `j` moving each of its first 1024
bytes `2^j` bytes under the mask of bit `j` of `idx + 1`: the message, then
zeros. With `ok` all ones exactly when `r = 1` and `acc = 0`, `out` receives
the buffer's first `k` bytes ANDed with `ok` (`outBody`), `*msg_len`
receives `(t - idx - 1) ∧ ok`, and the result is `(ok ∧ 1) ∨ (r = 2 ? 2 : 0)`.

Every comparison of a secret is the borrow of a subtraction (`cmp` or `sub`,
then `sbb` of a register with itself), and every selection a mask.
-/

@[expose] public section

namespace VG.Impl.RsaOaep.X86

open VG VG.X86
open VG.Impl.RsaPkcs1Sig.X86 (wrap stk at_)
open VG.Impl.RsaPss.X86 (seqs ld st mi addi atS addSlot countLoop zeroLoop clrArgs copyArg arg frameBytes sCtr
  sDone sAcc sPos sVal oCW oSt oDig oEm oRsa)
open VG.Impl.Pbkdf2.Stream.X86 (Hash)

/-! ## The slots

Besides those of `Impl/RsaPss/X86.lean` that we use as it does (`sCtr`,
`sDone`, `sAcc`, and `sPos`, `sVal`, `sA`, `sD`, `sPc` for the scan and the
shift). -/

/-- MGF1's source and destination: their addresses and lengths. -/
def sSrc : Nat := 80
def sSrcLen : Nat := 84
def sDst : Nat := 88
def sDstLen : Nat := 92
/-- The private-key operation's result. -/
def sRes : Nat := 96
/-- The mask `ok`. -/
def sOk : Nat := 100

/-! ## Our part of `scratch`

The working space of `update` and `finalize` (at most 512 bytes) is at
`oCW`, the streaming state (at most 256 bytes) at `oSt`, the digest
`finalize` writes (at most 64 bytes) at `oDig` and `EM` (`k` bytes) at
`oEm`, as for RSASSA-PSS. -/

/-- MGF1's counter. -/
def oCtr : Nat := 768
/-- `lHash`, when decrypting (at most 64 bytes). -/
def oLh : Nat := 896
/-- The buffer in which decryption shifts `T`: 2048 bytes. -/
def oBuf : Nat := 2048

/-! ## Calls of the streaming functions -/

/-- The registers `update`'s frame pushes: the state (`ebx`), the count
(`edi`, and `eax` its high word), the data (`edx`) and its length (`ecx`),
the working space (`ebp`). -/
abbrev upd6 : List Reg := [.ebp, .ecx, .edx, .eax, .edi, .ebx]

/-- The registers `finalize`'s frame pushes: the state (`ebx`), the count
(`eax`, and `ecx` its high word), the digest's place (`edx`), the working
space (`ebp`). -/
abbrev fin5 : List Reg := [.ebp, .edx, .ecx, .eax, .ebx]

variable (G : Hash)

def callInit : Prog isa := G.callInit .ebx
def callUpd : Prog isa := .frame (.push upd6) (.call G.updN G.updC) (.pop .eax 6)
def callFin : Prog isa := .frame (.push fin5) (.call G.finN G.finC) (.pop .eax 5)

/-! ## MGF1 -/

/-- `init(scratch + oSt)`. -/
def initArgs : List Instr := atS .ebx oSt

/-- `update(state, 0, src, srcLen)`. -/
def updSrcArgs : List Instr := atS .ebx oSt ++ [mi .edi 0, mi .eax 0, ld .edx sSrc, ld .ecx sSrcLen]

/-- The counter, big-endian, to `scratch + oCtr`. -/
def ctrSet : List Instr := [ld .eax sCtr, .bswap .eax, .store (at_ .ebp oCtr) .eax]

/-- `update(state, srcLen, scratch + oCtr, 4)`. -/
def updCtrArgs : List Instr := atS .ebx oSt ++ [ld .edi sSrcLen, mi .eax 0] ++ atS .edx oCtr ++ [mi .ecx 4]

/-- `finalize(state, srcLen + 4, scratch + oDig)`. -/
def finArgs : List Instr := atS .ebx oSt ++ [ld .eax sSrcLen, addi .eax 4, mi .ecx 0] ++ atS .edx oDig

/-- `dst + done` (`edi`), the digest (`esi`) and `min(hLen, dstLen - done)`
(`ecx`), for `xorBody`: `hLen` unless `dstLen - done < hLen`, the borrow of
the difference. -/
def xorSet : List Instr :=
  [ld .edi sDst, addSlot .edi sDone] ++ atS .esi oDig ++
    [ld .ecx sDstLen, .alu .sub .ecx (.mem (stk sDone)), .mov .eax (.reg .ecx),
      .alu .sub .eax (.imm (BitVec.ofNat 32 G.D)), .alu .sbb .edx (.reg .edx), .alu .and .eax (.reg .edx),
      addi .eax G.D, .mov .ecx (.reg .eax)]

/-- The next counter, and the flags of `done < dstLen`. -/
def mgfNext : List Instr :=
  [ld .eax sCtr, addi .eax 1, st .eax sCtr, ld .eax sDone, addi .eax G.D, st .eax sDone,
    .alu .cmp .eax (.mem (stk sDstLen))]

/-- One block of the mask: the digest of `src ‖ I2OSP(c, 4)`, XORed into
`dst`. -/
def mgfRound : Prog isa :=
  seqs [.block initArgs, callInit G, .block updSrcArgs, callUpd G, .block ctrSet, .block updCtrArgs, callUpd G,
    .block finArgs, callFin G, .block (xorSet G), countLoop Impl.RsaPss.X86.xorBody, .block (mgfNext G)]

/-- `dst ⊕= MGF1(src, dstLen)`, for `dstLen > 0`. -/
def mgfXor : Prog isa := .seq (.block Impl.RsaPss.X86.mgfInit) (.loop (mgfRound G) .b)

/-! ## Common pieces -/

section Common

variable (H : Hash)

/-- `update(state, 0, label, label_len)`, with the label argument `j` and its
length `j + 1`. -/
def updLabArgs (j : Nat) : List Instr := atS .ebx oSt ++ [mi .edi 0, mi .eax 0, ld .edx (arg j), ld .ecx (arg (j + 1))]

/-- `finalize(state, label_len, scratch + o)`. -/
def finLabArgs (j o : Nat) : List Instr := atS .ebx oSt ++ [ld .eax (arg (j + 1)), mi .ecx 0] ++ atS .edx o

/-- The label's hash, `H(label)`, to `scratch + o`, the label being
argument `j`. -/
def hashLabel (j o : Nat) : Prog isa :=
  seqs [.block initArgs, callInit H, .block (updLabArgs j), callUpd H, .block (finLabArgs j o), callFin H]

/-- MGF1's slots for masking `DB` (`k - hLen - 1` bytes at `EM + 1 + hLen`)
with the seed (`hLen` bytes at `EM + 1`), `k` being argument `j`. -/
def dbArgs (j : Nat) : List Instr :=
  atS .eax (oEm + 1 + H.D) ++ [st .eax sDst, ld .eax (arg j), .alu .sub .eax (.imm (BitVec.ofNat 32 (H.D + 1))),
    st .eax sDstLen] ++ atS .eax (oEm + 1) ++ [st .eax sSrc, mi .eax H.D, st .eax sSrcLen]

/-- MGF1's slots for masking the seed with `DB`. -/
def seedArgs (j : Nat) : List Instr :=
  atS .eax (oEm + 1) ++ [st .eax sDst, mi .eax H.D, st .eax sDstLen] ++ atS .eax (oEm + 1 + H.D) ++
    [st .eax sSrc, ld .eax (arg j), .alu .sub .eax (.imm (BitVec.ofNat 32 (H.D + 1))), st .eax sSrcLen]

end Common

/-! ## Encryption -/

section Enc

variable (H G : Hash)

/-- `scratch` into `ebp`; `ebx` nonzero if `k < 2 hLen + 2` (the borrow of
`k - 2 hLen - 2`) or `msg_len > k - 2 hLen - 2` (the borrow of their
comparison), with the flags of `ebx = 0`. -/
def encChk : List Instr :=
  [ld .ebp (arg 11), ld .eax (arg 3), .alu .sub .eax (.imm (BitVec.ofNat 32 (2 * H.D + 2))),
    .alu .sbb .ebx (.reg .ebx), .alu .cmp .eax (.mem (stk (arg 9))), .alu .sbb .edx (.reg .edx),
    .alu .or .ebx (.reg .edx), .alu .test .ebx (.reg .ebx)]

/-- Zeros to `out`, and 0 returned. -/
def encFail : Prog isa := seqs [.block [ld .esi (arg 0), ld .ecx (arg 3), mi .eax 0], zeroLoop, .block [mi .eax 0]]

/-- `EM`'s `k` bytes, for `zeroLoop`. -/
def clrEm : List Instr := atS .esi oEm ++ [ld .ecx (arg 3), mi .eax 0]

/-- The seed to `EM + 1`, for `copyBytes`. -/
def seedSet : List Instr := [ld .esi (arg 10)] ++ atS .ebx (oEm + 1) ++ [mi .ecx H.D]

/-- `lHash` (the digest at `scratch + oDig`) to `EM + 1 + hLen`, for
`copyBytes`. -/
def lhSet : List Instr := atS .esi oDig ++ atS .ebx (oEm + 1 + H.D) ++ [mi .ecx H.D]

/-- `EM + k - mLen - 1` (`ebx`). -/
def msgPos : List Instr :=
  atS .ebx oEm ++ [addSlot .ebx (arg 3), .alu .sub .ebx (.mem (stk (arg 9))), .alu .sub .ebx (.imm 1)]

/-- `0x01` there, `ebx` after it, the message (`esi`) and its length
(`ecx`), and the flags of an empty message. -/
def put1 : List Instr :=
  [mi .eax 1, .store8 (at_ .ebx 0) .al, addi .ebx 1, ld .esi (arg 8), ld .ecx (arg 9), .alu .test .ecx (.reg .ecx)]

/-- `EM`, before masking: zeros, the seed, `lHash`, `0x01` and the message. -/
def encEm : Prog isa :=
  seqs [.block clrEm, zeroLoop, .block (seedSet H), Impl.Bignum.X86.copyBytes, hashLabel H 6 oDig, .block (lhSet H),
    Impl.Bignum.X86.copyBytes, .block msgPos, .block put1, .ite .e (.block []) Impl.Bignum.X86.copyBytes]

/-- The arguments of the precomputed public operation: `out` (`k` bytes),
`pre` (`pre_len` words), `e`, `EM` as the input (`k` bytes), and the rest
of `scratch`. -/
def pubArgs : List Instr :=
  copyArg 0 0 ++ copyArg 3 1 ++ copyArg 13 2 ++ copyArg 14 3 ++ copyArg 4 4 ++ copyArg 5 5 ++ atS .eax oEm ++
    [st .eax 24] ++ copyArg 3 7 ++ atS .eax oRsa ++ [st .eax 32, ld .eax (arg 12), .alu .sub .eax (.imm 1024), st .eax 36]

variable (pubN : String) (pubC : Prog isa)

/-- After the checks. -/
def encMain : Prog isa :=
  seqs [encEm H, .block (dbArgs H 3), mgfXor G, .block (seedArgs H 3), mgfXor G, .block pubArgs, .call pubN pubC]

/-- The inner frame's body. -/
def encBody : Prog isa := seqs [.block (encChk H), .ite .ne encFail (encMain H G pubN pubC)]

/-- `vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed`, calling a precomputed
public operation by its name. -/
def encryptPrecomputed : Prog isa := wrap frameBytes (encBody H G pubN pubC)

end Enc

/-! ## Decryption -/

section Dec

variable (H G : Hash)

/-- `scratch` into `ebp`. -/
def decStart : List Instr := [ld .ebp (arg 21)]

/-- The arguments of `vg_rsa_private_checked`: `EM`'s place (`k` bytes), `n`,
`e`, the ciphertext as the input (`k` bytes), the private key, and the rest
of `scratch`. -/
def privArgs : List Instr :=
  atS .eax oEm ++ [st .eax 0] ++ copyArg 4 1 ++ copyArg 3 2 ++ copyArg 4 3 ++ copyArg 5 4 ++ copyArg 6 5 ++
    copyArg 19 6 ++ copyArg 4 7 ++ copyArg 7 8 ++ copyArg 8 9 ++ copyArg 9 10 ++ copyArg 10 11 ++
    copyArg 11 12 ++ copyArg 8 13 ++ copyArg 13 14 ++ copyArg 10 15 ++ copyArg 15 16 ++ copyArg 8 17 ++
    atS .eax oRsa ++ [st .eax 72, ld .eax (arg 22), .alu .sub .eax (.imm 1024), st .eax 76]

/-- The result to its slot; the flags of `k < 2 hLen + 2`. -/
def decChk : List Instr :=
  [st .eax sRes, ld .eax (arg 4), .alu .cmp .eax (.imm (BitVec.ofNat 32 (2 * H.D + 2)))]

/-- `eax := (r = 2) ? 2 : 0`, for `r` (in its slot) 0, 1 or 2: the borrow of
`(r ⊕ 2) - 1`, as a mask, and 2. -/
def faultBit : List Instr :=
  [ld .eax sRes, .alu .xor .eax (.imm 2), .alu .cmp .eax (.imm 1), .alu .sbb .eax (.reg .eax),
    .alu .and .eax (.imm 2)]

/-- `out` (`esi`), its `k` bytes and zero, for `zeroLoop`. -/
def outClr : List Instr := [ld .esi (arg 0), ld .ecx (arg 4), mi .eax 0]

/-- `*msg_len := 0`, as two words. -/
def mlZero : List Instr := [ld .esi (arg 2), mi .eax 0, .store (at_ .esi 0) .eax, .store (at_ .esi 4) .eax]

/-- Zeros to `out` and `*msg_len`, and the result `(r = 2) ? 2 : 0`. -/
def decFail : Prog isa := seqs [.block outClr, zeroLoop, .block (mlZero ++ faultBit)]

/-- `lHash'` (`EM + 1 + hLen`, `esi`) and `lHash` (`edi`), the differences
(`edx`) and the bytes (`ecx`), for `cmpBody`. -/
def cmpSet : List Instr := atS .esi (oEm + 1 + H.D) ++ atS .edi oLh ++ [mi .edx 0, mi .ecx H.D]

/-- `acc := EM[0] ∨ edx`, to its slot. -/
def accPut : List Instr := atS .esi oEm ++ [.movzx8 .eax (at_ .esi 0), .alu .or .edx (.reg .eax), st .edx sAcc]

/-- The scan's registers: `T` (`esi`), the index (`edi`), the bytes left
(`ecx = t`), all ones while no nonzero byte is found (`ebx`), and the first
nonzero byte's index and value, zero in their slots. -/
def scanSet : List Instr :=
  atS .esi (oEm + 1 + 2 * H.D) ++ [ld .ecx (arg 4), .alu .sub .ecx (.imm (BitVec.ofNat 32 (2 * H.D + 1))),
    mi .edi 0, mi .eax 0, st .eax sPos, st .eax sVal, mi .ebx 0, .alu .sub .ebx (.imm 1)]

/-- `scratch` into `ebp` again; `acc |= (val ⊕ 1) | notFound`. -/
def scanEnd : List Instr :=
  [ld .ebp (arg 21), ld .eax sAcc, ld .edx sVal, .alu .xor .edx (.imm 1), .alu .or .eax (.reg .edx),
    .shift .shr .ebx 31, .alu .or .eax (.reg .ebx), st .eax sAcc]

/-- `T` to the buffer, for `copyBytes`. -/
def tSet : List Instr :=
  atS .esi (oEm + 1 + 2 * H.D) ++ atS .ebx oBuf ++ [ld .ecx (arg 4),
    .alu .sub .ecx (.imm (BitVec.ofNat 32 (2 * H.D + 1)))]

/-- A pass's registers: the buffer (`esi`), the byte `d` after it (`edi`),
its first 1024 bytes (`ecx`) and the mask of bit 0 of the distance left
(`edx`). -/
def passSet : List Instr :=
  atS .esi oBuf ++ [.mov .edi (.reg .esi), addSlot .edi Impl.RsaPss.X86.sD, ld .eax Impl.RsaPss.X86.sA,
    .alu .and .eax (.imm 1), mi .edx 0, .alu .sub .edx (.reg .eax), mi .ecx 1024]

def passOne : Prog isa := seqs [.block passSet, countLoop Impl.RsaPss.X86.passBody, .block Impl.RsaPss.X86.passNext]

/-- The buffer shifted left by `idx + 1` bytes, in ten passes. -/
def shift : Prog isa := .seq (.block Impl.RsaPss.X86.shInit) (.loop passOne .ne)

/-- `ok`: all ones exactly when `r = 1` and `acc = 0`, the borrow of
`((r ⊕ 1) ∨ acc) - 1`, to its slot. -/
def okMask : List Instr :=
  [ld .eax sRes, .alu .xor .eax (.imm 1), .alu .or .eax (.mem (stk sAcc)), .alu .cmp .eax (.imm 1),
    .alu .sbb .eax (.reg .eax), st .eax sOk]

/-- The buffer (`esi`), `out` (`edi`), its `k` bytes (`ecx`) and `ok`
(`edx`), for `outBody`. -/
def outSet : List Instr := atS .esi oBuf ++ [ld .edi (arg 0), ld .ecx (arg 4), ld .edx sOk]

/-- A byte of the buffer, ANDed with `ok`, to `out`. -/
def outBody : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .alu .and .eax (.reg .edx), .store8 (at_ .edi 0) .al, addi .esi 1, addi .edi 1,
    .alu .sub .ecx (.imm 1)]

/-- `*msg_len := (t - idx - 1) ∧ ok`, as two words. -/
def mlSet : List Instr :=
  [ld .eax (arg 4), .alu .sub .eax (.imm (BitVec.ofNat 32 (2 * H.D + 2))), .alu .sub .eax (.mem (stk sPos)),
    .alu .and .eax (.mem (stk sOk)), ld .esi (arg 2), .store (at_ .esi 0) .eax, mi .eax 0,
    .store (at_ .esi 4) .eax]

/-- The result `(ok ∧ 1) ∨ ((r = 2) ? 2 : 0)`. -/
def decRet : List Instr := faultBit ++ [ld .edx sOk, .alu .and .edx (.imm 1), .alu .or .eax (.reg .edx)]

/-- After the private operation and the check of `k`: the decoding. -/
def decMain : Prog isa :=
  seqs [hashLabel H 17 oLh, .block (seedArgs H 4), mgfXor G, .block (dbArgs H 4), mgfXor G, .block (cmpSet H),
    countLoop Impl.RsaPss.X86.cmpBody, .block accPut, .block (scanSet H), countLoop Impl.RsaPss.X86.scanBody,
    .block scanEnd, .block (clrArgs oBuf 2048), zeroLoop, .block (tSet H), Impl.Bignum.X86.copyBytes, shift,
    .block okMask, .block outSet, countLoop outBody, .block (mlSet H), .block decRet]

variable (privN : String) (privC : Prog isa)

/-- The inner frame's body. -/
def decBody : Prog isa :=
  seqs [.block (decStart ++ privArgs), .call privN privC, .block (decChk H), .ite .b decFail (decMain H G)]

/-- `vg_rsa_oaep_<H>_mgf1_<G>_decrypt`, calling a checked private operation
by its name. -/
def decrypt : Prog isa := wrap frameBytes (decBody H G privN privC)

end Dec

end VG.Impl.RsaOaep.X86
