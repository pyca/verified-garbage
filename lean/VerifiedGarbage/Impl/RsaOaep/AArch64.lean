import VerifiedGarbage.Impl.RsaOaep.AArch64.Mgf1

/-!
# RSAES-OAEP (RFC 8017 §7.1) on AArch64

`encrypt` and `decrypt`, for a hash function `H` (the label's) and MGF1's
hash function `G`, each an `Impl.Pbkdf2.Md.AArch64.Hash` (its streaming
functions), calling those functions, MGF1 (`Impl/RsaOaep/AArch64/Mgf1.lean`)
and the RSA operation: the public-key operation within BoringSSL's limits
(`vg_rsa_public_checked`) when encrypting, the private-key operation checked
against `e` (`vg_rsa_private_checked`) when decrypting. The steps are those
of x86-64 (`Impl/RsaOaep/X86_64.lean`).

Each function runs in two frames: one saving our return address `x30`, and
in it one of `frameBytes` bytes holding, from `sp`, the RSA operation's
stack arguments, then the slots. Our own stack arguments are above both
frames, from `sp + frameBytes + 16`. Only caller-saved registers are used,
and nothing is kept in them across a call. The first `oRsa` = 8192 bytes of
`scratch` are ours; the RSA operation gets the rest, `scratch_len - 1024`
words.

## Encryption

`encrypt(out = x0, out_len = x1, n = x2, n_len = x3, e = x4, e_len = x5,
label = x6, label_len = x7, msg, msg_len, seed, scratch, scratch_len)`, the
last five on the stack. If `k < 2 hLen + 2` or `msg_len > k - 2 hLen - 2`
(public), it writes zeros to `out` and returns 0. Otherwise it writes
`EM = 0x00 ‖ seed ‖ DB` to `scratch` (`DB = lHash ‖ 0… ‖ 0x01 ‖ M`, the
label hashed with `H`), masks `DB` with MGF1 of the seed and then the seed
with MGF1 of `maskedDB` (`G`), and returns `vg_rsa_public_checked` of `EM`
into `out`.

## Decryption

`decrypt(out = x0, out_len = x1, msg_len = x2, n = x3, n_len = x4, e = x5,
e_len = x6, p = x7, p_len, q, q_len, dp, dp_len, dq, dq_len, qinv,
qinv_len, label, label_len, ct, ct_len, scratch, scratch_len)`, the last
fifteen on the stack. `vg_rsa_private_checked` writes `EM` (or zeros) to
`scratch` and returns `r` (1, 0 or 2), which only selects values without a
branch. If `k < 2 hLen + 2` (public), the result is `r = 2 ? 2 : 0`, with
zeros to `out` and `*msg_len`. Otherwise, without a branch on anything
secret: the label is hashed (`H`), the seed and `DB` unmasked in place
(`G`); an accumulator `acc` ORs together `EM`'s first byte and
`lHash' ⊕ lHash`; the scan over `T = DB[hLen..]` (`t = k - 2 hLen - 1`
bytes) finds the index `idx` of its first nonzero byte with masks, and ORs
into `acc` a mask if a byte before it is not zero or `0x01`, or if there is
none; `T` is copied into the 2048-byte buffer `scratch + oBuf`, zeros after
it, and shifted left by `idx + 1` bytes in ten passes, pass `j` moving every
one of its first 1024 bytes `2^j` bytes under the mask of bit `j` of
`idx + 1`: the message, then zeros. With `ok` all ones exactly when `r = 1`
and `acc = 0`, `out` receives the buffer's first `k` bytes ANDed with `ok`,
`*msg_len` receives `(t - idx - 1) ∧ ok`, and the result is
`(ok ∧ 1) ∨ (r = 2 ? 2 : 0)`.

The masks are computed from the borrow of a subtraction (`subs`, then `sbc`
of a register from itself): `x - 1` borrows exactly when `x = 0`.
-/

namespace VG.Impl.RsaOaep.AArch64

open VG VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs Layout mgfXor)

/-! ## The frame -/

/-- The inner frame: the RSA operation's stack arguments (12 words for the
private operation, 2 for the public one) at `sp`, then the slots. -/
def frameBytes : Nat := 272

/-- MGF1's slots. -/
def sScr : Nat := 96
def sSrc : Nat := 104
def sSrcLen : Nat := 112
def sDst : Nat := 120
def sDstLen : Nat := 128
def sCtr : Nat := 136
def sDone : Nat := 144
/-- The arguments. -/
def sOut : Nat := 152
def sN : Nat := 160
def sK : Nat := 168
def sE : Nat := 176
def sEl : Nat := 184
def sScrLen : Nat := 192
def sLab : Nat := 200
def sLabLen : Nat := 208
/-- Encryption: the message, its length and the seed. Decryption: the
address of `*msg_len`, the private operation's result, `acc`, `idx` and
`ok`. -/
def sMsg : Nat := 216
def sMsgLen : Nat := 224
def sSeed : Nat := 232
def sMl : Nat := 216
def sR : Nat := 224
def sAcc : Nat := 232
def sIdx : Nat := 240
def sOk : Nat := 248

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
/-- The working space of `update` and `finalize` (at most 1072 bytes). -/
def oW : Nat := 3520
/-- Where the RSA operation's working space starts. -/
def oRsa : Nat := 8192

/-- MGF1's layout. -/
def lay : Layout := ⟨sScr, sSrc, sSrcLen, sDst, sDstLen, sCtr, sDone, oSt, oCtr, oDig, oW⟩

/-- Our stack argument `j` (from 0), from `sp` in the frames. -/
def arg (j : Nat) : Nat := frameBytes + 16 + 8 * j

/-- `d ← scratch + o`, for `o < 4096`. -/
def scr (d : Reg) (o : Nat) : List Instr := Mgf1.scr lay d o

/-- Stack argument `j` to the frame's word at `d`, with `x9 = sp`. -/
def mvArg (j d : Nat) : List Instr := [.ldrSp .x10 (arg j), .str .x .x10 .x9 d]

/-- `d ← n` (`orr d, n, n`). -/
def mov (d n : Reg) : Instr := .logic .orr .x d n n

/-- `d ← -(n = 0)`, the borrow of `n - 1`, with `1` in `one`. -/
def isZero (d n one : Reg) : List Instr := [.subs .x d n one, .sbc .x d d d]

variable (H G : Hash)

/-! ## Common pieces -/

/-- The label's hash, `H(label)`, to `scratch + o`. -/
def hashLabel (o : Nat) : Prog isa :=
  seqs [.block (scr .x0 oSt), .call H.initN H.initC,
    .block (scr .x0 oSt ++ [.movz .x .x1 0 0, .ldrSp .x2 sLab, .ldrSp .x3 sLabLen] ++ scr .x4 oW),
    .call H.updN H.updC,
    .block (scr .x0 oSt ++ [.ldrSp .x1 sLabLen] ++ scr .x2 o ++ scr .x3 oW),
    .call H.finN H.finC]

/-- MGF1's slots for masking `DB` (`k - hLen - 1` bytes at `EM + 1 + hLen`)
with the seed (`hLen` bytes at `EM + 1`). -/
def dbArgs : List Instr :=
  scr .x10 (oEm + 1 + H.D) ++ [.ldrSp .x11 sK, .subImm .x .x11 .x11 (H.D + 1)] ++ scr .x12 (oEm + 1) ++
    [.movz .x .x13 (BitVec.ofNat 16 H.D) 0, .addSp .x9 0, .str .x .x10 .x9 sDst, .str .x .x11 .x9 sDstLen,
      .str .x .x12 .x9 sSrc, .str .x .x13 .x9 sSrcLen]

/-- MGF1's slots for masking the seed with `DB`. -/
def seedArgs : List Instr :=
  scr .x10 (oEm + 1) ++ [.movz .x .x11 (BitVec.ofNat 16 H.D) 0] ++ scr .x12 (oEm + 1 + H.D) ++
    [.ldrSp .x13 sK, .subImm .x .x13 .x13 (H.D + 1), .addSp .x9 0, .str .x .x10 .x9 sDst,
      .str .x .x11 .x9 sDstLen, .str .x .x12 .x9 sSrc, .str .x .x13 .x9 sSrcLen]

/-- `k` zeros to `out` (at `x11`, `x12` bytes left, the zero in `x13`). -/
def zeroOut : Prog isa :=
  .seq (.block [.ldrSp .x11 sOut, .ldrSp .x12 sK, .movz .x .x13 0 0])
    (.loop (.block [.strb .x13 .x11 0, .addImm .x .x11 .x11 1, .subImm .x .x12 .x12 1]) (.nonzero .x .x12))

/-- In `x11`, all ones if `k < 2 hLen + 2`, zero if not. -/
def chkK : List Instr :=
  [.ldrSp .x10 sK, .movz .x .x12 (BitVec.ofNat 16 (2 * H.D + 2)) 0, .subs .x .x11 .x10 .x12,
    .sbc .x .x11 .x11 .x11]

/-! ## Encryption -/

/-- The arguments into their slots, `x9 = sp`. -/
def encPrologue : List Instr :=
  [.addSp .x9 0, .str .x .x0 .x9 sOut, .str .x .x2 .x9 sN, .str .x .x3 .x9 sK, .str .x .x4 .x9 sE,
    .str .x .x5 .x9 sEl, .str .x .x6 .x9 sLab, .str .x .x7 .x9 sLabLen] ++
  mvArg 0 sMsg ++ mvArg 1 sMsgLen ++ mvArg 2 sSeed ++ mvArg 3 sScr ++ mvArg 4 sScrLen

/-- In `x11`, all ones if `msg_len > k - 2 hLen - 2`, zero if not: the
borrow of `k - 2 hLen - 2 - msg_len`, with `k ≥ 2 hLen + 2`. -/
def chkMsg : List Instr :=
  [.ldrSp .x10 sK, .subImm .x .x10 .x10 (2 * H.D + 2), .ldrSp .x12 sMsgLen, .subs .x .x11 .x10 .x12,
    .sbc .x .x11 .x11 .x11]

/-- Zeros to `out`, and 0. -/
def encFail : Prog isa := .seq zeroOut (.block [.movz .x .x0 0 0])

/-- `EM`'s place, the first 1024 bytes of `scratch`, cleared a word at a
time. -/
def clearEm : Prog isa :=
  .seq (.block (scr .x11 oEm ++ [.movz .x .x12 128 0, .movz .x .x13 0 0]))
    (.loop (.block [.str .x .x13 .x11 0, .addImm .x .x11 .x11 8, .subImm .x .x12 .x12 1]) (.nonzero .x .x12))

/-- `n` bytes from `x11` to `x12`, with `x13 = n`. -/
def copyLoop : Prog isa :=
  .loop (.block [.ldrb .x10 .x11 0, .strb .x10 .x12 0, .addImm .x .x11 .x11 1, .addImm .x .x12 .x12 1,
    .subImm .x .x13 .x13 1]) (.nonzero .x .x13)

/-- The seed to `EM + 1`. -/
def copySeed : Prog isa :=
  .seq (.block ([.ldrSp .x11 sSeed] ++ scr .x12 (oEm + 1) ++ [.movz .x .x13 (BitVec.ofNat 16 H.D) 0]))
    copyLoop

/-- `lHash` (the digest at `scratch + oDig`) to `EM + 1 + hLen`. -/
def copyLh : Prog isa :=
  .seq (.block (scr .x11 oDig ++ scr .x12 (oEm + 1 + H.D) ++ [.movz .x .x13 (BitVec.ofNat 16 H.D) 0]))
    copyLoop

/-- `0x01` at `EM + k - mLen - 1`, and the message after it, if it is not
empty. -/
def putMsg : Prog isa :=
  .seq (.block ([.ldrSp .x11 sMsg] ++ scr .x12 oEm ++ [.ldrSp .x10 sK, .add .x .x12 .x12 .x10,
      .ldrSp .x13 sMsgLen, .sub .x .x12 .x12 .x13, .subImm .x .x12 .x12 1, .movz .x .x10 1 0,
      .strb .x10 .x12 0, .addImm .x .x12 .x12 1]))
    (.ite (.nonzero .x .x13) copyLoop (.block []))

/-- `d ← scratch + oRsa`. -/
def scrRsa (d : Reg) : List Instr :=
  [.ldrSp d sScr, .movz .x .x15 (BitVec.ofNat 16 oRsa) 0, .add .x d d .x15]

/-- The arguments of `vg_rsa_public_checked`: `out` (`k` bytes), `n`, `e`,
`EM` as the input (`k` bytes), and the rest of `scratch`. -/
def pubArgs : List Instr :=
  scrRsa .x10 ++ [.ldrSp .x11 sScrLen, .subImm .x .x11 .x11 1024, .addSp .x9 0, .str .x .x10 .x9 0,
    .str .x .x11 .x9 8, .ldrSp .x0 sOut, .ldrSp .x1 sK, .ldrSp .x2 sN, .ldrSp .x3 sK, .ldrSp .x4 sE,
    .ldrSp .x5 sEl] ++ scr .x6 oEm ++ [.ldrSp .x7 sK]

/-- `EM`, before masking. -/
def encEm : Prog isa := seqs [clearEm, copySeed H, hashLabel H oDig, copyLh H, putMsg]

variable (pubN : String) (pubC : Prog isa)

/-- After the checks. -/
def encMain : Prog isa :=
  seqs [encEm H, .block (dbArgs H), mgfXor lay G, .block (seedArgs H), mgfXor lay G, .block pubArgs,
    .call pubN pubC]

/-- The inner frame's body. -/
def encBody : Prog isa :=
  seqs [.block (encPrologue ++ chkK H),
    .ite (.nonzero .x .x11) encFail (seqs [.block (chkMsg H), .ite (.nonzero .x .x11) encFail
      (encMain H G pubN pubC)])]

/-- `vg_rsa_oaep_<H>_mgf1_<G>_encrypt`. -/
def encrypt : Prog isa :=
  .frame (.push .x30) (.frame (.alloc frameBytes) (encBody H G pubN pubC) (.free frameBytes)) (.pop .x30)

/-! ## Decryption -/

/-- The arguments into their slots, `x9 = sp`; ours from `p_len` to
`qinv_len` to the frame's words 1 to 9, the private operation's stack
arguments after `p` (`x7`, word 0). -/
def decPrologue : List Instr :=
  [.addSp .x9 0, .str .x .x0 .x9 sOut, .str .x .x2 .x9 sMl, .str .x .x3 .x9 sN, .str .x .x4 .x9 sK,
    .str .x .x5 .x9 sE, .str .x .x6 .x9 sEl, .str .x .x7 .x9 0] ++
  mvArg 9 sLab ++ mvArg 10 sLabLen ++ mvArg 13 sScr ++ mvArg 14 sScrLen ++
  (List.range 9).flatMap (fun j => mvArg j (8 * (j + 1)))

/-- The rest of `vg_rsa_private_checked`'s arguments: the rest of `scratch`
(words 10 and 11), and its registers: `EM`'s place (`k` bytes), `n`, `e`,
the ciphertext as the input (`k` bytes). -/
def privArgs : List Instr :=
  scrRsa .x10 ++ [.ldrSp .x11 sScrLen, .subImm .x .x11 .x11 1024, .str .x .x10 .x9 80,
    .str .x .x11 .x9 88] ++ scr .x0 oEm ++ [.ldrSp .x1 sK, .ldrSp .x2 sN, .ldrSp .x3 sK, .ldrSp .x4 sE,
    .ldrSp .x5 sEl, .ldrSp .x6 (arg 11), .ldrSp .x7 sK]

/-- `x0 ← (r = 2) ? 2 : 0`. -/
def faultBit : List Instr :=
  [.ldrSp .x10 sR, .movz .x .x12 2 0, .logic .eor .x .x10 .x10 .x12, .movz .x .x13 1 0] ++
    isZero .x10 .x10 .x13 ++ [.logic .and .x .x0 .x10 .x12]

/-- Zeros to `out` and `*msg_len`, and the result `(r = 2) ? 2 : 0`. -/
def decFail : Prog isa :=
  .seq zeroOut (.block ([.ldrSp .x11 sMl, .str .x .x13 .x11 0] ++ faultBit))

/-- `acc := EM[0] ∨ ⋁ (lHash'[i] ⊕ lHash[i])`, to its slot. -/
def accLh : Prog isa :=
  .seq (.block (scr .x11 oLh ++ scr .x12 (oEm + 1 + H.D) ++ scr .x13 oEm ++
      [.ldrb .x14 .x13 0, .movz .x .x13 (BitVec.ofNat 16 H.D) 0]))
    (.seq (.loop (.block [.ldrb .x10 .x11 0, .ldrb .x15 .x12 0, .logic .eor .x .x10 .x10 .x15,
        .logic .orr .x .x14 .x14 .x10, .addImm .x .x11 .x11 1, .addImm .x .x12 .x12 1, .subImm .x .x13 .x13 1])
        (.nonzero .x .x13))
      (.block [.addSp .x9 0, .str .x .x14 .x9 sAcc]))

/-- The scan of `T` (at `x11`, `x12` bytes left, the index in `x9`): `x13`
all ones while no `0x01` has been seen (`looking`), `x8` the index of the
first, `x14` the accumulator, ORed with a mask for every byte other than
zero and `0x01` before it; `1` in `x17`. -/
def scanBody : List Instr :=
  [.ldrb .x10 .x11 0] ++ isZero .x15 .x10 .x17 ++ [.logic .eor .x .x16 .x10 .x17] ++ isZero .x16 .x16 .x17 ++
    [.logic .orr .x .x10 .x15 .x16, .bicRor .x .x10 .x13 .x10 0, .logic .orr .x .x14 .x14 .x10,
      .logic .and .x .x10 .x9 .x13, .logic .and .x .x10 .x10 .x16, .logic .orr .x .x8 .x8 .x10,
      .bicRor .x .x13 .x13 .x16 0, .addImm .x .x9 .x9 1, .addImm .x .x11 .x11 1, .subImm .x .x12 .x12 1]

/-- `T`'s address in `x11` and its length `t = k - 2 hLen - 1` in `x12`. -/
def tArgs : List Instr := scr .x11 (oEm + 1 + 2 * H.D) ++ [.ldrSp .x12 sK, .subImm .x .x12 .x12 (2 * H.D + 1)]

/-- The scan, then `acc |= looking`, and `acc` and `idx` into their slots. -/
def scan : Prog isa :=
  .seq (.block (tArgs H ++ [.movz .x .x13 0 0, .subImm .x .x13 .x13 1, .movz .x .x8 0 0, .ldrSp .x14 sAcc,
      .movz .x .x9 0 0, .movz .x .x17 1 0]))
    (.seq (.loop (.block scanBody) (.nonzero .x .x12))
      (.block [.logic .orr .x .x14 .x14 .x13, .addSp .x9 0, .str .x .x14 .x9 sAcc, .str .x .x8 .x9 sIdx]))

/-- The buffer's 2048 bytes cleared a word at a time. -/
def clearBuf : Prog isa :=
  .seq (.block (scr .x11 oBuf ++ [.movz .x .x12 256 0, .movz .x .x13 0 0]))
    (.loop (.block [.str .x .x13 .x11 0, .addImm .x .x11 .x11 8, .subImm .x .x12 .x12 1]) (.nonzero .x .x12))

/-- `T` to the buffer. -/
def copyT : Prog isa :=
  .seq (.block (tArgs H ++ [mov .x13 .x12, mov .x10 .x11] ++ scr .x12 oBuf ++ [mov .x11 .x10])) copyLoop

/-- One byte of a pass of the shift, at `x11`, replaced by the one `d` bytes
after it (at `x12`) under the mask `x15`; `x13` bytes left. -/
def passBody : List Instr :=
  [.ldrb .x10 .x11 0, .ldrb .x16 .x12 0, .logic .eor .x .x16 .x16 .x10, .logic .and .x .x16 .x16 .x15,
    .logic .eor .x .x10 .x10 .x16, .strb .x10 .x11 0, .addImm .x .x11 .x11 1, .addImm .x .x12 .x12 1,
    .subImm .x .x13 .x13 1]

/-- A pass of the shift, with the buffer at `x17`, the distance `d` in
`x14`, `a` in `x9`: each of the buffer's first 1024 bytes replaced by the one
`d` bytes after it if bit 0 of `a` is set; then `a >>= 1`, `d += d`, and
one pass less in `x8`. -/
def pass : Prog isa :=
  .seq (.block [mov .x11 .x17, .add .x .x12 .x17 .x14, .movz .x .x15 1 0, .logic .and .x .x15 .x9 .x15,
      .movz .x .x16 0 0, .sub .x .x15 .x16 .x15, .movz .x .x13 1024 0])
    (.seq (.loop (.block passBody) (.nonzero .x .x13))
      (.block [.lsr .x .x9 .x9 1, .add .x .x14 .x14 .x14, .subImm .x .x8 .x8 1]))

/-- The buffer shifted left by `idx + 1` bytes, in ten passes. -/
def shift : Prog isa :=
  .seq (.block (scr .x17 oBuf ++ [.ldrSp .x9 sIdx, .addImm .x .x9 .x9 1, .movz .x .x14 1 0,
      .movz .x .x8 10 0]))
    (.loop pass (.nonzero .x .x8))

/-- `ok`: all ones iff `r = 1` and `acc = 0`, to its slot. -/
def okMask : List Instr :=
  [.ldrSp .x10 sR, .movz .x .x17 1 0, .logic .eor .x .x10 .x10 .x17] ++ isZero .x10 .x10 .x17 ++
    [.ldrSp .x11 sAcc] ++ isZero .x11 .x11 .x17 ++ [.logic .and .x .x11 .x11 .x10, .addSp .x9 0,
      .str .x .x11 .x9 sOk]

/-- The buffer's first `k` bytes, ANDed with `ok` (`x15`), to `out`. -/
def outLoop : Prog isa :=
  .seq (.block (scr .x12 oBuf ++ [.ldrSp .x11 sOut, .ldrSp .x13 sK, .ldrSp .x15 sOk]))
    (.loop (.block [.ldrb .x10 .x12 0, .logic .and .x .x10 .x10 .x15, .strb .x10 .x11 0,
      .addImm .x .x11 .x11 1, .addImm .x .x12 .x12 1, .subImm .x .x13 .x13 1]) (.nonzero .x .x13))

/-- `*msg_len := (t - idx - 1) ∧ ok`, and the result `(ok ∧ 1) ∨ ((r = 2) ? 2 : 0)`. -/
def decRet : List Instr :=
  [.ldrSp .x14 sOk, .ldrSp .x10 sK, .subImm .x .x10 .x10 (2 * H.D + 2), .ldrSp .x11 sIdx,
    .sub .x .x10 .x10 .x11, .logic .and .x .x10 .x10 .x14, .ldrSp .x11 sMl, .str .x .x10 .x11 0,
    .movz .x .x15 1 0, .logic .and .x .x14 .x14 .x15] ++ faultBit ++ [.logic .orr .x .x0 .x0 .x14]

/-- After the private operation and the check of `k`: the decoding. -/
def decMain : Prog isa :=
  seqs [hashLabel H oLh, .block (seedArgs H), mgfXor lay G, .block (dbArgs H), mgfXor lay G, accLh H, scan H,
    clearBuf, copyT H, shift, .block okMask, outLoop, .block (decRet H)]

variable (privN : String) (privC : Prog isa)

/-- The inner frame's body. -/
def decBody : Prog isa :=
  seqs [.block (decPrologue ++ privArgs), .call privN privC,
    .block ([.logic .orr .w .x0 .x0 .x0, .addSp .x9 0, .str .x .x0 .x9 sR] ++ chkK H),
    .ite (.nonzero .x .x11) decFail (decMain H G)]

/-- `vg_rsa_oaep_<H>_mgf1_<G>_decrypt`. -/
def decrypt : Prog isa :=
  .frame (.push .x30) (.frame (.alloc frameBytes) (decBody H G privN privC) (.free frameBytes)) (.pop .x30)

end VG.Impl.RsaOaep.AArch64
