module

public import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE
public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Frame

/-!
# RSAES-OAEP encryption (RFC 8017 §7.1.1) with a precomputed public key on PPC64LE

`vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed(out = r3, out_len = r4,
n = r5, n_len = r6, e = r7, e_len = r8, label = r9, label_len = r10, msg,
msg_len, seed, scratch, scratch_len, pre, pre_len)`, the last seven on the
stack, for a hash function `H` (the label's) and MGF1's hash function `G`,
each an `Impl.Hmac.Stream.PPC64LE.Hash` (its streaming functions), which it
calls, with `vg_rsa_public_precomputed_checked`. The steps are those of
AArch64 (`Impl/RsaOaep/AArch64.lean`).

If `k < 2 hLen + 2` or `msg_len > k - 2 hLen - 2` (`k = n_len`, public), it
writes zeros to `out` and returns 0. Otherwise it writes
`EM = 0x00 ‖ seed ‖ DB` to `scratch` (`DB = lHash ‖ 0… ‖ 0x01 ‖ M`, the
label hashed with `H`), masks `DB` with MGF1 of the seed and then the seed
with MGF1 of `maskedDB` (`G`), and returns `vg_rsa_public_precomputed_checked`
of `EM` into `out`, with `pre` and the rest of `scratch`.

The function allocates a frame of `frameBytes` bytes. Its Parameter Save
Area holds the call's stack arguments (at `r1 + 96`, `r1 + 104`); then come
our caller's `r14`–`r29` (`saved`) and our return address. The values the
code keeps across the calls are in `r14`–`r29`, which every function it
calls saves and restores: `r14` = `scratch`, `r15` = `k`, `r16` = `out`,
`r17` = `e`, `r18` = `e_len`, `r19` = `label`, `r20` = `label_len`,
`r21` = `pre`, `r22` = `pre_len`, `r23` = `scratch_len`; and MGF1's
`r24` = `src`, `r25` = `srcLen`, `r26` = `dst`, `r27` = `dstLen`,
`r28` = the counter and `r29` = `done`, the bytes of the mask so far.
Before the first call, `r9`, `r10` and `r11` hold `msg`, `msg_len` and
`seed`.

The first `oRsa` = 8192 bytes of `scratch` are ours: `EM` (up to 1024
bytes), then the streaming state, the digest, MGF1's counter and the working
space of `update` and `finalize`. The public operation gets the rest,
`scratch_len - 1024` words.

A comparison `a < b` of values below `2⁶³` is the top bit of `a - b`. Every
branch and address depends only on the pointers and the lengths.
-/

@[expose] public section

namespace VG.Impl.RsaOaep.PPC64LE

open VG VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)

/-! ## The frame -/

/-- The size of the frame. -/
def frameBytes : Nat := 256

/-- Where our caller's `r14`–`r29` and our return address are saved. -/
def saved : List (Reg × Nat) :=
  [(.r14, 112), (.r15, 120), (.r16, 128), (.r17, 136), (.r18, 144), (.r19, 152), (.r20, 160), (.r21, 168),
    (.r22, 176), (.r23, 184), (.r24, 192), (.r25, 200), (.r26, 208), (.r27, 216), (.r28, 224), (.r29, 232)]
def oLr : Nat := 240

/-- Our stack argument `j` (from 0), in the frame. -/
def arg (j : Nat) : Nat := frameBytes + 96 + 8 * j

/-! ## Our part of `scratch` -/

/-- `EM`: `k` bytes. -/
def oEm : Nat := 0
/-- The streaming state (at most 192 bytes). -/
def oSt : Nat := 1024
/-- The bytes `finalize` writes (at most 64). -/
def oDig : Nat := 1280
/-- MGF1's counter. -/
def oCtr : Nat := 1344
/-- The working space of `update` and `finalize` (at most 1024 bytes). -/
def oW : Nat := 1352
/-- Where the public operation's working space starts. -/
def oRsa : Nat := 8192

/-! ## The saves and the restores -/

/-- `r12 := r1`; our caller's `r14`–`r29` and our return address into the
frame. -/
def save : List Instr :=
  [.addSp .r12 0] ++ saved.map (fun p => .store .d p.1 .r12 p.2) ++ [.mflr .r0, .store .d .r0 .r12 oLr]

/-- Our caller's `r14`–`r29` and our return address back from the frame. -/
def restore : List Instr :=
  [.addSp .r12 0, .load .d .r0 .r12 oLr, .mtlr .r0] ++ saved.map fun p => .load .d p.1 .r12 p.2

/-- The arguments into the registers that keep them, with `r12 = r1`; `msg`,
`msg_len` and `seed` into `r9`, `r10` and `r11`. -/
def prologue : List Instr :=
  [.load .d .r14 .r12 (arg 3), mov .r15 .r6, mov .r16 .r3, mov .r17 .r7, mov .r18 .r8, mov .r19 .r9,
    mov .r20 .r10, .load .d .r21 .r12 (arg 5), .load .d .r22 .r12 (arg 6), .load .d .r23 .r12 (arg 4),
    .load .d .r9 .r12 (arg 0), .load .d .r10 .r12 (arg 1), .load .d .r11 .r12 (arg 2)]

/-! ## Loops -/

/-- `r6` bytes from `r4` to `r5`, for `r6 > 0`. -/
def copyLoop : Prog isa :=
  .loop (.block [.lbz .r7 .r4 0, .stb .r7 .r5 0, .addi .r4 .r4 1, .addi .r5 .r5 1, .subi .r6 .r6 1])
    (.nonzero .d .r6)

/-- `r5` bytes `r6` from `r4`, for `r5 > 0`. -/
def zeroLoop : Prog isa :=
  .loop (.block [.stb .r6 .r4 0, .addi .r4 .r4 1, .subi .r5 .r5 1]) (.nonzero .d .r5)

/-- `k` zeros to `out`. -/
def zeroOut : Prog isa := .seq (.block [mov .r4 .r16, mov .r5 .r15, .li .r6 0]) zeroLoop

/-- Zeros to `out`, and 0. -/
def encFail : Prog isa := .seq zeroOut (.block [.li .r3 0])

variable (H G : Hash)

/-! ## The checks -/

/-- In `r3`, 1 if `k < 2 hLen + 2`, 0 if not. -/
def chkK : List Instr := [.li .r3 (2 * H.D + 2), .sub .r3 .r15 .r3, .lsr .d .r3 .r3 63]

/-- In `r3`, nonzero exactly when `msg_len > k - 2 hLen - 2`, for
`k ≥ 2 hLen + 2`: the top bit of `msg_len`, or of
`(k - 2 hLen - 2) - msg_len`. -/
def chkMsg : List Instr :=
  [.li .r3 (2 * H.D + 2), .sub .r4 .r15 .r3, .sub .r4 .r4 .r10, .lsr .d .r4 .r4 63, .lsr .d .r3 .r10 63,
    .logic .or .r3 .r3 .r4]

/-! ## `EM` before masking -/

/-- `EM`'s place, the first 1024 bytes of `scratch`, cleared. -/
def clearEm : Prog isa := .seq (.block [.addi .r4 .r14 oEm, .li .r5 1024, .li .r6 0]) zeroLoop

/-- The seed to `EM + 1`. -/
def copySeed : Prog isa := .seq (.block [mov .r4 .r11, .addi .r5 .r14 (oEm + 1), .li .r6 H.D]) copyLoop

/-- `0x01` at `EM + k - mLen - 1`, and the message after it, if it is not
empty. -/
def putMsg : Prog isa :=
  .seq (.block [.add .r5 .r14 .r15, .sub .r5 .r5 .r10, .subi .r5 .r5 1, .li .r7 1, .stb .r7 .r5 0,
      .addi .r5 .r5 1, mov .r4 .r9, mov .r6 .r10])
    (.ite (.nonzero .d .r6) copyLoop (.block []))

/-- `H(label)` to `scratch + oDig`. -/
def hashLabel : Prog isa :=
  .seq (.block [.addi .r3 .r14 oSt]) (.seq H.callInit
  (.seq (.block [.addi .r3 .r14 oSt, .li .r4 0, mov .r5 .r19, mov .r6 .r20, .addi .r7 .r14 oW]) (.seq H.callUpd
  (.seq (.block [.addi .r3 .r14 oSt, mov .r4 .r20, .addi .r5 .r14 oDig, .addi .r6 .r14 oW]) H.callFin))))

/-- `lHash` (the digest at `scratch + oDig`) to `EM + 1 + hLen`. -/
def copyLh : Prog isa :=
  .seq (.block [.addi .r4 .r14 oDig, .addi .r5 .r14 (oEm + 1 + H.D), .li .r6 H.D]) copyLoop

/-! ## MGF1

`dst ⊕= MGF1(src, dstLen)` (RFC 8017 Appendix B.2.1), for `dstLen > 0`, with
`src`, `srcLen`, `dst` and `dstLen` in `r24`–`r27`. For each counter `c`
(`r28`) from 0, while `done = c hLen` (`r29`) is below `dstLen`: the state
is set by `init`, `update` absorbs `src` and `I2OSP(c, 4)` (written
big-endian to `scratch + oCtr`), `finalize` writes the digest to
`scratch + oDig`, and its first `min(hLen, dstLen - done)` bytes are XORed
into `dst + done`. -/

/-- `update(state, srcLen, scratch + oCtr, 4, work)`, with the counter
written there big-endian first. -/
def updCtrArgs : List Instr :=
  [.addi .r5 .r14 oCtr, mov .r8 .r28, .stb .r8 .r5 3, .lsr .d .r8 .r8 8, .stb .r8 .r5 2, .lsr .d .r8 .r8 8,
    .stb .r8 .r5 1, .lsr .d .r8 .r8 8, .stb .r8 .r5 0, .addi .r3 .r14 oSt, mov .r4 .r25, .li .r6 4,
    .addi .r7 .r14 oW]

/-- The digest in `r11`, `dst + done` in `r12`, and in `r9`
`min(hLen, dstLen - done)`: `hLen + ((rem - hLen) ∧ -(rem < hLen))` for
`rem = dstLen - done`. -/
def xorHead : List Instr :=
  [.addi .r11 .r14 oDig, .add .r12 .r26 .r29, .sub .r8 .r27 .r29, .li .r9 G.D, .sub .r10 .r8 .r9,
    .lsr .d .r6 .r10 63, .li .r7 0, .sub .r6 .r7 .r6, .logic .and .r10 .r10 .r6, .add .r9 .r9 .r10]

/-- A byte of the digest XORed into `dst`. -/
def xorBody : List Instr :=
  [.lbz .r10 .r11 0, .lbz .r8 .r12 0, .logic .xor .r8 .r8 .r10, .stb .r8 .r12 0, .addi .r11 .r11 1,
    .addi .r12 .r12 1, .subi .r9 .r9 1]

/-- The first `min(hLen, dstLen - done)` bytes of the digest XORed into
`dst + done`. -/
def xorOut : Prog isa := .seq (.block (xorHead G)) (.loop (.block xorBody) (.nonzero .d .r9))

/-- The next counter and `done`, and in `r12` 1 while `done < dstLen`, 0
after. -/
def nextCtr : List Instr := [.addi .r28 .r28 1, .addi .r29 .r29 G.D, .sub .r12 .r29 .r27, .lsr .d .r12 .r12 63]

/-- One block: the digest of `src ‖ I2OSP(c, 4)`, XORed into `dst`. -/
def round : Prog isa :=
  .seq (.block [.addi .r3 .r14 oSt]) (.seq G.callInit
  (.seq (.block [.addi .r3 .r14 oSt, .li .r4 0, mov .r5 .r24, mov .r6 .r25, .addi .r7 .r14 oW]) (.seq G.callUpd
  (.seq (.block updCtrArgs) (.seq G.callUpd
  (.seq (.block [.addi .r3 .r14 oSt, .addi .r4 .r25 4, .addi .r5 .r14 oDig, .addi .r6 .r14 oW]) (.seq G.callFin
  (.seq (xorOut G) (.block (nextCtr G))))))))))

/-- `dst ⊕= MGF1(src, dstLen)`, for `dstLen > 0`. -/
def mgfXor : Prog isa := .seq (.block [.li .r28 0, .li .r29 0]) (.loop (round G) (.nonzero .d .r12))

/-- MGF1's registers for masking `DB` (`k - hLen - 1` bytes at
`EM + 1 + hLen`) with the seed (`hLen` bytes at `EM + 1`). -/
def dbArgs : List Instr :=
  [.addi .r24 .r14 (oEm + 1), .li .r25 H.D, .addi .r26 .r14 (oEm + 1 + H.D), .subi .r27 .r15 (H.D + 1)]

/-- MGF1's registers for masking the seed with `maskedDB`. -/
def seedArgs : List Instr :=
  [.addi .r24 .r14 (oEm + 1 + H.D), .subi .r25 .r15 (H.D + 1), .addi .r26 .r14 (oEm + 1), .li .r27 H.D]

/-! ## The public operation -/

/-- The arguments of `vg_rsa_public_precomputed_checked`: `out` (`k`
bytes), `pre`, `e`, `EM` as the input (`k` bytes), and the rest of
`scratch` on the stack. -/
def pubArgs : List Instr :=
  [.addSp .r12 0, .li .r4 oRsa, .add .r4 .r14 .r4, .store .d .r4 .r12 96, .subi .r5 .r23 1024,
    .store .d .r5 .r12 104, mov .r3 .r16, mov .r4 .r15, mov .r5 .r21, mov .r6 .r22, mov .r7 .r17,
    mov .r8 .r18, .addi .r9 .r14 oEm, mov .r10 .r15]

/-! ## The function -/

/-- `EM` before masking, but for `lHash`; the code before the first call. -/
def encEm : Prog isa := .seq clearEm (.seq (copySeed H) (putMsg))

/-- After the checks. -/
def encMain : Prog isa :=
  .seq (encEm H) (.seq (hashLabel H) (.seq (copyLh H)
  (.seq (.block (dbArgs H)) (.seq (mgfXor G)
  (.seq (.block (seedArgs H)) (.seq (mgfXor G)
  (.seq (.block pubArgs) Impl.RsaPkcs1Sig.PPC64LE.pubCall)))))))

/-- The checks, then `encMain`. -/
def checks : Prog isa :=
  .seq (.block (chkK H)) (.ite (.nonzero .d .r3) encFail
    (.seq (.block (chkMsg H)) (.ite (.nonzero .d .r3) encFail (encMain H G))))

/-- The frame's body. -/
def body : Prog isa := .seq (.block (save ++ prologue)) (.seq (checks H G) (.block restore))

/-- `vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed`. -/
def encrypt : Prog isa := .frame (.alloc frameBytes) (body H G) (.free frameBytes)

end VG.Impl.RsaOaep.PPC64LE
