module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.Priv
public import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE
public import VerifiedGarbage.Impl.Sha256.PPC64LE.Stream
public import VerifiedGarbage.Spec.Sha256.Contract
public import VerifiedGarbage.Spec.Hmac.Generic

/-!
# RSAES-PKCS1-v1_5 decryption with implicit rejection on PPC64LE

`vg_rsa_pkcs1_decrypt(out = r3, out_len = r4, msg_len = r5, n = r6,
n_len = r7, e = r8, e_len = r9, d = r10, d_len, input, input_len, p, p_len,
q, q_len, dp, dp_len, dq, dq_len, qinv, qinv_len, scratch, scratch_len)`,
the last fifteen on the stack (the Parameter Save Area at `r1 + 96`). As on
AArch64 (`Impl/RsaPkcs1Enc/AArch64/Decrypt.lean`), with
`vg_rsa_private_checked` and SHA-256's and HMAC-SHA-256's streaming
functions taking their working space as an argument, it runs
draft-irtf-cfrg-rsa-guidance-10 §7.2:

1. The private-key operation, `EM` (or zeros) to `out` and its result `r`
   (1, or 0 or 2 for its errors) into a slot (`setup`, the call).
2. `D = I2OSP(d, k)` in `scratch`: zeros, then `d` at its end (`dBuild`);
   `DH = SHA256(D)` (`hashD`); `KDK = HMAC(DH, C)` (`kdkMac`).
3. The candidate lengths `CL = IRPRF(KDK, "length", 256)` (`clLoop`) and the
   alternative message `AM = IRPRF(KDK, "message", k)` (`amLoop`), a block of
   32 bytes per HMAC, the block's counter in a slot.
4. The mask of the candidates, `2^bitLength(k - 11) - 1`, by doublings
   (`maskPart`), and the alternative length `AL`, the last candidate not
   above `k - 11` (`alPart`), selected with a mask.
5. The scan of `EM` for its first zero from index 2 (`scanPart`), the
   validity mask `v` and the lengths (`validBlock`), and the output
   (`selLoop`): byte `i` of `out` is `EM[i]` or `AM[i]` as `v` selects, if
   `i ≥ k - len` for the selected length `len`, and zero otherwise, and
   everything (`out`, and `len` to `*msg_len`) is masked by `r = 1`. The
   function returns `r`.

Without the carry bit, every comparison is of numbers below `2^63`, by the
top bit of their difference (`lsr r, r, 63`), and every selection is by
a mask, `0 - bit`. Every address and branch depends only on the pointers,
the lengths and the counters. `out`'s and `AM`'s bytes are all read,
whichever is returned.

The frame (`stdu r1, -frameBytes(r1)`) holds the Parameter Save Area of the
private-key operation (its twelve stack arguments, at `r1 + 96`), then the
slots from `oOut`, our return address among them. Only volatile registers
are used, so the slots hold everything kept across a call. Our own stack
arguments are at `r1 + frameBytes + 96 + 8 j` (`arg j`). In `scratch`, from
`sSt`: the streaming state (also HMAC's inner state), HMAC's outer state,
the working space, the message of an IRPRF block, `DH`, `KDK`, `CL`, `AM`
and `D`.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt

open VG VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov)

/-- The size of the frame. -/
def frameBytes : Nat := 304

/-! The slots. -/
def oOut : Nat := 192
def oML : Nat := 200
def oN : Nat := 208
def oK : Nat := 216
def oE : Nat := 224
def oEl : Nat := 232
def oD : Nat := 240
def oDl : Nat := 248
def oIn : Nat := 256
def oScr : Nat := 264
def oR : Nat := 272
def oI : Nat := 280
def oNB : Nat := 288
def oLr : Nat := 296

/-! Where things are in `scratch`. -/
def sSt : Nat := 0
def sOuter : Nat := 96
def sWork : Nat := 192
def sMsg : Nat := 1024
def sDH : Nat := 1040
def sKDK : Nat := 1104
def sCL : Nat := 1136
def sAM : Nat := 1392
def sD : Nat := 2416

/-- Our stack argument `j` (from 0), in the frame. -/
def arg (j : Nat) : Nat := frameBytes + 96 + 8 * j

/-- SHA-256's streaming functions, and HMAC-SHA-256's with them. -/
def sha256 : Impl.Hmac.Stream.PPC64LE.Hash where
  B := 64
  N := 32
  D := 32
  FD := 32
  W := 160
  initN := Spec.Sha256.initApi.name
  initC := Impl.Sha256.PPC64LE.Stream.init
  updN := "vg_sha256_update_scratch"
  updC := Impl.Sha256.PPC64LE.Stream.update
  finN := "vg_sha256_finalize_scratch"
  finC := Impl.Sha256.PPC64LE.Stream.finalize
  hmacInitN := "vg_hmac_sha256_init_scratch"

def privCall : Prog isa := .call "vg_rsa_private_checked" Impl.Rsa.PPC64LE.Priv.code
def initCall : Prog isa := .call Spec.Sha256.initApi.name Impl.Sha256.PPC64LE.Stream.init
def updCall : Prog isa := .call "vg_sha256_update_scratch" Impl.Sha256.PPC64LE.Stream.update
def finCall : Prog isa := .call "vg_sha256_finalize_scratch" Impl.Sha256.PPC64LE.Stream.finalize
def macInitCall : Prog isa := .call "vg_hmac_sha256_init_scratch" sha256.init
def macFinCall : Prog isa := .call "vg_hmac_sha256_finalize_scratch" sha256.finalize

/-- `d ← scratch + a`, through the frame at `r12`. -/
def scr (d : Reg) (a : Nat) : List Instr := [.load .d d .r12 oScr, .addi d d a]

/-- `r12 := r1`. -/
def fp : Instr := .addSp .r12 0

/-! ## 1. The private-key operation -/

/-- The slots of our return address (in `r0`, once moved there) and of the
registers' arguments. -/
def savedSlots : List (Reg × Nat) :=
  [(.r0, oLr), (.r3, oOut), (.r5, oML), (.r6, oN), (.r7, oK), (.r8, oE), (.r9, oEl), (.r10, oD)]

/-- Our return address and the registers' arguments to the slots. -/
def saves : List Instr := [fp, .mflr .r0] ++ savedSlots.map fun (r, d) => .store .d r .r12 d

/-- Our stack argument `j` to the frame's word at `d`. -/
def mvArg (j d : Nat) : List Instr := [.load .d .r0 .r12 (arg j), .store .d .r0 .r12 d]

/-- `d_len`, the input and `scratch` to their slots. -/
def slotMoves : List Instr := mvArg 0 oDl ++ mvArg 1 oIn ++ mvArg 13 oScr

/-- Our stack argument `3 + j` (`p` … `scratch_len`) to the private-key
operation's stack argument `j`. -/
def copyArg (j : Nat) : List Instr := mvArg (3 + j) (96 + 8 * j)

/-- Its registers: `out`, `n_len`, `n`, `n_len`, `e`, `e_len`, the input,
`n_len`. -/
def privRegs : List Instr :=
  [mov .r4 .r7, mov .r5 .r6, mov .r6 .r7, mov .r7 .r8, mov .r8 .r9, .load .d .r9 .r12 oIn, mov .r10 .r4]

def setup : List Instr := saves ++ slotMoves ++ (List.range 12).flatMap copyArg ++ privRegs

/-! ## 2. The key derivation key -/

/-- `r` (the low 32 bits of `r3`, which are all the call defines) to its
slot; the zeros of `D`: its base in `r11`, `k` in `r9` and a zero in
`r0`. -/
def dPtrs₁ : List Instr :=
  [.lsr .w .r3 .r3 0, fp, .store .d .r3 .r12 oR] ++ scr .r11 sD ++ [.load .d .r9 .r12 oK, .li .r0 0]

def zeroLoop : Prog isa :=
  .loop (.block [.stb .r0 .r11 0, .addi .r11 .r11 1, .subi .r9 .r9 1]) (.nonzero .d .r9)

/-- `d` at the end of `D`: `d` in `r10`, its length in `r9`, its place
(`scratch + sD + k - d_len`) in `r11`. -/
def dPtrs₂ : List Instr :=
  [.load .d .r10 .r12 oD, .load .d .r9 .r12 oDl] ++ scr .r11 sD ++ [.load .d .r8 .r12 oK, .add .r11 .r11 .r8,
    .sub .r11 .r11 .r9]

def copyLoop : Prog isa :=
  .loop (.block [.lbz .r0 .r10 0, .stb .r0 .r11 0, .addi .r10 .r10 1, .addi .r11 .r11 1, .subi .r9 .r9 1])
    (.nonzero .d .r9)

def dBuild : Prog isa := .seq (.block dPtrs₁) (.seq zeroLoop (.seq (.block dPtrs₂) copyLoop))

/-- `init(state)`. -/
def shaInitArgs : List Instr := fp :: scr .r3 sSt
/-- `update(state, 0, D, k, work)`. -/
def shaUpdArgs : List Instr :=
  fp :: scr .r3 sSt ++ [.li .r4 0] ++ scr .r5 sD ++ [.load .d .r6 .r12 oK] ++ scr .r7 sWork
/-- `finalize(state, k, DH, work)`. -/
def shaFinArgs : List Instr := fp :: scr .r3 sSt ++ [.load .d .r4 .r12 oK] ++ scr .r5 sDH ++ scr .r6 sWork

def hashD : Prog isa :=
  .seq (.block shaInitArgs) (.seq initCall (.seq (.block shaUpdArgs) (.seq updCall
    (.seq (.block shaFinArgs) finCall))))

/-- HMAC's `init(inner, outer, key, 32, work)` for the key at `scratch + key`. -/
def macInitArgs (key : Nat) : List Instr :=
  fp :: scr .r3 sSt ++ scr .r4 sOuter ++ scr .r5 key ++ [.li .r6 32] ++ scr .r7 sWork

/-- `update(inner, 64, C, k, work)`. -/
def kdkUpdArgs : List Instr :=
  fp :: scr .r3 sSt ++ [.li .r4 64, .load .d .r5 .r12 oIn, .load .d .r6 .r12 oK] ++ scr .r7 sWork

/-- HMAC's `finalize(inner, outer, 64 + k, KDK, work)`. -/
def kdkFinArgs : List Instr :=
  fp :: scr .r3 sSt ++ scr .r4 sOuter ++ [.load .d .r5 .r12 oK, .addi .r5 .r5 64] ++ scr .r6 sKDK ++ scr .r7 sWork

def kdkMac : Prog isa :=
  .seq (.block (macInitArgs sDH)) (.seq macInitCall (.seq (.block kdkUpdArgs)
    (.seq updCall (.seq (.block kdkFinArgs) macFinCall))))

/-! ## 3. IRPRF -/

/-- Byte `d` of the block's message (at `r9`): the immediate `v`. -/
def putByte (d v : Nat) : List Instr := [.li .r10 v, .stb .r10 .r9 d]

/-- The message `I2OSP(i, 2) ‖ label ‖ bitLength` at `scratch + sMsg` (in
`r9`), with `i < 256` in `r11`: the label's bytes, and the code `len`
writing the bit length's two bytes after them. -/
def msgBytes (label : List Nat) (len : List Instr) : List Instr :=
  putByte 0 0 ++ [.stb .r11 .r9 1] ++ (label.zipIdx.flatMap fun (v, j) => putByte (2 + j) v) ++ len

/-- The bit length 2048 of `CL`, after the 6 bytes of "length". -/
def clLen : List Instr := putByte 8 0x08 ++ putByte 9 0x00

/-- The bit length `8 k` of `AM`, after the 7 bytes of "message", from `k`
in `r8`. -/
def amLen : List Instr := [.lsl .r10 .r8 3, .stb .r10 .r9 10, .lsr .d .r10 .r10 8, .stb .r10 .r9 9]

/-- `update(inner, 64, msg, len, work)`. -/
def prfUpdArgs (len : Nat) : List Instr :=
  fp :: scr .r3 sSt ++ [.li .r4 64] ++ scr .r5 sMsg ++ [.li .r6 len] ++ scr .r7 sWork

/-- HMAC's `finalize(inner, outer, 64 + len, scratch + dst + 32 i, work)`. -/
def prfFinArgs (len dst : Nat) : List Instr :=
  fp :: scr .r3 sSt ++ scr .r4 sOuter ++ [.li .r5 (64 + len), .load .d .r6 .r12 oI, .lsl .r6 .r6 5] ++
    scr .r10 dst ++ [.add .r6 .r6 .r10] ++ scr .r7 sWork

/-- One more block: the counter to its slot, and in `r9` the blocks left. -/
def incr (count : List Instr) : List Instr :=
  [fp, .load .d .r11 .r12 oI, .addi .r11 .r11 1, .store .d .r11 .r12 oI] ++ count ++ [.sub .r9 .r9 .r11]

/-- Block `i` (in its slot) of IRPRF with the label `label`, the bit length's
code `len`, to `scratch + dst + 32 i`, and the code `count` putting the
number of blocks in `r9`. -/
def prfBody (label : List Nat) (len : List Instr) (dst : Nat) (count : List Instr) : Prog isa :=
  .seq (.block (fp :: scr .r9 sMsg ++ [.load .d .r11 .r12 oI, .load .d .r8 .r12 oK]))
  (.seq (.block (msgBytes label len))
  (.seq (.block (macInitArgs sKDK)) (.seq macInitCall
  (.seq (.block (prfUpdArgs (label.length + 4))) (.seq updCall
  (.seq (.block (prfFinArgs (label.length + 4) dst)) (.seq macFinCall
    (.block (incr count)))))))))

/-- "length" and "message", in ASCII. -/
def lengthLabel : List Nat := [0x6c, 0x65, 0x6e, 0x67, 0x74, 0x68]
def messageLabel : List Nat := [0x6d, 0x65, 0x73, 0x73, 0x61, 0x67, 0x65]

/-- The counter zero, and the number of `AM`'s blocks `⌈k / 32⌉` to its slot. -/
def clInit : List Instr :=
  [fp, .li .r10 0, .store .d .r10 .r12 oI, .load .d .r10 .r12 oK, .addi .r10 .r10 31, .lsr .d .r10 .r10 5,
    .store .d .r10 .r12 oNB]

def clLoop : Prog isa :=
  .seq (.block clInit) (.loop (prfBody lengthLabel clLen sCL [.li .r9 8]) (.nonzero .d .r9))

def amLoop : Prog isa :=
  .seq (.block [fp, .li .r10 0, .store .d .r10 .r12 oI])
    (.loop (prfBody messageLabel amLen sAM [.load .d .r9 .r12 oNB]) (.nonzero .d .r9))

/-! ## 4. The alternative length -/

/-- `k - 11` into `r9`, and the mask `r8` from 0. -/
def maskInit : List Instr := [fp, .load .d .r9 .r12 oK, .subi .r9 .r9 11, .li .r8 0]

/-- `r8 := 2 r8 + 1` while `r8 < r9`: `r10` is the borrow of `r8 - r9`. -/
def maskLoop : Prog isa :=
  .loop (.block [.add .r8 .r8 .r8, .addi .r8 .r8 1, .sub .r10 .r8 .r9, .lsr .d .r10 .r10 63])
    (.nonzero .d .r10)

def maskPart : Prog isa := .seq (.block maskInit) maskLoop

/-- `CL` in `r11`, the candidates left `r7` (128) and `AL` (`r6`) zero. -/
def alInit : List Instr := fp :: scr .r11 sCL ++ [.li .r7 128, .li .r6 0]

/-- One candidate: `c = (256 CL[2i] + CL[2i + 1]) & r8`, and `r6 := c` if
`c ≤ k - 11` (`r9`), by the mask `(borrow of r9 - c) - 1`. -/
def alBody : List Instr :=
  [.lbz .r10 .r11 0, .lsl .r10 .r10 8, .lbz .r5 .r11 1, .add .r10 .r10 .r5, .logic .and .r10 .r10 .r8,
    .sub .r5 .r9 .r10, .lsr .d .r5 .r5 63, .subi .r5 .r5 1, .logic .xor .r4 .r6 .r10,
    .logic .and .r4 .r4 .r5, .logic .xor .r6 .r6 .r4, .addi .r11 .r11 2, .subi .r7 .r7 1]

def alLoop : Prog isa := .loop (.block alBody) (.nonzero .d .r7)

def alPart : Prog isa := .seq (.block alInit) alLoop

/-! ## 5. The padding and the output -/

/-- `EM` (`out`) from byte 2 in `r11`, the bytes left `r7` (`k - 2`), the
index `r4` from 2, whether a zero was found (`r5`) and where (`r3`), zero in
`r0` and all ones in `r8`. -/
def scanInit : List Instr :=
  [fp, .load .d .r11 .r12 oOut, .addi .r11 .r11 2, .load .d .r7 .r12 oK, .subi .r7 .r7 2, .li .r4 2,
    .li .r5 0, .li .r3 0, .li .r0 0, .li .r8 0, .subi .r8 .r8 1]

/-- Byte `i` (`r4`): `z = -(EM[i] = 0)`, `r3 |= i & z & ~r5`, `r5 |= z`. -/
def scanBody : List Instr :=
  [.lbz .r10 .r11 0, .subi .r10 .r10 1, .lsr .d .r10 .r10 63, .sub .r10 .r0 .r10, .logic .xor .r9 .r5 .r8,
    .logic .and .r9 .r9 .r10, .logic .and .r9 .r9 .r4, .logic .or .r3 .r3 .r9, .logic .or .r5 .r5 .r10,
    .addi .r4 .r4 1, .addi .r11 .r11 1, .subi .r7 .r7 1]

def scanLoop : Prog isa := .loop (.block scanBody) (.nonzero .d .r7)

def scanPart : Prog isa := .seq (.block scanInit) scanLoop

/-- The validity mask `v` (`r5`), the selected length `len` (`r6`), the
mask of `r = 1` (`r4`), and `k - len` (`r3`):
`v = -(EM[0] = 0) & -(EM[1] = 2) & found & ~-(sep < 10)`,
`len = AL ^ ((AL ^ L) & v)` for `L = k - sep - 1`. With `out` in `r11` and
`k` in `r7`. -/
def validBlock : List Instr :=
  [fp, .load .d .r11 .r12 oOut, .load .d .r7 .r12 oK,
    -- `-(EM[0] = 0)` into `r10`
    .lbz .r10 .r11 0, .subi .r10 .r10 1, .lsr .d .r10 .r10 63, .sub .r10 .r0 .r10,
    -- `-(EM[1] = 2)` into `r9`, and both into `r5`
    .lbz .r9 .r11 1, .li .r4 2, .logic .xor .r9 .r9 .r4, .subi .r9 .r9 1, .lsr .d .r9 .r9 63,
    .sub .r9 .r0 .r9, .logic .and .r10 .r10 .r9, .logic .and .r5 .r5 .r10,
    -- `-(sep < 10)` into `r9`, cleared from `r5`
    .li .r4 10, .sub .r9 .r3 .r4, .lsr .d .r9 .r9 63, .sub .r9 .r0 .r9, .logic .xor .r9 .r9 .r8,
    .logic .and .r5 .r5 .r9,
    -- `L = k - sep - 1` into `r9`, and `len` into `r6`
    .sub .r9 .r7 .r3, .subi .r9 .r9 1, .logic .xor .r9 .r9 .r6, .logic .and .r9 .r9 .r5,
    .logic .xor .r6 .r6 .r9,
    -- the mask of `r = 1` into `r4`
    .load .d .r4 .r12 oR, .li .r9 1, .logic .xor .r4 .r4 .r9, .subi .r4 .r4 1, .lsr .d .r4 .r4 63,
    .sub .r4 .r0 .r4,
    -- `k - len` into `r3`, and `len` masked
    .sub .r3 .r7 .r6, .logic .and .r6 .r6 .r4]

/-- `*msg_len := len & ok`; then `AM` in `r10`, the index `r9` zero. -/
def outInit : List Instr :=
  [.load .d .r10 .r12 oML, .store .d .r6 .r10 0] ++ scr .r10 sAM ++ [.li .r9 0]

/-- Byte `i` (`r9`) of `out`: `(EM[i] & v | AM[i] & ~v) & ~-(i < k - len) & ok`. -/
def selBody : List Instr :=
  [.lbz .r6 .r11 0, .lbz .r12 .r10 0, .logic .xor .r6 .r6 .r12, .logic .and .r6 .r6 .r5,
    .logic .xor .r6 .r6 .r12, .sub .r12 .r9 .r3, .lsr .d .r12 .r12 63, .sub .r12 .r0 .r12,
    .logic .xor .r12 .r12 .r8, .logic .and .r12 .r12 .r4, .logic .and .r6 .r6 .r12, .stb .r6 .r11 0,
    .addi .r9 .r9 1, .addi .r11 .r11 1, .addi .r10 .r10 1, .subi .r7 .r7 1]

def selLoop : Prog isa := .loop (.block selBody) (.nonzero .d .r7)

/-- The result and our return address. -/
def finish : List Instr := [fp, .load .d .r3 .r12 oR, .load .d .r0 .r12 oLr, .mtlr .r0]

def selPart : Prog isa :=
  .seq (.block validBlock) (.seq (.block outInit) (.seq selLoop (.block finish)))

/-! ## The function -/

def body : Prog isa :=
  .seq (.block setup) (.seq privCall (.seq dBuild (.seq hashD (.seq kdkMac (.seq clLoop
    (.seq amLoop (.seq maskPart (.seq alPart (.seq scanPart selPart)))))))))

/-- `vg_rsa_pkcs1_decrypt`. -/
def code : Prog isa := .frame (.alloc frameBytes) body (.free frameBytes)

end VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
