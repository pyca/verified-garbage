module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Wrap
public import VerifiedGarbage.Impl.Bignum.Arm.MaskBytes

/-!
# RSAES-PKCS1-v1_5 decryption with implicit rejection on ARMv7

`vg_rsa_pkcs1_decrypt(out = r0, out_len = r1, msg_len = r2, n = r3, n_len,
e, e_len, d, d_len, input, input_len, p, p_len, q, q_len, dp, dp_len, dq,
dq_len, qinv, qinv_len, scratch, scratch_len)`, the last nineteen on the
stack. As on AArch64 (`Impl/RsaPkcs1Enc/AArch64/Decrypt.lean`), with
`vg_rsa_private_checked` (`priv`, by its name `privN`) and SHA-256's and
HMAC-SHA-256's functions (`H`), it runs draft-irtf-cfrg-rsa-guidance-10 §7.2:

1. The private-key operation, `EM` (or zeros) to `out` and its result `r`
   (1, or 0 or 2 for its errors) into a slot (`privArgs`, the call).
2. `D = I2OSP(d, k)` in `scratch`: zeros (`Bignum.Arm.maskBytes` with a zero
   mask), then `d` at its end (`Bignum.Arm.copyBytes`); `DH = SHA256(D)`;
   `KDK = HMAC(DH, C)`.
3. The candidate lengths `CL = IRPRF(KDK, "length", 256)` and the
   alternative message `AM = IRPRF(KDK, "message", k)`, a block of 32 bytes
   per HMAC (`prfBody`), the block's counter and the number of blocks in
   slots.
4. The mask of the candidates, `2^bitLength(k - 11) - 1`, by doublings
   (`maskLoop`, on public values), and the alternative length `AL`, the last
   candidate not above `k - 11` (`alLoop`), selected with masks.
5. The scan of `EM` for its first zero from index 2 (`scanLoop`), the
   validity `v` and the lengths (`validBlock`), `*msg_len`, and the output
   (`selLoop`): byte `i` of `out` is `EM[i]` or `AM[i]` as `v` selects, if
   `i ≥ k - len` for the selected length `len`, and zero otherwise, and
   everything (`out`, and `len` to `*msg_len`) is masked by `r = 1`. The
   function returns `r`.

ARMv7 has no conditional select or subtraction with borrow: every mask is
built from the top bit of a difference of two numbers below `2^31`
(`(x - y) >> 31` is 1 exactly when `x < y`). Every address and branch
depends only on the pointers, the lengths and the counters; `out`'s and
`AM`'s bytes are all read, whichever is returned.

The frame (`Impl/RsaPkcs1Sig/Arm/Wrap.lean`) holds, from its base, the
calls' stack arguments, then the slots. In `scratch`: SHA-256's and HMAC's
inner state (`sSt`), HMAC's outer state (`sOuter`), the message of an IRPRF
block (`sMsg`), `DH`, `KDK`, `CL`, `AM` and `D`. The SHA-256 and HMAC
functions called keep their working space in their own frames.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.Arm.Decrypt

open VG VG.Arm
open VG.Impl.RsaPkcs1Sig.Arm (wrap argOff)

/-- The size of the inner frame. -/
def frameBytes : Nat := 88

/-! The slots. -/
def oR : Nat := 64
def oI : Nat := 68
def oNB : Nat := 72
def oAL : Nat := 76
def oMK : Nat := 80

/-! Where things are in `scratch`. -/
def sSt : Nat := 0
def sOuter : Nat := 96
def sMsg : Nat := 192
def sDH : Nat := 208
def sKDK : Nat := 240
def sCL : Nat := 272
def sAM : Nat := 528
def sD : Nat := 1552

/-- Argument `j` (from 0). -/
def arg (j : Nat) : Nat := argOff frameBytes j

/-- `d ← n + v`. -/
def addI (d n : Reg) (v : Nat) : Instr := .dp .add d n (.imm (BitVec.ofNat 32 v))

/-- `d ← #v`. -/
def movI (d : Reg) (v : Nat) : Instr := .mov d (.imm (BitVec.ofNat 32 v))

/-- Argument `j` to the call's stack argument `i`. -/
def copyArg (j i : Nat) : List Instr := [.ldrSp .r0 (arg j), .str .r0 .r12 (4 * i)]

/-! ## 1. The private-key operation -/

/-- Its stack arguments (`e`, `e_len`, the input, `n_len`, then `p` …
`scratch_len`), then its registers: `out`, `n_len`, `n`, `n_len`. -/
def privArgs : List Instr :=
  [.addSp .r12 0] ++ copyArg 5 0 ++ copyArg 6 1 ++ copyArg 9 2 ++ copyArg 4 3 ++ copyArg 11 4 ++
    copyArg 12 5 ++ copyArg 13 6 ++ copyArg 14 7 ++ copyArg 15 8 ++ copyArg 16 9 ++ copyArg 17 10 ++
    copyArg 18 11 ++ copyArg 19 12 ++ copyArg 20 13 ++ copyArg 21 14 ++ copyArg 22 15 ++
    ([.ldrSp .r0 (arg 0), .ldrSp .r1 (arg 4), .ldrSp .r2 (arg 3), .ldrSp .r3 (arg 4)] : List Instr)

/-! ## 2. The key derivation key -/

/-- `r` to its slot; `D`'s place, its length and the zero mask for
`maskBytes`. -/
def dZero : List Instr :=
  [.addSp .r12 0, .str .r0 .r12 oR, .ldrSp .r0 (arg 21), addI .r0 .r0 sD, .ldrSp .lr (arg 4), movI .r2 0]

/-- `d`'s place at the end of `D`, `d` and its length for `copyBytes`. -/
def dCopy : List Instr :=
  [.addSp .r12 0, .ldrSp .r0 (arg 21), addI .r0 .r0 sD, .ldrSp .r2 (arg 4), .dp .add .r0 .r0 (.reg .r2),
    .ldrSp .lr (arg 8), .dp .sub .r0 .r0 (.reg .lr), .ldrSp .r1 (arg 7)]

/-- `init(state)`. -/
def shaInitArgs : List Instr := [.addSp .r12 0, .ldrSp .r0 (arg 21)]

/-- `update(state, 0, D, k)`. -/
def shaUpdArgs : List Instr :=
  [.addSp .r12 0, .ldrSp .r0 (arg 21), addI .r1 .r0 sD, .str .r1 .r12 0, .ldrSp .r1 (arg 4), .str .r1 .r12 4,
    movI .r2 0, movI .r3 0]

/-- `finalize(state, k, DH)`. -/
def shaFinArgs : List Instr :=
  [.addSp .r12 0, .ldrSp .r0 (arg 21), addI .r1 .r0 sDH, .str .r1 .r12 0, .ldrSp .r2 (arg 4), movI .r3 0]

/-- HMAC's `init(inner, outer, scratch + key, 32)`. -/
def macInitArgs (key : Nat) : List Instr :=
  [.addSp .r12 0, .ldrSp .r0 (arg 21), addI .r1 .r0 sOuter, addI .r2 .r0 key, movI .r3 32]

/-- `update(inner, 64, C, k)`. -/
def kdkUpdArgs : List Instr :=
  [.addSp .r12 0, .ldrSp .r0 (arg 21), .ldrSp .r1 (arg 9), .str .r1 .r12 0, .ldrSp .r1 (arg 4), .str .r1 .r12 4,
    movI .r2 64, movI .r3 0]

/-- HMAC's `finalize(inner, outer, 64 + k, KDK)`. -/
def kdkFinArgs : List Instr :=
  [.addSp .r12 0, .ldrSp .r0 (arg 21), addI .r1 .r0 sKDK, .str .r1 .r12 0, addI .r1 .r0 sOuter,
    .ldrSp .r2 (arg 4), addI .r2 .r2 64, movI .r3 0]

/-- The call of the SHA-256 or HMAC function `f` (by its name) after the
block of its arguments. -/
def callAfter (args : List Instr) (n : String) (c : Prog isa) : Prog isa := .seq (.block args) (.call n c)

/-- The functions this one calls, by their names. -/
structure Fns where
  initN : String
  initC : Prog isa
  updN : String
  updC : Prog isa
  finN : String
  finC : Prog isa
  hiN : String
  hiC : Prog isa
  hfN : String
  hfC : Prog isa

variable (H : Fns)

def hashD : Prog isa :=
  .seq (callAfter shaInitArgs H.initN H.initC) (.seq (callAfter shaUpdArgs H.updN H.updC)
    (callAfter shaFinArgs H.finN H.finC))

def kdkMac : Prog isa :=
  .seq (callAfter (macInitArgs sDH) H.hiN H.hiC) (.seq (callAfter kdkUpdArgs H.updN H.updC)
    (callAfter kdkFinArgs H.hfN H.hfC))

/-! ## 3. IRPRF -/

/-- Byte `d` of the block's message (at `r0`): the immediate `v`. -/
def putByte (d v : Nat) : List Instr := [movI .r2 v, .strb .r2 .r0 d]

/-- The bytes `vs` from byte `d` of the message on. -/
def putLabel : List Nat → Nat → List Instr
  | [], _ => []
  | v :: vs, d => putByte d v ++ putLabel vs (d + 1)

/-- The message `I2OSP(i, 2) ‖ label ‖ bitLength` at `scratch + sMsg` (in
`r0`), with `i < 256` in `r1`: the label's bytes, and the code `len`
writing the bit length's two bytes after them, all in order. -/
def msgBytes (label : List Nat) (len : List Instr) : List Instr :=
  putByte 0 0 ++ .strb .r1 .r0 1 :: (putLabel label 2 ++ len)

/-- The bit length 2048 of `CL`, after the 6 bytes of "length". -/
def clLen : List Instr := putByte 8 0x08 ++ putByte 9 0x00

/-- The bit length `8 k` of `AM`, after the 7 bytes of "message", from `k`
in `r3`: its high byte, then its low byte. -/
def amLen : List Instr :=
  [.mov .r2 (.shifted .r3 .lsl 3), .mov .r2 (.shifted .r2 .lsr 8), .strb .r2 .r0 9, .mov .r2 (.shifted .r3 .lsl 3),
    .strb .r2 .r0 10]

/-- The message's place in `r0`, the counter `i` in `r1` and `k` in `r3`. -/
def msgPtr : List Instr := [.addSp .r12 0, .ldrSp .r0 (arg 21), addI .r0 .r0 sMsg, .ldrSp .r1 oI, .ldrSp .r3 (arg 4)]

/-- `update(inner, 64, msg, len)`. -/
def prfUpdArgs (len : Nat) : List Instr :=
  [.addSp .r12 0, .ldrSp .r0 (arg 21), addI .r1 .r0 sMsg, .str .r1 .r12 0, movI .r1 len, .str .r1 .r12 4,
    movI .r2 64, movI .r3 0]

/-- HMAC's `finalize(inner, outer, 64 + len, scratch + dst + 32 i)`. -/
def prfFinArgs (len dst : Nat) : List Instr :=
  [.addSp .r12 0, .ldrSp .r0 (arg 21), .ldrSp .r2 oI, addI .r1 .r0 dst, .dp .add .r1 .r1 (.shifted .r2 .lsl 5),
    .str .r1 .r12 0, addI .r1 .r0 sOuter, movI .r2 (64 + len), movI .r3 0]

/-- One more block: the counter to its slot, and the number of blocks in `r2`. -/
def incr : List Instr := [.addSp .r12 0, .ldrSp .r1 oI, addI .r1 .r1 1, .str .r1 .r12 oI, .ldrSp .r2 oNB]

/-- Block `i` (in its slot) of IRPRF with the label `label`, the bit length's
code `len`, to `scratch + dst + 32 i`; then whether there is another. -/
def prfBody (label : List Nat) (len : List Instr) (dst : Nat) : Prog isa :=
  .seq (.block msgPtr) (.seq (.block (msgBytes label len))
  (.seq (callAfter (macInitArgs sKDK) H.hiN H.hiC) (.seq (callAfter (prfUpdArgs (label.length + 4)) H.updN H.updC)
  (.seq (callAfter (prfFinArgs (label.length + 4) dst) H.hfN H.hfC)
    (.seq (.block incr) (.block [.cmp .r1 (.reg .r2)]))))))

/-- "length" and "message", in ASCII. -/
def lengthLabel : List Nat := [0x6c, 0x65, 0x6e, 0x67, 0x74, 0x68]
def messageLabel : List Nat := [0x6d, 0x65, 0x73, 0x73, 0x61, 0x67, 0x65]

/-- The counter zero, and the number of blocks 8 to its slot. -/
def clInit : List Instr := [.addSp .r12 0, movI .r0 0, .str .r0 .r12 oI, movI .r0 8, .str .r0 .r12 oNB]

def clLoop : Prog isa := .seq (.block clInit) (.loop (prfBody H lengthLabel clLen sCL) .ne)

/-- The counter zero, and the number of `AM`'s blocks `⌈k / 32⌉` to its slot. -/
def amInit : List Instr :=
  [.addSp .r12 0, movI .r0 0, .str .r0 .r12 oI, .ldrSp .r0 (arg 4), addI .r0 .r0 31, .mov .r0 (.shifted .r0 .lsr 5),
    .str .r0 .r12 oNB]

def amLoop : Prog isa := .seq (.block amInit) (.loop (prfBody H messageLabel amLen sAM) .ne)

/-! ## 4. The alternative length -/

/-- `k - 11` into `r1`, and the mask `r0` from 0. -/
def maskInit : List Instr := [.addSp .r12 0, .ldrSp .r1 (arg 4), .dp .sub .r1 .r1 (.imm 11), movI .r0 0]

/-- `r0 := 2 r0 + 1` while `r0 < r1`: the top bit of `r0 - r1`. -/
def maskBody : List Instr :=
  [.dp .add .r0 .r0 (.reg .r0), addI .r0 .r0 1, .dp .sub .r2 .r0 (.reg .r1), .mov .r2 (.shifted .r2 .lsr 31),
    .cmp .r2 (.imm 0)]

def maskLoop : Prog isa := .loop (.block maskBody) .ne

/-- The mask to its slot; `CL` in `r0`, the mask in `r4`, `k - 11` in `r5`,
`AL` (`r6`) zero and the candidates left (`lr`) 128. -/
def alInit : List Instr :=
  [.addSp .r12 0, .str .r0 .r12 oMK, .ldrSp .r0 (arg 21), addI .r0 .r0 sCL, .ldrSp .r4 oMK, .ldrSp .r5 (arg 4),
    .dp .sub .r5 .r5 (.imm 11), movI .r6 0, movI .lr 128]

/-- One candidate: `c = (256 CL[2i] + CL[2i + 1]) & mask`, and
`AL := AL ^ ((AL ^ c) & keep)` with `keep = ((k - 11 - c) >> 31) - 1`, all
ones exactly when `c ≤ k - 11`. -/
def alBody : List Instr :=
  [.ldrb .r2 .r0 0, .ldrb .r3 .r0 1, .dp .add .r2 .r3 (.shifted .r2 .lsl 8), .dp .and .r2 .r2 (.reg .r4),
    .dp .sub .r3 .r5 (.reg .r2), .mov .r3 (.shifted .r3 .lsr 31), .dp .sub .r3 .r3 (.imm 1),
    .dp .eor .r7 .r6 (.reg .r2), .dp .and .r7 .r7 (.reg .r3), .dp .eor .r6 .r6 (.reg .r7), addI .r0 .r0 2,
    .subs .lr .lr (.imm 1)]

def alLoop : Prog isa := .loop (.block alBody) .ne

/-- `AL` to its slot. -/
def alSave : List Instr := [.addSp .r12 0, .str .r6 .r12 oAL]

def alPart : Prog isa :=
  .seq (.block maskInit) (.seq maskLoop (.seq (.block alInit) (.seq alLoop (.block alSave))))

/-! ## 5. The padding and the output -/

/-- `EM` (`out`) from byte 2 in `r0`, the bytes left `lr` (`k - 2`), the
index `r1` from 2, whether a zero was found (`r4`) and where (`r5`), and the
constant 0 in `r6`. -/
def scanInit : List Instr :=
  [.addSp .r12 0, .ldrSp .r0 (arg 0), addI .r0 .r0 2, .ldrSp .lr (arg 4), .dp .sub .lr .lr (.imm 2), movI .r1 2,
    movI .r4 0, movI .r5 0, movI .r6 0]

/-- Byte `i` (`r1`): `z = (EM[i] - 1) >> 31` (1 exactly when it is 0),
`r5 |= i & -(z & ~found)`, `found |= z`. -/
def scanBody : List Instr :=
  [.ldrb .r2 .r0 0, .dp .sub .r2 .r2 (.imm 1), .mov .r2 (.shifted .r2 .lsr 31), .dp .eor .r3 .r4 (.imm 1),
    .dp .and .r3 .r3 (.reg .r2), .dp .sub .r3 .r6 (.reg .r3), .dp .and .r3 .r3 (.reg .r1),
    .dp .orr .r5 .r5 (.reg .r3), .dp .orr .r4 .r4 (.reg .r2), addI .r1 .r1 1, addI .r0 .r0 1,
    .subs .lr .lr (.imm 1)]

def scanLoop : Prog isa := .loop (.block scanBody) .ne

/-- `out` in `r0`, `k` in `r7`, `AL` in `r8` and `r` in `r9`. -/
def validLoads : List Instr := [.addSp .r12 0, .ldrSp .r0 (arg 0), .ldrSp .r7 (arg 4), .ldrSp .r8 oAL, .ldrSp .r9 oR]

/-- The validity `v` (`r2`):
`v = (EM[0] = 0) & (EM[1] = 2) & found & (sep ≥ 10)`, each a bit; the
selected length `len = AL ^ ((AL ^ L) & -v)` for `L = k - sep - 1`; the
mask of `r = 1` (`r11`), and `k - len` (`r9`) and `len` masked (`r3`).
`r10` keeps `-v` and `r6` zero. -/
def validBlock : List Instr :=
  [.ldrb .r2 .r0 0, .dp .sub .r2 .r2 (.imm 1), .mov .r2 (.shifted .r2 .lsr 31),
    .ldrb .r3 .r0 1, .dp .eor .r3 .r3 (.imm 2), .dp .sub .r3 .r3 (.imm 1), .mov .r3 (.shifted .r3 .lsr 31),
    .dp .and .r2 .r2 (.reg .r3), .dp .and .r2 .r2 (.reg .r4),
    .dp .sub .r3 .r5 (.imm 10), .mov .r3 (.shifted .r3 .lsr 31), .dp .eor .r3 .r3 (.imm 1),
    .dp .and .r2 .r2 (.reg .r3),
    .dp .sub .r3 .r7 (.reg .r5), .dp .sub .r3 .r3 (.imm 1), .dp .eor .r3 .r3 (.reg .r8), .dp .sub .r10 .r6 (.reg .r2),
    .dp .and .r3 .r3 (.reg .r10), .dp .eor .r3 .r3 (.reg .r8),
    .dp .eor .r11 .r9 (.imm 1), .dp .sub .r11 .r11 (.imm 1), .mov .r11 (.shifted .r11 .lsr 31),
    .dp .sub .r11 .r6 (.reg .r11),
    .dp .sub .r9 .r7 (.reg .r3), .dp .and .r3 .r3 (.reg .r11)]

/-- `msg_len` in `r1`. -/
def mlLoad : List Instr := [.addSp .r12 0, .ldrSp .r1 (arg 2)]

/-- `*msg_len := len & ok`, as two words. -/
def mlStore : List Instr := [.str .r3 .r1 0, .str .r6 .r1 4]

/-- `out` in `r0`, `AM` in `r1`, the index `r4` from 0, and the bytes left
`lr` (`k`). -/
def selInit : List Instr :=
  [.addSp .r12 0, .ldrSp .r0 (arg 0), .ldrSp .r1 (arg 21), addI .r1 .r1 sAM, movI .r4 0, .ldrSp .lr (arg 4)]

/-- Byte `i` (`r4`) of `out`:
`(AM[i] ^ ((AM[i] ^ EM[i]) & -v)) & (((i - (k - len)) >> 31) - 1) & ok`. -/
def selBody : List Instr :=
  [.ldrb .r2 .r0 0, .ldrb .r3 .r1 0, .dp .eor .r2 .r2 (.reg .r3), .dp .and .r2 .r2 (.reg .r10),
    .dp .eor .r2 .r2 (.reg .r3), .dp .sub .r5 .r4 (.reg .r9), .mov .r5 (.shifted .r5 .lsr 31),
    .dp .sub .r5 .r5 (.imm 1), .dp .and .r5 .r5 (.reg .r11), .dp .and .r2 .r2 (.reg .r5), .strb .r2 .r0 0,
    addI .r0 .r0 1, addI .r1 .r1 1, addI .r4 .r4 1, .subs .lr .lr (.imm 1)]

def selLoop : Prog isa := .loop (.block selBody) .ne

/-- `r` returned. -/
def fin : List Instr := [.addSp .r12 0, .ldrSp .r0 oR]

def selPart : Prog isa :=
  .seq (.block scanInit) (.seq scanLoop (.seq (.block validLoads) (.seq (.block validBlock)
    (.seq (.block mlLoad) (.seq (.block mlStore) (.seq (.block selInit) (.seq selLoop (.block fin))))))))

/-! ## The function -/

/-- The inner frame's body, with the private-key operation `priv` (by its
name `privN`). -/
def body (privN : String) (priv : Prog isa) : Prog isa :=
  .seq (.block privArgs) (.seq (.call privN priv) (.seq (.block dZero) (.seq Bignum.Arm.maskBytes
    (.seq (.block dCopy) (.seq Bignum.Arm.copyBytes (.seq (hashD H) (.seq (kdkMac H) (.seq (clLoop H)
    (.seq (amLoop H) (.seq alPart selPart))))))))))

/-- `vg_rsa_pkcs1_decrypt`. -/
def code (privN : String) (priv : Prog isa) : Prog isa := wrap frameBytes (body H privN priv)

end VG.Impl.RsaPkcs1Enc.Arm.Decrypt
