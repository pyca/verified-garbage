module

public import VerifiedGarbage.Impl.Pbkdf2.Md.AArch64

/-!
# RSAES-PKCS1-v1_5 decryption with implicit rejection on AArch64

`vg_rsa_pkcs1_decrypt(out = x0, out_len = x1, msg_len = x2, n = x3,
n_len = x4, e = x5, e_len = x6, d = x7, d_len, input, input_len, p, p_len,
q, q_len, dp, dp_len, dq, dq_len, qinv, qinv_len, scratch, scratch_len)`,
the last fifteen on the stack, as on x86-64
(`Impl/RsaPkcs1Enc/X86_64/Decrypt.lean`). With `vg_rsa_private_checked`
(`priv`, by its name `privN`) and SHA-256's streaming functions and HMAC's
(`H`), it runs draft-irtf-cfrg-rsa-guidance-10 §7.2:

1. The private-key operation, `EM` (or zeros) to `out` and its result `r`
   (1, or 0 or 2 for its errors) into a slot (`setup`, the call).
2. `D = I2OSP(d, k)` in `scratch`: zeros, then `d` at its end (`dBuild`);
   `DH = SHA256(D)` (`hashD`); `KDK = HMAC(DH, C)` (`kdkMac`).
3. The candidate lengths `CL = IRPRF(KDK, "length", 256)` (`clLoop`) and the
   alternative message `AM = IRPRF(KDK, "message", k)` (`amLoop`), a block of
   32 bytes per HMAC, the block's counter in a slot.
4. The mask of the candidates, `2^bitLength(k - 11) - 1`, by doublings
   (`maskPart`), and the alternative length `AL`, the last candidate not
   above `k - 11` (`alPart`), selected with `csel`.
5. The scan of `EM` for its first zero from index 2 (`scanPart`), the
   validity mask `v` and the lengths (`validBlock`), and the output
   (`selLoop`): byte `i` of `out` is `EM[i]` or `AM[i]` as `v` selects, if
   `i ≥ k - len` for the selected length `len`, and zero otherwise, and
   everything (`out`, and `len` to `*msg_len`) is masked by `r = 1`. The
   function returns `r`.

Every address and branch depends only on the pointers, the lengths and the
counters: the validity of the padding, `L`, `AL` and the selection are masks
and values in registers, computed with the borrow of a subtraction
(`subs`, then `sbc` of a register from itself) and `csel`. `out`'s and
`AM`'s bytes are all read, whichever is returned.

The function runs in two frames: one saving our return address `x30`, and
in it one of `frameBytes` bytes holding, from `sp`, the stack arguments of
the private-key operation, then the slots from `oOut`. Our own stack
arguments are above both frames, from `sp + frameBytes + 16`. Only
caller-saved registers are used, so the slots hold everything kept across a
call. In `scratch`, from `sSt`: the streaming state (also HMAC's inner
state), HMAC's outer state, the working space, the message of an IRPRF
block, `DH`, `KDK`, `CL`, `AM` and `D`.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.AArch64.Decrypt

open VG VG.AArch64

/-- The size of the inner frame. -/
def frameBytes : Nat := 208

/-! The slots. -/
def oOut : Nat := 96
def oML : Nat := 104
def oN : Nat := 112
def oK : Nat := 120
def oE : Nat := 128
def oEl : Nat := 136
def oD : Nat := 144
def oDl : Nat := 152
def oIn : Nat := 160
def oScr : Nat := 168
def oR : Nat := 176
def oI : Nat := 184
def oNB : Nat := 192

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

/-- Our stack argument `j` (from 0), from `sp` in the frames. -/
def arg (j : Nat) : Nat := frameBytes + 16 + 8 * j

/-- `d ← n` (`orr d, n, n`). -/
def mov (d n : Reg) : Instr := .logic .orr .x d n n

/-- `d ← scratch + a`. -/
def scr (d : Reg) (a : Nat) : List Instr := [.ldrSp d oScr, .addImm .x d d a]

/-! ## 1. The private-key operation -/

/-- The registers' arguments to the slots, `x9 = sp`. -/
def saves : List Instr :=
  [.addSp .x9 0, .str .x .x0 .x9 oOut, .str .x .x2 .x9 oML, .str .x .x3 .x9 oN, .str .x .x4 .x9 oK,
    .str .x .x5 .x9 oE, .str .x .x6 .x9 oEl, .str .x .x7 .x9 oD]

/-- The stack arguments kept in the frame: `d_len`, the input and `scratch`
to their slots, and ours from `p` on to the frame's first 12 words, the
private-key operation's stack arguments. -/
def argMoves : List (Nat × Nat) :=
  [(0, oDl), (1, oIn), (13, oScr)] ++ (List.range 12).map fun j => (j + 3, 8 * j)

/-- Stack argument `j` to the frame's word at `d`. -/
def mvArg (j d : Nat) : List Instr := [.ldrSp .x10 (arg j), .str .x .x10 .x9 d]

/-- Its registers: `out`, `n_len`, `n`, `n_len`, `e`, `e_len`, the input,
`n_len`. -/
def privRegs : List Instr :=
  [mov .x1 .x4, mov .x2 .x3, mov .x3 .x4, mov .x4 .x5, mov .x5 .x6, .ldrSp .x6 (arg 1), mov .x7 .x1]

def setup : List Instr := saves ++ (argMoves.flatMap (fun p => mvArg p.1 p.2) ++ privRegs)

/-! ## 2. The key derivation key -/

/-- `r` (the low 32 bits of `x0`, which are all the call defines) to its
slot; the zeros of `D`: its base in `x11`, `k` in `x12` and a zero in
`x13`. -/
def dPtrs₁ : List Instr :=
  [.logic .orr .w .x0 .x0 .x0, .addSp .x9 0, .str .x .x0 .x9 oR] ++ scr .x11 sD ++ [.ldrSp .x12 oK, .movz .x .x13 0 0]

def zeroLoop : Prog isa :=
  .loop (.block [.strb .x13 .x11 0, .addImm .x .x11 .x11 1, .subImm .x .x12 .x12 1]) (.nonzero .x .x12)

/-- `d` at the end of `D`: `d` in `x14`, its length in `x12`, its place
(`scratch + sD + k - d_len`) in `x11`. -/
def dPtrs₂ : List Instr :=
  [.ldrSp .x14 oD, .ldrSp .x12 oDl] ++ scr .x11 sD ++ [.ldrSp .x15 oK, .add .x .x11 .x11 .x15,
    .sub .x .x11 .x11 .x12]

def copyLoop : Prog isa :=
  .loop (.block [.ldrb .x10 .x14 0, .strb .x10 .x11 0, .addImm .x .x14 .x14 1, .addImm .x .x11 .x11 1,
    .subImm .x .x12 .x12 1]) (.nonzero .x .x12)

def dBuild : Prog isa := .seq (.block dPtrs₁) (.seq zeroLoop (.seq (.block dPtrs₂) copyLoop))

variable (H : Impl.Pbkdf2.Md.AArch64.Hash)

/-- `init(state)`. -/
def shaInitArgs : List Instr := scr .x0 sSt
/-- `update(state, 0, D, k, work)`. -/
def shaUpdArgs : List Instr :=
  scr .x0 sSt ++ [.movz .x .x1 0 0] ++ scr .x2 sD ++ [.ldrSp .x3 oK] ++ scr .x4 sWork
/-- `finalize(state, k, DH, work)`. -/
def shaFinArgs : List Instr := scr .x0 sSt ++ [.ldrSp .x1 oK] ++ scr .x2 sDH ++ scr .x3 sWork

def hashD : Prog isa :=
  .seq (.block shaInitArgs) (.seq (.call H.initN H.initC) (.seq (.block shaUpdArgs) (.seq (.call H.updN H.updC)
    (.seq (.block shaFinArgs) (.call H.finN H.finC)))))

/-- HMAC's `init(inner, outer, key, 32, work)` for the key at `scratch + key`. -/
def macInitArgs (key : Nat) : List Instr :=
  scr .x0 sSt ++ scr .x1 sOuter ++ scr .x2 key ++ [.movz .x .x3 32 0] ++ scr .x4 sWork

/-- `update(inner, 64, C, k, work)`. -/
def kdkUpdArgs : List Instr :=
  scr .x0 sSt ++ [.movz .x .x1 64 0, .ldrSp .x2 oIn, .ldrSp .x3 oK] ++ scr .x4 sWork

/-- HMAC's `finalize(inner, outer, 64 + k, KDK, work)`. -/
def kdkFinArgs : List Instr :=
  scr .x0 sSt ++ scr .x1 sOuter ++ [.ldrSp .x2 oK, .addImm .x .x2 .x2 64] ++ scr .x3 sKDK ++ scr .x4 sWork

def kdkMac : Prog isa :=
  .seq (.block (macInitArgs sDH)) (.seq (.call H.hmacInitN H.hmacInit) (.seq (.block kdkUpdArgs)
    (.seq (.call H.updN H.updC) (.seq (.block kdkFinArgs) (.call H.hmacFinN H.hmacFin)))))

/-! ## 3. IRPRF -/

/-- Byte `d` of the block's message (at `x9`): the immediate `v`. -/
def putByte (d v : Nat) : List Instr := [.movz .x .x10 (BitVec.ofNat 16 v) 0, .strb .x10 .x9 d]

/-- The message `I2OSP(i, 2) ‖ label ‖ bitLength` at `scratch + sMsg` (in
`x9`), with `i < 256` in `x11`: the label's bytes, and the code `len`
writing the bit length's two bytes after them. -/
def msgBytes (label : List Nat) (len : List Instr) : List Instr :=
  putByte 0 0 ++ [.strb .x11 .x9 1] ++ (label.zipIdx.flatMap fun (v, j) => putByte (2 + j) v) ++ len

/-- The bit length 2048 of `CL`, after the 6 bytes of "length". -/
def clLen : List Instr := putByte 8 0x08 ++ putByte 9 0x00

/-- The bit length `8 k` of `AM`, after the 7 bytes of "message", from `k`
in `x12`. -/
def amLen : List Instr :=
  [.lsl .x .x10 .x12 3, .strb .x10 .x9 10, .lsr .x .x10 .x10 8, .strb .x10 .x9 9]

/-- `update(inner, 64, msg, len, work)`. -/
def prfUpdArgs (len : Nat) : List Instr :=
  scr .x0 sSt ++ [.movz .x .x1 64 0] ++ scr .x2 sMsg ++ [.movz .x .x3 (BitVec.ofNat 16 len) 0] ++ scr .x4 sWork

/-- HMAC's `finalize(inner, outer, 64 + len, scratch + dst + 32 i, work)`. -/
def prfFinArgs (len dst : Nat) : List Instr :=
  scr .x0 sSt ++ scr .x1 sOuter ++ [.movz .x .x2 (BitVec.ofNat 16 (64 + len)) 0, .ldrSp .x3 oI,
    .lsl .x .x3 .x3 5] ++ scr .x10 dst ++ [.add .x .x3 .x3 .x10] ++ scr .x4 sWork

/-- One more block: the counter to its slot, and in `x12` the blocks left. -/
def incr (count : List Instr) : List Instr :=
  [.ldrSp .x11 oI, .addImm .x .x11 .x11 1, .addSp .x9 0, .str .x .x11 .x9 oI] ++ count ++
    [.sub .x .x12 .x12 .x11]

/-- Block `i` (in its slot) of IRPRF with the label `label`, the bit length's
code `len`, to `scratch + dst + 32 i`, and the code `count` putting the
number of blocks in `x12`. -/
def prfBody (label : List Nat) (len : List Instr) (dst : Nat) (count : List Instr) : Prog isa :=
  .seq (.block (scr .x9 sMsg ++ [.ldrSp .x11 oI, .ldrSp .x12 oK]))
  (.seq (.block (msgBytes label len))
  (.seq (.block (macInitArgs sKDK)) (.seq (.call H.hmacInitN H.hmacInit)
  (.seq (.block (prfUpdArgs (label.length + 4))) (.seq (.call H.updN H.updC)
  (.seq (.block (prfFinArgs (label.length + 4) dst)) (.seq (.call H.hmacFinN H.hmacFin)
    (.block (incr count)))))))))

/-- "length" and "message", in ASCII. -/
def lengthLabel : List Nat := [0x6c, 0x65, 0x6e, 0x67, 0x74, 0x68]
def messageLabel : List Nat := [0x6d, 0x65, 0x73, 0x73, 0x61, 0x67, 0x65]

/-- The counter zero, and the number of `AM`'s blocks `⌈k / 32⌉` to its slot. -/
def clInit : List Instr :=
  [.addSp .x9 0, .movz .x .x10 0 0, .str .x .x10 .x9 oI, .ldrSp .x10 oK, .addImm .x .x10 .x10 31,
    .lsr .x .x10 .x10 5, .str .x .x10 .x9 oNB]

def clLoop : Prog isa :=
  .seq (.block clInit) (.loop (prfBody H lengthLabel clLen sCL [.movz .x .x12 8 0]) (.nonzero .x .x12))

def amLoop : Prog isa :=
  .seq (.block [.addSp .x9 0, .movz .x .x10 0 0, .str .x .x10 .x9 oI])
    (.loop (prfBody H messageLabel amLen sAM [.ldrSp .x12 oNB]) (.nonzero .x .x12))

/-! ## 4. The alternative length -/

/-- `k - 11` into `x9`, and the mask `x8` from 0. -/
def maskInit : List Instr := [.ldrSp .x9 oK, .subImm .x .x9 .x9 11, .movz .x .x8 0 0]

/-- `x8 := 2 x8 + 1` while `x8 < x9`: `x10` is the borrow of `x8 - x9`. -/
def maskLoop : Prog isa :=
  .loop (.block [.add .x .x8 .x8 .x8, .addImm .x .x8 .x8 1, .subs .x .x10 .x8 .x9, .sbc .x .x10 .x10 .x10])
    (.nonzero .x .x10)

def maskPart : Prog isa := .seq (.block maskInit) maskLoop

/-- `CL` in `x11`, the candidates left `x12` (128) and `AL` (`x13`) zero. -/
def alInit : List Instr := scr .x11 sCL ++ [.movz .x .x12 128 0, .movz .x .x13 0 0]

/-- One candidate: `c = (256 CL[2i] + CL[2i + 1]) & x8`, and `x13 := c` if
`c ≤ k - 11` (`x9`), by `csel` on the carry of `x9 - c`. -/
def alBody : List Instr :=
  [.ldrb .x10 .x11 0, .lsl .x .x10 .x10 8, .ldrb .x14 .x11 1, .add .x .x10 .x10 .x14,
    .logic .and .x .x10 .x10 .x8, .subs .x .x14 .x9 .x10, .csel .x .x13 .x10 .x13,
    .addImm .x .x11 .x11 2, .subImm .x .x12 .x12 1]

def alLoop : Prog isa := .loop (.block alBody) (.nonzero .x .x12)

def alPart : Prog isa := .seq (.block alInit) alLoop

/-! ## 5. The padding and the output -/

/-- `EM` (`out`) from byte 2 in `x11`, the bytes left `x12` (`k - 2`), the
index `x14` from 2, whether a zero was found (`x15`) and where (`x16`), and
the constant 1 in `x17`. -/
def scanInit : List Instr :=
  [.ldrSp .x11 oOut, .addImm .x .x11 .x11 2, .ldrSp .x12 oK, .subImm .x .x12 .x12 2, .movz .x .x14 2 0,
    .movz .x .x15 0 0, .movz .x .x16 0 0, .movz .x .x17 1 0]

/-- Byte `i` (`x14`): `z = -(EM[i] = 0)`, `x16 |= i & z & ~x15`, `x15 |= z`. -/
def scanBody : List Instr :=
  [.ldrb .x10 .x11 0, .subs .x .x10 .x10 .x17, .sbc .x .x10 .x10 .x10, .bicRor .x .x9 .x10 .x15 0,
    .logic .and .x .x9 .x9 .x14, .logic .orr .x .x16 .x16 .x9, .logic .orr .x .x15 .x15 .x10,
    .addImm .x .x14 .x14 1, .addImm .x .x11 .x11 1, .subImm .x .x12 .x12 1]

def scanLoop : Prog isa := .loop (.block scanBody) (.nonzero .x .x12)

def scanPart : Prog isa := .seq (.block scanInit) scanLoop

/-- The validity mask `v` (`x15`), the selected length `len` (`x13`), the
mask of `r = 1` (`x14`), and `k - len` (`x16`):
`v = -(EM[0] = 0) & -(EM[1] = 2) & found & -(sep ≥ 10)`,
`len = AL ^ ((AL ^ L) & v)` for `L = k - sep - 1`. With `out` in `x11` and
`k` in `x12`. -/
def validBlock : List Instr :=
  [.ldrSp .x11 oOut, .ldrSp .x12 oK,
    -- `-(EM[0] = 0)` into `x10`
    .ldrb .x10 .x11 0, .subs .x .x10 .x10 .x17, .sbc .x .x10 .x10 .x10,
    -- `-(EM[1] = 2)` into `x9`, and both into `x15`
    .ldrb .x9 .x11 1, .movz .x .x14 2 0, .logic .eor .x .x9 .x9 .x14, .subs .x .x9 .x9 .x17,
    .sbc .x .x9 .x9 .x9, .logic .and .x .x10 .x10 .x9, .logic .and .x .x15 .x15 .x10,
    -- `-(sep < 10)` into `x9`, cleared from `x15`
    .movz .x .x14 10 0, .subs .x .x9 .x16 .x14, .sbc .x .x9 .x9 .x9, .bicRor .x .x15 .x15 .x9 0,
    -- `L = k - sep - 1` into `x9`, and `len` into `x13`
    .sub .x .x9 .x12 .x16, .subImm .x .x9 .x9 1, .logic .eor .x .x9 .x9 .x13, .logic .and .x .x9 .x9 .x15,
    .logic .eor .x .x13 .x13 .x9,
    -- the mask of `r = 1` into `x14`
    .ldrSp .x14 oR, .logic .eor .x .x14 .x14 .x17, .subs .x .x14 .x14 .x17, .sbc .x .x14 .x14 .x14,
    -- `k - len` into `x16`, and `len` masked
    .sub .x .x16 .x12 .x13, .logic .and .x .x13 .x13 .x14]

/-- `*msg_len := len & ok`; then `AM` in `x10`, the index `x9` zero. -/
def outInit : List Instr :=
  [.ldrSp .x10 oML, .str .x .x13 .x10 0] ++ scr .x10 sAM ++ [.movz .x .x9 0 0]

/-- Byte `i` (`x9`) of `out`: `(EM[i] & v | AM[i] & ~v) & -(i ≥ k - len) & ok`. -/
def selBody : List Instr :=
  [.ldrb .x13 .x11 0, .ldrb .x8 .x10 0, .logic .eor .x .x13 .x13 .x8, .logic .and .x .x13 .x13 .x15,
    .logic .eor .x .x13 .x13 .x8, .subs .x .x8 .x9 .x16, .sbc .x .x8 .x8 .x8, .bicRor .x .x8 .x14 .x8 0,
    .logic .and .x .x13 .x13 .x8, .strb .x13 .x11 0, .addImm .x .x9 .x9 1, .addImm .x .x11 .x11 1,
    .addImm .x .x10 .x10 1, .subImm .x .x12 .x12 1]

def selLoop : Prog isa := .loop (.block selBody) (.nonzero .x .x12)

def selPart : Prog isa :=
  .seq (.block validBlock) (.seq (.block outInit) (.seq selLoop (.block [.ldrSp .x0 oR])))

/-! ## The function -/

/-- The inner frame's body, with the private-key operation `priv` (by its
name `privN`). -/
def body (privN : String) (priv : Prog isa) : Prog isa :=
  .seq (.block setup) (.seq (.call privN priv) (.seq dBuild (.seq (hashD H) (.seq (kdkMac H) (.seq (clLoop H)
    (.seq (amLoop H) (.seq maskPart (.seq alPart (.seq scanPart selPart)))))))))

/-- `vg_rsa_pkcs1_decrypt`. -/
def code (privN : String) (priv : Prog isa) : Prog isa :=
  .frame (.push .x30) (.frame (.alloc frameBytes) (body H privN priv) (.free frameBytes)) (.pop .x30)

end VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
