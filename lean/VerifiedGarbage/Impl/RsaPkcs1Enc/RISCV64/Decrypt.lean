module

public import VerifiedGarbage.Impl.Rsa.RISCV64.Priv
public import VerifiedGarbage.Impl.Hmac.Stream.RISCV64
public import VerifiedGarbage.Impl.Sha256.RISCV64.Stream
public import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.Encode
public import VerifiedGarbage.Spec.Sha256.Contract
public import VerifiedGarbage.Spec.Hmac.Generic

/-!
# RSAES-PKCS1-v1_5 decryption with implicit rejection on RISC-V

`vg_rsa_pkcs1_decrypt(out = a0, out_len = a1, msg_len = a2, n = a3,
n_len = a4, e = a5, e_len = a6, d = a7, d_len, input, input_len, p, p_len,
q, q_len, dp, dp_len, dq, dq_len, qinv, qinv_len, scratch, scratch_len)`,
the last fifteen on the stack. As on PPC64LE
(`Impl/RsaPkcs1Enc/PPC64LE/Decrypt.lean`), with `vg_rsa_private_checked` and
SHA-256's and HMAC-SHA-256's streaming functions, it runs
draft-irtf-cfrg-rsa-guidance-10 §7.2:

1. The private-key operation, `EM` (or zeros) to `out` and its result `r`
   (1, or 0 or 2 for its errors) into `s7` (`setup`, the call).
2. `D = I2OSP(d, k)` in `scratch`: zeros, then `d` at its end (`dBuild`);
   `DH = SHA256(D)` (`hashD`); `KDK = HMAC(DH, C)` (`kdkMac`).
3. The candidate lengths `CL = IRPRF(KDK, "length", 256)` (`clLoop`) and the
   alternative message `AM = IRPRF(KDK, "message", k)` (`amLoop`), a block of
   32 bytes per HMAC, the block's counter in `s8`.
4. The mask of the candidates, `2^bitLength(k - 11) - 1`, by doublings
   (`maskPart`), and the alternative length `AL`, the last candidate not
   above `k - 11` (`alPart`), selected with a mask.
5. The scan of `EM` for its first zero from index 2 (`scanPart`), the
   validity mask `v` and the lengths (`validBlock`), and the output
   (`selLoop`): byte `i` of `out` is `EM[i]` or `AM[i]` as `v` selects, if
   `i ≥ k - len` for the selected length `len`, and zero otherwise, and
   everything (`out`, and `len` to `*msg_len`) is masked by `r = 1`. The
   function returns `r`.

Every comparison is of numbers below `2^63`, by the top bit of their
difference, and every selection is by a mask, `0 - bit`. Every address and
branch depends only on the pointers, the lengths and the counters. `out`'s
and `AM`'s bytes are all read, whichever is returned.

The frame (`alloc frameBytes`) holds the private-key operation's twelve
stack arguments (at `sp`), then our caller's `s0`–`s9` and our return
address (`saved`). Our own stack arguments are at `sp + frameBytes + 8 j`,
from `t6` (`argBase`). The values kept across the calls are in `s0`–`s9`,
which every function called saves and restores: `s0` = `scratch`, `s1` =
`k`, `s2` = `out`, `s3` = `msg_len`, `s4` = `d`, `s5` = `d_len`, `s6` = the
input, `s7` = `r`, `s8` = the IRPRF counter and `s9` = the number of `AM`'s
blocks. In `scratch`, from `sSt`: the streaming state (also HMAC's inner
state), HMAC's outer state, the message of an IRPRF block, `DH`, `KDK`,
`CL`, `AM` and `D`.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt

open VG VG.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open VG.Impl.RsaPkcs1Sig.RISCV64 (copyLoop fillLoop)

/-- The size of the frame. -/
def frameBytes : Nat := 192

/-- Where our caller's `s0`–`s9` and our return address are saved. -/
def saved : List (Reg × Nat) :=
  [(.s0, 96), (.s1, 104), (.s2, 112), (.s3, 120), (.s4, 128), (.s5, 136), (.s6, 144), (.s7, 152), (.s8, 160),
    (.s9, 168), (.ra, 176)]

/-- `t6 :=` the address of our first stack argument, `sp + frameBytes`. -/
def argBase : Instr := .addSp .t6 frameBytes

/-! Where things are in `scratch`. -/
def sSt : Nat := 0
def sOuter : Nat := 96
def sMsg : Nat := 192
def sDH : Nat := 208
def sKDK : Nat := 240
def sCL : Nat := 272
def sAM : Nat := 528
def sD : Nat := 1552

/-- SHA-256's streaming functions, as HMAC calls them. -/
def sha256 : Hash where
  b := 6
  N := 32
  D := 32
  F := 144
  initN := Spec.Sha256.initApi.name
  initC := Impl.Sha256.RISCV64.Stream.init
  updN := Spec.Sha256.updateApi.name
  updC := Impl.Sha256.RISCV64.Stream.update
  finN := Spec.Sha256.finalizeApi.name
  finC := Impl.Sha256.RISCV64.Stream.finalize

def privCall : Prog isa := .call "vg_rsa_private_checked" Impl.Rsa.RISCV64.Priv.code
def macInitCall : Prog isa := .call Spec.Hmac.sha256I.initAnyKeyApi.name sha256.init
def macFinCall : Prog isa := .call Spec.Hmac.sha256I.finalizeApi.name sha256.finalize

/-! ## 1. The private-key operation -/

/-- `t0 := sp`; our caller's `s0`–`s9` and our return address into the
frame. -/
def save : List Instr := .addSp .t0 0 :: saved.map fun p => .store .d p.1 .t0 p.2

/-- Our caller's `s0`–`s9` and our return address back from the frame. -/
def restore : List Instr := .addSp .t0 0 :: saved.map fun p => .load .d p.1 .t0 p.2

/-- The values kept across the calls into `s0`–`s6`. -/
def keeps : List Instr :=
  [argBase, mov .s1 .a4, mov .s2 .a0, mov .s3 .a2, mov .s4 .a7, .load .d .s5 .t6 0, .load .d .s6 .t6 8,
    .load .d .s0 .t6 104]

/-- Our stack argument `3 + j` (`p` … `scratch_len`) to the private-key
operation's stack argument `j`. -/
def copyArg (j : Nat) : List Instr := [.load .d .t1 .t6 (8 * (3 + j)), .store .d .t1 .t0 (8 * j)]

/-- Its registers: `out`, `k`, `n`, `k`, `e`, `e_len`, the input, `k`. -/
def privRegs : List Instr :=
  [mov .a1 .s1, mov .a2 .a3, mov .a3 .s1, mov .a4 .a5, mov .a5 .a6, mov .a6 .s6, mov .a7 .s1]

def setup : List Instr := save ++ keeps ++ (List.range 12).flatMap copyArg ++ privRegs

/-! ## 2. The key derivation key -/

/-- `r` (the low 32 bits of `a0`, which are all the call defines) into
`s7`; the zeros of `D`: `k` bytes from `scratch + sD`. -/
def dZeros : List Instr :=
  [.shift .sll .d .s7 .a0 32, .shift .srl .d .s7 .s7 32, .addi .a1 .s0 sD, mov .t5 .s1, .li .t0 0]

/-- `d` at the end of `D`: from `d`, `d_len` bytes to `scratch + sD + k - d_len`. -/
def dCopy : List Instr := [mov .a4 .s4, mov .a5 .s5, .addi .a1 .s0 sD, .add .a1 .a1 .s1, .sub .a1 .a1 .s5]

def dBuild : Prog isa := .seq (.block dZeros) (.seq fillLoop (.seq (.block dCopy) copyLoop))

/-- `init(state)`. -/
def shaInitArgs : List Instr := [.addi .a0 .s0 sSt]
/-- `update(state, 0, D, k)`. -/
def shaUpdArgs : List Instr := [.addi .a0 .s0 sSt, .li .a1 0, .addi .a2 .s0 sD, mov .a3 .s1]
/-- `finalize(state, k, DH)`. -/
def shaFinArgs : List Instr := [.addi .a0 .s0 sSt, mov .a1 .s1, .addi .a2 .s0 sDH]

def hashD : Prog isa :=
  .seq (.block shaInitArgs) (.seq sha256.callInit (.seq (.block shaUpdArgs) (.seq sha256.callUpd
    (.seq (.block shaFinArgs) sha256.callFin))))

/-- HMAC's `init(inner, outer, key, 32)` for the key at `scratch + key`. -/
def macInitArgs (key : Nat) : List Instr :=
  [.addi .a0 .s0 sSt, .addi .a1 .s0 sOuter, .addi .a2 .s0 key, .li .a3 32]

/-- `update(inner, 64, C, k)`. -/
def kdkUpdArgs : List Instr := [.addi .a0 .s0 sSt, .li .a1 64, mov .a2 .s6, mov .a3 .s1]

/-- HMAC's `finalize(inner, outer, 64 + k, KDK)`. -/
def kdkFinArgs : List Instr := [.addi .a0 .s0 sSt, .addi .a1 .s0 sOuter, .addi .a2 .s1 64, .addi .a3 .s0 sKDK]

def kdkMac : Prog isa :=
  .seq (.block (macInitArgs sDH)) (.seq macInitCall (.seq (.block kdkUpdArgs)
    (.seq sha256.callUpd (.seq (.block kdkFinArgs) macFinCall))))

/-! ## 3. IRPRF -/

/-- Byte `d` of the block's message (at `t1`): the immediate `v`. -/
def putByte (d v : Nat) : List Instr := [.li .t2 v, .store .b .t2 .t1 d]

/-- The message `I2OSP(i, 2) ‖ label ‖ bitLength` at `scratch + sMsg` (in
`t1`), with `i < 256` in `s8`: the label's bytes, and the code `len`
writing the bit length's two bytes after them. -/
def msgBytes (label : List Nat) (len : List Instr) : List Instr :=
  [.addi .t1 .s0 sMsg] ++ putByte 0 0 ++ [.store .b .s8 .t1 1] ++
    (label.zipIdx.flatMap fun (v, j) => putByte (2 + j) v) ++ len

/-- The bit length 2048 of `CL`, after the 6 bytes of "length". -/
def clLen : List Instr := putByte 8 0x08 ++ putByte 9 0x00

/-- The bit length `8 k` of `AM`, after the 7 bytes of "message". -/
def amLen : List Instr :=
  [.shift .sll .d .t2 .s1 3, .store .b .t2 .t1 10, .shift .srl .d .t2 .t2 8, .store .b .t2 .t1 9]

/-- `update(inner, 64, msg, len)`. -/
def prfUpdArgs (len : Nat) : List Instr := [.addi .a0 .s0 sSt, .li .a1 64, .addi .a2 .s0 sMsg, .li .a3 len]

/-- HMAC's `finalize(inner, outer, 64 + len, scratch + dst + 32 i)`. -/
def prfFinArgs (len dst : Nat) : List Instr :=
  [.addi .a0 .s0 sSt, .addi .a1 .s0 sOuter, .li .a2 (64 + len), .shift .sll .d .a3 .s8 5, .add .a3 .a3 .s0,
    .addi .a3 .a3 dst]

/-- One more block: the counter, and in `t1` the blocks left, from the code
`count` putting the number of blocks in `t1`. -/
def incr (count : List Instr) : List Instr := [.addi .s8 .s8 1] ++ count ++ [.sub .t1 .t1 .s8]

/-- Block `i` (in `s8`) of IRPRF with the label `label`, the bit length's
code `len`, to `scratch + dst + 32 i`. -/
def prfBody (label : List Nat) (len : List Instr) (dst : Nat) (count : List Instr) : Prog isa :=
  .seq (.block (msgBytes label len))
  (.seq (.block (macInitArgs sKDK)) (.seq macInitCall
  (.seq (.block (prfUpdArgs (label.length + 4))) (.seq sha256.callUpd
  (.seq (.block (prfFinArgs (label.length + 4) dst)) (.seq macFinCall
    (.block (incr count))))))))

/-- "length" and "message", in ASCII. -/
def lengthLabel : List Nat := [0x6c, 0x65, 0x6e, 0x67, 0x74, 0x68]
def messageLabel : List Nat := [0x6d, 0x65, 0x73, 0x73, 0x61, 0x67, 0x65]

/-- The counter zero, and the number of `AM`'s blocks `⌈k / 32⌉` into `s9`. -/
def clInit : List Instr := [.li .s8 0, .addi .s9 .s1 31, .shift .srl .d .s9 .s9 5]

def clLoop : Prog isa :=
  .seq (.block clInit) (.loop (prfBody lengthLabel clLen sCL [.li .t1 8]) (.nonzero .t1))

def amLoop : Prog isa :=
  .seq (.block [.li .s8 0]) (.loop (prfBody messageLabel amLen sAM [mov .t1 .s9]) (.nonzero .t1))

/-! ## 4. The alternative length -/

/-- `k - 11` into `t3`, and the mask `t4` from 0. -/
def maskInit : List Instr := [.addi .t3 .s1 (-11), .li .t4 0]

/-- `t4 := 2 t4 + 1` while `t4 < t3`: `t5` is the borrow of `t4 - t3`. -/
def maskLoop : Prog isa :=
  .loop (.block [.add .t4 .t4 .t4, .addi .t4 .t4 1, .sub .t5 .t4 .t3, .shift .srl .d .t5 .t5 63])
    (.nonzero .t5)

def maskPart : Prog isa := .seq (.block maskInit) maskLoop

/-- `CL` in `t1`, the candidates left `t2` (128) and `AL` (`t6`) zero. -/
def alInit : List Instr := [.addi .t1 .s0 sCL, .li .t2 128, .li .t6 0]

/-- One candidate: `c = (256 CL[2i] + CL[2i + 1]) & t4`, and `t6 := c` if
`c ≤ k - 11` (`t3`), by the mask `(borrow of t3 - c) - 1`. -/
def alBody : List Instr :=
  [.load .b .a0 .t1 0, .shift .sll .d .a0 .a0 8, .load .b .a1 .t1 1, .add .a0 .a0 .a1, .logic .and .a0 .a0 .t4,
    .sub .a1 .t3 .a0, .shift .srl .d .a1 .a1 63, .addi .a1 .a1 (-1), .logic .xor .a2 .t6 .a0,
    .logic .and .a2 .a2 .a1, .logic .xor .t6 .t6 .a2, .addi .t1 .t1 2, .addi .t2 .t2 (-1)]

def alLoop : Prog isa := .loop (.block alBody) (.nonzero .t2)

def alPart : Prog isa := .seq (.block alInit) alLoop

/-! ## 5. The padding and the output -/

/-- `EM` (`out`) from byte 2 in `t1`, the bytes left `t2` (`k - 2`), the
index `a3` from 2, whether a zero was found (`a4`) and where (`a5`), zero in
`a6` and all ones in `a7`. -/
def scanInit : List Instr :=
  [.addi .t1 .s2 2, .addi .t2 .s1 (-2), .li .a3 2, .li .a4 0, .li .a5 0, .li .a6 0, .li .a7 0,
    .addi .a7 .a7 (-1)]

/-- Byte `i` (`a3`): `z = -(EM[i] = 0)`, `a5 |= i & z & ~a4`, `a4 |= z`. -/
def scanBody : List Instr :=
  [.load .b .a0 .t1 0, .addi .a0 .a0 (-1), .shift .srl .d .a0 .a0 63, .sub .a0 .a6 .a0, .logic .xor .a1 .a4 .a7,
    .logic .and .a1 .a1 .a0, .logic .and .a1 .a1 .a3, .logic .or .a5 .a5 .a1, .logic .or .a4 .a4 .a0,
    .addi .a3 .a3 1, .addi .t1 .t1 1, .addi .t2 .t2 (-1)]

def scanLoop : Prog isa := .loop (.block scanBody) (.nonzero .t2)

def scanPart : Prog isa := .seq (.block scanInit) scanLoop

/-- The validity mask `v` (`a4`), the selected length `len` (`t6`), the
mask of `r = 1` (`a3`), and `k - len` (`a5`):
`v = -(EM[0] = 0) & -(EM[1] = 2) & found & ~-(sep < 10)`,
`len = AL ^ ((AL ^ L) & v)` for `L = k - sep - 1`. With `out` in `t1` and
`k` in `t2`. -/
def validBlock : List Instr :=
  [mov .t1 .s2, mov .t2 .s1,
    -- `-(EM[0] = 0)` into `a0`
    .load .b .a0 .t1 0, .addi .a0 .a0 (-1), .shift .srl .d .a0 .a0 63, .sub .a0 .a6 .a0,
    -- `-(EM[1] = 2)` into `a1`, and both into `a4`
    .load .b .a1 .t1 1, .li .a3 2, .logic .xor .a1 .a1 .a3, .addi .a1 .a1 (-1), .shift .srl .d .a1 .a1 63,
    .sub .a1 .a6 .a1, .logic .and .a0 .a0 .a1, .logic .and .a4 .a4 .a0,
    -- `-(sep < 10)` into `a1`, cleared from `a4`
    .li .a3 10, .sub .a1 .a5 .a3, .shift .srl .d .a1 .a1 63, .sub .a1 .a6 .a1, .logic .xor .a1 .a1 .a7,
    .logic .and .a4 .a4 .a1,
    -- `L = k - sep - 1` into `a1`, and `len` into `t6`
    .sub .a1 .t2 .a5, .addi .a1 .a1 (-1), .logic .xor .a1 .a1 .t6, .logic .and .a1 .a1 .a4,
    .logic .xor .t6 .t6 .a1,
    -- the mask of `r = 1` into `a3`
    mov .a3 .s7, .li .a1 1, .logic .xor .a3 .a3 .a1, .addi .a3 .a3 (-1), .shift .srl .d .a3 .a3 63,
    .sub .a3 .a6 .a3,
    -- `k - len` into `a5`, and `len` masked
    .sub .a5 .t2 .t6, .logic .and .t6 .t6 .a3]

/-- `*msg_len := len & ok`; then `AM` in `a0`, the index `a1` zero. -/
def outInit : List Instr := [.store .d .t6 .s3 0, .addi .a0 .s0 sAM, .li .a1 0]

/-- Byte `i` (`a1`) of `out`: `(EM[i] & v | AM[i] & ~v) & ~-(i < k - len) & ok`. -/
def selBody : List Instr :=
  [.load .b .t6 .t1 0, .load .b .a2 .a0 0, .logic .xor .t6 .t6 .a2, .logic .and .t6 .t6 .a4,
    .logic .xor .t6 .t6 .a2, .sub .a2 .a1 .a5, .shift .srl .d .a2 .a2 63, .sub .a2 .a6 .a2,
    .logic .xor .a2 .a2 .a7, .logic .and .a2 .a2 .a3, .logic .and .t6 .t6 .a2, .store .b .t6 .t1 0,
    .addi .a1 .a1 1, .addi .t1 .t1 1, .addi .a0 .a0 1, .addi .t2 .t2 (-1)]

def selLoop : Prog isa := .loop (.block selBody) (.nonzero .t2)

/-- The result, and our caller's registers. -/
def finish : List Instr := mov .a0 .s7 :: restore

def selPart : Prog isa :=
  .seq (.block validBlock) (.seq (.block outInit) (.seq selLoop (.block finish)))

/-! ## The function -/

def body : Prog isa :=
  .seq (.block setup) (.seq privCall (.seq dBuild (.seq hashD (.seq kdkMac (.seq clLoop
    (.seq amLoop (.seq maskPart (.seq alPart (.seq scanPart selPart)))))))))

/-- `vg_rsa_pkcs1_decrypt`. -/
def code : Prog isa := .frame (.alloc frameBytes) body (.free frameBytes)

end VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt
