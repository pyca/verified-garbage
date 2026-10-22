module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Wrap
public import VerifiedGarbage.Impl.Bignum.X86.CopyBytes
public import VerifiedGarbage.Impl.Bignum.X86.PublicFn
public import VerifiedGarbage.Impl.Pbkdf2.Whole.X86

/-!
# RSAES-PKCS1-v1_5 decryption with implicit rejection on x86 (32-bit)

`vg_rsa_pkcs1_decrypt(out, out_len, msg_len, n, n_len, e, e_len, d, d_len,
input, input_len, p, p_len, q, q_len, dp, dp_len, dq, dq_len, qinv,
qinv_len, scratch, scratch_len)`, all on the stack. As on ARMv7
(`Impl/RsaPkcs1Enc/Arm/Decrypt.lean`), with `vg_rsa_private_checked`
(`priv`, by its name `privN`) and SHA-256's streaming functions and
HMAC-SHA-256's `init` and `finalize` made with one SHA-256 backend (`F`,
the functions PBKDF2 calls, `Impl/Pbkdf2/Whole/X86.lean`), it runs
draft-irtf-cfrg-rsa-guidance-10 §7.2:

1. The private-key operation, `EM` (or zeros) to `out` and its result `r`
   (1, or 0 or 2 for its errors) into a slot (`privArgs`, the call, with
   its twenty arguments at the frame's base).
2. `D = I2OSP(d, k)` in `scratch`: zeros (`zeroLoop`), then `d` at its end
   (`Bignum.X86.copyBytes`); `DH = SHA256(D)`; `KDK = HMAC(DH, C)`.
3. The candidate lengths `CL = IRPRF(KDK, "length", 256)` and the
   alternative message `AM = IRPRF(KDK, "message", k)`, a block of 32 bytes
   per HMAC (`prfBody`), the block's counter and the number of blocks in
   slots.
4. The mask of the candidates, `2^bitLength(k - 11) - 1`, by doublings
   (`maskLoop`, on public values), and the alternative length `AL`, the last
   candidate not above `k - 11` (`alLoop`), selected with masks.
5. The scan of `EM` for its first zero from index 2 (`scanLoop`), the
   validity mask `V` and the lengths (`validBlock`), `*msg_len`, and the
   output (`selLoop`): byte `i` of `out` is `EM[i]` or `AM[i]` as `V`
   selects, if `i ≥ k - len` for the selected length `len`, and zero
   otherwise, and everything (`out`, and `len` to `*msg_len`) is masked by
   `r = 1`. The function returns `r`.

Every mask is all ones or zero, from the carry of a subtraction (`sbb r, r`
after `sub` or `cmp`). Every address and branch depends only on the
pointers, the lengths and the counters; `out`'s and `AM`'s bytes are all
read, whichever is returned.

Each SHA-256 or HMAC function is called in a frame of its arguments, pushed
from registers (as PBKDF2's code calls them), with its working space at
`scratch + sW`. The frame (`Impl/RsaPkcs1Sig/X86/Wrap.lean`) holds the
private-key operation's arguments from its base, then the slots. In
`scratch`: SHA-256's and HMAC's inner state (`sSt`), HMAC's outer state
(`sOuter`), the message of an IRPRF block (`sMsg`), `DH`, `KDK`, `CL`,
`AM`, `D`, and the callees' working space (`sW`).
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.X86.Decrypt

open VG VG.X86
open VG.Impl.RsaPkcs1Sig.X86 (wrap argOff stk at_)
open VG.Impl.Pbkdf2.Whole.X86 (Fns)

/-- The size of the inner frame. -/
def frameBytes : Nat := 104

/-! The slots. -/
def oR : Nat := 80
def oI : Nat := 84
def oNB : Nat := 88
def oAL : Nat := 92
def oV : Nat := 96
def oOK : Nat := 100

/-! Where things are in `scratch`. -/
def sSt : Nat := 0
def sOuter : Nat := 96
def sMsg : Nat := 192
def sDH : Nat := 208
def sKDK : Nat := 240
def sCL : Nat := 272
def sAM : Nat := 528
def sD : Nat := 1552
def sW : Nat := 2576

/-- Argument `j` (from 0). -/
def arg (j : Nat) : Src := .mem (stk (argOff frameBytes j))

/-- `d ← v`. -/
def movI (d : Reg) (v : Nat) : Instr := .mov d (.imm (BitVec.ofNat 32 v))

/-- `d ← scratch + o`. -/
def scr (d : Reg) (o : Nat) : List Instr := [.mov d (arg 21), .alu .add d (.imm (BitVec.ofNat 32 o))]

/-- Argument `j` to the call's stack argument `i`. -/
def copyArg (j i : Nat) : List Instr := [.mov .eax (arg j), .store (stk (4 * i)) .eax]

/-! ## 1. The private-key operation -/

/-- The arguments of `vg_rsa_private_checked`, in its order: `out`, `n_len`,
`n`, `n_len`, `e`, `e_len`, the input, `n_len`, then `p` … `scratch_len`. -/
def privSrc : List Nat := [0, 4, 3, 4, 5, 6, 9, 4, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

def privArgs : List Instr := (privSrc.zipIdx).flatMap fun (j, i) => copyArg j i

/-- Its result to its slot. -/
def saveR : List Instr := [.store (stk oR) .eax]

/-! ## 2. The key derivation key -/

/-- `D`'s place, its length and zero for `zeroLoop`. -/
def dZero : List Instr := scr .esi sD ++ [.mov .ecx (arg 4), movI .eax 0]

/-- `k` zero bytes from `esi`. -/
def zeroLoop : Prog isa := .loop (.block Impl.Bignum.X86.PublicFn.clearStep) .ne

/-- `d` (`esi`), its place at the end of `D` (`ebx`) and its length (`ecx`)
for `copyBytes`. -/
def dCopy : List Instr :=
  scr .ebx sD ++ [.alu .add .ebx (arg 4), .alu .sub .ebx (arg 8), .mov .esi (arg 7), .mov .ecx (arg 8)]

/-- The registers `update`'s frame pushes: the state (`edi`), the count
(`esi`, and `eax` its high word), the data (`edx`) and its length (`ecx`),
the working space (`ebp`). -/
abbrev upd6 : List Reg := [.ebp, .ecx, .edx, .eax, .esi, .edi]

/-- The registers `finalize`'s frame pushes: the state (`edi`), the count
(`eax`, and `ecx` its high word), the digest's place (`edx`), the working
space (`ebp`). -/
abbrev fin5 : List Reg := [.ebp, .edx, .ecx, .eax, .edi]

/-- The registers HMAC's `init` frame pushes: the states (`edi`, `esi`), the
key (`edx`) and its length (`ecx`), the working space (`ebp`). -/
abbrev hi5 : List Reg := [.ebp, .ecx, .edx, .esi, .edi]

/-- The registers HMAC's `finalize` frame pushes: the states (`edx`,
`esi`), the count (`eax`, and `ecx` its high word), the MAC's place
(`edi`), the working space (`ebp`). -/
abbrev hf6 : List Reg := [.ebp, .edi, .ecx, .eax, .esi, .edx]

/-- `init(state)`. -/
def shaInitArgs : List Instr := scr .edi sSt

/-- `update(state, 0, D, k)`. -/
def shaUpdArgs : List Instr :=
  scr .edi sSt ++ [movI .esi 0, movI .eax 0] ++ scr .edx sD ++ [.mov .ecx (arg 4)] ++ scr .ebp sW

/-- `finalize(state, k, DH)`. -/
def shaFinArgs : List Instr :=
  scr .edi sSt ++ [.mov .eax (arg 4), movI .ecx 0] ++ scr .edx sDH ++ scr .ebp sW

/-- HMAC's `init(inner, outer, scratch + key, 32)`. -/
def macInitArgs (key : Nat) : List Instr :=
  scr .edi sSt ++ scr .esi sOuter ++ scr .edx key ++ [movI .ecx 32] ++ scr .ebp sW

/-- `update(inner, 64, C, k)`. -/
def kdkUpdArgs : List Instr :=
  scr .edi sSt ++ [movI .esi 64, movI .eax 0, .mov .edx (arg 9), .mov .ecx (arg 4)] ++ scr .ebp sW

/-- HMAC's `finalize(inner, outer, 64 + k, KDK)`. -/
def kdkFinArgs : List Instr :=
  scr .edx sSt ++ scr .esi sOuter ++ [.mov .eax (arg 4), .alu .add .eax (.imm 64), movI .ecx 0] ++
    scr .edi sKDK ++ scr .ebp sW

variable (F : Fns)

def callInit : Prog isa := .frame (.push [.edi]) (.call F.H.initN F.H.initC) (.pop .eax 1)
def callUpd : Prog isa := .frame (.push upd6) (.call F.H.updN F.H.updC) (.pop .eax 6)
def callFin : Prog isa := .frame (.push fin5) (.call F.H.finN F.H.finC) (.pop .eax 5)
def callHi : Prog isa := .frame (.push hi5) (.call F.hiN F.hiC) (.pop .eax 5)
def callHf : Prog isa := .frame (.push hf6) (.call F.hfN F.hfC) (.pop .eax 6)

def hashD : Prog isa :=
  .seq (.block shaInitArgs) (.seq (callInit F) (.seq (.block shaUpdArgs) (.seq (callUpd F)
    (.seq (.block shaFinArgs) (callFin F)))))

def kdkMac : Prog isa :=
  .seq (.block (macInitArgs sDH)) (.seq (callHi F) (.seq (.block kdkUpdArgs) (.seq (callUpd F)
    (.seq (.block kdkFinArgs) (callHf F)))))

/-! ## 3. IRPRF -/

/-- Byte `d` of the block's message (at `ebx`): the immediate `v`. -/
def putByte (d v : Nat) : List Instr := [movI .eax v, .store8 (at_ .ebx d) .al]

/-- The bytes `vs` from byte `d` of the message on. -/
def putLabel : List Nat → Nat → List Instr
  | [], _ => []
  | v :: vs, d => putByte d v ++ putLabel vs (d + 1)

/-- The message `I2OSP(i, 2) ‖ label ‖ bitLength` at `scratch + sMsg` (in
`ebx`), with `i < 256` in `ecx`: the label's bytes, and the code `len`
writing the bit length's two bytes after them, all in order. -/
def msgBytes (label : List Nat) (len : List Instr) : List Instr :=
  putByte 0 0 ++ .store8 (at_ .ebx 1) .cl :: (putLabel label 2 ++ len)

/-- The bit length 2048 of `CL`, after the 6 bytes of "length". -/
def clLen : List Instr := putByte 8 0x08 ++ putByte 9 0x00

/-- The bit length `8 k` of `AM`, after the 7 bytes of "message", from `k`
in `edx`: its high byte `k >> 5`, then its low byte. -/
def amLen : List Instr :=
  [.mov .eax (.reg .edx), .shift .shr .eax 5, .store8 (at_ .ebx 9) .al, .mov .eax (.reg .edx),
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
    .store8 (at_ .ebx 10) .al]

/-- The message's place in `ebx`, the counter `i` in `ecx` and `k` in `edx`. -/
def msgPtr : List Instr := scr .ebx sMsg ++ [.mov .ecx (.mem (stk oI)), .mov .edx (arg 4)]

/-- `update(inner, 64, msg, len)`. -/
def prfUpdArgs (len : Nat) : List Instr :=
  scr .edi sSt ++ [movI .esi 64, movI .eax 0] ++ scr .edx sMsg ++ [movI .ecx len] ++ scr .ebp sW

/-- HMAC's `finalize(inner, outer, 64 + len, scratch + dst + 32 i)`. -/
def prfFinArgs (len dst : Nat) : List Instr :=
  scr .edx sSt ++ scr .esi sOuter ++ [movI .eax (64 + len), movI .ecx 0, .mov .edi (.mem (stk oI)),
    .alu .add .edi (.reg .edi), .alu .add .edi (.reg .edi), .alu .add .edi (.reg .edi),
    .alu .add .edi (.reg .edi), .alu .add .edi (.reg .edi), .alu .add .edi (arg 21),
    .alu .add .edi (.imm (BitVec.ofNat 32 dst))] ++ scr .ebp sW

/-- One more block: the counter to its slot, compared with the number of
blocks. -/
def incr : List Instr :=
  [.mov .eax (.mem (stk oI)), .alu .add .eax (.imm 1), .store (stk oI) .eax, .alu .cmp .eax (.mem (stk oNB))]

/-- Block `i` (in its slot) of IRPRF with the label `label`, the bit length's
code `len`, to `scratch + dst + 32 i`; then whether there is another. -/
def prfBody (label : List Nat) (len : List Instr) (dst : Nat) : Prog isa :=
  .seq (.block (msgPtr ++ msgBytes label len)) (.seq (.block (macInitArgs sKDK)) (.seq (callHi F)
  (.seq (.block (prfUpdArgs (label.length + 4))) (.seq (callUpd F)
  (.seq (.block (prfFinArgs (label.length + 4) dst)) (.seq (callHf F) (.block incr)))))))

/-- "length" and "message", in ASCII. -/
def lengthLabel : List Nat := [0x6c, 0x65, 0x6e, 0x67, 0x74, 0x68]
def messageLabel : List Nat := [0x6d, 0x65, 0x73, 0x73, 0x61, 0x67, 0x65]

/-- The counter zero, and the number of blocks 8 to its slot. -/
def clInit : List Instr := [movI .eax 0, .store (stk oI) .eax, movI .eax 8, .store (stk oNB) .eax]

def clLoop : Prog isa := .seq (.block clInit) (.loop (prfBody F lengthLabel clLen sCL) .ne)

/-- The counter zero, and the number of `AM`'s blocks `⌈k / 32⌉` to its slot. -/
def amInit : List Instr :=
  [movI .eax 0, .store (stk oI) .eax, .mov .eax (arg 4), .alu .add .eax (.imm 31), .shift .shr .eax 5,
    .store (stk oNB) .eax]

def amLoop : Prog isa := .seq (.block amInit) (.loop (prfBody F messageLabel amLen sAM) .ne)

/-! ## 4. The alternative length -/

/-- `k - 11` into `ecx`, and the mask `eax` from 0. -/
def maskInit : List Instr := [.mov .ecx (arg 4), .alu .sub .ecx (.imm 11), movI .eax 0]

/-- `eax := 2 eax + 1` while `eax < ecx`. -/
def maskBody : List Instr := [.alu .add .eax (.reg .eax), .alu .add .eax (.imm 1), .alu .cmp .eax (.reg .ecx)]

def maskLoop : Prog isa := .loop (.block maskBody) .b

/-- `CL` in `esi`, the mask in `edi`, `k - 11` in `ebp`, `AL` (`ebx`) zero
and the candidates left (`ecx`) 128. -/
def alInit : List Instr :=
  scr .esi sCL ++ [.mov .edi (.reg .eax), .mov .ebp (.reg .ecx), movI .ebx 0, movI .ecx 128]

/-- One candidate: `c = (256 CL[2i] + CL[2i + 1]) & mask` (`eax`), the mask
`keep` (`edx`), all ones exactly when `c ≤ k - 11`, and
`AL := AL ^ ((AL ^ c) & keep)`. -/
def alBody : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .shift .ror .eax 24, .movzx8 .edx (at_ .esi 1), .alu .or .eax (.reg .edx),
    .alu .and .eax (.reg .edi), .mov .edx (.reg .ebp), .alu .sub .edx (.reg .eax), .alu .sbb .edx (.reg .edx),
    .alu .xor .edx (.imm (BitVec.allOnes 32)), .alu .xor .eax (.reg .ebx), .alu .and .eax (.reg .edx),
    .alu .xor .ebx (.reg .eax), .alu .add .esi (.imm 2), .alu .sub .ecx (.imm 1)]

def alLoop : Prog isa := .loop (.block alBody) .ne

/-- `AL` to its slot. -/
def alSave : List Instr := [.store (stk oAL) .ebx]

def alPart : Prog isa :=
  .seq (.block maskInit) (.seq maskLoop (.seq (.block alInit) (.seq alLoop (.block alSave))))

/-! ## 5. The padding and the output -/

/-- `EM` (`out`) from byte 2 in `esi`, the bytes left `ecx` (`k - 2`), the
index `edx` from 2, the mask of whether a zero was found (`ebx`) and where
(`edi`). -/
def scanInit : List Instr :=
  [.mov .esi (arg 0), .alu .add .esi (.imm 2), .mov .ecx (arg 4), .alu .sub .ecx (.imm 2), movI .edx 2,
    movI .ebx 0, movI .edi 0]

/-- Byte `i` (`edx`): the mask `z` (`eax`) of `EM[i] = 0`,
`sep |= i & z & ~found`, `found |= z`. -/
def scanBody : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .alu .sub .eax (.imm 1), .alu .sbb .eax (.reg .eax), .mov .ebp (.reg .ebx),
    .alu .xor .ebp (.imm (BitVec.allOnes 32)), .alu .and .ebp (.reg .eax), .alu .and .ebp (.reg .edx),
    .alu .or .edi (.reg .ebp), .alu .or .ebx (.reg .eax), .alu .add .edx (.imm 1), .alu .add .esi (.imm 1),
    .alu .sub .ecx (.imm 1)]

def scanLoop : Prog isa := .loop (.block scanBody) .ne

/-- The validity mask `V` (`eax`, to its slot) of
`EM[0] = 0 ∧ EM[1] = 2 ∧ found ∧ sep ≥ 10`; the selected length
`len = AL ^ ((AL ^ L) & V)` (`edx`) for `L = k - sep - 1`; the mask `OK`
of `r = 1` (to its slot); `k - len` (`ebx`), and `len` masked by `OK`
(`edx`). -/
def validBlock : List Instr :=
  [.mov .esi (arg 0), .movzx8 .eax (at_ .esi 0), .alu .sub .eax (.imm 1), .alu .sbb .eax (.reg .eax),
    .movzx8 .edx (at_ .esi 1), .alu .xor .edx (.imm 2), .alu .sub .edx (.imm 1), .alu .sbb .edx (.reg .edx),
    .alu .and .eax (.reg .edx), .alu .and .eax (.reg .ebx),
    .mov .edx (.reg .edi), .alu .sub .edx (.imm 10), .alu .sbb .edx (.reg .edx),
    .alu .xor .edx (.imm (BitVec.allOnes 32)), .alu .and .eax (.reg .edx), .store (stk oV) .eax,
    .mov .edx (arg 4), .alu .sub .edx (.reg .edi), .alu .sub .edx (.imm 1), .mov .ecx (.mem (stk oAL)),
    .alu .xor .edx (.reg .ecx), .alu .and .edx (.reg .eax), .alu .xor .edx (.reg .ecx),
    .mov .eax (.mem (stk oR)), .alu .xor .eax (.imm 1), .alu .sub .eax (.imm 1), .alu .sbb .eax (.reg .eax),
    .store (stk oOK) .eax, .mov .ebx (arg 4), .alu .sub .ebx (.reg .edx), .alu .and .edx (.reg .eax)]

/-- `*msg_len := len & OK`, as two words. -/
def mlStore : List Instr := [.mov .esi (arg 2), .store (at_ .esi 0) .edx, movI .eax 0, .store (at_ .esi 4) .eax]

/-- `out` in `esi`, `AM` in `edi`, the index `edx` from 0, and the bytes
left `ecx` (`k`). -/
def selInit : List Instr := [.mov .esi (arg 0)] ++ scr .edi sAM ++ [movI .edx 0, .mov .ecx (arg 4)]

/-- Byte `i` (`edx`) of `out`:
`(AM[i] ^ ((AM[i] ^ EM[i]) & V)) & ~(i < k - len ? ~0 : 0) & OK`. -/
def selBody : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .movzx8 .ebp (at_ .edi 0), .alu .xor .eax (.reg .ebp),
    .alu .and .eax (.mem (stk oV)), .alu .xor .eax (.reg .ebp), .mov .ebp (.reg .edx),
    .alu .sub .ebp (.reg .ebx), .alu .sbb .ebp (.reg .ebp), .alu .xor .ebp (.imm (BitVec.allOnes 32)),
    .alu .and .ebp (.mem (stk oOK)), .alu .and .eax (.reg .ebp), .store8 (at_ .esi 0) .al,
    .alu .add .esi (.imm 1), .alu .add .edi (.imm 1), .alu .add .edx (.imm 1), .alu .sub .ecx (.imm 1)]

def selLoop : Prog isa := .loop (.block selBody) .ne

/-- `r` returned. -/
def fin : List Instr := [.mov .eax (.mem (stk oR))]

def selPart : Prog isa :=
  .seq (.block scanInit) (.seq scanLoop (.seq (.block validBlock) (.seq (.block mlStore)
    (.seq (.block selInit) (.seq selLoop (.block fin))))))

/-! ## The function -/

/-- The inner frame's body, with the private-key operation `priv` (by its
name `privN`). -/
def body (privN : String) (priv : Prog isa) : Prog isa :=
  .seq (.block privArgs) (.seq (.call privN priv) (.seq (.block (saveR ++ dZero)) (.seq zeroLoop
    (.seq (.block dCopy) (.seq Impl.Bignum.X86.copyBytes (.seq (hashD F) (.seq (kdkMac F) (.seq (clLoop F)
    (.seq (amLoop F) (.seq alPart selPart))))))))))

/-- `vg_rsa_pkcs1_decrypt`. -/
def code (privN : String) (priv : Prog isa) : Prog isa := wrap frameBytes (body F privN priv)

end VG.Impl.RsaPkcs1Enc.X86.Decrypt
