module

public import VerifiedGarbage.Impl.RsaPss.PPC64LE
public import VerifiedGarbage.Impl.Rsa.PPC64LE.Priv

/-!
# RSASSA-PSS signing (RFC 8017 §8.1.1) on PPC64LE

`vg_rsa_pss_<H>_mgf1_<H>_sign(out = r3, out_len = r4, n = r5, n_len = r6,
e = r7, e_len = r8, p = r9, p_len = r10, q, q_len, dp, dp_len, dq, dq_len,
qinv, qinv_len, digest, salt, salt_len, scratch, scratch_len)`, the last
thirteen on the stack, for a hash function `H` (an
`Impl.Hmac.Stream.PPC64LE.Hash`, its streaming functions) as both the hash
function and MGF1's, which it calls, with `vg_rsa_private_checked`.

It runs in the frame of RSAES-OAEP encryption (`Impl/RsaOaep/PPC64LE.lean`),
with its part of `scratch` and its MGF1 (`mgfXor`), and hashes
`M' = 0⁸ ‖ mHash ‖ salt` at `oY` as verification does for a given salt length
(`Impl/RsaPss/PPC64LE.lean`, `hashFixed`). The values the code keeps across
the calls are in `r14`–`r23`, all public: `r14` = `scratch`, `r15` = `k =
n_len`, `r16` = `out`, `r17` = `p`, `r18` = `p_len`, `r19` = `salt_len`, `r20`
= `n`, `r21` = `e`, `r22` = `e_len`, `r23` = `lo` (1 if `emLen = k - 1`, else
0, from the modulus' first byte `n₀`, as verification computes it). The
digest and the salt are read from our stack arguments where they are copied.

If `n₀ = 0`, `emLen < hLen + 2` or `salt_len > emLen - hLen - 2` (all public),
it writes zeros to `out` and returns 0. Otherwise it writes `M'` and hashes it
to `H` (at `oDig`); writes `EM` at `scratch`: zeros, `0x01` at
`k - salt_len - hLen - 2`, the salt after it, `H` at `k - hLen - 1` and
`0xbc` last; masks `DB` (`dbLen = k - lo - hLen - 1` bytes at `lo`) with
MGF1 of `H`, and clears its top bits with the mask `c` of verification; and
calls `vg_rsa_private_checked` on `EM`, from a frame of `privBytes` bytes
whose Parameter Save Area holds its twelve stack arguments, as RSAES-OAEP
decryption does. That function writes the signature (or zeros) to `out`, and
its result is ours. Every branch and address depends only on the pointers,
the lengths and `n₀`; the digest and the salt are only copied and hashed.
-/

@[expose] public section

namespace VG.Impl.RsaPss.PPC64LE.Sign

open VG VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Impl.RsaOaep.PPC64LE (frameBytes arg save restore copyLoop zeroLoop encFail oEm oSt oDig oW oRsa
  mgfXor)
open VG.Impl.RsaPss.PPC64LE (oY hashFixed)

/-- `smear(b >> 1)` of the byte in `r9` into `r10`, and `lo` into `r11`. -/
def smear : List Instr :=
  [.lsr .d .r10 .r9 1, .lsr .d .r11 .r10 1, .logic .or .r10 .r10 .r11, .lsr .d .r11 .r10 2,
    .logic .or .r10 .r10 .r11, .lsr .d .r11 .r10 4, .logic .or .r10 .r10 .r11, .subi .r11 .r10 1,
    .lsr .d .r11 .r11 63]

/-- The arguments into the registers that keep them, with `r12 = r1`; `n₀`
into `r9` and `lo` into `r23`. -/
def prologue : List Instr :=
  [.load .d .r14 .r12 (arg 11), mov .r15 .r6, mov .r16 .r3, mov .r17 .r9, mov .r18 .r10,
    .load .d .r19 .r12 (arg 10), mov .r20 .r5, mov .r21 .r7, mov .r22 .r8, .lbz .r9 .r5 0] ++ smear ++
    [mov .r23 .r11]

variable (H : Hash)

/-! ## The checks -/

/-- In `r3`, 1 if `emLen < hLen + 2`, 0 if not. -/
def chkEm : List Instr := [.sub .r3 .r15 .r23, .subi .r3 .r3 (H.D + 2), .lsr .d .r3 .r3 63]

/-- In `r3`, nonzero exactly when `salt_len > emLen - hLen - 2`, for
`emLen ≥ hLen + 2`: the top bit of `salt_len`, or of
`(emLen - hLen - 2) - salt_len`. -/
def chkSalt : List Instr :=
  [.sub .r3 .r15 .r23, .subi .r3 .r3 (H.D + 2), .sub .r3 .r3 .r19, .lsr .d .r3 .r3 63, .lsr .d .r5 .r19 63,
    .logic .or .r3 .r3 .r5]

/-! ## `M'` and its hash -/

/-- Our stack argument `j` into `r`, with `r12 = r1`. -/
def ldArg (r : Reg) (j : Nat) : List Instr := [.addSp .r12 0, .load .d r .r12 (arg j)]

/-- `salt_len` bytes of the salt to `r5`, if it is not empty. -/
def copySalt : Prog isa :=
  .seq (.block (ldArg .r4 9 ++ [mov .r6 .r19])) (.ite (.nonzero .d .r6) copyLoop (.block []))

/-- `M' = 0⁸ ‖ mHash ‖ salt` at `scratch + oY`. -/
def mPrime : Prog isa :=
  .seq (.seq (.block [.addi .r4 .r14 oY, .li .r5 8, .li .r6 0]) zeroLoop)
    (.seq (.seq (.block (ldArg .r4 8 ++ [.addi .r5 .r14 (oY + 8), .li .r6 H.D])) copyLoop)
      (.seq (.block [.addi .r5 .r14 (oY + 8 + H.D)]) copySalt))

/-! ## `EM` -/

/-- `EM`'s `k` bytes cleared. -/
def clearEm : Prog isa := .seq (.block [.addi .r4 .r14 oEm, mov .r5 .r15, .li .r6 0]) zeroLoop

/-- `0x01` at `EM + k - salt_len - hLen - 2`, and the salt after it. -/
def putSalt : Prog isa :=
  .seq (.block [.addi .r4 .r14 oEm, .add .r4 .r4 .r15, .sub .r4 .r4 .r19, .subi .r4 .r4 (H.D + 2), .li .r5 1,
      .stb .r5 .r4 0, .addi .r5 .r4 1]) copySalt

/-- `H` at `EM + k - hLen - 1`, and `0xbc` at `EM + k - 1`. -/
def putH : Prog isa :=
  .seq (.seq (.block [.addi .r4 .r14 oDig, .addi .r5 .r14 oEm, .add .r5 .r5 .r15, .subi .r5 .r5 (H.D + 1),
      .li .r6 H.D]) copyLoop)
    (.block [.addi .r4 .r14 oEm, .add .r4 .r4 .r15, .subi .r4 .r4 1, .li .r5 0xbc, .stb .r5 .r4 0])

/-- MGF1's registers for masking `DB` (`dbLen` bytes at `EM + lo`) with `H`. -/
def dbArgs : List Instr :=
  [.addi .r24 .r14 oEm, .add .r24 .r24 .r15, .subi .r24 .r24 (H.D + 1), .li .r25 H.D, .addi .r26 .r14 oEm,
    .add .r26 .r26 .r23, .sub .r27 .r15 .r23, .subi .r27 .r27 (H.D + 1)]

/-- `DB`'s first byte ANDed with `c = smear(n₀ >> 1) ∨ (0xFF ∧ -lo)`, from
`n₀` again. -/
def clearTop : List Instr :=
  [.lbz .r9 .r20 0] ++ smear ++
    [.li .r8 0, .sub .r8 .r8 .r11, .li .r7 0xFF, .logic .and .r8 .r8 .r7, .logic .or .r10 .r10 .r8,
      .addi .r4 .r14 oEm, .add .r4 .r4 .r23, .lbz .r5 .r4 0, .logic .and .r5 .r5 .r10, .stb .r5 .r4 0]

/-! ## The private operation -/

/-- The frame from which `vg_rsa_private_checked` is called: its Parameter
Save Area, with its twelve stack arguments at `r1 + 96`. -/
def privBytes : Nat := 192

/-- Our stack argument `j`, from that frame. -/
def argP (j : Nat) : Nat := privBytes + arg j

/-- `vg_rsa_private_checked`. -/
def privCall : Prog isa := .call "vg_rsa_private_checked" Impl.Rsa.PPC64LE.Priv.code

/-- Its arguments, with `r12 = r1` in its frame: on the stack `p` and `p_len`
(`r17`, `r18`), our stack arguments 0 to 7 (`q` to `qinv_len`), then the
rest of `scratch` from `oRsa` and `scratch_len - 1024`; in the registers
`out` (`k` bytes), `n`, `e` and `EM` (`k` bytes). -/
def privArgs : List Instr :=
  [.addSp .r12 0, .store .d .r17 .r12 96, .store .d .r18 .r12 104] ++
    (List.range 8).flatMap (fun j => [.load .d .r0 .r12 (argP j), .store .d .r0 .r12 (112 + 8 * j)]) ++
    [.li .r0 oRsa, .add .r0 .r14 .r0, .store .d .r0 .r12 176, .load .d .r11 .r12 (argP 12),
      .subi .r11 .r11 1024, .store .d .r11 .r12 184, mov .r3 .r16, mov .r4 .r15, mov .r5 .r20, mov .r6 .r15,
      mov .r7 .r21, mov .r8 .r22, .addi .r9 .r14 oEm, mov .r10 .r15]

/-- The private operation, from its frame. -/
def priv : Prog isa := .frame (.alloc privBytes) (.seq (.block privArgs) privCall) (.free privBytes)

/-! ## The function -/

/-- After the checks: `M'` and `H`, `EM`, and the private operation. -/
def signMain : Prog isa :=
  .seq (mPrime H) (.seq (hashFixed H) (.seq clearEm (.seq (putSalt H) (.seq (putH H)
    (.seq (.block (dbArgs H)) (.seq (mgfXor H) (.seq (.block clearTop) priv)))))))

/-- The checks, then `signMain`. -/
def checks : Prog isa :=
  .ite (.zero .d .r9) encFail
    (.seq (.block (chkEm H)) (.ite (.nonzero .d .r3) encFail
      (.seq (.block (chkSalt H)) (.ite (.nonzero .d .r3) encFail (signMain H)))))

/-- The frame's body. -/
def body : Prog isa := .seq (.block (save ++ prologue)) (.seq (checks H) (.block restore))

/-- `vg_rsa_pss_<H>_mgf1_<H>_sign`. -/
def sign : Prog isa := .frame (.alloc frameBytes) (body H) (.free frameBytes)

end VG.Impl.RsaPss.PPC64LE.Sign
