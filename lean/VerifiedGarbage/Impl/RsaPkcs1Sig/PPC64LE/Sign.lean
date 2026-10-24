module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Encode
public import VerifiedGarbage.Impl.Rsa.PPC64LE.Priv

/-!
# RSASSA-PKCS1-v1_5 signing on PPC64LE

`vg_rsa_pkcs1_sign(out = r3, out_len = r4, n = r5, n_len = r6, e = r7,
e_len = r8, hash = r9, digest = r10, digest_len, p, p_len, q, q_len, dp,
dp_len, dq, dq_len, qinv, qinv_len, scratch, scratch_len)`, the last
thirteen on the stack (the Parameter Save Area at `r1 + 96`). As on AArch64
(`Impl/RsaPkcs1Sig/AArch64/Sign.lean`), RFC 8017 §8.2.1 from verified
functions:

1. `encode` writes the encoding of `digest` to a buffer `EM` in the frame;
   if that fails, zeros are written to `out` and 0 is returned;
2. `vg_rsa_private_checked` computes the signature of `EM` into `out`,
   checked against `e`, and returns its result;
3. `EM` is overwritten with zeros.

Only the public key, the lengths and `hash` decide a branch or an address:
the hash value is only copied into `EM`, which only the private operation
reads.

The frame (`stdu r1, -frameBytes(r1)`) holds the Parameter Save Area of the
call (its twelve stack arguments, at `r1 + 96`); our caller's `r26`–`r30`
and our return address, which the call (`bl`) overwrites in the link
register (`oSave`, `oLr`); and `EM`, of up to 1024 bytes (`oEM`). Our own
stack arguments are then at `r1 + frameBytes + 96 + 8 i` (`arg i`). Across
`encode` and the call, `out`, `n`, `k`, `e` and `e_len` are kept in
`r26`–`r30`. The frame is addressed through `r12`, which holds `r1`.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.PPC64LE.Sign

open VG VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov)

/-- The size of the frame. -/
def frameBytes : Nat := 1264

/-- Our caller's `r26`–`r30` and our return address. -/
def oSave : Nat := 192
def oLr : Nat := 232

/-- `EM`. -/
def oEM : Nat := 240

/-- Our stack argument `i` (from 0), in the frame. -/
def arg (i : Nat) : Nat := frameBytes + 96 + 8 * i

/-- `vg_rsa_private_checked`. -/
def privCall : Prog isa := .call "vg_rsa_private_checked" Impl.Rsa.PPC64LE.Priv.code

/-- `r12 := r1`; our caller's `r26`–`r30` and our return address into the
frame; `out`, `n`, `k`, `e` and `e_len` into `r26`–`r30`. -/
def save : List Instr :=
  [.addSp .r12 0, .store .d .r26 .r12 oSave, .store .d .r27 .r12 (oSave + 8), .store .d .r28 .r12 (oSave + 16),
    .store .d .r29 .r12 (oSave + 24), .store .d .r30 .r12 (oSave + 32), .mflr .r0, .store .d .r0 .r12 oLr,
    mov .r26 .r3, mov .r27 .r5, mov .r28 .r6, mov .r29 .r7, mov .r30 .r8]

/-- `encode`'s arguments: `EM`, `k`, `hash`, `digest` and `digest_len` (our
stack argument 0). -/
def encArgs : List Instr :=
  [.addi .r4 .r12 oEM, mov .r5 .r28, mov .r6 .r9, mov .r7 .r10, .load .d .r8 .r12 (arg 0)]

/-- `r8` (at least 1) bytes `r0` from `[r7]` on. -/
def zeroLoop : Prog isa :=
  .loop (.block [.stb .r0 .r7 0, .addi .r7 .r7 1, .subi .r8 .r8 1]) (.nonzero .d .r8)

/-- Zeros to `out` (`k` bytes), keeping 0 in `r3`. -/
def zeroOut : Prog isa := .seq (.block [mov .r7 .r26, mov .r8 .r28, .li .r0 0]) zeroLoop

/-- Our stack argument `1 + j` (`p` … `scratch_len`) to the call's stack
argument `j`. -/
def copyArg (j : Nat) : List Instr := [.load .d .r0 .r12 (arg (1 + j)), .store .d .r0 .r12 (96 + 8 * j)]

/-- `vg_rsa_private_checked`'s arguments: `out`, `k`, `n`, `k`, `e`,
`e_len`, `EM`, `k`, and its twelve stack arguments, ours from `p` on. -/
def callArgs : List Instr :=
  [.addSp .r12 0] ++ (List.range 12).flatMap copyArg ++
  [mov .r3 .r26, mov .r4 .r28, mov .r5 .r27, mov .r6 .r28, mov .r7 .r29, mov .r8 .r30, .addi .r9 .r12 oEM,
    mov .r10 .r28]

/-- `EM` overwritten with zeros, keeping the result in `r3`. -/
def wipe : Prog isa := .seq (.block [.addSp .r12 0, .addi .r7 .r12 oEM, mov .r8 .r28, .li .r0 0]) zeroLoop

/-- After the encoding: zeros and 0 if it failed, else the signature. -/
def afterEnc : Prog isa :=
  .ite (.zero .d .r3) zeroOut (.seq (.block callArgs) (.seq privCall wipe))

/-- Our caller's `r26`–`r30` and our return address back from the frame. -/
def restore : List Instr :=
  [.addSp .r12 0, .load .d .r0 .r12 oLr, .mtlr .r0, .load .d .r26 .r12 oSave, .load .d .r27 .r12 (oSave + 8),
    .load .d .r28 .r12 (oSave + 16), .load .d .r29 .r12 (oSave + 24), .load .d .r30 .r12 (oSave + 32)]

/-- The body of the frame. -/
def body : Prog isa :=
  .seq (.block (save ++ encArgs)) (.seq encode (.seq afterEnc (.block restore)))

/-- `vg_rsa_pkcs1_sign`. -/
def code : Prog isa := .frame (.alloc frameBytes) body (.free frameBytes)

end VG.Impl.RsaPkcs1Sig.PPC64LE.Sign
