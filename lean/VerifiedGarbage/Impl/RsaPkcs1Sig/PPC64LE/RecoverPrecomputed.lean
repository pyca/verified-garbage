module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Frame
public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Encode

/-!
# RSASSA-PKCS1-v1_5 recovery with a precomputed public key on PPC64LE

`vg_rsa_pkcs1_recover_precomputed(out = r3, out_len = r4, n = r5,
n_len = r6, e = r7, e_len = r8, hash = r9, sig = r10, sig_len, scratch,
scratch_len, pre, pre_len)`, the last five on the stack. As on AArch64
(`Impl/RsaPkcs1Sig/AArch64/RecoverPrecomputed.lean`), it recovers as
OpenSSL's `ossl_rsa_verify` with `rm` does:

1. if `sig_len` is not `n_len`, it writes zeros to `out` and returns 0;
2. `vg_rsa_public_precomputed_checked`, given `pre` in place of the modulus,
   writes `EM₁ = s^e mod n` or zeros to the frame, and its status is kept in
   the frame's word at `oSt`;
3. `encode` writes the encoding of the last `out_len` bytes of `EM₁` (the
   hash value, if `EM₁` is an encoding) to `EM₂`, and it writes zeros and
   returns 0 if that fails (a branch on `hash` and the lengths);
4. `compare` compares `EM₁` and `EM₂`; the value is copied to `out`, and
   `out` and the result 1 are masked with all ones if the two are equal and
   the status is not 0, with zeros if not (`release`).

The status, and so `EM₁`, is unspecified when `pre` is not the modulus'
values, so nothing after the call branches on them. Across the call, `out`,
`out_len`, `k` and `hash` are kept in `r28`–`r31` (`Frame.lean`).
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.PPC64LE.RecoverPrecomputed

open VG VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov)

/-- `r11 := sig_len - n_len`. -/
def lenCheck : List Instr := [.addSp .r12 0, .load .d .r11 .r12 96, .sub .r11 .r11 .r6]

/-- Zeros to the `r11` (at least 1) bytes at `r4` (`encode`'s `fillLoop`),
and 0 returned. -/
def zeroOut : Prog isa := .seq (.block [.li .r0 0]) (.seq fillLoop (.block ret0))

/-- Zeros to `out` (`out_len` bytes), from the function's registers. -/
def zeroArgs : Prog isa := .seq (.block [mov .r11 .r4, mov .r4 .r3]) zeroOut

/-- Zeros to `out`, kept in `r28` and `r29`. -/
def zeroKept : Prog isa := .seq (.block [mov .r4 .r28, mov .r11 .r29]) zeroOut

/-- Our caller's registers saved; `out`, `out_len`, `k` and `hash` (zero-extended) kept in
`r28`–`r31`; and the arguments of the call: `EM₁`, `n_len`, `pre`, `pre_len`,
`e`, `e_len`, `sig` and `n_len`, then `scratch` and `scratch_len`. -/
def pubArgs : List Instr :=
  save ++ [mov .r28 .r3, mov .r29 .r4, mov .r30 .r6, .lsr .w .r31 .r9 0, mov .r9 .r10, mov .r10 .r6, mov .r4 .r6] ++
    callTail

/-- `r7 := EM₁ + k - out_len`, the hash value's place in `EM₁`. -/
def valPtr : List Instr := [.addi .r7 .r12 oEM1, .add .r7 .r7 .r30, .sub .r7 .r7 .r29]

/-- The status kept, and `encode`'s registers: `EM₂`, `k`, `hash`, the last
`out_len` bytes of `EM₁` and `out_len`. -/
def encArgs : List Instr :=
  [.addSp .r12 0, .store .d .r3 .r12 oSt, .addi .r4 .r12 oEM2, mov .r5 .r30, mov .r6 .r31, mov .r8 .r29] ++
    valPtr

/-- The mask into its word: all ones if `r7` (the comparison's difference,
at most 255) is 0 and the low 32 bits of the status are not, zero if not. -/
def maskM : List Instr :=
  [.subi .r8 .r7 1, .lsr .d .r8 .r8 63, .addSp .r12 0, .load .d .r9 .r12 oSt, .lsl .r9 .r9 32,
    .lsr .d .r9 .r9 32, .li .r10 0, .sub .r9 .r10 .r9, .lsr .d .r9 .r9 63, .logic .and .r8 .r8 .r9,
    .sub .r8 .r10 .r8, .store .d .r8 .r12 oMk]

/-- The value to `out`: `out_len` bytes from the hash value's place in `EM₁`
(`encode`'s `copyLoop`). -/
def copyOut : Prog isa := .seq (.block ([mov .r4 .r28, mov .r8 .r29] ++ valPtr)) copyLoop

/-- The registers of `maskLoop`: the mask, `out` and `out_len`. -/
def maskArgs : List Instr := [.addSp .r12 0, .load .d .r9 .r12 oMk, mov .r11 .r28, mov .r8 .r29]

/-- `out[i] &= r9` for each of its `r8` bytes, at `r11`. -/
def maskLoop : Prog isa :=
  .loop (.block [.lbz .r10 .r11 0, .logic .and .r10 .r10 .r9, .stb .r10 .r11 0, .addi .r11 .r11 1,
    .subi .r8 .r8 1]) (.nonzero .d .r8)

/-- The result: 1 under the mask. -/
def fin : List Instr := [.li .r3 1, .logic .and .r3 .r3 .r9]

/-- After the comparison, its difference in `r7`: the value to `out`, then
`out` and the result masked. -/
def release : Prog isa :=
  .seq (.block maskM) (.seq copyOut (.seq (.block maskArgs) (.seq maskLoop (.block fin))))

/-- After the encoding. -/
def tail : Prog isa :=
  .ite (.zero .d .r3) zeroKept (.seq (.block (cmpArgs .r30)) (.seq compare release))

/-- The body of the frame. -/
def body : Prog isa :=
  .seq (.block pubArgs) (.seq pubCall (.seq (.block encArgs) (.seq encode (.seq tail (.block restore)))))

/-- `vg_rsa_pkcs1_recover_precomputed`. -/
def code : Prog isa :=
  .seq (.block lenCheck) (.ite (.nonzero .d .r11) zeroArgs (.frame (.alloc frameBytes) body (.free frameBytes)))

end VG.Impl.RsaPkcs1Sig.PPC64LE.RecoverPrecomputed
