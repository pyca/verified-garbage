module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Frame
public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Encode

/-!
# RSASSA-PKCS1-v1_5 verification with a precomputed public key on PPC64LE

`vg_rsa_pkcs1_verify_precomputed(n = r3, n_len = r4, e = r5, e_len = r6,
hash = r7, digest = r8, digest_len = r9, sig = r10, sig_len, scratch,
scratch_len, pre, pre_len)`, the last five on the stack (ELFv2 ABI
§2.2.3.3, the Parameter Save Area at `sp + 96`). RFC 8017 §8.2.2, as on
AArch64 (`Impl/RsaPkcs1Sig/AArch64/Precomputed.lean`):

1. if `sig_len` is not `n_len`, it returns 0 (a branch on public lengths);
2. `vg_rsa_public_precomputed_checked`, given `pre` in place of the modulus,
   writes `EM₁ = s^e mod n` or zeros to the frame, and its status is kept in
   the frame's word at `oSt`;
3. `encode` writes the encoding of `digest` to `EM₂`, and it returns 0 if
   that fails (a branch on `hash` and the lengths);
4. `compare` compares `EM₁` and `EM₂`, and the result, 1 if they are equal,
   is masked with the status.

The status, and so `EM₁`, is unspecified when `pre` is not the modulus'
values, so nothing after the call branches on them. Across the call, `k`,
`hash`, `digest` and `digest_len` are kept in `r28`–`r31`, which the callee
preserves (`Frame.lean`).
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.PPC64LE.Precomputed

open VG VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov)

/-- `r11 := sig_len - n_len`. -/
def lenCheck : List Instr := [.addSp .r12 0, .load .d .r11 .r12 96, .sub .r11 .r11 .r4]

/-- Our caller's registers saved; `k`, `hash` (zero-extended, since only
its low 32 bits are an argument), `digest` and `digest_len` kept in
`r28`–`r31`; and the arguments of the call: `EM₁`, `n_len`, `pre`,
`pre_len`, `e`, `e_len`, `sig` and `n_len`, then `scratch` and
`scratch_len`. -/
def pubArgs : List Instr :=
  save ++ [mov .r28 .r4, .lsr .w .r29 .r7 0, mov .r30 .r8, mov .r31 .r9, mov .r9 .r10, mov .r10 .r4, mov .r7 .r5,
    mov .r8 .r6] ++ callTail

/-- The status kept, and `encode`'s registers: `EM₂`, `k`, `hash`, `digest`
and `digest_len`. -/
def encArgs : List Instr :=
  [.addSp .r12 0, .store .d .r3 .r12 oSt, .addi .r4 .r12 oEM2, mov .r5 .r28, mov .r6 .r29, mov .r7 .r30,
    mov .r8 .r31]

/-- 1 if `r7` (at most 255) is 0, 0 if not: the borrow of `r7 - 1`. -/
def result : List Instr := [.subi .r3 .r7 1, .lsr .d .r3 .r3 63]

/-- The result masked with the status. -/
def mask : List Instr := [.addSp .r12 0, .load .d .r4 .r12 oSt, .logic .and .r3 .r3 .r4]

/-- After the encoding. -/
def tail : Prog isa :=
  .ite (.zero .d .r3) (.block ret0) (.seq (.block (cmpArgs .r28)) (.seq compare (.block result)))

/-- The body of the frame. -/
def body : Prog isa :=
  .seq (.block pubArgs) (.seq pubCall (.seq (.block encArgs) (.seq encode (.seq tail
    (.seq (.block mask) (.block restore))))))

/-- `vg_rsa_pkcs1_verify_precomputed`. -/
def code : Prog isa :=
  .seq (.block lenCheck) (.ite (.nonzero .d .r11) (.block ret0) (.frame (.alloc frameBytes) body (.free frameBytes)))

end VG.Impl.RsaPkcs1Sig.PPC64LE.Precomputed
