module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.Frame

/-!
# RSASSA-PKCS1-v1_5 verification with a precomputed public key on RISC-V

`vg_rsa_pkcs1_verify_precomputed(n = a0, n_len = a1, e = a2, e_len = a3,
hash = a4, digest = a5, digest_len = a6, sig = a7, sig_len, scratch,
scratch_len, pre, pre_len)`, the last five on the stack. RFC 8017 §8.2.2, as
on PPC64LE (`Impl/RsaPkcs1Sig/PPC64LE/Precomputed.lean`):

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
`hash` (zero-extended), `digest` and `digest_len` are kept in `s1`–`s4`,
which the callee preserves (`Frame.lean`).
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.RISCV64.Precomputed

open VG VG.RISCV64

/-- Our caller's registers saved; `k`, `hash`, `digest` and `digest_len`
kept in `s1`–`s4`; and the arguments of the call: `EM₁`, `k`, `pre`,
`pre_len`, `e`, `e_len`, `sig` and `k`, then `scratch` and `scratch_len`. -/
def pubArgs : List Instr :=
  save ++ [mov .s1 .a1] ++ zext .s2 .a4 ++ [mov .s3 .a5, mov .s4 .a6, mov .a4 .a2, mov .a5 .a3, mov .a6 .a7,
    mov .a7 .a1] ++ callTail .s1

/-- The status kept, and `encode`'s registers: `EM₂`, `k`, `hash`, `digest`
and `digest_len`. -/
def encArgs : List Instr :=
  [.addSp .t0 0, .store .d .a0 .t0 oSt, .addi .a1 .t0 oEM2, mov .a2 .s1, mov .a3 .s2, mov .a4 .s3,
    mov .a5 .s4]

/-- 1 if `t4` (at most 255) is 0, 0 if not: the borrow of `t4 - 1`. -/
def result : List Instr := [.addi .a0 .t4 (-1), .shift .srl .d .a0 .a0 63]

/-- The result masked with the status. -/
def mask : List Instr := [.addSp .t0 0, .load .d .a1 .t0 oSt, .logic .and .a0 .a0 .a1]

/-- After the encoding. -/
def tail : Prog isa :=
  .ite (.zero .a0) (.block ret0) (.seq (.block (cmpArgs .s1)) (.seq compare (.block result)))

/-- The body of the frame. -/
def body : Prog isa :=
  .seq (.block pubArgs) (.seq pubCall (.seq (.block encArgs) (.seq encode (.seq tail
    (.seq (.block mask) (.block restore))))))

/-- `vg_rsa_pkcs1_verify_precomputed`. -/
def code : Prog isa :=
  .seq (.block (lenCheck .a1)) (.ite (.nonzero .t0) (.block ret0) (.frame (.alloc frameBytes) body (.free frameBytes)))

end VG.Impl.RsaPkcs1Sig.RISCV64.Precomputed
