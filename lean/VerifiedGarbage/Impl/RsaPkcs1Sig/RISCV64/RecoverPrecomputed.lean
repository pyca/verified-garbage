module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.Frame

/-!
# RSASSA-PKCS1-v1_5 recovery with a precomputed public key on RISC-V

`vg_rsa_pkcs1_recover_precomputed(out = a0, out_len = a1, n = a2,
n_len = a3, e = a4, e_len = a5, hash = a6, sig = a7, sig_len, scratch,
scratch_len, pre, pre_len)`, the last five on the stack. As on PPC64LE
(`Impl/RsaPkcs1Sig/PPC64LE/RecoverPrecomputed.lean`), it recovers as
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
`out_len`, `k` and `hash` (zero-extended) are kept in `s1`–`s4`
(`Frame.lean`).
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.RISCV64.RecoverPrecomputed

open VG VG.RISCV64

/-- Zeros to the `t5` (at least 1) bytes at `a1` (`encode`'s `fillLoop`),
and 0 returned. -/
def zeroOut : Prog isa := .seq (.block [.li .t0 0]) (.seq fillLoop (.block ret0))

/-- Zeros to `out` (`out_len` bytes), from the function's registers. -/
def zeroArgs : Prog isa := .seq (.block [mov .t5 .a1, mov .a1 .a0]) zeroOut

/-- Zeros to `out`, kept in `s1` and `s2`. -/
def zeroKept : Prog isa := .seq (.block [mov .a1 .s1, mov .t5 .s2]) zeroOut

/-- Our caller's registers saved; `out`, `out_len`, `k` and `hash` kept in
`s1`–`s4`; and the arguments of the call: `EM₁`, `k`, `pre`, `pre_len`,
`e`, `e_len`, `sig` and `k`, then `scratch` and `scratch_len`. -/
def pubArgs : List Instr :=
  save ++ [mov .s1 .a0, mov .s2 .a1, mov .s3 .a3] ++ zext .s4 .a6 ++ [mov .a6 .a7, mov .a7 .a3] ++ callTail .s3

/-- `a4 := EM₁ + k - out_len`, the hash value's place in `EM₁`. -/
def valPtr : List Instr := [.addi .a4 .t0 oEM1, .add .a4 .a4 .s3, .sub .a4 .a4 .s2]

/-- The status kept, and `encode`'s registers: `EM₂`, `k`, `hash`, the last
`out_len` bytes of `EM₁` and `out_len`. -/
def encArgs : List Instr :=
  [.addSp .t0 0, .store .d .a0 .t0 oSt, .addi .a1 .t0 oEM2, mov .a2 .s3, mov .a3 .s4, mov .a5 .s2] ++ valPtr

/-- The mask into its word: all ones if `t4` (the comparison's difference,
at most 255) is 0 and the low 32 bits of the status are not, zero if not. -/
def maskM : List Instr :=
  [.addi .a1 .t4 (-1), .shift .srl .d .a1 .a1 63, .addSp .t0 0, .load .d .a2 .t0 oSt] ++ zext .a2 .a2 ++
    [.li .a3 0, .sub .a2 .a3 .a2, .shift .srl .d .a2 .a2 63, .logic .and .a1 .a1 .a2, .sub .a1 .a3 .a1,
      .store .d .a1 .t0 oMk]

/-- The value to `out`: `out_len` bytes from the hash value's place in `EM₁`
(`encode`'s `copyLoop`). -/
def copyOut : Prog isa := .seq (.block ([mov .a1 .s1, mov .a5 .s2] ++ valPtr)) copyLoop

/-- The registers of `maskLoop`: the mask, `out` and `out_len`. -/
def maskArgs : List Instr := [.addSp .t0 0, .load .d .a3 .t0 oMk, mov .a1 .s1, mov .a5 .s2]

/-- `out[i] &= a3` for each of its `a5` bytes, at `a1`. -/
def maskLoop : Prog isa :=
  Impl.Bignum.RISCV64.countLoop .a5
    [.load .b .t1 .a1 0, .logic .and .t1 .t1 .a3, .store .b .t1 .a1 0, .addi .a1 .a1 1]

/-- The result: 1 under the mask. -/
def fin : List Instr := [.li .a0 1, .logic .and .a0 .a0 .a3]

/-- After the comparison, its difference in `t4`: the value to `out`, then
`out` and the result masked. -/
def release : Prog isa :=
  .seq (.block maskM) (.seq copyOut (.seq (.block maskArgs) (.seq maskLoop (.block fin))))

/-- After the encoding. -/
def tail : Prog isa :=
  .ite (.zero .a0) zeroKept (.seq (.block (cmpArgs .s3)) (.seq compare release))

/-- The body of the frame. -/
def body : Prog isa :=
  .seq (.block pubArgs) (.seq pubCall (.seq (.block encArgs) (.seq encode (.seq tail (.block restore)))))

/-- `vg_rsa_pkcs1_recover_precomputed`. -/
def code : Prog isa :=
  .seq (.block (lenCheck .a3)) (.ite (.nonzero .t0) zeroArgs (.frame (.alloc frameBytes) body (.free frameBytes)))

end VG.Impl.RsaPkcs1Sig.RISCV64.RecoverPrecomputed
