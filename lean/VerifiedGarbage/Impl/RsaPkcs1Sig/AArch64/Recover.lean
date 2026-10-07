import VerifiedGarbage.Impl.RsaPkcs1Sig.AArch64.Verify

/-!
# RSASSA-PKCS1-v1_5 recovery on AArch64

`vg_rsa_pkcs1_recover(out = x0, out_len = x1, n = x2, n_len = x3, e = x4,
e_len = x5, hash = w6, sig = x7, sig_len = [sp], scratch = [sp + 8],
scratch_len = [sp + 16])`. As on x86-64
(`Impl/RsaPkcs1Sig/X86_64/Recover.lean`), it recovers as OpenSSL's
`ossl_rsa_verify` with `rm` does, which `Proof/RsaPkcs1Sig/Recover.lean`
proves BoringSSL's recovery:

1. if `sig_len` is not `n_len`, it writes zeros to `out` and returns 0;
2. `vg_rsa_public_checked` writes `EM = s^e mod n` (`k` bytes) to a buffer
   `EM₁` in its frame, and it writes zeros and returns 0 if that fails;
3. `encode` writes the encoding of the last `out_len` bytes of `EM₁` (the
   hash value, if `EM` is an encoding) to a buffer `EM₂`, and it writes
   zeros and returns 0 if that fails;
4. if `EM₁` and `EM₂` are equal (`compare`), it copies those `out_len` bytes
   to `out` and returns 1; otherwise it writes zeros and returns 0.

Everything is public, so it branches freely. The frame is
`vg_rsa_pkcs1_verify`'s; across the call, `out`, `out_len`, `k` and `hash`
are kept in `x19`–`x22`.
-/

namespace VG.Impl.RsaPkcs1Sig.AArch64.Recover

open VG VG.AArch64
open VG.Impl.RsaPkcs1Sig.AArch64.Verify (frameBytes oEM1 oEM2 mov movw save restore copyArg)

/-- `sig_len` against `n_len`. -/
def lenCheck : List Instr := [.ldrSp .x8 0, .sub .x .x8 .x8 .x3]

/-- Zeros to the `x13` (at least 1) bytes at `x14` (`encode`'s loop for
`PS`), and 0 returned. -/
def zeroOut : Prog isa := .seq (.block [.movz .x .x15 0 0]) (.seq psLoop (.block [.movz .x .x0 0 0]))

/-- Zeros to `out` (`out_len` bytes), from the function's registers. -/
def zeroArgs : Prog isa := .seq (.block [mov .x14 .x0, mov .x13 .x1]) zeroOut

/-- Zeros to `out`, kept in `x19` and `x20`. -/
def zeroKept : Prog isa := .seq (.block [mov .x14 .x19, mov .x13 .x20]) zeroOut

/-- The registers saved; `out`, `out_len`, `k` and `hash` kept in
`x19`–`x22`; and the arguments of `vg_rsa_public_checked`: `EM₁`, `n`, `e`,
`sig` and the working space, `n_len` as every length of the modulus. -/
def pubArgs : List Instr :=
  save ++ [mov .x19 .x0, mov .x20 .x1, mov .x21 .x3, movw .x22 .x6] ++ copyArg 1 0 ++ copyArg 2 1 ++
    [mov .x1 .x3, mov .x6 .x7, mov .x7 .x3, .addSp .x0 oEM1]

/-- `x11 := EM₁ + k - out_len`, the hash value's place in `EM₁`. -/
def valPtr : List Instr := [.addSp .x11 oEM1, .add .x .x11 .x11 .x21, .sub .x .x11 .x11 .x20]

/-- The arguments of `encode`: `EM₂`, `k`, `hash`, the last `out_len` bytes
of `EM₁` and `out_len`. -/
def encArgs : List Instr := [.addSp .x8 oEM2, mov .x9 .x21, mov .x10 .x22, mov .x12 .x20] ++ valPtr

/-- The value to `out`, and 1 returned: `out_len` bytes from the hash
value's place in `EM₁` (`encode`'s loop for the hash value). -/
def copyOut : Prog isa :=
  .seq (.block ([mov .x14 .x19, mov .x12 .x20] ++ valPtr)) (.seq copyLoop (.block [.movz .x .x0 1 0]))

/-- The arguments of `compare`: `EM₁`, `EM₂` and `k`. -/
def cmpArgs : List Instr := [.addSp .x14 oEM1, .addSp .x15 oEM2, mov .x13 .x21]

/-- After the comparison, its result in `x12`. -/
def release : Prog isa := .ite (.nonzero .x .x12) zeroKept copyOut

/-- After the encoding. -/
def tail : Prog isa :=
  .ite (.zero .x .x0) zeroKept (.seq (.block cmpArgs) (.seq compare release))

/-- After the call. -/
def afterPub : Prog isa :=
  .ite (.zero .w .x0) zeroKept (.seq (.block encArgs) (.seq encode tail))

def body (pubName : String) (pub : Prog isa) : Prog isa :=
  .seq (.block pubArgs) (.seq (.call pubName pub) (.seq afterPub (.block restore)))

/-- `vg_rsa_pkcs1_recover`, calling `vg_rsa_public_checked` (`pub`) by its
name. -/
def code (pubName : String) (pub : Prog isa) : Prog isa :=
  .seq (.block lenCheck)
    (.ite (.nonzero .x .x8) zeroArgs (.frame (.alloc frameBytes) (body pubName pub) (.free frameBytes)))

end VG.Impl.RsaPkcs1Sig.AArch64.Recover
