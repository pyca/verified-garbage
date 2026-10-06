import VerifiedGarbage.Impl.RsaPkcs1Sig.AArch64.Verify

/-!
# RSASSA-PKCS1-v1_5 verification with a precomputed public key on AArch64

`vg_rsa_pkcs1_verify_precomputed`: `vg_rsa_pkcs1_verify`'s arguments, then
`pre = [sp + 24]` and `pre_len = [sp + 32]`. As on x86-64
(`Impl/RsaPkcs1Sig/X86_64/Precomputed.lean`): the precomputed public
operation (a variant of `vg_rsa_public_precomputed_checked`) is given the
precomputed values in place of the modulus, and the padding check runs
whatever its status, which then masks the result: no branch depends on the
status, which is unspecified if `pre` is not the modulus' values. The status
is kept in the frame's word at `oSt`, which `vg_rsa_pkcs1_verify` does not
use. The frame and the registers kept are `vg_rsa_pkcs1_verify`'s.
-/

namespace VG.Impl.RsaPkcs1Sig.AArch64.Precomputed

open VG VG.AArch64
open VG.Impl.RsaPkcs1Sig.AArch64.Verify (frameBytes oEM1 mov movw save restore copyArg lenCheck ret0 encArgs
  tail)

/-- Where the status is kept. -/
def oSt : Nat := 56

/-- `vg_rsa_pkcs1_verify`'s arguments of the call, with `pre` and
`pre_len` for the modulus. -/
def pubArgs : List Instr :=
  save ++ [mov .x19 .x1, movw .x20 .x4, mov .x21 .x5, mov .x22 .x6] ++ copyArg 1 0 ++ copyArg 2 1 ++
    [mov .x4 .x2, mov .x5 .x3, .ldrSp .x2 (frameBytes + 24), .ldrSp .x3 (frameBytes + 32), mov .x6 .x7,
      mov .x7 .x1, .addSp .x0 oEM1]

/-- The status kept, the padding checked, and its result masked with the
status. -/
def afterPub : Prog isa :=
  .seq (.block ([.addSp .x16 0, .str .x .x0 .x16 oSt] ++ encArgs)) (.seq encode
    (.seq tail (.block [.addSp .x16 0, .ldr .x .x8 .x16 oSt, .logic .and .w .x0 .x0 .x8])))

def body (pubName : String) (pub : Prog isa) : Prog isa :=
  .seq (.block pubArgs) (.seq (.call pubName pub) (.seq afterPub (.block restore)))

/-- `vg_rsa_pkcs1_verify_precomputed`, calling a precomputed public
operation (`pub`) by its name. -/
def code (pubName : String) (pub : Prog isa) : Prog isa :=
  .seq (.block lenCheck)
    (.ite (.nonzero .x .x8) ret0 (.frame (.alloc frameBytes) (body pubName pub) (.free frameBytes)))

end VG.Impl.RsaPkcs1Sig.AArch64.Precomputed
