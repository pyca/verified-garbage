module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.AArch64.Recover

/-!
# RSASSA-PKCS1-v1_5 recovery with a precomputed public key on AArch64

`vg_rsa_pkcs1_recover_precomputed`: `vg_rsa_pkcs1_recover`'s arguments, then
`pre = [sp + 24]` and `pre_len = [sp + 32]`. As on x86-64
(`Impl/RsaPkcs1Sig/X86_64/RecoverPrecomputed.lean`): `Recover.code`, with
the precomputed modulus `pre` in place of `n` for the public operation,
`vg_rsa_public_precomputed_checked` or one of its variants. Its result is
unspecified when `pre` does not hold the values for `n`, so nothing after the
call branches on it or on `EM₁`: the call's status is kept in the frame's
word at `oSt`, the encoding of the last `out_len` bytes of `EM₁` is always
written and compared with `EM₁`, and the value is copied to `out` and masked
to zeros, and the result to 0, unless the status is not 0 and the two are
equal (`release`); the mask is kept in the frame's word at `oMk`. The branch
on whether `encode` succeeds depends only on `hash` and `n_len`. The frame
and the registers kept are `vg_rsa_pkcs1_recover`'s.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.AArch64.RecoverPrecomputed

open VG VG.AArch64
open VG.Impl.RsaPkcs1Sig.AArch64.Verify (frameBytes mov restore)
open VG.Impl.RsaPkcs1Sig.AArch64.Recover (lenCheck zeroArgs zeroKept copyOut encArgs cmpArgs)

/-- Where the status and the mask are kept. -/
def oSt : Nat := 56
def oMk : Nat := 64

/-- `vg_rsa_pkcs1_recover`'s arguments of the call, with `pre` and
`pre_len` for the modulus. -/
def pubArgs : List Instr :=
  Recover.pubArgs ++ [.ldrSp .x2 (frameBytes + 24), .ldrSp .x3 (frameBytes + 32)]

/-- The mask into its word: all ones if `x12` (the comparison's difference)
is 0 and the low 32 bits of the status are not, zero if not. -/
def maskM : List Instr :=
  [.movz .x .x13 1 0, .subs .x .x12 .x12 .x13, .sbc .x .x12 .x12 .x12, .addSp .x16 0,
    .ldr .x .x8 .x16 oSt, .subs .w .x8 .x8 .x13, .sbc .x .x8 .x8 .x8, .bicRor .x .x12 .x12 .x8 0,
    .str .x .x12 .x16 oMk]

/-- The registers of `maskLoop`: the mask, `out` and `out_len`. -/
def maskArgs : List Instr := [.addSp .x16 0, .ldr .x .x9 .x16 oMk, mov .x11 .x19, mov .x12 .x20]

/-- `out[i] &= x9` for each of its `x12` bytes, at `x11`. -/
def maskLoop : Prog isa :=
  .loop (.block [.ldrb .x10 .x11 0, .logic .and .x .x10 .x10 .x9, .strb .x10 .x11 0, .addImm .x .x11 .x11 1,
    .subImm .x .x12 .x12 1]) (.nonzero .x .x12)

/-- The result: `copyOut`'s 1 under the mask. -/
def fin : List Instr := [.logic .and .x .x0 .x0 .x9]

/-- After the comparison, its difference in `x12`: the value to `out`, then
`out` and the result masked. -/
def release : Prog isa :=
  .seq (.block maskM) (.seq copyOut (.seq (.block maskArgs) (.seq maskLoop (.block fin))))

/-- After the encoding. -/
def tail : Prog isa :=
  .ite (.zero .x .x0) zeroKept (.seq (.block cmpArgs) (.seq compare release))

/-- After the call: its status to its word, and the encoding. -/
def afterPub : Prog isa :=
  .seq (.block ([.addSp .x16 0, .str .x .x0 .x16 oSt] ++ encArgs)) (.seq encode tail)

def body (pubName : String) (pub : Prog isa) : Prog isa :=
  .seq (.block pubArgs) (.seq (.call pubName pub) (.seq afterPub (.block restore)))

/-- `vg_rsa_pkcs1_recover_precomputed`, calling a precomputed public
operation (`pub`) by its name. -/
def code (pubName : String) (pub : Prog isa) : Prog isa :=
  .seq (.block lenCheck)
    (.ite (.nonzero .x .x8) zeroArgs (.frame (.alloc frameBytes) (body pubName pub) (.free frameBytes)))

end VG.Impl.RsaPkcs1Sig.AArch64.RecoverPrecomputed
