module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Encrypt

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on AArch64

`vg_rsa_pkcs1_encrypt_precomputed`: `vg_rsa_pkcs1_encrypt`'s arguments,
then `pre` and `pre_len` on the stack after `scratch_len`. As
`Encrypt.code`, with the precomputed modulus `pre` in place of `n` (`x2`,
`x3`) for the public operation, `vg_rsa_public_precomputed_checked` or one
of its variants; the mask after the call does not branch on its result.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.AArch64.Precomputed

open VG VG.AArch64 Encrypt

/-- The call's `input` and `input_len`, then `pre` and `pre_len` for `n`
and `n_len`. -/
def callArgs : List Instr := Encrypt.callArgs ++ [.ldrSp .x2 (arg 4), .ldrSp .x3 (arg 5)]

/-- The inner frame's body. -/
def body (pubName : String) (pub : Prog isa) : Prog isa :=
  .seq (.block setup) (.seq psLoop (.seq (.block sep) (.seq msgCopy (.seq (.block callArgs)
    (.seq (.call pubName pub) (.seq (.block maskArgs) maskLoop))))))

/-- `vg_rsa_pkcs1_encrypt_precomputed`, calling a precomputed public
operation (`pub`) by its name. -/
def code (pubName : String) (pub : Prog isa) : Prog isa :=
  .frame (.push .x30) (.frame (.alloc frameBytes) (body pubName pub) (.free frameBytes)) (.pop .x30)

end VG.Impl.RsaPkcs1Enc.AArch64.Precomputed
