module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86_64.Encrypt

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86-64

`vg_rsa_pkcs1_encrypt_precomputed(out, out_len, n, n_len, e, e_len, msg,
msg_len, ps, ps_len, scratch, scratch_len, pre, pre_len)`: `Encrypt.code`,
with the precomputed modulus `pre` (the stack arguments 6 and 7) in place of
`n` for the public operation, `vg_rsa_public_precomputed_checked` or one of
its variants. The mask after the call does not branch on its result.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.X86_64.Precomputed

open VG VG.X86_64 Encrypt

/-- The original arguments of the public operation, then `pre` and
`pre_len` in place of `n` and `n_len`. -/
def callArgs : List Instr := Encrypt.callArgs ++
  ([.mov .rdx (.mem (arg 6)), .mov .rcx (.mem (arg 7))] : List Instr)

/-- The body of the frame. -/
def body (pubName : String) (pub : Prog isa) : Prog isa :=
  .seq (.block setup) (.seq psLoop (.seq (.block sep) (.seq msgCopy (.seq (.block callArgs)
    (.seq (.call pubName pub) (.seq (.block maskArgs) (.seq maskLoop (.block [.mov .rax (.reg .r11)]))))))))

/-- `vg_rsa_pkcs1_encrypt_precomputed`, calling an implementation of
`vg_rsa_public_precomputed_checked`'s code `pub` by its name. -/
def code (pubName : String) (pub : Prog isa) : Prog isa :=
  .frame (.alloc frameBytes) (body pubName pub) (.free frameBytes)

end VG.Impl.RsaPkcs1Enc.X86_64.Precomputed
