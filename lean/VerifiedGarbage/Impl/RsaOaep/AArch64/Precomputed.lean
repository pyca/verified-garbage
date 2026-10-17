module

public import VerifiedGarbage.Impl.RsaOaep.AArch64

/-!
# RSAES-OAEP encryption with a precomputed public key on AArch64

`vg_rsa_oaep_encrypt_precomputed(out, out_len, n, n_len, e, e_len, label,
label_len, msg, msg_len, seed, seed_len, scratch, scratch_len, pre, pre_len,
hash, mgf1_hash)`: the encryption of `Impl/RsaOaep/AArch64.lean`, with the
precomputed modulus `pre` (the stack arguments 6 and 7) in place of `n`
(`x2`, `x3`) for the public operation, `vg_rsa_public_precomputed_checked`
or one of its variants, whose result it returns. The seed's length is that
of `hash`'s values, by the precondition, so `seed_len` is not read.
-/

@[expose] public section

namespace VG.Impl.RsaOaep.AArch64.Precomputed

open VG VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs mgfXor)

/-- The original arguments of the public operation, then `pre` and
`pre_len` in place of `n` and `n_len`. -/
def pubArgs : List Instr := AArch64.pubArgs ++ ([.ldrSp .x2 (arg 6), .ldrSp .x3 (arg 7)] : List Instr)

variable (hs : List Hash) (pubN : String) (pubC : Prog isa)

/-- After the checks. -/
def encMain : Prog isa :=
  seqs [encEm hs, .block dbArgs, mgfXor lay hs, .block seedArgs, mgfXor lay hs, .block pubArgs,
    .call pubN pubC]

/-- `vg_rsa_oaep_encrypt_precomputed`. -/
def encrypt : Prog isa :=
  .frame (.push .x30) (.frame (.alloc frameBytes) (encBodyWith hs (encMain hs pubN pubC)) (.free frameBytes))
    (.pop .x30)

end VG.Impl.RsaOaep.AArch64.Precomputed
