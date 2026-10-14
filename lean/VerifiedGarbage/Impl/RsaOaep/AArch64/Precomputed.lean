module

public import VerifiedGarbage.Impl.RsaOaep.AArch64

/-!
# RSAES-OAEP encryption with a precomputed public key on AArch64

`vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed(out, out_len, n, n_len, e,
e_len, label, label_len, msg, msg_len, seed, scratch, scratch_len, pre,
pre_len)`: `encrypt`, with the precomputed modulus `pre` (the stack
arguments 5 and 6) in place of `n` (`x2`, `x3`) for the public operation,
`vg_rsa_public_precomputed_checked` or one of its variants, whose result it
returns.
-/

@[expose] public section

namespace VG.Impl.RsaOaep.AArch64.Precomputed

open VG VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs mgfXor)

/-- The original arguments of the public operation, then `pre` and
`pre_len` in place of `n` and `n_len`. -/
def pubArgs : List Instr := AArch64.pubArgs ++ ([.ldrSp .x2 (arg 5), .ldrSp .x3 (arg 6)] : List Instr)

variable (H G : Hash) (pubN : String) (pubC : Prog isa)

/-- After the checks. -/
def encMain : Prog isa :=
  seqs [encEm H, .block (dbArgs H), mgfXor lay G, .block (seedArgs H), mgfXor lay G, .block pubArgs,
    .call pubN pubC]

/-- `vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed`. -/
def encrypt : Prog isa :=
  .frame (.push .x30) (.frame (.alloc frameBytes) (encBodyWith H (encMain H G pubN pubC)) (.free frameBytes))
    (.pop .x30)

end VG.Impl.RsaOaep.AArch64.Precomputed
