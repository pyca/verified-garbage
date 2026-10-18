module

public import VerifiedGarbage.Impl.RsaOaep.X86_64

/-!
# RSAES-OAEP encryption with a precomputed public key on x86-64

`vg_rsa_oaep_encrypt_precomputed(out, out_len, n, n_len, e, e_len, label,
label_len, msg, msg_len, seed, seed_len, scratch, scratch_len, pre, pre_len,
hash, mgf1_hash, hash_fns, mgf1_fns)`: `encrypt`, with the precomputed modulus `pre` (the stack
arguments 8 and 9) in place of `n` for the public operation,
`vg_rsa_public_precomputed_checked` or one of its variants, whose result it
returns.
-/

@[expose] public section

namespace VG.Impl.RsaOaep.X86_64.Precomputed

open VG.X86_64
open VG.Impl.Mgf1.X86_64 (seqs mgfXor)

/-- The original arguments of the public operation, then `pre` and
`pre_len` in place of `n` and `n_len`. -/
def pubArgs : List Instr := X86_64.pubArgs ++
  ([.mov .rdx (.mem (arg 8)), .mov .rcx (.mem (arg 9))] : List Instr)

variable (pubN : String) (pubC : Prog isa)

/-- After the checks. -/
def encMain : Prog isa :=
  seqs [encEm, .block dbArgs, mgfXor lay, .block seedArgs, mgfXor lay, .block pubArgs,
    .call pubN pubC]

/-- `vg_rsa_oaep_encrypt_precomputed`. -/
def encrypt : Prog isa :=
  .frame (.alloc frameBytes) (encBodyWith (encMain pubN pubC)) (.free frameBytes)

end VG.Impl.RsaOaep.X86_64.Precomputed
