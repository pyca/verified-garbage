module

public import VerifiedGarbage.Impl.RsaOaep.X86_64

/-!
# RSAES-OAEP encryption with a precomputed public key on x86-64

`vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed(out, out_len, n, n_len, e,
e_len, label, label_len, msg, msg_len, seed, scratch, scratch_len, pre,
pre_len)`: `encrypt`, with the precomputed modulus `pre` (the stack
arguments 7 and 8) in place of `n` for the public operation,
`vg_rsa_public_precomputed_checked` or one of its variants, whose result it
returns.
-/

@[expose] public section

namespace VG.Impl.RsaOaep.X86_64.Precomputed

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Impl.Mgf1.X86_64 (seqs mgfXor)

/-- The original arguments of the public operation, then `pre` and
`pre_len` in place of `n` and `n_len`. -/
def pubArgs : List Instr := X86_64.pubArgs ++
  ([.mov .rdx (.mem (arg 7)), .mov .rcx (.mem (arg 8))] : List Instr)

variable (H G : Stream) (pubN : String) (pubC : Prog isa)

/-- After the checks. -/
def encMain : Prog isa :=
  seqs [encEm H, .block (dbArgs H), mgfXor lay G, .block (seedArgs H), mgfXor lay G, .block pubArgs,
    .call pubN pubC]

/-- `vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed`. -/
def encrypt : Prog isa :=
  .frame (.alloc frameBytes) (encBodyWith H (encMain H G pubN pubC)) (.free frameBytes)

end VG.Impl.RsaOaep.X86_64.Precomputed
