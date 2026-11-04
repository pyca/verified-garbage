module

public import VerifiedGarbage.Impl.RsaOaep.AArch64

/-!
# RSAES-OAEP encryption with a precomputed public key on AArch64

`vg_rsa_oaep_<H>_mgf1_encrypt_precomputed(out, out_len, n, n_len, e,
e_len, label, label_len, msg, msg_len, seed, scratch, scratch_len, pre,
pre_len, mgf1)`: RSAES-OAEP encryption (`Impl/RsaOaep/AArch64.lean`), with
the precomputed modulus `pre` (the stack arguments 5 and 6) in place of `n`
(`x2`, `x3`) for the public operation, `vg_rsa_public_precomputed_checked`
or one of its variants, whose result it returns, and MGF1 over the hash
function of the table `mgf1` (the stack argument 7, `mgfT`).
-/

@[expose] public section

namespace VG.Impl.RsaOaep.AArch64.Precomputed

open VG VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs)
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)

/-- The original arguments of the public operation, then `pre` and
`pre_len` in place of `n` and `n_len`. -/
def pubArgs : List Instr := AArch64.pubArgs ++ ([.ldrSp .x2 (arg 6), .ldrSp .x3 (arg 7)] : List Instr)

variable (H : Hash) (f : Fns) (pubN : String) (pubC : Prog isa)

/-- After the checks. -/
def encMain : Prog isa :=
  seqs [encEm H f, .block (dbArgs H), mgfT f 9, .block (seedArgs H), mgfT f 9, .block pubArgs,
    .call pubN pubC]

/-- `vg_rsa_oaep_encrypt_precomputed`, with the label's hash function the
table that is its stack argument 8 (`hash`, after the 16 words of
`encryptTablesSig`'s other parameters) and MGF1's the table that is its
stack argument 9 (`mgf1`). -/
def encrypt : Prog isa :=
  .frame (.push .x30) (.frame (.alloc frameBytes) (encBodyWith (fun d => encMain (ofLen d) f pubN pubC))
    (.free frameBytes)) (.pop .x30)

end VG.Impl.RsaOaep.AArch64.Precomputed
