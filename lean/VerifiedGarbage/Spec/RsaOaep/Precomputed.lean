module

public import VerifiedGarbage.Spec.RsaOaep.Contract

/-!
# RSAES-OAEP encryption with a precomputed public key: its parameters

**Trusted** (as every file in `Spec/`). The parameters of encryption with
the modulus' `Rsa.publicPrecompute` values (`encryptPrecomputedSig`), which
`Spec/RsaOaep/Table.lean`'s contract takes, so that implementations can
reuse key setup and call `vg_rsa_public_precomputed_checked` and its
variants.
-/

@[expose] public section

namespace VG.Spec.RsaOaep

open Mgf1 (Hash)
variable (H : Hash)

/-- The parameters of encryption: `(out: *mut u8, out_len: usize,
n: *const u8, n_len: usize, e: *const u8, e_len: usize, label: *const u8,
label_len: usize, msg: *const u8, msg_len: usize, seed: *const [u8; hLen],
scratch: *mut u64, scratch_len: usize, pre: *const u64, pre_len: usize)
-> u32`, with `pre` the modulus' precomputed `u64` words. -/
def encryptPrecomputedSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("n", .slice false .u8 "n_len"),
    ("e", .slice false .u8 "e_len"), ("label", .slice false .u8 "label_len"),
    ("msg", .slice false .u8 "msg_len"), ("seed", .array false .u8 H.len),
    ("scratch", .slice true .u64 "scratch_len"), ("pre", .slice false .u64 "pre_len")]
  ret := some .u32

end VG.Spec.RsaOaep
