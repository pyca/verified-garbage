module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.InverseVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# secp256k1's inversions modulo `p` and `n` on AArch64

`vg_secp256k1_inv_mod_p` and `vg_secp256k1_inv_mod_n` (`Spec/Weierstrass/Inverse.lean`),
which the signature, the public key derivation, verification and ECDH call.
A generic file (see `TCB/Emit.lean`) over secp256k1's group law and inversions
`h`, the variant `Variants/Secp256k1/AArch64/Law.lean`, whose inversions'
soundness the proofs take.
-/

@[expose] public section

namespace VG.Generic.Secp256k1.AArch64.InverseSecp256k1

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.Secp256k1.Inverse

/-- What the functions run. -/
def note (mod : String) : String :=
  "The function keeps `x19` in bytes 2584 to 2591 of `ws` while it runs, and computes the \
  inverse modulo `" ++ mod ++ "` by Bernstein and Yang's divsteps, in batches of 59 (10 batches \
  for four words), each run on the low words of `f` and `g` and applied to `f`, `g` and the \
  numbers `d`, `e` by the batch's matrix, in its working area at bytes 2296 to 2583, then \
  multiplies by a constant (`2^(5 B) R³ mod " ++ mod ++ "`) to return to Montgomery form, by \
  word-by-word Montgomery multiplication with `mul` and `umulh`, its temporary area at bytes \
  128 to 159; nothing depends on the numbers but through masks and `csel`."

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.Secp256k1.curve) : List Artifact := [
  C.invPApi.artifact AArch64.target {
    notes := [note "p"]
    code := secp256k1.invFn secp256k1.pPowI
    verified := p_verified h.inv },
  C.invNApi.artifact AArch64.target {
    notes := [note "n"]
    code := secp256k1.invFn secp256k1.nPowI
    verified := n_verified h.inv }]

end VG.Generic.Secp256k1.AArch64.InverseSecp256k1
