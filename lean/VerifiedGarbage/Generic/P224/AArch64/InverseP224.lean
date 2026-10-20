module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.InverseVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# P-224's inversions modulo `p` and `n` on AArch64

`vg_p224_inv_mod_p` and `vg_p224_inv_mod_n` (`Spec/Weierstrass/Inverse.lean`),
which the signature, the public key derivation, verification and ECDH call.
A generic file (see `TCB/Emit.lean`) over P-224's group law and inversions
`h`, the variant `Variants/P224/AArch64/Law.lean`, whose inversions'
soundness the proofs take.
-/

@[expose] public section

namespace VG.Generic.P224.AArch64.InverseP224

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P224.Inverse

/-- What the functions run. -/
def note (mod : String) : String :=
  "The function keeps `x19` in bytes 2584 to 2591 of `ws` while it runs, and computes the \
  inverse modulo `" ++ mod ++ "` by Bernstein and Yang's divsteps, in batches of 59 (10 batches \
  for four words), each run on the low words of `f` and `g` and applied to `f`, `g` and the \
  numbers `d`, `e` by the batch's matrix, in its working area at bytes 2296 to 2583, then \
  multiplies by a constant (`2^(5 B) R³ mod " ++ mod ++ "`) to return to Montgomery form, by \
  word-by-word Montgomery multiplication with `mul` and `umulh`, its temporary area at bytes \
  128 to 159; nothing depends on the numbers but through masks and `csel`."

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P224.curve) : List Artifact := [
  C.invPApi.artifact AArch64.target {
    notes := [note "p"]
    code := p224.invFn p224.pPowI
    verified := p_verified h.inv },
  C.invNApi.artifact AArch64.target {
    notes := [note "n"]
    code := p224.invFn p224.nPowI
    verified := n_verified h.inv }]

end VG.Generic.P224.AArch64.InverseP224
