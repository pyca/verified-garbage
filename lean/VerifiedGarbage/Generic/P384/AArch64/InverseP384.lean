module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.InverseVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface

/-!
# P-384's inversions modulo `p` and `n` on AArch64

`vg_p384_inv_mod_p` and `vg_p384_inv_mod_n` (`Spec/Weierstrass/Inverse.lean`),
which the signature, the public key derivation, verification and ECDH call.
A generic file (see `TCB/Emit.lean`) over P-384's group law and inversions
`h`, the variant `Variants/P384/AArch64/Law.lean`, whose inversions'
soundness the proofs take.
-/

@[expose] public section

namespace VG.Generic.P384.AArch64.InverseP384

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P384.Inverse

/-- What the functions run. -/
def note (mod : String) : String :=
  "The function keeps `x19` in bytes 3832 to 3839 of `ws` while it runs, and computes the \
  inverse modulo `" ++ mod ++ "` by Bernstein and Yang's divsteps, in batches of 59 (15 batches \
  for six words), each run on the low words of `f` and `g` and applied to `f`, `g` and the \
  numbers `d`, `e` by the batch's matrix, in its working area at bytes 3400 to 3831, then \
  multiplies by a constant (`2^(5 B) R³ mod " ++ mod ++ "`) to return to Montgomery form, by \
  word-by-word Montgomery multiplication with `mul` and `umulh`, its temporary area at bytes \
  4048 to 4095; nothing depends on the numbers but through masks and `csel`."

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvOrd Spec.P384.curve) : List Artifact := [
  C.invPApi.artifact AArch64.target {
    notes := [note "p"]
    code := p384.invFn p384.pPowI
    verified := p_verified h.inv },
  C.invNApi.artifact AArch64.target {
    notes := [note "n"]
    code := p384.invFn p384.nPowI
    verified := n_verified h.inv }]

end VG.Generic.P384.AArch64.InverseP384
