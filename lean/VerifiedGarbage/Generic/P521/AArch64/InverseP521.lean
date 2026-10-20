module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.InverseVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# P-521's inversions modulo `p` and `n` on AArch64

`vg_p521_inv_mod_p` and `vg_p521_inv_mod_n` (`Spec/Weierstrass/Inverse.lean`),
which the signature, the public key derivation, verification and ECDH call.
A generic file (see `TCB/Emit.lean`) over P-521's group law and inversions
`h`, the variant `Variants/P521/AArch64/Law.lean`, whose inversions'
soundness the proofs take.
-/

@[expose] public section

namespace VG.Generic.P521.AArch64.InverseP521

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P521.Inverse

/-- What the functions run. -/
def note (mod : String) : String :=
  "The function keeps `x19` and `x21` to `x25` in bytes 5704 to 5751 of `ws` while it runs, \
  and computes the inverse modulo `" ++ mod ++ "` by Bernstein and Yang's divsteps, in batches \
  of 59 (23 batches for nine words), each run on the low words of `f` and `g` and applied to \
  `f`, `g` and the numbers `d`, `e` by the batch's matrix, in its working area at bytes 5056 to \
  5703, then multiplies by a constant (`2^(5 B) R³ mod " ++ mod ++ "`) to return to Montgomery \
  form, by word-by-word Montgomery multiplication with `mul` and `umulh`, its temporary area at \
  bytes 4024 to 4095; nothing depends on the numbers but through masks and `csel`."

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvOrd Spec.P521.curve) : List Artifact := [
  C.invPApi.artifact AArch64.target {
    notes := [note "p"]
    code := p521.invFn p521.pPowI
    verified := p_verified h.inv },
  C.invNApi.artifact AArch64.target {
    notes := [note "n"]
    code := p521.invFn p521.nPowI
    verified := n_verified h.inv }]

end VG.Generic.P521.AArch64.InverseP521
