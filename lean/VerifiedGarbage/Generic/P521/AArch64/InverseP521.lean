module

import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.InverseVerified
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.AArch64.Lit

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

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P521.curve) : List Artifact := [
  { C.invPApi with
    target := AArch64.target
    doc := C.invPApi.doc (notes := [note "p"])
    code := p521.invFn p521.pPowI
    contract := C.invPContract AArch64.abi
    ofSig := by exact (⟨_, _, _, by
      unfold Spec.Weierstrass.Inverse.Curve.invPContract Spec.Weierstrass.Inverse.Curve.invContract
      rfl⟩)
    verified := p_verified h.inv
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { C.invNApi with
    target := AArch64.target
    doc := C.invNApi.doc (notes := [note "n"])
    code := p521.invFn p521.nPowI
    contract := C.invNContract AArch64.abi
    ofSig := by exact (⟨_, _, _, by
      unfold Spec.Weierstrass.Inverse.Curve.invNContract Spec.Weierstrass.Inverse.Curve.invContract
      rfl⟩)
    verified := n_verified h.inv
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.P521.AArch64.InverseP521
