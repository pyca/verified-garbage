module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP384r1.InverseVerified
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb

/-!
# brainpoolP384r1's inversions modulo `p` and `n` on AArch64

`vg_brainpoolp384r1_inv_mod_p` and `vg_brainpoolp384r1_inv_mod_n` (`Spec/Weierstrass/Inverse.lean`),
which the signature, the public key derivation, verification and ECDH call.
A generic file (see `TCB/Emit.lean`) over brainpoolP384r1's group law and inversions
`h`, the variant `Variants/BrainpoolP384r1/AArch64/Law.lean`, whose inversions'
soundness the proofs take.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.AArch64.InverseBrainpoolP384r1

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.BrainpoolP384r1.Inverse

/-- What the functions run. -/
def note (mod : String) : String :=
  "The function keeps `x19` in bytes 3832 to 3839 of `ws` while it runs, and computes the \
  inverse modulo `" ++ mod ++ "` by Bernstein and Yang's divsteps, in batches of 59 (15 batches \
  for six words), each run on the low words of `f` and `g` and applied to `f`, `g` and the \
  numbers `d`, `e` by the batch's matrix, in its working area at bytes 3400 to 3831, then \
  multiplies by a constant (`2^(5 B) R³ mod " ++ mod ++ "`) to return to Montgomery form, by \
  word-by-word Montgomery multiplication with `mul` and `umulh`, its temporary area at bytes \
  4048 to 4095; nothing depends on the numbers but through masks and `csel`."

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.BrainpoolP384r1.curve) : List Artifact := [
  { C.invPApi with
    target := AArch64.target
    doc := C.invPApi.doc (notes := [note "p"])
    code := brainpoolp384r1.invFn brainpoolp384r1.pPowI
    contract := C.invPContract AArch64.abi
    ofSig := by exact (⟨_, _, _, by
      unfold Spec.Weierstrass.Inverse.Curve.invPContract Spec.Weierstrass.Inverse.Curve.invContract
      rfl⟩)
    verified := p_verified h.inv
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { C.invNApi with
    target := AArch64.target
    doc := C.invNApi.doc (notes := [note "n"])
    code := brainpoolp384r1.invFn brainpoolp384r1.nPowI
    contract := C.invNContract AArch64.abi
    ofSig := by exact (⟨_, _, _, by
      unfold Spec.Weierstrass.Inverse.Curve.invNContract Spec.Weierstrass.Inverse.Curve.invContract
      rfl⟩)
    verified := n_verified h.inv
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.BrainpoolP384r1.AArch64.InverseBrainpoolP384r1
