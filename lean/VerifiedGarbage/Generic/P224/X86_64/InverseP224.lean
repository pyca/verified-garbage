import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.InverseVerified

/-!
# P-224's inversions modulo `p` and `n` on x86-64

`vg_p224_inv_mod_p` and `vg_p224_inv_mod_n` (`Spec/Weierstrass/Inverse.lean`),
which the signature, the public key derivation, verification and ECDH call. A generic file (see
`TCB/Emit.lean`) over P-224's group law and inversions `h`, the variant
`Variants/P224/X86_64/Law.lean`, whose inversions' soundness the proofs take.
-/

namespace VG.Generic.P224.X86_64.InverseP224

open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P224.Inverse

/-- What the functions run. -/
def note (_ : Bool) (mod : String) : String :=
  "The function keeps `rbx`, `rbp` and `r12`–`r15` in `xmm0` to `xmm5` while it runs, and \
  computes the inverse modulo `" ++ mod ++ "` by Bernstein and Yang's divsteps, in batches of 59 \
  (10 batches for four words), each run on the low words of `f` and `g` packed into 64-bit \
  registers and applied to `f`, `g` and the numbers `d`, `e` by the batch's matrix, in its working \
  area at bytes 2296 to 2615, then multiplies by a constant (`2^(5 B) R³ mod " ++ mod ++
  "`) to return to Montgomery form, by `mul` and word-by-word Montgomery reduction; nothing \
  depends on the numbers but through masks and `cmov`."

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P224.curve) : List Artifact :=
  ([false].map fun adx =>
    { C.invPApi with
      name := C.invPApi.name ++ (if adx then "_adx" else "")
      target := X86_64.target
      doc := C.invPApi.doc (notes := [note adx "p"])
      code := (cfg adx).invFn (cfg adx).pPowI
      contract := C.invPContract X86_64.abi
      ofSig := ⟨_, _, _, by
        unfold Spec.Weierstrass.Inverse.Curve.invPContract Spec.Weierstrass.Inverse.Curve.invContract
        rfl⟩
      verified := p_verified h.inv adx
      spSafe := Code.all_of_allInstrs (show invP.allInstrs _ = true by lit_decide)
      features := if adx then ["bmi2", "adx"] else [] }) ++
  ([false].map fun adx =>
    { C.invNApi with
      name := C.invNApi.name ++ (if adx then "_adx" else "")
      target := X86_64.target
      doc := C.invNApi.doc (notes := [note adx "n"])
      code := (cfg adx).invFn (cfg adx).nPowI
      contract := C.invNContract X86_64.abi
      ofSig := ⟨_, _, _, by
        unfold Spec.Weierstrass.Inverse.Curve.invNContract Spec.Weierstrass.Inverse.Curve.invContract
        rfl⟩
      verified := n_verified h.inv adx
      spSafe := Code.all_of_allInstrs (show invN.allInstrs _ = true by lit_decide)
      features := if adx then ["bmi2", "adx"] else [] })

end VG.Generic.P224.X86_64.InverseP224
