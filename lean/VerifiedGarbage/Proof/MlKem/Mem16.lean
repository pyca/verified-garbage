module

public import VerifiedGarbage.Spec.MlKem.Kpke16
public import VerifiedGarbage.Proof.MlKem.Arith

/-!
# ML-KEM: polynomials stored with `w`-bit coefficients

The coefficients of `polyAtW` (`polyAtW_get`), and a stored polynomial from
its coefficients (`polyIsW_of_toNat`), as `Mem.lean` has them for `[u32; 256]`.
-/

@[expose] public section

namespace VG.Proof.MlKem

open VG.Spec.MlKem

theorem polyAtW_get (w : Nat) (m : Mem) (p : Addr) {i : Nat} (hi : i < n) :
    (polyAtW w m p)[i]! = ofNat (coeffAtW w m p i).toNat := by
  rw [getElem!_eq _ hi]
  simp only [polyAtW, Vector.getElem_ofFn]

/-- `f` is stored at `p` with `w`-bit coefficients if each of its
coefficients is. -/
theorem polyIsW_of_toNat {w : Nat} {m : Mem} {p : Addr} {f : Poly}
    (h : ∀ i < n, (coeffAtW w m p i).toNat = (f[i]!).val) : PolyIsW w m p f := by
  refine ⟨fun i hi => by rw [h i hi]; exact (f[i]!).isLt, ext_getElem! fun i hi => ?_⟩
  rw [polyAtW_get _ _ _ hi, h i hi, ofNat_val]

end VG.Proof.MlKem
