import VerifiedGarbage.Proof.Weierstrass.X86.MontCall

/-!
# Montgomery arithmetic as functions on x86 (32-bit): the moduli

Each modulus of `Spec.Weierstrass.Mont.moduli` is one the functions support
(`FnOk`): its product's facts (`MulOk`), and code that never writes `esp`.
-/

namespace VG.Proof.Weierstrass.X86.Mont

open VG VG.X86 Spec.Weierstrass.Mont

theorem p224p_ok : FnOk p224p where
  mul := ⟨by decide, by decide +kernel, by decide +kernel⟩
  k9 := by decide
  nsMul := NoSp.of_all (by decide +kernel)
  nsAdd := NoSp.of_all (by decide +kernel)
  nsSub := NoSp.of_all (by decide +kernel)

theorem p224n_ok : FnOk p224n where
  mul := ⟨by decide, by decide +kernel, by decide +kernel⟩
  k9 := by decide
  nsMul := NoSp.of_all (by decide +kernel)
  nsAdd := NoSp.of_all (by decide +kernel)
  nsSub := NoSp.of_all (by decide +kernel)

theorem p256p_ok : FnOk p256p where
  mul := ⟨by decide, by decide +kernel, by decide +kernel⟩
  k9 := by decide
  nsMul := NoSp.of_all (by decide +kernel)
  nsAdd := NoSp.of_all (by decide +kernel)
  nsSub := NoSp.of_all (by decide +kernel)

theorem p256n_ok : FnOk p256n where
  mul := ⟨by decide, by decide +kernel, by decide +kernel⟩
  k9 := by decide
  nsMul := NoSp.of_all (by decide +kernel)
  nsAdd := NoSp.of_all (by decide +kernel)
  nsSub := NoSp.of_all (by decide +kernel)

theorem p384p_ok : FnOk p384p where
  mul := ⟨by decide, by decide +kernel, by decide +kernel⟩
  k9 := by decide
  nsMul := NoSp.of_all (by decide +kernel)
  nsAdd := NoSp.of_all (by decide +kernel)
  nsSub := NoSp.of_all (by decide +kernel)

theorem p384n_ok : FnOk p384n where
  mul := ⟨by decide, by decide +kernel, by decide +kernel⟩
  k9 := by decide
  nsMul := NoSp.of_all (by decide +kernel)
  nsAdd := NoSp.of_all (by decide +kernel)
  nsSub := NoSp.of_all (by decide +kernel)

theorem p521p_ok : FnOk p521p where
  mul := ⟨by decide, by decide +kernel, by decide +kernel⟩
  k9 := by decide
  nsMul := NoSp.of_all (by decide +kernel)
  nsAdd := NoSp.of_all (by decide +kernel)
  nsSub := NoSp.of_all (by decide +kernel)

theorem p521n_ok : FnOk p521n where
  mul := ⟨by decide, by decide +kernel, by decide +kernel⟩
  k9 := by decide
  nsMul := NoSp.of_all (by decide +kernel)
  nsAdd := NoSp.of_all (by decide +kernel)
  nsSub := NoSp.of_all (by decide +kernel)

end VG.Proof.Weierstrass.X86.Mont
