module

public import VerifiedGarbage.Proof.MlKem.X86_64.Lazy
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ML-KEM on x86-64: the butterflies of the lazy layers

`vibflyL` does exactly what `invW` does to the words of `xmm0` and `xmm1`, with the zetas of `xmm13` (`VBflyOk` with the words
themselves as values).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

theorem zw_lane {x : BitVec 128} {ζ : Nat → Zq} (h : ZLanes x ζ) {i : Nat} (hi : i < 8) : word x i = zw (ζ i) :=
  BitVec.eq_of_toNat_eq (by rw [h i hi, zw_toNat])

theorem vibflyL_spec : VBflyOk (· = ·) vibflyL invW := by
  intro s hc x y ζ hx hy hz
  have hx' : ∀ i < 8, word (s.xmm .xmm0) i = x i := hx
  have hy' : ∀ i < 8, word (s.xmm .xmm1) i = y i := hy
  rw [vibflyL, WP.block_append_iff]
  simp only [xmov, xb]
  vrun
  refine WP.mono (vmont_ok (d := .xmm3) (z := .xmm13) (t := .xmm2) (by decide) (by decide) (by decide)
    (by decide) (by decide) (((hc.setXmm (d := .xmm3) (by decide) (by decide) _).setXmm (d := .xmm3) (by decide)
      (by decide) _).setXmm (d := .xmm0) (by decide) (by decide) _)) fun s2 ⟨l2, o2⟩ => ?_
  refine ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
  · show word _ i = _
    rw [o2.xmm _ (by decide)]
    simp only [xmm_setXmm, ifp, reduceCtorEq, ite_false]
    rw [word_paddw _ _ hi, hx' i hi, hy' i hi]; rfl
  · show word _ i = _
    rw [l2 i hi]
    simp only [xmm_setXmm, reduceCtorEq, ite_true, ite_false]
    rw [word_psubw _ _ hi, word_movdqa, hx' i hi, hy' i hi, zw_lane hz hi]; rfl
  · exact ((XOnly.setXmm (by simp) (XOnly.setXmm (by simp) (XOnly.setXmm (by simp)
      (XOnly.refl [.xmm3, .xmm0] s) _) _) _).trans o2).mono (by simp)

end VG.Proof.MlKem.X86_64
