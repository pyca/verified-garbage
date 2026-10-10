import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedVerified
import VerifiedGarbage.Proof.Ed25519.X86_64.CombSelectY

/-!
# Ed25519's fixed-base multiplication with BMI2 and ADX: `Verified`

`scalarBase_adx` is `scalarBase_precomputed adx` with the comb's entries selected with AVX2
(`combSelectY`): the comb is `combMultiplyWith_ok`'s with `combSelectY_sel` (constant time by
taint tracking, the static's address public), and the rest as `scalarBase_precomputed_okI`, with
`vg_gf25519_r64_invert` inlined.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

/-- The comb with BMI2 and ADX, its entries selected with AVX2. -/
theorem combOkY : CombOk (combMultiply Impl.X25519.X86_64.adx combSelectY (Point64.bodies Impl.X25519.X86_64.adx)) :=
  ⟨fun hs hS hd hb ht hfar => combMultiplyWith_ok (fld := Impl.X25519.X86_64.adx) combSelectY_sel hs hS hd hb
      ht hfar,
    fun _ hp => taintSymFld (Taint.ofRegs [.rdi]) hp (by exact ⟨_, by taint_decide⟩)⟩

theorem combY_inline : (combMultiply Impl.X25519.X86_64.adx combSelectY).inline =
    combMultiply Impl.X25519.X86_64.adx combSelectY (Point64.bodies Impl.X25519.X86_64.adx) := rfl

theorem scalarBase_adx_okI [X25519.X86_64.DivstepInv] (s : State) (hs : scalarBaseLocal.pre s) :
    ∃ t s', Exec isa scalarBase_adx.inline s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := scalarBase_correct_of_engine _
    (fun hs hp hr hd ht hfar => scalarBaseEngineOf_ok (fld := Impl.X25519.X86_64.adx) combOkY combY_inline
      hs hp hr hd ht hfar) hs
  rw [← scalarBaseWith_inline] at he
  exact ⟨t, s', he, abiPreserved_of_exec (by rw [Code.allInstrs_inline]; lit_decide) he h.1, h.2⟩

theorem scalarBase_adx_ctI [X25519.X86_64.DivstepInv] :
    ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase_adx.inline := by
  rw [scalarBase_adx, scalarBaseWith_inline]
  exact scalarBase_ct_of_engine _ (fun hs hp hr hd ht hfar =>
      scalarBaseEngineOf_ok (fld := Impl.X25519.X86_64.adx) combOkY combY_inline hs hp hr hd ht hfar)
    (scalarBaseEngineOf_ct (fld := Impl.X25519.X86_64.adx) combOkY combY_inline)

theorem scalarBase_adx_ok [X25519.X86_64.DivstepInv] :
    ∀ s, scalarBaseLocal.clear.pre s → ∃ t s', Exec isa scalarBase_adx s t s' ∧ abiPreserved s s' ∧
      scalarBaseLocal.post s s' :=
  ok_of_inline (by lit_decide) scalarBase_adx_okI scalarBase_patch

theorem scalarBase_adx_ct [X25519.X86_64.DivstepInv] :
    ConstantTime isa scalarBaseLocal.clear.pre scalarBaseLocal.pub scalarBase_adx :=
  ct_of_inline (by lit_decide) (fun s h => let ⟨t, s', e, _⟩ := scalarBase_adx_okI s h; ⟨t, s', e⟩)
    (fun _ _ h => h.1) scalarBase_adx_ctI

theorem scalarBase_adx_verified [X25519.X86_64.DivstepInv] : Verified X86_64.target scalarBase_adx
    (Spec.Ed25519.scalarBaseContract (X86_64.abi.withConsts combConsts) 8) :=
  scalarBase_verified_of (by lit_decide) scalarBase_adx_okI scalarBase_adx_ctI

end VG.Proof.Ed25519.X86_64
