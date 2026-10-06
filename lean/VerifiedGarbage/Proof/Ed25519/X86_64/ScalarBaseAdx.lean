import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedVerified
import VerifiedGarbage.Proof.Ed25519.X86_64.CombSelectY

/-!
# Ed25519's fixed-base multiplication with BMI2 and ADX: `Verified`

`scalarBase_adx` is `scalarBase_precomputed adx` with the comb's entries selected with AVX2
(`combSelectY`): the comb is `combMultiplyWith_ok`'s with `combSelectY_sel` (constant time by
taint tracking, the static's address public), and the rest as `scalarBase_precomputed_ok`.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

/-- The comb with BMI2 and ADX, its entries selected with AVX2. -/
theorem combOkY : CombOk (combMultiply Impl.X25519.X86_64.adx combSelectY) :=
  ⟨fun hs hS hd hb ht hfar => combMultiplyWith_ok (fld := Impl.X25519.X86_64.adx) combSelectY_sel hs hS hd hb
      ht hfar,
    fun _ hp => taintSymFld (Taint.ofRegs [.rdi]) hp (by exact ⟨_, by taint_decide⟩)⟩

theorem scalarBase_adx_ok [X25519.X86_64.DivstepInv] (s : State) (hs : scalarBaseLocal.pre s) :
    ∃ t s', Exec isa scalarBase_adx s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := scalarBase_correct_of_engine _
    (fun hs hp hr hd ht hfar => scalarBaseEngineOf_ok (fld := Impl.X25519.X86_64.adx) combOkY hs hp hr hd ht hfar) hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem scalarBase_adx_ct [X25519.X86_64.DivstepInv] :
    ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase_adx :=
  scalarBase_ct_of_engine _ (fun hs hp hr hd ht hfar =>
      scalarBaseEngineOf_ok (fld := Impl.X25519.X86_64.adx) combOkY hs hp hr hd ht hfar)
    (scalarBaseEngineOf_ct (fld := Impl.X25519.X86_64.adx) combOkY)

theorem scalarBase_adx_verified [X25519.X86_64.DivstepInv] : Verified X86_64.target scalarBase_adx
    (Spec.Ed25519.scalarBaseContract (X86_64.abi.withConsts combConsts)) :=
  Verified.of_correct scalarBase_adx_ok scalarBase_adx_ct scalarBase_implies

end VG.Proof.Ed25519.X86_64
