import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Mul
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombLit
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedVerified
import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr

/-!
# Ed25519's fixed-base multiplication with AVX512_IFMA: `Verified`

`scalarBase_ifma` is `scalarBase_precomputed adx` with the comb
`Zmm.combMultiply` (`zcomb_ok`; constant time by taint tracking, the
static's address public): correctness from the engine's (`scalarBaseEngineOf_ok`),
MXCSR's control bits kept, as the comb loads MXCSR only between saving it in
`r11` and loading it back (`ctlOk`), and the shared contract.
-/

namespace VG.Proof.Ed25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519.X86_64

/-- The comb with AVX512_IFMA. -/
theorem combOk : CombOk (Impl.Ed25519.X86_64.Zmm.combMultiply Impl.X25519.X86_64.adx) :=
  ⟨fun hs hS _ hb ht hfar => Zmm.zcomb_ok hs hS hb ht hfar,
    fun _ hp => taintSymFld (Taint.ofRegs [.rdi]) hp (by exact ⟨_, by taint_decide⟩)⟩

theorem scalarBase_ifma_ok [X25519.X86_64.DivstepInv] (s : State) (hs : scalarBaseLocal.pre s) :
    ∃ t s', Exec isa scalarBase_ifma s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := scalarBase_correct_of_engine _
    (fun hs hp hr hd ht hfar => scalarBaseEngineOf_ok (fld := Impl.X25519.X86_64.adx) combOk hs hp hr hd ht hfar) hs
  exact ⟨t, s', he, abiPreserved_of_ctl (by lit_decide) he h.1, h.2⟩

theorem scalarBase_ifma_ct [X25519.X86_64.DivstepInv] : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase_ifma :=
  scalarBase_ct_of_engine _ (fun hs hp hr hd ht hfar => scalarBaseEngineOf_ok (fld := Impl.X25519.X86_64.adx) combOk hs hp hr hd ht hfar)
    (scalarBaseEngineOf_ct (fld := Impl.X25519.X86_64.adx) combOk)

theorem scalarBase_ifma_verified [X25519.X86_64.DivstepInv] : Verified X86_64.target scalarBase_ifma
    (Spec.Ed25519.scalarBaseContract (X86_64.abi.withConsts combConsts)) :=
  Verified.of_correct scalarBase_ifma_ok scalarBase_ifma_ct scalarBase_implies

end VG.Proof.Ed25519.X86_64.Ifma
