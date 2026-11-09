module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.LookupCode
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Lit

/-! The final digit reuses the exact main-loop constant-time affine lookup. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.P521Native

def finishLookupCode : List Instr := (outerBlock152.drop 209).take 693

theorem finish_lookup_source : finishLookupCode=(outerBlock142.drop 54).take 693 := by lit_decide

theorem finish_vector_lookup_source : (outerBlock152.drop 231).take 564=lookupCode := by lit_decide

/-- Any machine contract for the full main-loop nibble/lookup/sign-selection
phase applies to the final digit unchanged; its public index is zero. -/
theorem finish_lookup_wp {s : State} {Q : State → Prop}
    (h : WP isa (.block ((outerBlock142.drop 54).take 693)) s Q) :
    WP isa (.block finishLookupCode) s Q := by
  rw [finish_lookup_source]
  exact h

end VG.Proof.Weierstrass.AArch64.P521Native
