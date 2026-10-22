module

import VerifiedGarbage.Proof.MlKem.AArch64.NttR.RunF
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.LitFI
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttR.RunF
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttR.LitFI
meta import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.RunW

/-!
# ML-KEM on AArch64: the run of `vg_mlkem16_inv_ntt` (mlkem-native's schedule)

The regions of `invFast` (`rsFI`: the polynomial at `x0`, and its table of
zetas), the terms it starts from (`initFI`: coefficient `p` of the input in
halfword `p`, the table's halfwords as constants), and the check, by the
kernel, that the run leaves the reduced coefficients of `NTT⁻¹` in the
polynomial (`checkFI_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Impl.MlKem.AArch64.Ntt16.FastInv

def rsFI : List Rg :=
  [⟨.reg .x0, 0, 32, true⟩, ⟨.sym name, 0, 58, false⟩]

/-- Nothing followed but the pointer to the polynomial. -/
def initFI : St := (⟨0, 0, [fInW, tabFIT]⟩ : St).setG .x0 (.ptr 0 0)

theorem checkFI_ok : (initFI.runP fastInvRules rsFI 16 invFast).elim false outW = true := by
  lit_decide

theorem initFI_f : ∀ j < 32, ∀ e < 8, (initFI.chunk 0 j).get e = lvT 0 (8 * j + e) := by decide +kernel

theorem tabI_length : tab.length = 464 := by rw [tab.lit_eq]; decide +kernel

theorem initFI_t {j e : Nat} (hj : j < 58) (he : e < 8) :
    (initFI.chunk 1 j).get e = cT (tab.getD (8 * j + e) 0) :=
  packH_get he (by rw [tabI_length]; omega)

end VG.Proof.MlKem.AArch64.NttR
