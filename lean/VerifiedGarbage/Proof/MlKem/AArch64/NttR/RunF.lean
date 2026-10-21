module

public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.RunW
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.LitF
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sound
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttR.RunW
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttR.LitF
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# ML-KEM on AArch64: the run of `vg_mlkem16_ntt` (mlkem-native's schedule)

The regions of `fwdFast` (`rsF`: the polynomial at `x0`, and its table of
zetas), the terms it starts from (`initF`: coefficient `p` of the input in
halfword `p`, the table's halfwords as constants), and the check, by the
kernel, that the run leaves the reduced coefficients of `NTT` in the
polynomial (`checkF_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Impl.MlKem.AArch64.Ntt16.Fast

def rsF : List Rg :=
  [⟨.reg .x0, 0, 32, true⟩, ⟨.sym name, 0, 58, false⟩]

/-- Nothing followed but the pointer to the polynomial. -/
def initF : St := (⟨0, 0, [fInW, tabFT]⟩ : St).setG .x0 (.ptr 0 0)

theorem checkF_ok : (initF.runP fwdRules rsF 16 fwdFast).elim false outW = true := by
  lit_decide

theorem initF_f : ∀ j < 32, ∀ e < 8, (initF.chunk 0 j).get e = lvT 0 (8 * j + e) := by decide +kernel

/-- Lane `e` of chunk `j` of halfwords packed by `packH`. -/
theorem packH_get {L : List Nat} {j e : Nat} (he : e < 8) (h : 8 * j + e < L.length) :
    Y.get (slot yw (packH L) j) e = cT (L.getD (8 * j + e) 0) := by
  show slot tw (slot (tw * 8) (packH L) j) e = _
  rw [slot_slot _ _ _ _ _ he, packH, slot_foldr cT (fun h => Nat.lt_trans (mk_lt _ _ _ _ _) (by decide)) _ _
    (by omega)]

theorem tab_length : tab.length = 464 := by rw [tab.lit_eq]; decide +kernel

theorem initF_t {j e : Nat} (hj : j < 58) (he : e < 8) :
    (initF.chunk 1 j).get e = cT (tab.getD (8 * j + e) 0) :=
  packH_get he (by rw [tab_length]; omega)

end VG.Proof.MlKem.AArch64.NttR
