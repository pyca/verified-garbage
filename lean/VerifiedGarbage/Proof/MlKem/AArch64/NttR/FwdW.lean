module

public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Step
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
public import VerifiedGarbage.Proof.MlKem.Kpke16Contract
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.RunW
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Model
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Ctx
import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
import VerifiedGarbage.Proof.MlKem.Mem16

/-!
# ML-KEM on AArch64: the 16-bit NTTs of a polynomial stored with 16 bits, their inputs

The coefficients of the polynomial at `x0` (`Wi`), and those of a reduced
polynomial represent themselves (`lrep_red`), for the runs of
`vg_mlkem16_ntt` and `vg_mlkem16_inv_ntt` (`FwdF`, `InvFI`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Ntt16 (hw4 vhalf_table LRep)

/-- The input's coefficients. -/
def Wi (s₀ : State) (p : Nat) : BitVec 16 := coeffAtW 16 s₀.mem (s₀.gpr .x0) p

/-- The coefficients of a reduced polynomial represent themselves. -/
theorem lrep_red {m : Mem} {p : Addr} (h : ReducedW 16 m p) {i : Nat} (hi : i < 256) :
    LRep (coeffAtW 16 m p i) (polyAtW 16 m p)[i]! 3329 := by
  have hv := polyIsW16_toNat (⟨h, rfl⟩ : PolyIsW 16 m p (polyAtW 16 m p)) hi
  have hl : (coeffAtW 16 m p i).toNat < 3329 := h i hi
  have hz : ((polyAtW 16 m p)[i]!).val < 3329 := ((polyAtW 16 m p)[i]!).isLt
  rw [LRep, BitVec.toInt_eq_toNat_of_lt (by omega), hv]
  exact ⟨by omega, by omega, by simp⟩

end VG.Proof.MlKem.AArch64.NttR
