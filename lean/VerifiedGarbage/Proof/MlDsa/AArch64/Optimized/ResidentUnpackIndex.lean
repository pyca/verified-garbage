import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentUnpack
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask

/-- The third input vector overlaps the preceding input rather than reading
past a 16-field group. -/
def tableOffset (d i : Nat) : Nat := if i < 32 then i else i+2*d-48

def indexCorrect (d : Nat) : Prop :=
  ∀ g < 4, ∀ e < 16,
    let ix := (Unpack.indices d g)[e]!
    (e%4 < 3 → ix < 48 ∧ tableOffset d ix = d*(4*g+e/4)/8+e%4 ∧ tableOffset d ix < 2*d) ∧
    (e%4 = 3 → ix = 255)

/-- Finite shuffle certificates cover all input byte indices of both widths. -/
theorem indexCorrect18 : indexCorrect 18 := by unfold indexCorrect; decide +kernel
theorem indexCorrect20 : indexCorrect 20 := by unfold indexCorrect; decide +kernel

theorem indexCorrect_of_width {d : Nat} (hd : d=18 ∨ d=20) : indexCorrect d := by
  rcases hd with rfl | rfl
  · exact indexCorrect18
  · exact indexCorrect20

/-- Each vector multiply aligns the field before a uniform right shift. -/
theorem fieldShift_bounds {d g e : Nat} (hd : d=18 ∨ d=20) :
    d*(4*g+e)%8 = d*e%8 ∧ d+d*e%8 ≤ 24 ∧
    d*e%8 ≤ (if d=20 then 4 else 6) := by
  rcases hd with rfl | rfl <;> simp only [ite_true,ite_eq_right (by decide : ¬ (18:Nat)=20)] <;> omega
end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
