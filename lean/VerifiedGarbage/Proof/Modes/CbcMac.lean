module

public import VerifiedGarbage.Proof.Modes.Steps
public import VerifiedGarbage.Impl.Modes.CbcMac
public import VerifiedGarbage.Spec.Cmac

/-!
# CBC-MAC, one step at a time, for any target

`Mode.cbcMac` computes `cbcMacF` (`cbcMac_computes`): each step leaves its
data block as it was and makes `CIPH_K(Mⱼ ⊕ C)` the chaining value. So a run
leaves the data as they were and its chaining value is CMAC's chaining of
the blocks (`cbcMac_run`, `Spec.Cmac.chain`). Nothing here depends on a
target.
-/

@[expose] public section

namespace VG.Proof.Modes

open VG VG.Impl.Modes
open VG.Spec.Cbc (Cipher xor)

/-- CBC-MAC: the data block unchanged, `CIPH_K(Mⱼ ⊕ C)` the next chaining
value. -/
def cbcMacF (ciph : Cipher) : StepFn := fun c x => (x, ciph (xor x c))

theorem cbc_xor_comm (x y : List Byte) : Spec.Cbc.xor x y = Spec.Cmac.xor y x := by
  simp only [Spec.Cbc.xor, Spec.Cmac.xor]
  rw [List.zipWith_comm]
  simp only [BitVec.xor_comm]

/-- A run leaves the blocks as they were, and chains them as CMAC does. -/
theorem cbcMac_run (ciph : Cipher) : ∀ (c : List Byte) (xs : List (List Byte)),
    (run (cbcMacF ciph) c xs).1 = xs ∧ (run (cbcMacF ciph) c xs).2 = Spec.Cmac.chain ciph c xs
  | _, [] => ⟨rfl, rfl⟩
  | c, x :: xs => by
    obtain ⟨h1, h2⟩ := cbcMac_run ciph (ciph (xor x c)) xs
    refine ⟨by simp only [run, cbcMacF, h1], ?_⟩
    simp only [run, cbcMacF]
    rw [h2, cbc_xor_comm]; rfl

section
variable {bw : Nat} {ciph : Cipher} (hc : ∀ b, (ciph b).length = 4 * bw)
include hc

theorem cbcMac_computes : Computes (Mode.cbcMac bw) (4 * bw) ciph (cbcMacF ciph) := by
  intro a
  have hb : rd (applyOps (Mode.cbcMac bw).pre a) .buf (4 * bw) = xor (rd a .dat (4 * bw)) (rd a .chn (4 * bw)) :=
    rd_eq (by simp [xor_length, rd_length]) fun i hi => by
      simp only [Mode.cbcMac, xorBlk_apply, true_and, hi, ite_true]
      rw [getD_xor (by simpa [rd_length]) (by simpa [rd_length]), getD_rd hi, getD_rd hi]
  simp only [stepA, Mode.cbcMac, cbcMacF] at hb ⊢
  refine ⟨rd_eq (rd_length _ _ _) fun i hi => ?_, rd_eq (hc _) fun i hi => ?_⟩
  · rw [copyBlk_apply (by decide), ite_eq_right (by simp)]
    simp only [cryptBuf, ite_eq_right (show Loc.dat ≠ Loc.buf by decide)]
    rw [xorBlk_apply, ite_eq_right (by simp), getD_rd hi]
  · rw [copyBlk_apply (by decide), ite_eq_left ⟨rfl, hi⟩]
    simp only [cryptBuf, ite_true, hb]

end

end VG.Proof.Modes
