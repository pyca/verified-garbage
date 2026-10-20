module

public import VerifiedGarbage.Impl.Modes.Ctr
public import VerifiedGarbage.Proof.Modes.Steps
import VerifiedGarbage.Proof.AesCtr.Spec
import Std.Data.DTreeMap.Internal.Balancing
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The operations of CTR meet the existing CTR specification -/

@[expose] public section

namespace VG.Proof.Modes

open VG VG.Impl.Modes VG.Spec.Cbc

/-- One counter block, encrypted and XORed with the input. -/
def ctrF (ciph : Cipher) : StepFn := fun ctr x => (xor x (ciph ctr), Spec.Ctr.inc ctr)

theorem ctr_run (ciph : Cipher) : ∀ (ctr : List Byte) (xs : List (List Byte)),
    Spec.Ctr.crypt ciph ctr xs = (run (ctrF ciph) ctr xs).1 ∧
      Spec.Ctr.next ctr xs.length = (run (ctrF ciph) ctr xs).2
  | _, [] => ⟨rfl, rfl⟩
  | ctr, x :: xs => by
    obtain ⟨h1, h2⟩ := ctr_run ciph (Spec.Ctr.inc ctr) xs
    refine ⟨?_, ?_⟩
    · simp only [Spec.Ctr.crypt, List.length_cons, Spec.Ctr.counters, List.map_cons,
        List.zipWith_cons_cons] at h1 ⊢
      rw [h1]; rfl
    · rw [List.length_cons, AesCtr.next_succ', h2]; rfl

theorem ctr_computes {ciph : Cipher} (hc : ∀ b, (ciph b).length = 16) :
    Computes Mode.ctr 16 ciph (ctrF ciph) := by
  intro a
  have hb : rd (applyOps (copyBlk 4 .buf .chn) a) .buf 16 = rd a .chn 16 :=
    rd_eq (rd_length _ _ _) fun i hi => by
      rw [copyBlk_apply (by decide), ite_eq_left ⟨rfl, hi⟩, getD_rd hi]
  let b := cryptBuf 16 ciph (applyOps (copyBlk 4 .buf .chn) a)
  have hchn : rd (applyOps (xorBlk 4 .dat .dat .buf) b) .chn 16 = rd a .chn 16 := by
    apply List.map_congr_left
    intro i hi
    rw [xorBlk_apply, ite_eq_right (by simp)]
    simp only [b, cryptBuf, reduceCtorEq, ite_false]
    rw [copyBlk_apply (by decide), ite_eq_right (by simp)]
  simp only [stepA, Mode.ctr, ctrF, applyOps_snoc]
  refine ⟨rd_eq (by simp [xor_length, rd_length, hc]) fun i hi => ?_,
    rd_eq (by simp [Spec.Ctr.inc, Spec.Ctr.ofNat]) fun i hi => ?_⟩
  · simp only [Op.apply, reduceCtorEq, false_and, ite_false]
    rw [xorBlk_apply, ite_eq_left ⟨rfl, hi⟩]
    simp only [cryptBuf, reduceCtorEq, ite_false, ite_true, hb]
    rw [copyBlk_apply (by decide), ite_eq_right (by simp),
      getD_xor (by rw [rd_length]; exact hi) (by rw [hc]; exact hi), getD_rd hi]
  · simp only [Op.apply, Op.width, ite_true, Nat.zero_add, Nat.zero_le, hi, and_self,
      Op.val, Nat.sub_zero]
    change (Spec.Ctr.inc (rd (applyOps (xorBlk 4 .dat .dat .buf) b) .chn 16)).getD i 0 = _
    rw [hchn]

end VG.Proof.Modes
