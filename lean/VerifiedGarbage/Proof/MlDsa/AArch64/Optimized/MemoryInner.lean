import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FiveTraversal
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FiveLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemorySchedule

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

private theorem positive_toInt {x : BitVec 32} (h : x.toNat<3*8380417) :
    x.toInt=(x.toNat : Int) := by
  have ht := BitVec.toInt_eq_toNat_cond x
  split at ht <;> omega

private theorem ofInt_nat (n : Nat) : ofInt (n : Int)=ofNat n := by
  apply Fin.ext
  simp only [ofInt,ofNat,Fin.val_ofNat,← Int.natCast_emod,Int.toNat_natCast,Nat.mod_mod]

def fiveMemStep (m : Mem) (p : Addr) (u : Nat) : Mem :=
  writeBank (fiveValues (readBank m (coeffAddr p (32*u)) 16) (innerRoot u) (tailRoot u))
    (coeffAddr p (32*u)) 16 m

theorem readInner_bank {m : Mem} {p : Addr} {w : Poly} {u : Nat} (hu : u<8)
    (h : SignedPolyIs m p w (-15*8380417) (15*8380417)) :
    BankBound (readBank m (coeffAddr p (32*u)) 16) (15*8380417) ∧
      InnerBankField u (readBank m (coeffAddr p (32*u)) 16) w := by
  constructor
  · intro i e he
    rw [readBank_coeff m p (32*u) 4 i he]
    exact h.bound _ (by unfold n; omega)
  · intro i e he
    rw [readBank_coeff m p (32*u) 4 i he]
    exact h.value _ (by unfold n; omega)

theorem fiveMemStep_at (m : Mem) (p : Addr) {u : Nat} (hu : u<8) (i : Fin 8)
    {e : Nat} (he : e<4) :
    coeffAt (fiveMemStep m p u) p (32*u+4*i.val+e)=
      vword (fiveValues (readBank m (coeffAddr p (32*u)) 16) (innerRoot u) (tailRoot u))[i.val] e := by
  unfold fiveMemStep
  exact writeBank_coeff_at _ m p (start := 32*u) (step := 4) (by decide) (by omega) i he

theorem fiveMemStep_outside (m : Mem) (p : Addr) {u k : Nat} (hu : u<8) (hk : k<256)
    (ho : k/32≠u) : coeffAt (fiveMemStep m p u) p k=coeffAt m p k := by
  unfold fiveMemStep
  exact writeBank_coeff_outside _ m p (start := 32*u) (step := 4) (by omega) hk (fun i => by omega)

/-- One contiguous slice preserves the signed representation globally and
normalizes its own 32 coefficients into the positive range. -/
theorem fiveMemStep_field {m : Mem} {p : Addr} {w : Poly} {u : Nat} (hu : u<8)
    (h : SignedPolyIs m p w (-15*8380417) (15*8380417)) :
    SignedPolyIs (fiveMemStep m p u) p (Traversal.run (Traversal.innerSlice u) w)
      (-15*8380417) (15*8380417) ∧
    (∀ k<256, k/32=u → (coeffAt (fiveMemStep m p u) p k).toNat<3*8380417) := by
  have hb := readInner_bank hu h
  have hv := fiveValues_field _ w hu hb.1 hb.2
  have hAt (k : Nat) (hk : k<256) (he : k/32=u) :
      (coeffAt (fiveMemStep m p u) p k).toNat<3*8380417 ∧
      ofNat (coeffAt (fiveMemStep m p u) p k).toNat=
        (Traversal.run (Traversal.innerSlice u) w)[k]! := by
    let i : Fin 8 := ⟨k%32/4,by omega⟩
    have heq : k=32*u+4*i.val+k%4 := by dsimp only [i]; omega
    rw [heq,fiveMemStep_at m p hu i (by omega)]
    exact ⟨hv.1 i _ (by omega),hv.2 i _ (by omega)⟩
  constructor
  · constructor
    · intro k hk
      by_cases he : k/32=u
      · have hv := (hAt k hk he).1
        rw [positive_toInt hv]
        omega
      · rw [fiveMemStep_outside m p hu hk he]
        exact h.bound k hk
    · intro k hk
      by_cases he : k/32=u
      · have hv := hAt k hk he
        rw [positive_toInt hv.1,ofInt_nat]
        exact hv.2
      · rw [fiveMemStep_outside m p hu hk he,
          Traversal.run_outside _ _ _ (Traversal.inner_supported ⟨u,hu⟩) w hk he]
        exact h.value k hk
  · intro k hk he
    exact (hAt k hk he).1

end VG.Proof.MlDsa.AArch64.Optimized
