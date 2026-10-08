import VerifiedGarbage.Proof.Divstep.BatchBasic

namespace VG.Proof.P256.EcdhInverse
open VG.Proof.Divstep

/-- Packed initial rows and all their successors fit signed63 bits. -/
def rowBounds (t : MSt) : Prop :=
  -(2^62)≤t.f ∧ t.f<2^62 ∧ -(2^62)≤t.g ∧ t.g<2^62

theorem rowBounds_step {t : MSt} (h : rowBounds t) : rowBounds (mstep t) := by
  rcases h with ⟨hf,hf',hg,hg'⟩
  unfold rowBounds mstep
  split
  · simp only
    omega
  · rcases Int.emod_two_eq_zero_or_one t.g with hz|ho
    · simp only [hz,zero_mul,add_zero]
      omega
    · simp only [ho,one_mul]
      omega

theorem rowBounds_steps {t : MSt} (h : rowBounds t) (n : Nat) : rowBounds (msteps n t) := by
  induction n with
  | zero => exact h
  | succ n ih => rw [msteps_succ]; exact rowBounds_step ih

theorem packed_initial_bounds (d : Int) {a b : Nat} (ha : a<2^20) (hb : b<2^20) :
    rowBounds (MSt.init d ((a:Int)-2^41) ((b:Int)-2^62)) := by
  unfold rowBounds MSt.init
  simp only at *
  omega

/-- The unhalved second row is still a representable signed64-bit integer. -/
theorem row_numerator_bound {t : MSt} (h : rowBounds t) :
    let z := if 0≤t.d ∧ t.g%2=1 then t.g - t.f else t.g + t.g%2*t.f;
    -(2^63)≤z ∧ z<2^63 := by
  rcases h with ⟨hf,hf',hg,hg'⟩
  dsimp only
  split
  · omega
  · rcases Int.emod_two_eq_zero_or_one t.g with hz|ho
    · simp only [hz,zero_mul,add_zero]
      omega
    · simp only [ho,one_mul]
      omega

end VG.Proof.P256.EcdhInverse
