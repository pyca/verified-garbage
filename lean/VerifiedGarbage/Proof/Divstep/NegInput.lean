import VerifiedGarbage.Proof.Divstep.Batch

namespace VG.Proof.Divstep

/-- Change the simultaneous sign of the input pair, keeping its transition matrix. -/
def MSt.negInput (t : MSt) : MSt := {t with f := -t.f, g := -t.g}

theorem mstep_negInput {t : MSt} (hf : t.f%2=1) :
    mstep t.negInput=(mstep t).negInput := by
  have hg : (-t.g)%2=t.g%2 := by omega
  unfold mstep MSt.negInput
  simp only [hg]
  split
  · rename_i h
    congr 1
    dsimp only
    omega
  · rename_i h
    congr 1
    rcases Int.emod_two_eq_zero_or_one t.g with hg|hg <;> simp only [hg]
    all_goals omega

theorem msteps_negInput {t : MSt} (hf : t.f%2=1) (n : Nat) :
    msteps n t.negInput=(msteps n t).negInput := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    rw [msteps,mstep_negInput hf,ih (mstep_f_odd hf)]
    rfl

theorem msteps_init_negInput (d f g : Int) (hf : f%2=1) (n : Nat) :
    msteps n (MSt.init d (-f) (-g))=(msteps n (MSt.init d f g)).negInput :=
  msteps_negInput (t:=MSt.init d f g) hf n

end VG.Proof.Divstep
