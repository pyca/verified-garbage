import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSchedule

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

def regs (i : Nat) : Vector VReg 8 := Vector.ofFn fun k => (before i).regs[k.val]!

def leftSide (i k : Nat) : Prop :=
  2*steps[i]!.1*steps[i]!.2≤k ∧ k<2*steps[i]!.1*steps[i]!.2+steps[i]!.1
instance (i k : Nat) : Decidable (leftSide i k) := inferInstanceAs (Decidable (_ ∧ _))
def rightSide (i k : Nat) : Prop :=
  2*steps[i]!.1*steps[i]!.2+steps[i]!.1≤k ∧ k<2*steps[i]!.1*steps[i]!.2+2*steps[i]!.1
instance (i k : Nat) : Decidable (rightSide i k) := inferInstanceAs (Decidable (_ ∧ _))

def leftSource (i : Nat) (k : Fin 8) : Fin 8 :=
  ⟨(if rightSide i k.val then k.val-steps[i]!.1 else k.val)%8,Nat.mod_lt _ (by decide)⟩
def rightSource (i : Nat) (k : Fin 8) : Fin 8 :=
  ⟨(if leftSide i k.val then k.val+steps[i]!.1 else k.val)%8,Nat.mod_lt _ (by decide)⟩
def stagePair (i k : Nat) : PairRegs := (stagePairs i)[k%steps[i]!.1]!
def stageClobs (i : Nat) : List VReg :=
  pairWrites (stagePairs i) ++ (stageProducts i).map Prod.snd ++ (stageProducts i).map Prod.fst

def stageValues (i : Nat) (v : Vector (BitVec 128) 8) (z : Nat → Int) : Vector (BitVec 128) 8 :=
  Vector.ofFn fun k =>
    if leftSide i k.val then VArr.s4.map2 (fun _ a b => a+b) v[(leftSource i k).val] v[(rightSource i k).val]
    else if rightSide i k.val then fastVector
      (VArr.s4.map2 (fun _ a b => a-b) v[(leftSource i k).val] v[(rightSource i k).val]) z
    else v[k.val]

/-- Finite register-geometry certificate, independent of coefficient values. -/
theorem stage_geometry (i : Fin 7) (k : Fin 8) :
    if leftSide i.val k.val then
      stagePair i.val k.val∈stagePairs i.val ∧
      (regs (i.val+1))[k.val]=(stagePair i.val k.val).left ∧
      (stagePair i.val k.val).left=(regs i.val)[(leftSource i.val k).val] ∧
      (stagePair i.val k.val).right=(regs i.val)[(rightSource i.val k).val]
    else if rightSide i.val k.val then
      stagePair i.val k.val∈stagePairs i.val ∧
      (regs (i.val+1))[k.val]=(stagePair i.val k.val).free ∧
      (stagePair i.val k.val).left=(regs i.val)[(leftSource i.val k).val] ∧
      (stagePair i.val k.val).right=(regs i.val)[(rightSource i.val k).val]
    else (regs (i.val+1))[k.val]=(regs i.val)[k.val] ∧ (regs i.val)[k.val]∉stageClobs i.val := by
  revert i k
  decide +kernel

/-- One concrete renamed group updates the logical bank exactly, regardless
of its initial representatives. -/
theorem stage_ok (i : Fin 7) {v : Vector (BitVec 128) 8}
    {s : State} {rest : List Instr} {Q : State → Prop} {z : Nat → Int}
    (hbank : Bank s (regs i.val) v)
    (hz : ∀ e<4, 0≤z e ∧ z e<8380417)
    (hzw : ∀ e<4, vword (s.v .v20) e=BitVec.ofInt 32 (z e))
    (hbw : ∀ e<4, vword (s.v .v21) e=BitVec.ofInt 32 (reciprocal (z e)))
    (hqw : ∀ e<4, vword (s.v .v31) e=8380417#32)
    (k : ∀ t, VChg (stageClobs i.val) s t →
      Bank t (regs (i.val+1)) (stageValues i.val v z) → WP isa (.block rest) t Q) :
    WP isa (.block ((stagePairs i.val).flatMap PairRegs.code ++ multiplyCode (stageProducts i.val) ++ rest)) s Q := by
  refine batch_ok _ _ (stage_shape i) hz hzw hbw hqw fun t ht hv => k t ht ?_
  intro j
  have hg := stage_geometry i j
  change t.v (regs (i.val+1))[j.val] = (stageValues i.val v z)[j.val]
  simp only [stageValues,Vector.getElem_ofFn]
  by_cases hl : leftSide i.val j.val
  · rw [ite_eq_left hl] at hg ⊢
    rw [hg.2.1,(hv _ hg.1).1,hg.2.2.1,hg.2.2.2,hbank (leftSource i.val j),hbank (rightSource i.val j)]
  · rw [ite_eq_right hl] at hg ⊢
    by_cases hr : rightSide i.val j.val
    · rw [ite_eq_left hr] at hg ⊢
      rw [hg.2.1,(hv _ hg.1).2,hg.2.2.1,hg.2.2.2,hbank (leftSource i.val j),hbank (rightSource i.val j)]
    · rw [ite_eq_right hr] at hg ⊢
      rw [hg.1,ht.get _ hg.2,hbank j]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
