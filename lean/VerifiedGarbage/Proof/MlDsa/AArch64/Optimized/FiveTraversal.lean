import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TailValues
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FiveCore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Mem

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def innerRootIndex (u gap g : Nat) : Nat :=
  if gap=4 then 8+u else if gap=2 then 16+2*u+g else 32+4*u+g

def tailRootIndex (u g len e : Nat) : Nat :=
  if len=2 then 64+8*u+2*g+e/2 else 128+16*u+4*g+e

theorem inner_schedule (u : Nat) :
    outerSteps.flatMap (innerGroupSchedule u (innerRootIndex u)) ++
      tailSteps.flatMap (tailGroupSchedule u (tailRootIndex u))=Traversal.innerSlice u := by
  simp [outerSteps,tailSteps,innerGroupSchedule,tailGroupSchedule,innerRootIndex,tailRootIndex,
    Traversal.innerRegGroupSchedule,Traversal.packedSchedule,Traversal.innerSlice,Traversal.innerLoc,
    show (3:Fin 4).val=3 from rfl,List.range_succ,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  omega

theorem fiveValues_field (v : Vector (BitVec 128) 8) (w : Poly) {u : Nat} (hu : u<8)
    (hv : BankBound v (15*8380417)) (hf : InnerBankField u v w) :
    (∀ i : Fin 8, ∀ e<4, (vword (fiveValues v (innerRoot u) (tailRoot u))[i.val] e).toNat<3*8380417) ∧
    (∀ i : Fin 8, ∀ e<4, ofNat (vword (fiveValues v (innerRoot u) (tailRoot u))[i.val] e).toNat=
      (Traversal.run (Traversal.innerSlice u) w)[Traversal.innerLoc u i.val e]!) := by
  have hi := innerValues_field v w outerSteps outerSteps_valid (innerRootIndex u) hu
    (by decide) (by decide) hv hf
  have ht := tailValues_field _ _ tailSteps tailSteps_valid (tailRootIndex u) hu
    (by decide) (by decide) hi.1 hi.2
  have hei : (fun gap g _ => (zetaNat (innerRootIndex u gap g) : Int))=innerRoot u := rfl
  have het : (fun g len e => (zetaNat (tailRootIndex u g len e) : Int))=tailRoot u := rfl
  rw [hei,het,← Traversal.run_append,inner_schedule] at ht
  constructor
  · intro i e he
    simp only [fiveValues,Vector.getElem_map,positiveVector_word _ he,positiveWord_nat]
    have hb := positive_lt_three_q
      (BitVec.le_toInt (vword (tailValues (innerValues v (innerRoot u) outerSteps) (tailRoot u) tailSteps)[i.val] e))
      (BitVec.toInt_lt (x := vword (tailValues (innerValues v (innerRoot u) outerSteps) (tailRoot u) tailSteps)[i.val] e))
    simp only [q] at hb
    omega
  · intro i e he
    simp only [fiveValues,Vector.getElem_map,positiveVector_word _ he,positiveWord_field]
    exact ht.2 i e he

end VG.Proof.MlDsa.AArch64.Optimized
