module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleBody
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.RepresentationFin

/-! The doubler's final live slots are a canonical Jacobian double. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass (dblJF)

def ordinaryPoint (m : Mem) (base : Addr) (d : Nat) : Fin fieldPrime × Fin fieldPrime × Fin fieldPrime :=
  (Fin.ofNat fieldPrime (wordsVal m base d 9),
   Fin.ofNat fieldPrime (wordsVal m base (d+72) 9),
   Fin.ofNat fieldPrime (wordsVal m base (d+144) 9))

def canonicalPoint (m : Mem) (base : Addr) (d : Nat) : Prop :=
  wordsVal m base d 9<fieldPrime ∧ wordsVal m base (d+72) 9<fieldPrime ∧ wordsVal m base (d+144) 9<fieldPrime

def doubleInputEnv (m : Mem) (base : Addr) (a o : Nat) (i : Nat) : Fin fieldPrime :=
  Fin.ofNat fieldPrime (wordsVal m base (doubleSlot a o i) 9)

theorem double_input_inv {m : Mem} {base : Addr} {a o : Nat} {s : State}
    (hm : s.mem=m) (bound : canonicalPoint m base a) :
    OrdinaryInv base fieldPrime (doubleSlot a o) [0,1,2] (doubleInputEnv m base a o) (fun _ => 1) s := by
  constructor
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    · simpa only [hm,Nat.one_mul,doubleSlot,Nat.reduceLT,ite_true,Nat.mul_zero,Nat.add_zero] using bound.1
    · simpa only [hm,Nat.one_mul,doubleSlot,Nat.reduceLT,ite_true,Nat.mul_one] using bound.2.1
    · simpa only [hm,Nat.one_mul,doubleSlot,Nat.reduceLT,ite_true,Nat.reduceMul] using bound.2.2
  · intro x _
    rw [hm]
    rfl

theorem double_output {s : State} {base : Addr} {a o : Nat} {E : Nat → Fin fieldPrime}
    (inv : OrdinaryInv base fieldPrime (doubleSlot a o) (doubleLive 16) (pointRun doubleOps E) (doubleCaps 16) s) :
    canonicalPoint s.mem base o ∧ ordinaryPoint s.mem base o=dblJF (E 0) (E 1) (E 2) := by
  have b3 := inv.bound 3 (by decide)
  have b4 := inv.bound 4 (by decide)
  have b5 := inv.bound 5 (by decide)
  rw [show doubleCaps 16 3=1 from rfl,Nat.one_mul] at b3
  rw [show doubleCaps 16 4=1 from rfl,Nat.one_mul] at b4
  rw [show doubleCaps 16 5=1 from rfl,Nat.one_mul] at b5
  have v3 := inv.value 3 (by decide)
  have v4 := inv.value 4 (by decide)
  have v5 := inv.value 5 (by decide)
  have ds3 : doubleSlot a o 3=o := rfl
  have ds4 : doubleSlot a o 4=o+72 := rfl
  have ds5 : doubleSlot a o 5=o+144 := rfl
  rw [ds3] at b3 v3
  rw [ds4] at b4 v4
  rw [ds5] at b5 v5
  exact ⟨⟨b3,b4,b5⟩,by rw [ordinaryPoint,v3,v4,v5]; exact doubleOps_value E⟩

theorem double_input_env_point (m : Mem) (base : Addr) (a o : Nat) :
    (doubleInputEnv m base a o 0,doubleInputEnv m base a o 1,doubleInputEnv m base a o 2)=ordinaryPoint m base a := rfl

end VG.Proof.Mont.AArch64.P521Field
