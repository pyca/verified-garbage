module

public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Step

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64 VG.Spec.MlKem

def blockValues (F : (Nat × Nat) → Nat → Nat) (c : Nat) : (Nat × Nat) → Nat → Nat :=
  fun fg e => F fg (8*c+e)

def blockGamma (Γ : Nat → Nat) (c : Nat) : Nat → Nat := fun e => Γ (4*c+e)

def result (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Nat → Nat) (Γ : Nat → Nat)
    (j : Nat) : BitVec 32 :=
  interleave (evenResult terms (blockValues F (j/8)) (blockValues G (j/8)) (blockGamma Γ (j/8)))
    (oddResult terms (blockValues F (j/8)) (blockValues G (j/8))) (j%8)

theorem result_block (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Nat → Nat) (Γ : Nat → Nat)
    (c : Nat) {e : Nat} (he : e < 8) :
    result terms F G Γ (8*c+e) =
      interleave (evenResult terms (blockValues F c) (blockValues G c) (blockGamma Γ c))
        (oddResult terms (blockValues F c) (blockValues G c)) e := by
  unfold result
  rw [show (8*c+e)/8 = c by omega, show (8*c+e)%8 = e by omega]

end VG.Proof.MlKem.AArch64.Dot
