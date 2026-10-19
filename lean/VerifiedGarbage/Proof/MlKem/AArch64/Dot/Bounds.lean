module
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem


/-! Bounds for the unreduced accumulators. No arithmetic wraps for at most
four canonical polynomial terms. -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot

structure Sums where
  even : Nat
  odd : Nat
  cross : Nat

def Sums.next (s : Sums) (fe fo ge go : Nat) : Sums :=
  ⟨s.even + fe*ge, s.odd + fo*go, s.cross + fe*go + fo*ge⟩

def Sums.Bounded (s : Sums) (n : Nat) : Prop :=
  s.even ≤ n*(3329*3329) ∧ s.odd ≤ n*(3329*3329) ∧ s.cross ≤ 2*n*(3329*3329)

theorem Sums.Bounded.next {s : Sums} {n fe fo ge go : Nat} (h : s.Bounded n)
    (hf : fe < 3329) (ho : fo < 3329) (hg : ge < 3329) (hp : go < 3329) :
    (s.next fe fo ge go).Bounded (n+1) := by
  have a : fe*ge ≤ 3329*3329 := Nat.mul_le_mul (Nat.le_of_lt hf) (Nat.le_of_lt hg)
  have b : fo*go ≤ 3329*3329 := Nat.mul_le_mul (Nat.le_of_lt ho) (Nat.le_of_lt hp)
  have c : fe*go ≤ 3329*3329 := Nat.mul_le_mul (Nat.le_of_lt hf) (Nat.le_of_lt hp)
  have d : fo*ge ≤ 3329*3329 := Nat.mul_le_mul (Nat.le_of_lt ho) (Nat.le_of_lt hg)
  simp only [Sums.Bounded, Sums.next] at *
  bdd_omega

theorem Sums.Bounded.machine {s : Sums} {n : Nat} (h : s.Bounded n) (hn : n ≤ 4) :
    s.even ≤ 4*3329*3329 ∧ s.odd ≤ 4*3329*3329 ∧ s.cross ≤ 8*3329*3329 := by
  change s.even ≤ 4*(3329*3329) ∧ s.odd ≤ 4*(3329*3329) ∧ s.cross ≤ 8*(3329*3329)
  exact ⟨Nat.le_trans h.1 (Nat.mul_le_mul_right _ hn),
    Nat.le_trans h.2.1 (Nat.mul_le_mul_right _ hn),
    Nat.le_trans h.2.2 (Nat.mul_le_mul_right _ (show 2*n ≤ 8 by omega))⟩

theorem Sums.Bounded.noWrap {s : Sums} {n : Nat} (h : s.Bounded n) (hn : n ≤ 4) :
    s.even < 2^31 ∧ s.odd < 2^31 ∧ s.cross < 2^31 := by
  have := h.machine hn
  bdd_omega

end VG.Proof.MlKem.AArch64.Dot
