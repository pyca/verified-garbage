module
import VerifiedGarbage.Proof.Framework.Offset
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeLayout
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Round
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleMemory
import VerifiedGarbage.Proof.Framework.InstancePriority

/-! # The witness loop's mutable footprint excludes its prepared constants -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

def primeWrites (n : Nat) : List (Nat × Nat) :=
  [(4, 4), (slot n 1, 8 * n), (slot n 2, 16 * n + 4), (slot n 5, 8 * n),
   (slot n 6, 8 * n), (slot n 7, 8 * n), (slot n 8, 8 * n),
   (roundCount, 4), (roundStatus, 4), (primeUniform, 4), (primeUsed, 4), (primeStatus, 4), (primeIsUniform, 4)]

def PrimeFrame (base : Addr) (n : Nat) (witness : Addr) (len : Nat) (s t : Mem) : Prop :=
  Frame ((primeWrites n).map (fun r => ⟨off base r.1, r.2⟩) ++ [⟨witness, len⟩]) s t

theorem primeWrites_bound {n size : Nat} (width : n ≤ 48) (room : primeIsUniform + 4 ≤ size) :
    ∀ r ∈ primeWrites n, r.1 + r.2 ≤ size := by
  intro r hr
  simp only [primeWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [slot, stride, roundCount, roundStatus, primeUniform, primeUsed, primeStatus, primeIsUniform] at * <;> omega

theorem PrimeFrame.constants {base witness : Addr} {n len size j : Nat} {s t : Mem}
    (O : PrimeFrame base n witness len s t) (width : n ≤ 48)
    (sizeBound : size ≤ 2 ^ 64) (room : primeIsUniform + 4 ≤ size)
    (apart : Region.Disjoint ⟨base, size⟩ ⟨witness, len⟩) (hj : j = 0 ∨ j = 3 ∨ j = 4) :
    wordsVal t base (slot n j) n = wordsVal s base (slot n j) n := by
  have bound : slot n j + 8 * n ≤ size := by
    rcases hj with rfl | rfl | rfl <;> simp only [slot, stride, primeIsUniform] at * <;> omega
  apply sampleFrame_words O ?_ (by omega)
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨item, hi, rfl⟩ := List.mem_map.mp hr
    apply Offset.disjoint base ?_ (by omega) (Nat.le_trans (primeWrites_bound width room item hi) sizeBound)
    simp only [primeWrites, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl <;>
      simp only [slot, stride, roundCount, roundStatus, primeUniform, primeUsed, primeStatus, primeIsUniform] <;> omega
  · obtain rfl := List.mem_singleton.mp hr
    exact apart.sub_left (Offset.sub_base _ bound)

theorem PrimeFrame.exponent {base witness : Addr} {n len size : Nat} {s t : Mem}
    (O : PrimeFrame base n witness len s t) (width : n ≤ 48)
    (sizeBound : size ≤ 2 ^ 64) (room : primeExponent + 8 * n ≤ size)
    (apart : Region.Disjoint ⟨base, size⟩ ⟨witness, len⟩) :
    val32 t base primeExponent (2 * n) = val32 s base primeExponent (2 * n) := by
  rw [← wordsVal_eq_val32, ← wordsVal_eq_val32]
  apply sampleFrame_words O ?_ (by omega)
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨item, hi, rfl⟩ := List.mem_map.mp hr
    have flagRoom : primeIsUniform + 4 ≤ size := by unfold primeIsUniform primeExponent at *; omega
    apply Offset.disjoint base ?_ (by omega) (Nat.le_trans (primeWrites_bound width flagRoom item hi) sizeBound)
    simp only [primeWrites, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [slot, stride, roundCount, roundStatus, primeUniform, primeUsed, primeStatus, primeIsUniform, primeExponent] <;> omega
  · obtain rfl := List.mem_singleton.mp hr
    exact apart.sub_left (Offset.sub_base _ room)
end VG.Proof.Dsa.X86.Generation
