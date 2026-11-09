module

public import VerifiedGarbage.Spec.Aes
public import VerifiedGarbage.Spec.TripleDes
public import VerifiedGarbage.TCB.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# TDEA-CMAC: what memory reads depend on

Reading bytes, a TDEA key schedule or a fold over the memory gives the same
result in two memories that agree on the bytes read (`bytesAt_congr`,
`tdesBytesAt_congr`, `scheduleAt_congr`, `agree_of`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes

/-! ## Locality -/

theorem foldl_congr {α β : Type} {f g : β → α → β} :
    ∀ (l : List α) (b : β), (∀ x ∈ l, ∀ b, f b x = g b x) → l.foldl f b = l.foldl g b
  | [], _, _ => rfl
  | x :: l, b, h => by
    simp only [List.foldl_cons]
    rw [h x List.mem_cons_self]
    exact foldl_congr l _ fun y hy => h y (List.mem_cons_of_mem _ hy)

section

variable {m₁ m₂ : Mem} {p : Addr}

theorem bytesAt_congr {n : Nat} (h : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Aes.bytesAt m₂ p n = Spec.Aes.bytesAt m₁ p n := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem tdesBytesAt_congr {n : Nat}
    (h : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.TripleDes.bytesAt m₂ p n = Spec.TripleDes.bytesAt m₁ p n := by
  simp only [Spec.TripleDes.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem scheduleAt_congr
    (h : ∀ i < 384, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.TripleDes.scheduleAt m₂ p = Spec.TripleDes.scheduleAt m₁ p := by
  simp only [Spec.TripleDes.scheduleAt]
  congr 1
  funext i
  refine foldl_congr _ _ fun j hj out => ?_
  rw [h _ (by have := i.isLt; have := List.mem_range.mp hj; omega_arith)]

end

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on the
region. -/
theorem agree_of {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega_arith) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega_arith

end VG.Proof.CmacTripleDes
