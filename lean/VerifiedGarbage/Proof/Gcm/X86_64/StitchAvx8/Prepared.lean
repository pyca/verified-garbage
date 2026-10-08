import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Templates
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Hash

/-! # Reusing each GHASH input slot after its product has been consumed -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block)

def hashAddr (s₀ : State) (i : Nat) : Addr := pp s₀ + BitVec.ofNat 64 (512 + 16 * i)
def hashR (s₀ : State) : Region := ⟨pp s₀ + 512, 128⟩

/-- GHASH consumes slots 1,…,7,0, replacing consumed slots with `Y`. -/
def Prepared (s₀ : State) (X Y : Nat → Block) (n : Nat) (m : Mem) : Prop :=
  ∀ i < 8, m.readW (hashAddr s₀ i) 128 = if (i + 7) % 8 < n then Y i else X i

theorem slot_position (n : Nat) (hn : n < 8) : (((n + 1) % 8) + 7) % 8 = n := by omega

theorem Prepared.current {s₀ : State} {X Y : Nat → Block} {n : Nat} {m : Mem}
    (h : Prepared s₀ X Y n m) (hn : n < 8) :
    m.readW (hashAddr s₀ ((n + 1) % 8)) 128 = X ((n + 1) % 8) := by
  have hi := h ((n + 1) % 8) (Nat.mod_lt _ (by decide))
  rw [slot_position n hn, ite_eq_right (Nat.lt_irrefl n)] at hi
  exact hi

theorem Prepared.next {s₀ : State} {X Y : Nat → Block} {n : Nat} {m m' : Mem}
    (h : Prepared s₀ X Y n m) (hn : n < 8)
    (hv : m'.readW (hashAddr s₀ ((n + 1) % 8)) 128 = Y ((n + 1) % 8))
    (hf : Frame [⟨hashAddr s₀ ((n + 1) % 8), 16⟩] m m') :
    Prepared s₀ X Y (n + 1) m' := by
  intro i hi
  by_cases he : i = (n + 1) % 8
  · subst i
    rw [slot_position n hn, ite_eq_left (by omega : n < n + 1)]
    exact hv
  · have hp : (i + 7) % 8 ≠ n := by omega
    have hv' : m'.readW (hashAddr s₀ i) 128 = m.readW (hashAddr s₀ i) 128 := by
      apply hf.readW (r := ⟨hashAddr s₀ i, 16⟩)
      · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
      · intro r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact Offset.disjoint (pp s₀) (by omega) (by omega) (by omega)
      · decide
    have hc : (if (i + 7) % 8 < n + 1 then Y i else X i) =
        (if (i + 7) % 8 < n then Y i else X i) := by split_ifs <;> first | rfl | omega
    exact hv'.trans ((h i hi).trans hc.symm)

theorem Prepared.frame {s₀ : State} {X Y : Nat → Block} {n : Nat} {m m' : Mem}
    {rs : List Region} (h : Prepared s₀ X Y n m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (hashR s₀).Disjoint r) : Prepared s₀ X Y n m' := by
  intro i hi
  refine (hf.readW (r := ⟨hashAddr s₀ i, 16⟩) ?_ ?_ (by decide)).trans (h i hi)
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
  · intro r hr
    exact (hd r hr).sub_left (Offset.sub (pp s₀) (d := 512 + 16 * i) (e := 512)
      (n := 16) (k := 128) (by omega) (by omega))

theorem Prepared.done {s₀ : State} {X Y : Nat → Block} {m : Mem}
    (h : Prepared s₀ X Y 8 m) : ∀ i < 8, m.readW (hashAddr s₀ i) 128 = Y i := by
  intro i hi
  have hv := h i hi
  rw [ite_eq_left (Nat.mod_lt _ (by decide))] at hv
  exact hv

theorem Prepared.same_next {s₀ : State} {X Y : Nat → Block} {n : Nat} {m : Mem}
    (h : Prepared s₀ X Y n m) (he : ∀ i < 8, Y i = X i) : Prepared s₀ X Y (n + 1) m := by
  intro i hi
  have hv := h i hi
  simpa only [he i hi, ite_self] using hv

end VG.Proof.Gcm.X86_64.StitchAvx8
