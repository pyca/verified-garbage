module

public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Saving registers in the working space changes only their slots

`saveMem_unch`: `Spill.saveMem` of registers into bytes `[o, o + L)` of the
working space leaves the rest of it unchanged (`Unch`), for the functions
that keep their caller's callee-saved registers in their own working space.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Proof.Mont VG.Proof.Weierstrass

/-- `saveMem` of slots in `[o, o + L)` of `base` changes nothing else of the
working space. -/
theorem saveMem_unch (m : Mem) (base : Addr) (g : Reg → BitVec 64) {o L : Nat}
    (l : List (Reg × Nat)) (h : ∀ p ∈ l, o ≤ p.2 ∧ p.2 + 8 ≤ o + L) (hL : o + L < 2 ^ 64) :
    Unch base [(o, L)] m (Spill.saveMem m base g l) := by
  intro x hx
  refine Spill.saveMem_frame (r := ⟨base + BitVec.ofNat 64 o, L⟩) m base g l
    (fun p hp => Offset.contains base (h p hp).1 (h p hp).2 hL) x fun r hr hc => ?_
  rw [List.mem_singleton.mp hr] at hc
  have hx' := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hc
  have := (Offset.lt_iff x base (d := o) (n := L) (by omega)).mp (by omega)
  simp only [ofs] at hx'
  omega

/-- `saveMem` of slots each in one of the ranges `W` of `base` changes
nothing else of the working space. -/
theorem saveMem_unch_of (m : Mem) (base : Addr) (g : Reg → BitVec 64) (W : List (Nat × Nat)) :
    ∀ l : List (Reg × Nat), (∀ p ∈ l, ∃ w ∈ W, w.1 ≤ p.2 ∧ p.2 + 8 ≤ w.1 + w.2 ∧ w.1 + w.2 < 2 ^ 64) →
      Unch base W m (Spill.saveMem m base g l) := by
  intro l
  induction l generalizing m with
  | nil => intro _; exact Unch.refl _ _ _
  | cons p l ih =>
    intro h
    obtain ⟨w, hw, h₁, h₂, h₃⟩ := h p List.mem_cons_self
    have U := saveMem_unch m base g [p] (o := w.1) (L := w.2)
      (fun q hq => by rw [List.mem_singleton.mp hq]; exact ⟨h₁, h₂⟩) h₃
    exact Unch.mono (U.trans (ih _ fun q hq => h q (List.mem_cons_of_mem _ hq))) fun v hv =>
      (List.mem_append.mp hv).elim (fun hv => List.mem_singleton.mp hv ▸ hw) id

end VG.Proof.Weierstrass.X86_64
