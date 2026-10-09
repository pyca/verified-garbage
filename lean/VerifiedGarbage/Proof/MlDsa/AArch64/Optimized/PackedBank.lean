import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Packed
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Registers

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def packedValues (v : Vector (BitVec 128) 8) (i j : Fin 8) (len : Nat) (z : Nat → Int) :
    Vector (BitVec 128) 8 :=
  (v.set i.val (packedResult len false v[i.val] v[j.val] z)).set j.val
    (packedResult len true v[i.val] v[j.val] z)

def packedClobs (r : Ren) (i j : Fin 8) : List VReg :=
  [.v25,.v26,.v4,r.free,r.data[i.val],r.data[j.val]]

theorem packedBank_ok (r : Ren) (i j : Fin 8) (len : Nat) (hij : i ≠ j) (hr : GoodRen r)
    {s : State} {rest : List Instr} {Q : State → Prop} {values : Vector (BitVec 128) 8}
    {z : Nat → Int} (hbank : Bank s r.data values)
    (hz : ∀ e < 4, 0 ≤ z e ∧ z e < 8380417)
    (hzw : ∀ e < 4, vword (s.v .v18) e = BitVec.ofInt 32 (z e))
    (hbw : ∀ e < 4, vword (s.v .v19) e = BitVec.ofInt 32 (reciprocal (z e)))
    (hqw : ∀ e < 4, vword (s.v .v16) e = 8380417#32)
    (k : ∀ t, VChg (packedClobs r i j) s t →
      Bank t r.data (packedValues values i j len z) → WP isa (.block rest) t Q) :
    WP isa (.block (renInnerPair r.data[i.val] r.data[j.val] r.free len ++ rest)) s Q := by
  have hs : ∀ v ∈ liveRegs, v ∉ [VReg.v25,.v26,.v4] := by decide
  have ha : r.data[i.val] ∉ [.v25,.v26] := fun h => hs _ (hr.data i) (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h))
  have hb : r.data[j.val] ∉ [.v25,.v26] := fun h => hs _ (hr.data j) (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h))
  have ht25 : r.free ≠ .v25 := fun h => hs _ hr.free (by simp [h])
  have ht26 : r.free ≠ .v26 := fun h => hs _ hr.free (by simp [h])
  refine renInnerPair_ok _ _ _ len (fun he => hij (hr.injective he)) ha hb (hr.apart i) ht25 ht26
    hz hzw hbw hqw fun t hc ha hb => k t hc ?_
  intro a
  simp only [packedValues,Vector.getElem_set]
  by_cases hja : j = a
  · subst a
    simp only [ite_true]
    rw [hb,hbank i,hbank j]
  · have hja' : j.val ≠ a.val := fun h => hja (Fin.ext h)
    simp only [hja',ite_false]
    by_cases hia : i = a
    · subst a
      simp only [ite_true]
      rw [ha,hbank i,hbank j]
    · have hia' : i.val ≠ a.val := fun h => hia (Fin.ext h)
      simp only [hia',ite_false]
      rw [hc.get _ ?_,hbank a]
      have hri : r.data[a.val] ≠ r.data[i.val] := fun h => hia (hr.injective h).symm
      have hrj : r.data[a.val] ≠ r.data[j.val] := fun h => hja (hr.injective h).symm
      have hsmall := hs _ (hr.data a)
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hsmall ⊢
      exact ⟨hsmall.1,hsmall.2.1,hsmall.2.2,hr.apart a,hri,hrj⟩

end VG.Proof.MlDsa.AArch64.Optimized
