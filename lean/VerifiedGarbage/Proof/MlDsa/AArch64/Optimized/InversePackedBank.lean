import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePacked
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseStage

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

def packedValues (v : Vector (BitVec 128) 8) (i j : Fin 8) (len : Nat) (z : Nat → Int) :
    Vector (BitVec 128) 8 :=
  (v.set i.val (packedResult len false v[i.val] v[j.val] z)).set j.val
    (packedResult len true v[i.val] v[j.val] z)

def packedClobs (r : Vector VReg 8) (i j : Fin 8) : List VReg :=
  [.v16,.v17,.v18,.v19,r[i.val],r[j.val]]

theorem packedBank_ok (r : Vector VReg 8) (i j : Fin 8) (len : Nat) (hij : i ≠ j)
    (hinj : Function.Injective (fun a : Fin 8 => r[a.val]))
    (hsmall : ∀ a : Fin 8, r[a.val]∉[.v16,.v17,.v18,.v19])
    {s : State} {rest : List Instr} {Q : State → Prop} {values : Vector (BitVec 128) 8}
    {z : Nat → Int} (hbank : Bank s r values)
    (hz : ∀ e<4, 0≤z e ∧ z e<8380417)
    (hzw : ∀ e<4, vword (s.v .v20) e=BitVec.ofInt 32 (z e))
    (hbw : ∀ e<4, vword (s.v .v21) e=BitVec.ofInt 32 (reciprocal (z e)))
    (hqw : ∀ e<4, vword (s.v .v31) e=8380417#32)
    (k : ∀ t, VChg (packedClobs r i j) s t →
      Bank t r (packedValues values i j len z) → WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.Inverse.packed r[i.val] r[j.val] len ++ rest)) s Q := by
  have hs (a : Fin 8) : r[a.val]∉[.v16,.v17,.v18] := fun h => hsmall a (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    grind only)
  refine packed_ok _ _ len (fun h => hij (hinj h)) (hs i) (hs j)
    hz hzw hbw hqw fun t hc ha hb => k t hc ?_
  intro a
  simp only [packedValues,Vector.getElem_set]
  by_cases hja : j=a
  · subst a
    simp only [ite_true]
    rw [hb,hbank i,hbank j]
  · have hja' : j.val≠a.val := fun h => hja (Fin.ext h)
    simp only [hja',ite_false]
    by_cases hia : i=a
    · subst a
      simp only [ite_true]
      rw [ha,hbank i,hbank j]
    · have hia' : i.val≠a.val := fun h => hia (Fin.ext h)
      simp only [hia',ite_false]
      rw [hc.get _ ?_,hbank a]
      have hri : r[a.val]≠r[i.val] := fun h => hia (hinj h).symm
      have hrj : r[a.val]≠r[j.val] := fun h => hja (hinj h).symm
      have hm := hsmall a
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hm ⊢
      exact ⟨hm.1,hm.2.1,hm.2.2.1,hm.2.2.2,hri,hrj⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
