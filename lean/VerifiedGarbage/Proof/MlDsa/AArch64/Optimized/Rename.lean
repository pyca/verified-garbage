import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Ntt
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Bank

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

theorem setBang_eq_set {α : Type} (v : Vector α 8) (j : Fin 8) (x : α) :
    v.set! j.val x = v.set j.val x := by
  apply Vector.ext
  intro k hk
  simp only [Vector.getElem_set!, Vector.getElem_set]

def pairValues (v : Vector (BitVec 128) 8) (i j : Fin 8) : Vector (BitVec 128) 8 :=
  (v.set i.val (VArr.s4.map2 (fun _ a b => a + b) v[i.val] v[j.val])).set j.val
    (VArr.s4.map2 (fun _ a b => a - b) v[i.val] v[j.val])

/-- The actual emitted two-instruction renaming step preserves the logical
bank and the free-register invariant needed by the next pair. -/
theorem renamePair_ok (r : Ren) (i j : Fin 8)
    {s : State} {rest : List Instr} {Q : State → Prop} {values : Vector (BitVec 128) 8}
    (h : Bank s r.data values)
    (hinj : Function.Injective (fun i : Fin 8 => r.data[i.val]))
    (hf : ∀ i : Fin 8, r.data[i.val] ≠ r.free)
    (k : ∀ t, VChg [r.free,r.data[i.val]] s t →
      Bank t (renamePair r i.val j.val).data (pairValues values i j) →
      Function.Injective (fun k : Fin 8 => (renamePair r i.val j.val).data[k.val]) →
      (∀ k : Fin 8, (renamePair r i.val j.val).data[k.val] ≠ (renamePair r i.val j.val).free) →
      WP isa (.block rest) t Q) :
    WP isa (.block (pairCode r i.val j.val ++ rest)) s Q := by
  simp only [pairCode, getElem!_pos r.data i.val i.isLt, getElem!_pos r.data j.val j.isLt,
    List.cons_append, List.nil_append]
  refine renamed_pair_ok (hf i) (hf j) fun t hc ha hb => ?_
  have ha' : t.v r.data[i.val] = VArr.s4.map2 (fun _ a b => a + b) (s.v r.data[i.val]) (s.v r.data[j.val]) := by
    apply vec_ext
    intro e he
    rw [ha e he, VG.AArch64.vword_map2 _ _ _ he]
  have hb' : t.v r.free = VArr.s4.map2 (fun _ a b => a - b) (s.v r.data[i.val]) (s.v r.data[j.val]) := by
    apply vec_ext
    intro e he
    rw [hb e he, VG.AArch64.vword_map2 _ _ _ he]
  have hs := rename_shape r.data j r.free hinj hf
  apply k t hc
  · change Bank t (r.data.set! j.val r.free) (pairValues values i j)
    rw [setBang_eq_set]
    exact h.pair hinj i j r.free hf hc ha' hb'
  · change Function.Injective (fun k : Fin 8 => (r.data.set! j.val r.free)[k.val])
    rw [setBang_eq_set]
    exact hs.1
  · change ∀ k : Fin 8, (r.data.set! j.val r.free)[k.val] ≠ r.data[j.val]!
    rw [setBang_eq_set, getElem!_pos r.data j.val j.isLt]
    exact hs.2

def afterPairs (r : Ren) : List (Fin 8 × Fin 8) → Ren
  | [] => r
  | (i,j) :: ps => afterPairs (renamePair r i.val j.val) ps

def pairOps (r : Ren) : List (Fin 8 × Fin 8) → List Instr
  | [] => []
  | (i,j) :: ps => pairCode r i.val j.val ++ pairOps (renamePair r i.val j.val) ps

def pairClobs (r : Ren) : List (Fin 8 × Fin 8) → List VReg
  | [] => []
  | (i,j) :: ps => [r.free,r.data[i.val]] ++ pairClobs (renamePair r i.val j.val) ps

def afterValues (values : Vector (BitVec 128) 8) : List (Fin 8 × Fin 8) → Vector (BitVec 128) 8
  | [] => values
  | (i,j) :: ps => afterValues (pairValues values i j) ps

theorem pairOps_same {r r' : Ren} (hd : r.data = r'.data) (hf : r.free = r'.free)
    (ps : List (Fin 8 × Fin 8)) : pairOps r ps = pairOps r' ps := by
  induction ps generalizing r r' with
  | nil => rfl
  | cons p ps ih =>
    simp only [pairOps]
    congr 1
    · simp only [pairCode, hd, hf]
    · exact ih (by simp only [renamePair, hd, hf]) (by simp only [renamePair, hd])

theorem afterPairs_same {r r' : Ren} (hd : r.data = r'.data) (hf : r.free = r'.free)
    (ps : List (Fin 8 × Fin 8)) :
    (afterPairs r ps).data = (afterPairs r' ps).data ∧
      (afterPairs r ps).free = (afterPairs r' ps).free := by
  induction ps generalizing r r' with
  | nil => exact ⟨hd,hf⟩
  | cons p ps ih =>
    exact ih (by simp only [renamePair, hd, hf]) (by simp only [renamePair, hd])

/-- Relate the compositional proof program to the generator's accumulated code. -/
theorem afterPairs_code (r : Ren) (ps : List (Fin 8 × Fin 8)) :
    (afterPairs r ps).code = r.code ++ pairOps r ps := by
  induction ps generalizing r with
  | nil => simp only [afterPairs, pairOps, List.append_nil]
  | cons p ps ih =>
    rw [afterPairs, ih]
    simp only [renamePair, pairOps, List.append_assoc]

theorem pairOps_ok (r : Ren) (ps : List (Fin 8 × Fin 8))
    {s : State} {rest : List Instr} {Q : State → Prop} {values : Vector (BitVec 128) 8}
    (h : Bank s r.data values)
    (hinj : Function.Injective (fun i : Fin 8 => r.data[i.val]))
    (hf : ∀ i : Fin 8, r.data[i.val] ≠ r.free)
    (k : ∀ t, VChg (pairClobs r ps) s t →
      Bank t (afterPairs r ps).data (afterValues values ps) →
      Function.Injective (fun i : Fin 8 => (afterPairs r ps).data[i.val]) →
      (∀ i : Fin 8, (afterPairs r ps).data[i.val] ≠ (afterPairs r ps).free) →
      WP isa (.block rest) t Q) :
    WP isa (.block (pairOps r ps ++ rest)) s Q := by
  induction ps generalizing r s values with
  | nil => exact k s (VChg.refl _ _) h hinj hf
  | cons p ps ih =>
    rw [pairOps, List.append_assoc]
    refine renamePair_ok r p.1 p.2 h hinj hf fun s₁ hc₁ h₁ hi₁ hf₁ => ?_
    refine ih _ h₁ hi₁ hf₁ fun s₂ hc₂ h₂ hi₂ hf₂ => ?_
    exact k s₂ (hc₁.trans hc₂) h₂ hi₂ hf₂

end VG.Proof.MlDsa.AArch64.Optimized
