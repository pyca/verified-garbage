import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourShake
import VerifiedGarbage.Spec.MlDsa.BoundedFour

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sample

private theorem mapM_map {α β γ : Type} (f : α→Option β) (g : β→γ) (l : List α) :
    (l.mapM f).map (List.map g)=l.mapM (fun x=>(f x).map g) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.mapM_cons,List.mapM_cons]
    cases f x <;> simp only [Option.bind_eq_bind,Option.bind_none,Option.bind_some,
      Option.map_none,Option.map_some]
    case some a =>
      rw [←ih]
      cases l.mapM f <;> rfl

private theorem mapM_some {α β : Type} {f : α→Option β} {g : α→β} :
    ∀ {l : List α}, (∀x∈l,f x=some (g x))→l.mapM f=some (l.map g)
  | [],_ => rfl
  | x::l,h => by
    rw [List.mapM_cons,h x (by simp),mapM_some (fun y hy=>h y (by simp [hy]))]
    rfl

private theorem mapM_none {α β : Type} {f : α→Option β} :
    ∀ {l : List α}, (∃x∈l,f x=none)→l.mapM f=none
  | [],⟨_,h,_⟩ => False.elim (List.not_mem_nil h)
  | x::l,⟨y,hy,hn⟩ => by
    rw [List.mapM_cons]
    rcases List.mem_cons.mp hy with rfl|hy
    · rw [hn]; rfl
    · cases f x with
      | none => rfl
      | some _ =>
        simp only [Option.bind_eq_bind,Option.bind_some]
        rw [mapM_none ⟨y,hy,hn⟩]; rfl

theorem Result.reduced {σ t : State} {L : Nat→List Zq} (h : Result σ t L)
    {i : Nat} (hi : i<4) : Reduced t.mem (outputAt (samplerOut σ) i) := by
  intro j hj
  rw [h.words i hi j hj,resultWord]
  split
  · rw [zw_toNat]; exact (L i |>.getD j 0).isLt
  · decide

theorem Result.full {σ t : State} {L : Nat→List Zq} (h : Result σ t L)
    {i : Nat} (hi : i<4) (hlen : (L i).length=256) :
    polyAt t.mem (outputAt (samplerOut σ) i)=toPoly (L i) :=
  (stored_polyIs (fun j hj=>by rw [h.words i hi j (by omega),resultWord,ite_eq_left hlen]) hlen).2

/-- Success is exactly the four standard samplers at the measured 544-byte bound;
failure implies failure at the standard's minimum allowed bound. -/
theorem Result.outcome {σ t : State} {η : Nat} (h : Result σ t (sampledRows σ η)) :
    Outcome (fun b=>(rejBoundedFour η b.rejBounded σ.mem (samplerSeed σ)).map (List.map toRq))
      ((t.gpr .x0).setWidth 32)
      ((List.range 4).map fun i=>polyAt t.mem (outputAt (samplerOut σ) i)) := by
  classical
  by_cases hf : ∀i<4,(sampledRows σ η i).length=256
  · refine Or.inl ⟨?_,{minBounds with rejBounded:=544},?_⟩
    · rw [h.status,ite_eq_left hf]; rfl
    · unfold rejBoundedFour
      dsimp only
      rw [mapM_map]
      apply mapM_some
      intro i hi
      have hi4:=List.mem_range.mp hi
      rw [h.full hi4 (hf i hi4)]
      have hlen:=hf i hi4
      rw [sampledRows_H σ η i] at hlen
      have hh:=rejBounded_some η (ρ := Spec.Sha3.bytesAt σ.mem (samplerSeedAt σ i) 66) (B := 544) hlen
      rw [←sampledRows_H σ η i] at hh
      exact hh
  · refine Or.inr ⟨?_,?_⟩
    · rw [h.status,ite_eq_right hf]; rfl
    · unfold rejBoundedFour
      dsimp only
      rw [mapM_map]
      apply mapM_none
      obtain ⟨i,hi,hlen⟩ : ∃i,i<4 ∧ (sampledRows σ η i).length≠256 := by
        by_contra hn
        apply hf
        intro i hi
        by_contra hh
        exact hn ⟨i,hi,hh⟩
      refine ⟨i,List.mem_range.mpr hi,?_⟩
      rw [rejBounded_none η (B := 544) (by decide)
        (by
          change (rbFold η [] (H (Spec.Sha3.bytesAt σ.mem (samplerSeedAt σ i) 66) 544)).length≠256
          rw [←sampledRows_H σ η i]
          exact hlen)]
      rfl

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
