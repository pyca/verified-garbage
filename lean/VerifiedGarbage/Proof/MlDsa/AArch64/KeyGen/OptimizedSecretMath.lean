import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSpec

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.Spec.MlDsa

theorem mapM_some_map_iff {α β : Type} (f : α→Option β) (g : α→β) :
    ∀l : List α,l.mapM f=some (l.map g) ↔ ∀x∈l,f x=some (g x)
  | [] => by simp
  | x::xs => by
    rw [List.mapM_cons,List.map_cons]
    cases hx : f x with
    | none => simp [hx]
    | some y =>
      simp only [Option.bind_eq_bind,Option.bind_some]
      cases ht : xs.mapM f with
      | none =>
        change (none : Option (List β))=some _ ↔ _
        simp only [reduceCtorEq,false_iff]
        intro h
        have he := (mapM_some_map_iff f g xs).mpr (fun z hz=>h z (by simp [hz]))
        rw [ht] at he
        cases he
      | some ys =>
        change some (y::ys)=some (g x::xs.map g) ↔ _
        rw [Option.some.injEq,List.cons.injEq]
        constructor
        · rintro ⟨hy,he⟩ z hz
          subst y
          rcases List.mem_cons.mp hz with rfl|hz
          · exact hx
          · exact (mapM_some_map_iff f g xs).mp (ht.trans (congrArg some he)) z hz
        · intro h
          have hy := h x (by simp)
          rw [hx] at hy
          have ht' := (mapM_some_map_iff f g xs).mpr (fun z hz=>h z (by simp [hz]))
          exact ⟨Option.some.inj hy,Option.some.inj (ht.symm.trans ht')⟩

theorem mapM_map_result {α β γ : Type} (f : α→Option β) (g : β→γ) (l : List α) :
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

theorem mapM_none_iff {α β : Type} (f : α→Option β) :
    ∀l : List α,l.mapM f=none ↔ ∃x∈l,f x=none
  | [] => by simp
  | x::xs => by
    rw [List.mapM_cons]
    cases hx : f x with
    | none => simp [hx]
    | some y =>
      simp only [Option.bind_eq_bind,Option.bind_some]
      cases ht : xs.mapM f with
      | none =>
        constructor
        · intro _
          obtain ⟨z,hz,he⟩:=(mapM_none_iff f xs).mp ht
          exact ⟨z,by simp [hz],he⟩
        · intro _; rfl
      | some ys =>
        change some (y::ys)=none ↔ _
        simp only [reduceCtorEq,false_iff]
        rintro ⟨z,hz,he⟩
        rcases List.mem_cons.mp hz with rfl|hz
        · rw [hx] at he; cases he
        · have hn:=(mapM_none_iff f xs).mpr ⟨z,hz,he⟩
          rw [ht] at hn; cases hn

theorem boundedFour_some_iff (η B : Nat) (m : Mem) (seed : Addr) (f : Nat→Poly) :
    (rejBoundedFour η B m seed).map (List.map toRq)=some ((List.range 4).map f) ↔
      ∀i<4,(rejBoundedPoly η B (Spec.Sha3.bytesAt m (seed+BitVec.ofNat 64 (66*i)) 66)).map toRq=
        some (f i) := by
  unfold rejBoundedFour
  rw [mapM_map_result,mapM_some_map_iff]
  simp only [List.mem_range]

theorem boundedFour_none_iff (η B : Nat) (m : Mem) (seed : Addr) :
    (rejBoundedFour η B m seed).map (List.map toRq)=none ↔
      ∃i<4,rejBoundedPoly η B (Spec.Sha3.bytesAt m (seed+BitVec.ofNat 64 (66*i)) 66)=none := by
  rw [Option.map_eq_none_iff]
  unfold rejBoundedFour
  rw [mapM_none_iff]
  simp only [List.mem_range]

/-- Ignoring a duplicated fourth lane retains exactly the three requested
samplers, including their failure result. -/
theorem mapM_duplicate_tail {α : Type} (a b c : Option α) :
    (([a,b,c,a].mapM id).map (List.take 3))=[a,b,c].mapM id := by
  cases a <;> cases b <;> cases c <;> rfl

theorem mapM_duplicate_none {α : Type} (a b c : Option α) :
    [a,b,c,a].mapM id=none ↔ [a,b,c].mapM id=none := by
  cases a <;> cases b <;> cases c <;> simp

/-- Duplicating a stream cannot introduce a failure or make failure depend on
an additional secret stream. The successful output keeps the first three. -/
theorem outcome_duplicate_tail {α : Type} {f g h : Bounds→Option α} {r : BitVec 32} {out : List α}
    (ho : Outcome (fun B=>[f B,g B,h B,f B].mapM id) r out) :
    Outcome (fun B=>[f B,g B,h B].mapM id) r (out.take 3) := by
  rcases ho with ⟨hr,B,hB⟩|⟨hr,hB⟩
  · refine Or.inl ⟨hr,B,?_⟩
    dsimp only at hB ⊢
    rw [←mapM_duplicate_tail,hB]
    rfl
  · exact Or.inr ⟨hr,(mapM_duplicate_none _ _ _).mp hB⟩

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
