module

public import VerifiedGarbage.TCB.Sig
import VerifiedGarbage.Proof.Framework.Scratch

-- separate module: every target's `Proof/Framework/<ISA>/CallWipe.lean` imports it (x86-64's so far).

/-!
# A call that wipes part of a buffer afterwards: what every target shares

The facts about a signature that each target's `Verified.callWipe`
(`Proof/Framework/<ISA>/CallWipe.lean`) needs of the array it wipes,
whatever the target: that it is one of the buffers (`Sig.bufs_mem_array`),
and that its address is a public argument of a pointer's bits
(`Sig.pub_array`).
-/

@[expose] public section

namespace VG

/-! ## The array among the parameters -/

theorem Sig.bufs_mem_array {pb : Nat} {w : Bool} {e : Elem} {k : Nat} {nm : String} (ps₂ : List (String × Param)) :
    ∀ (ps₁ : List (String × Param)) (vs : List (BitVec 64)),
      (ps₁.flatMap fun p => p.2.words pb).length < vs.length →
      (⟨vs.getD (ps₁.flatMap fun p => p.2.words pb).length 0, k * e.size⟩, w) ∈
        Sig.bufs (ps₁ ++ (nm, .array w e k) :: ps₂) vs
  | [], p :: vs, _ => List.mem_cons_self ..
  | (_, .int ..) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_1, List.length_append, List.length_cons,
      List.length_nil] at h ⊢
    simp only [List.cons_append, Sig.bufs, show 0 + 1 + (ps.flatMap fun p => p.2.words pb).length =
      (ps.flatMap fun p => p.2.words pb).length + 1 by omega, List.getD_cons_succ]
    exact Sig.bufs_mem_array (pb := pb) ps₂ ps vs (by omega)
  | (_, .array ..) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_2, List.length_append, List.length_cons,
      List.length_nil] at h ⊢
    simp only [List.cons_append, Sig.bufs, show 0 + 1 + (ps.flatMap fun p => p.2.words pb).length =
      (ps.flatMap fun p => p.2.words pb).length + 1 by omega, List.getD_cons_succ]
    exact List.mem_cons_of_mem _ (Sig.bufs_mem_array (pb := pb) ps₂ ps vs (by omega))
  | (_, .slice ..) :: ps, v :: l :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_3, List.length_append, List.length_cons,
      List.length_nil] at h ⊢
    simp only [List.cons_append, Sig.bufs, show 0 + 1 + 1 + (ps.flatMap fun p => p.2.words pb).length =
      (ps.flatMap fun p => p.2.words pb).length + 1 + 1 by omega, List.getD_cons_succ]
    exact List.mem_cons_of_mem _ (Sig.bufs_mem_array (pb := pb) ps₂ ps vs (by omega))
  | (_, .slices ..) :: ps, v :: l :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_4, List.length_append, List.length_cons,
      List.length_nil] at h ⊢
    simp only [List.cons_append, Sig.bufs, show 0 + 1 + 1 + (ps.flatMap fun p => p.2.words pb).length =
      (ps.flatMap fun p => p.2.words pb).length + 1 + 1 by omega, List.getD_cons_succ]
    exact Sig.bufs_mem_array (pb := pb) ps₂ ps vs (by omega)
  | (_, .table _) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_5, List.length_append, List.length_cons,
      List.length_nil] at h ⊢
    simp only [List.cons_append, Sig.bufs, show 0 + 1 + (ps.flatMap fun p => p.2.words pb).length =
      (ps.flatMap fun p => p.2.words pb).length + 1 by omega, List.getD_cons_succ]
    exact Sig.bufs_mem_array (pb := pb) ps₂ ps vs (by omega)
  | [], [], h => by simp at h
  | (_, .int ..) :: _, [], h => by simp at h
  | (_, .array ..) :: _, [], h => by simp at h
  | (_, .slice ..) :: _, [], h => by simp at h
  | (_, .slice ..) :: _, [_], h => by simp [Param.words.eq_3] at h
  | (_, .slices ..) :: _, [], h => by simp at h
  | (_, .slices ..) :: _, [_], h => by simp [Param.words.eq_4] at h
  | (_, .table _) :: _, [], h => by simp at h

/-- The array's address is a public argument, of a pointer's `pb` bits. -/
theorem Sig.pub_array {pb : Nat} {w : Bool} {e : Elem} {k : Nat} {nm : String} (ps₁ ps₂ : List (String × Param)) :
    ((ps₁ ++ (nm, .array w e k) :: ps₂).flatMap (·.2.pubs)).getD
        (ps₁.flatMap fun p => p.2.words pb).length false = true ∧
      (((ps₁ ++ (nm, .array w e k) :: ps₂).flatMap fun p => p.2.words pb).map (·.bits pb)).getD
        (ps₁.flatMap fun p => p.2.words pb).length 64 = pb := by
  rw [← Sig.pubs_length ps₁ pb]
  simp only [List.flatMap_append, List.flatMap_cons, List.getD_eq_getElem?_getD, List.map_append]
  constructor
  · rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
  · rw [List.getElem?_append_right (by rw [List.length_map, Sig.pubs_length (pb := pb)]; exact Nat.le_refl _), List.length_map,
      Sig.pubs_length (pb := pb), Nat.sub_self]; rfl

end VG
