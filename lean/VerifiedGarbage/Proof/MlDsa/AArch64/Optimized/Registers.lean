import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.GroupArithmetic

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def liveRegs : List VReg := [.v0,.v1,.v5,.v6,.v7,.v21,.v22,.v23,.v24]
def groupRegs : List VReg := liveRegs ++ prodTemps

structure GoodRen (r : Ren) : Prop where
  injective : Function.Injective (fun i : Fin 8 => r.data[i.val])
  apart : ∀ i : Fin 8, r.data[i.val] ≠ r.free
  data : ∀ i : Fin 8, r.data[i.val] ∈ liveRegs
  free : r.free ∈ liveRegs

theorem GoodRen.pair {r : Ren} (h : GoodRen r) (i j : Fin 8) :
    GoodRen (renamePair r i.val j.val) := by
  have hs := rename_shape r.data j r.free h.injective h.apart
  constructor
  · change Function.Injective (fun k : Fin 8 => (r.data.set! j.val r.free)[k.val])
    rw [setBang_eq_set]
    exact hs.1
  · change ∀ k : Fin 8, (r.data.set! j.val r.free)[k.val] ≠ r.data[j.val]!
    rw [setBang_eq_set, getElem!_pos r.data j.val j.isLt]
    exact hs.2
  · intro k
    change (r.data.set! j.val r.free)[k.val] ∈ liveRegs
    rw [Vector.getElem_set!]
    split
    · exact h.free
    · exact h.data k
  · change r.data[j.val]! ∈ liveRegs
    rw [getElem!_pos r.data j.val j.isLt]
    exact h.data j

theorem GoodRen.afterPairs {r : Ren} (h : GoodRen r) (ps : List (Fin 8 × Fin 8)) :
    GoodRen (afterPairs r ps) := by
  induction ps generalizing r with
  | nil => exact h
  | cons p ps ih => exact ih (h.pair p.1 p.2)

theorem GoodRen.pairClobs_mem {r : Ren} (h : GoodRen r) (ps : List (Fin 8 × Fin 8)) :
    ∀ v ∈ pairClobs r ps, v ∈ liveRegs := by
  induction ps generalizing r with
  | nil => simp [pairClobs]
  | cons p ps ih =>
    intro v hv
    simp only [pairClobs, List.mem_append, List.mem_cons] at hv
    rcases hv with (rfl | rfl | hfalse) | ht
    · exact h.free
    · exact h.data p.1
    · simp at hfalse
    · exact ih (h.pair p.1 p.2) v ht

theorem GoodRen.coreClobs_mem {r : Ren} (h : GoodRen r) (gap group : Nat) (hv : ValidGroup gap group) :
    ∀ v ∈ coreClobs r gap group, v ∈ groupRegs := by
  intro v hm
  simp only [coreClobs, List.mem_append] at hm
  rcases hm with (ht | hd) | hp
  · rcases List.mem_map.mp ht with ⟨p,hp,rfl⟩
    exact List.mem_append_right _ ((groupIndices_shape gap group hv).2.2.2 p hp)
  · rcases List.mem_map.mp hd with ⟨i,_,rfl⟩
    exact List.mem_append_left _ (h.data i)
  · exact List.mem_append_left _ (h.pairClobs_mem _ v hp)

theorem initial_good : GoodRen ({} : Ren) := by
  constructor
  · change ∀ i j : Fin 8, _ → i = j
    decide
  · decide
  · decide
  · decide

theorem GoodRen.group {r : Ren} (h : GoodRen r) (gap group : Nat) (hv : ValidGroup gap group)
    (roots : List Instr) : GoodRen (renGroup r gap group roots) := by
  have h' := h.afterPairs (groupSteps gap group)
  constructor
  · rw [renGroup_data r gap group hv roots]
    exact h'.injective
  · rw [renGroup_data r gap group hv roots, renGroup_free r gap group hv roots]
    exact h'.apart
  · rw [renGroup_data r gap group hv roots]
    exact h'.data
  · rw [renGroup_free r gap group hv roots]
    exact h'.free

end VG.Proof.MlDsa.AArch64.Optimized
