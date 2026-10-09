import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Batch

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

/-- The eight live vectors of one fused transform slice, independent of the
physical register selected by the renaming schedule. -/
def Bank (s : State) (regs : Vector VReg 8) (values : Vector (BitVec 128) 8) : Prop :=
  ∀ i : Fin 8, s.v regs[i.val] = values[i.val]

/-- Renaming the difference preserves the logical eight-vector bank. -/
theorem Bank.pair {s t : State} {regs : Vector VReg 8} {values : Vector (BitVec 128) 8}
    (h : Bank s regs values) (hinj : Function.Injective (fun i : Fin 8 => regs[i.val]))
    (i j : Fin 8) (free : VReg) (hf : ∀ k : Fin 8, regs[k.val] ≠ free)
    (hc : VChg [free,regs[i.val]] s t)
    (ha : t.v regs[i.val] = VArr.s4.map2 (fun _ a b => a + b) (s.v regs[i.val]) (s.v regs[j.val]))
    (hb : t.v free = VArr.s4.map2 (fun _ a b => a - b) (s.v regs[i.val]) (s.v regs[j.val])) :
    Bank t (regs.set j.val free)
      ((values.set i.val (VArr.s4.map2 (fun _ a b => a + b) values[i.val] values[j.val])).set j.val
        (VArr.s4.map2 (fun _ a b => a - b) values[i.val] values[j.val])) := by
  intro k
  change t.v (regs.set j.val free)[k.val] =
    ((values.set i.val (VArr.s4.map2 (fun _ a b => a + b) values[i.val] values[j.val])).set j.val
      (VArr.s4.map2 (fun _ a b => a - b) values[i.val] values[j.val]))[k.val]
  by_cases hjk : j = k
  · subst k
    simp only [Vector.getElem_set, ite_true]
    rw [hb, h i, h j]
  · have hjk' : j.val ≠ k.val := fun he => hjk (Fin.ext he)
    simp only [Vector.getElem_set, hjk', ite_false]
    by_cases hik : i = k
    · subst k
      simp only [ite_true]
      rw [ha, h i, h j]
    · have hik' : i.val ≠ k.val := fun he => hik (Fin.ext he)
      simp only [hik', ite_false]
      rw [hc.get (regs[k.val]) (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
        exact ⟨hf k, fun he => hik (hinj he.symm)⟩)]
      exact h k

/-- The register allocator's exchange of a live register and its free register
preserves injectivity and leaves the evicted register available for reuse. -/
theorem rename_shape (regs : Vector VReg 8) (j : Fin 8) (free : VReg)
    (hinj : Function.Injective (fun i : Fin 8 => regs[i.val]))
    (hf : ∀ i : Fin 8, regs[i.val] ≠ free) :
    Function.Injective (fun i : Fin 8 => (regs.set j.val free)[i.val]) ∧
      ∀ i : Fin 8, (regs.set j.val free)[i.val] ≠ regs[j.val] := by
  constructor
  · intro a b he
    simp only [Vector.getElem_set] at he
    split_ifs at he with ha hb hb
    · exact Fin.ext (ha.symm.trans hb)
    · exact False.elim (hf b he.symm)
    · exact False.elim (hf a he)
    · exact hinj he
  · intro i
    simp only [Vector.getElem_set]
    split_ifs with he
    · exact Ne.symm (hf j)
    · intro h
      have hi := congrArg Fin.val (hinj h)
      exact he hi.symm

def fastVector (v : BitVec 128) (z : Nat → Int) : BitVec 128 :=
  ofVWords (fastMulWord (vword v 0) (z 0)) (fastMulWord (vword v 1) (z 1))
    (fastMulWord (vword v 2) (z 2)) (fastMulWord (vword v 3) (z 3))

theorem fastVector_word (v : BitVec 128) (z : Nat → Int) {e : Nat} (he : e < 4) :
    vword (fastVector v z) e = fastMulWord (vword v e) (z e) := by
  rw [fastVector, VG.AArch64.vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

def productValues (v : Vector (BitVec 128) 8) (indices : List (Fin 8)) (z : Nat → Int) :
    Vector (BitVec 128) 8 :=
  Vector.ofFn fun i => if i ∈ indices then fastVector v[i.val] z else v[i.val]

/-- Lift a scheduled multiplication's lane results into the logical register
bank, preserving every coefficient not selected for multiplication. -/
theorem Bank.products {s t : State} {regs : Vector VReg 8} {values : Vector (BitVec 128) 8}
    (h : Bank s regs values) (hinj : Function.Injective (fun i : Fin 8 => regs[i.val]))
    (indices : List (Fin 8)) (temps : List VReg) (z : Nat → Int)
    (ht : ∀ i : Fin 8, regs[i.val] ∉ temps)
    (hc : VChg (temps ++ indices.map (fun i => regs[i.val])) s t)
    (hw : ∀ i ∈ indices, ∀ e < 4,
      vword (t.v regs[i.val]) e = fastMulWord (vword (s.v regs[i.val]) e) (z e)) :
    Bank t regs (productValues values indices z) := by
  intro i
  change t.v regs[i.val] = (productValues values indices z)[i.val]
  simp only [productValues, Vector.getElem_ofFn, Fin.eta]
  by_cases hi : i ∈ indices
  · rw [ite_eq_left hi]
    apply vec_ext
    intro e he
    rw [hw i hi e he, h i, fastVector_word _ _ he]
  · rw [ite_eq_right hi, hc.get (regs[i.val]) ?_]
    · exact h i
    · simp only [List.mem_append, not_or]
      refine ⟨ht i, ?_⟩
      intro hm
      rcases List.mem_map.mp hm with ⟨j,hj,he⟩
      exact hi ((hinj he) ▸ hj)

end VG.Proof.MlDsa.AArch64.Optimized
