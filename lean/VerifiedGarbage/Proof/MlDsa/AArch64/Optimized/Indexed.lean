import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Bank

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

/-- Scheduled multiplications selected by logical bank indices. -/
theorem indexed_multiply_ok (pairs : List (Fin 8 × VReg)) (regs : Vector VReg 8)
    (zr br qr : VReg) (hi : (pairs.map Prod.fst).Nodup) (ht : (pairs.map Prod.snd).Nodup)
    (hinj : Function.Injective (fun i : Fin 8 => regs[i.val]))
    (hap : ∀ i : Fin 8, regs[i.val] ∉ pairs.map Prod.snd)
    (hzr : ∀ i : Fin 8, regs[i.val] ≠ zr) (hqr : ∀ i : Fin 8, regs[i.val] ≠ qr)
    (hzt : zr ∉ pairs.map Prod.snd) (hbt : br ∉ pairs.map Prod.snd) (hqt : qr ∉ pairs.map Prod.snd)
    {s : State} {rest : List Instr} {Q : State → Prop} {values : Vector (BitVec 128) 8}
    {z : Nat → Int} (hbank : Bank s regs values)
    (hz : ∀ e < 4, 0 ≤ z e ∧ z e < 8380417)
    (hzw : ∀ e < 4, vword (s.v zr) e = BitVec.ofInt 32 (z e))
    (hbw : ∀ e < 4, vword (s.v br) e = BitVec.ofInt 32 (reciprocal (z e)))
    (hqw : ∀ e < 4, vword (s.v qr) e = 8380417#32)
    (k : ∀ t, VChg (pairs.map Prod.snd ++ (pairs.map Prod.fst).map (fun i => regs[i.val])) s t →
      Bank t regs (productValues values (pairs.map Prod.fst) z) → WP isa (.block rest) t Q) :
    let ps := pairs.map (fun p => (regs[p.1.val],p.2))
    WP isa (.block (ps.map (fun p => Instr.vop (.sqdmulh p.2 p.1 br)) ++
      (ps.map Prod.fst).map (fun d => Instr.vop (.mul d d zr)) ++
      ps.map (fun p => Instr.vop (.mls p.1 p.2 qr)) ++ rest)) s Q := by
  intro ps
  have hd : ps.map Prod.fst = (pairs.map Prod.fst).map (fun i => regs[i.val]) := by
    simp only [ps, List.map_map, Function.comp_def]
  have hp : ps.map Prod.snd = pairs.map Prod.snd := by
    simp only [ps, List.map_map, Function.comp_def]
  have hdno : (ps.map Prod.fst).Nodup := by
    rw [hd]
    exact List.Pairwise.map (S := fun a b : VReg => a ≠ b) (fun i => regs[i.val]) (fun _ _ hne heq => hne (hinj heq)) hi
  have htno : (ps.map Prod.snd).Nodup := by rw [hp]; exact ht
  have hap' : ∀ p ∈ ps, p.1 ∉ ps.map Prod.snd := by
    intro p h
    rcases List.mem_map.mp (show p ∈ pairs.map (fun a => (regs[a.1.val],a.2)) from h) with ⟨a,ha,rfl⟩
    rw [hp]
    exact hap a.1
  have hpa' : ∀ p ∈ ps, p.2 ∉ ps.map Prod.fst := by
    intro p h hm
    rcases List.mem_map.mp (show p ∈ pairs.map (fun a => (regs[a.1.val],a.2)) from h) with ⟨a,ha,rfl⟩
    rw [hd] at hm
    rcases List.mem_map.mp hm with ⟨i,_,he⟩
    exact hap i (he.symm ▸ List.mem_map_of_mem ha)
  have rootNot (r : VReg) (hr : ∀ i : Fin 8, regs[i.val] ≠ r) : r ∉ ps.map Prod.fst := by
    rw [hd]
    intro h
    rcases List.mem_map.mp h with ⟨i,_,he⟩
    exact hr i he
  refine multiply_batch_ok ps zr br qr hdno htno hap' hpa' (rootNot zr hzr)
    (by rw [hp]; exact hzt) (by rw [hp]; exact hbt) (rootNot qr hqr)
    (by rw [hp]; exact hqt) hz hzw hbw hqw fun t hc hv => ?_
  have hc' : VChg (pairs.map Prod.snd ++ (pairs.map Prod.fst).map (fun i => regs[i.val])) s t := by
    simpa only [hd,hp] using hc
  refine k t hc' (hbank.products hinj (pairs.map Prod.fst) (pairs.map Prod.snd) z hap hc' ?_)
  intro i hi e he
  rcases List.mem_map.mp hi with ⟨p,hp',rfl⟩
  exact hv (regs[p.1.val],p.2) (List.mem_map_of_mem hp') e he

end VG.Proof.MlDsa.AArch64.Optimized
