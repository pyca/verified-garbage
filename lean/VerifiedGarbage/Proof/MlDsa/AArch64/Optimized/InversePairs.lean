import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Batch

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

/-- One independent inverse butterfly before reciprocal multiplication. -/
structure PairRegs where
  left : VReg
  right : VReg
  free : VReg
  deriving DecidableEq, Inhabited

def PairRegs.all (p : PairRegs) : List VReg := [p.left,p.right,p.free]
def PairRegs.writes (p : PairRegs) : List VReg := [p.free,p.left]
def PairRegs.code (p : PairRegs) : List Instr :=
  [.vop (.sub .s4 p.free p.left p.right),.vop (.add .s4 p.left p.left p.right)]

def pairWrites (ps : List PairRegs) : List VReg := ps.flatMap PairRegs.writes

theorem pairWrites_subset (ps : List PairRegs) {r : VReg} (hr : r∈pairWrites ps) :
    r∈ps.flatMap PairRegs.all := by
  rcases List.mem_flatMap.mp hr with ⟨p,hp,hr⟩
  apply List.mem_flatMap.mpr ⟨p,hp,?_⟩
  simp only [PairRegs.writes,PairRegs.all,List.mem_cons,List.not_mem_nil,or_false] at *
  grind only

/-- Interleaving SUB and ADD for disjoint pairs preserves every original input
needed by the remaining pairs. The proof records the whole read/write set. -/
theorem pairs_ok (ps : List PairRegs) (hn : (ps.flatMap PairRegs.all).Nodup)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg (pairWrites ps) s t →
      (∀ p∈ps, t.v p.left=VArr.s4.map2 (fun _ a b => a+b) (s.v p.left) (s.v p.right) ∧
        t.v p.free=VArr.s4.map2 (fun _ a b => a-b) (s.v p.left) (s.v p.right)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (ps.flatMap PairRegs.code ++ rest)) s Q := by
  induction ps generalizing s with
  | nil => exact k s (VChg.refl _ _) (by simp)
  | cons p ps ih =>
    have hn' := List.nodup_append.mp hn
    have hd : ∀ r∈p.all, r∉ps.flatMap PairRegs.all := by
      intro r hr hm
      exact hn'.2.2 r hr r hm rfl
    have hab : p.left≠p.free ∧ p.right≠p.free := by
      have hh := hn'.1
      simp only [PairRegs.all,List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false] at hh
      grind only
    have leftKeep {r : VReg} (hr : r∈p.all) : r∉pairWrites ps := by
      intro hm
      exact hd _ hr (pairWrites_subset ps hm)
    have rightKeep {q : PairRegs} (hq : q∈ps) {r : VReg} (hr : r∈q.all) : r∉[p.free,p.left] := by
      have hm : r∈ps.flatMap PairRegs.all := List.mem_flatMap.mpr ⟨q,hq,hr⟩
      intro hw
      have hw' : r∈p.all := by
        simp only [PairRegs.all,List.mem_cons,List.not_mem_nil,or_false] at *
        grind only
      exact hd _ hw' hm
    simp only [List.flatMap_cons,PairRegs.code,List.cons_append,List.nil_append]
    refine renamed_pair_ok hab.1 hab.2 fun a ha hsum hdiff => ?_
    have hs : a.v p.left=VArr.s4.map2 (fun _ x y => x+y) (s.v p.left) (s.v p.right) := by
      apply vec_ext
      intro e he
      rw [hsum e he,VG.AArch64.vword_map2 _ _ _ he]
    have hdf : a.v p.free=VArr.s4.map2 (fun _ x y => x-y) (s.v p.left) (s.v p.right) := by
      apply vec_ext
      intro e he
      rw [hdiff e he,VG.AArch64.vword_map2 _ _ _ he]
    refine ih hn'.2.1 fun t ht hv => ?_
    refine k t (ha.trans ht) ?_
    intro q hq
    rcases List.mem_cons.mp hq with hq | hq
    · subst q
      rw [ht.get p.left (leftKeep (by simp [PairRegs.all])),
        ht.get p.free (leftKeep (by simp [PairRegs.all]))]
      exact ⟨hs,hdf⟩
    · have he := hv q hq
      rw [ha.get q.left (rightKeep hq (by simp [PairRegs.all])),
        ha.get q.right (rightKeep hq (by simp [PairRegs.all]))] at he
      exact he

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
