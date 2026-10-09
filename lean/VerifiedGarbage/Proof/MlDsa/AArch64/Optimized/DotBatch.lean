import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotTerms
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductBatch

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized

def dotResult (s : State) (n off e : Nat) : BitVec 32 :=
  centeredDot (fun k => dotInput s .x13 off k e) (fun k => dotInput s .x14 off k e) n

/-- Several direct product loads retain every destination while reusing the
same temporary registers. This is the raw inverse's resident input bank. -/
theorem dotBatch_ok {n : Nat} (hpos : 0<n) (ops : List (VReg × Nat))
    (hn : (ops.map Prod.fst).Nodup)
    (hd : ∀ d off, (d,off)∈ops → d∉productTemps ∧ d≠.v30 ∧ d≠.v31)
    {s : State} (hc : ProductConstants s)
    (hr : ∀ d off, (d,off)∈ops → ∀j<n,(1024*j+off)%16=0 ∧ 1024*j+off<4096*16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (1024*j+off)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*j+off)) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg (productClobs ops) s t → ProductConstants t →
      (∀ d off, (d,off)∈ops → ∀ e<4, vword (t.v d) e=dotResult s n off e) →
      WP isa (.block rest) t Q) :
    WP isa (.block (ops.flatMap (fun p => dotLoad n p.1 p.2) ++ rest)) s Q := by
  induction ops generalizing s with
  | nil => exact k s (VChg.refl _ _) hc (by simp)
  | cons op ops ih =>
    rcases op with ⟨d,off⟩
    have hh := hd d off (by simp)
    have rr := hr d off (by simp)
    have nn := List.nodup_cons.mp hn
    simp only [List.flatMap_cons,List.append_assoc]
    refine dotLoad_ok hpos hh.2.1 hh.2.2 hc
      (fun j hj => ⟨(rr j hj).1,(rr j hj).2.1⟩)
      (fun j hj => (rr j hj).2.2) fun a ha ca va => ?_
    refine ih nn.2 (fun d off hm => hd d off (List.mem_cons_of_mem _ hm)) ca ?_ ?_
    · intro d off hm j hj
      rw [ha.rd,ha.wr,ha.gpr]
      exact hr d off (List.mem_cons_of_mem _ hm) j hj
    · intro t ht ct vt
      have hst : VChg (productClobs ((d,off)::ops)) s t := (ha.trans ht).mono (by
        intro r hm
        simp only [productClobs,productTemps,List.map_cons,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
        grind only)
      refine k t hst ct ?_
      intro d' off' hm e he
      rcases List.mem_cons.mp hm with h | h
      · cases h
        rw [ht.get d (by
          simp only [productClobs,List.mem_append]
          exact fun h => h.elim hh.1 nn.1),va e he]
        rfl
      · rw [vt d' off' h e he]
        simp only [dotResult,dotInput_chg ha]

end VG.Proof.MlDsa.AArch64.Optimized
