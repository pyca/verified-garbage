import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductLoad

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized

def productTemps : List VReg := [.v16,.v17,.v18,.v19,.v20]
def productClobs (ops : List (VReg × Nat)) : List VReg := productTemps ++ ops.map Prod.fst

def productInput (s : State) (off e : Nat) : BitVec 32 :=
  centeredProduct (vword (s.mem.read (s.gpr .x13+BitVec.ofNat 64 off) 16) e)
    (vword (s.mem.read (s.gpr .x14+BitVec.ofNat 64 off) 16) e)

/-- Several direct product loads retain every destination while reusing the
same temporary registers. This is the raw inverse's resident input bank. -/
theorem productBatch_ok (ops : List (VReg × Nat))
    (hn : (ops.map Prod.fst).Nodup)
    (hd : ∀ d off, (d,off)∈ops → d∉productTemps ∧ d≠.v30 ∧ d≠.v31)
    {s : State} (hc : ProductConstants s)
    (hr : ∀ d off, (d,off)∈ops → off%16=0 ∧ off<4096*16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 off) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 off) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg (productClobs ops) s t → ProductConstants t →
      (∀ d off, (d,off)∈ops → ∀ e<4, vword (t.v d) e=productInput s off e) →
      WP isa (.block rest) t Q) :
    WP isa (.block (ops.flatMap (fun p => productLoad p.1 p.2) ++ rest)) s Q := by
  induction ops generalizing s with
  | nil => exact k s (VChg.refl _ _) hc (by simp)
  | cons op ops ih =>
    rcases op with ⟨d,off⟩
    have hh := hd d off (by simp)
    have rr := hr d off (by simp)
    have nn := List.nodup_cons.mp hn
    simp only [List.flatMap_cons,List.append_assoc]
    refine productLoad_ok hh.2.1 hh.2.2 hc ⟨rr.1,rr.2.1⟩ rr.2.2.1 rr.2.2.2 fun a ha ca va => ?_
    refine ih nn.2 (fun d off hm => hd d off (List.mem_cons_of_mem _ hm)) ca ?_ ?_
    · intro d off hm
      rw [ha.rd,ha.wr,ha.gpr]
      exact hr d off (List.mem_cons_of_mem _ hm)
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
        unfold productInput
        rw [ha.mem,ha.gpr]

end VG.Proof.MlDsa.AArch64.Optimized
