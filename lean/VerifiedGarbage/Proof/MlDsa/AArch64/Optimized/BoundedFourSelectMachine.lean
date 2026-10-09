import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourState

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (vectorVal acceptedIndices)

/-- The vector parser through reduction and table compaction, before its store. -/
def selectCode (η : Nat) : List Instr :=
 (extractCode++acceptCode++maskCode)++
 (([.lsl .x .x6 .x6 6,.add .x .x13 .x12 .x6] : List Instr)++
 (([.ldrq .v6 .x13 0,.ldr .x .x6 .x13 32] : List Instr)++
 (vectorVal η++[.vop (.tbl .v1 .v1 .v6)])))

theorem selectCode_ok {η : Nat} (hη : η=2∨η=4) {s : State} {p : Addr}
    (hC : Consts η p s) (hT : TableAt s.mem p)
    (hR : ∀m<16,InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 (64*m)) 16 ∧
      InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 (64*m)+32) 8) :
    WP isa (.block (selectCode η)) s fun t=>
      Keep [.x6,.x7,.x13] s t ∧ t.mem=s.mem ∧
      t.gpr .x6=BitVec.ofNat 64 (sourceValues η s).length ∧
      (∀i<(sourceValues η s).length,vword (t.v .v1) i=
        VG.Proof.MlDsa.Sample.zw ((sourceValues η s).getD i 0)) ∧
      (∀r,r∉bodyVecs→t.v r=s.v r) := by
  unfold selectCode
  rw [WP.block_append_iff]
  refine WP.mono (nibbleMask_ok hη s hC.nibble hC.expand hC.bound hC.weights hC.mask)
    fun a ⟨hak,ham,hamask,han,hav⟩=>?_
  rw [WP.block_append_iff]
  have hma:=sourceMask_lt η s
  refine WP.mono (tableAddress_ok (s := a) (p := p) (mask := sourceMask η s) hma (by rw [hak.gpr .x12 (by decide)]; exact hC.table) hamask)
    fun b ⟨⟨⟨hbaddr,hbm⟩,hbk⟩,hbv⟩=>?_
  rw [WP.block_append_iff]
  have hbk' : Keep [.x6,.x7,.x13] s b:=(hak.trans hbk).mono (by decide)
  have hbmem : b.mem=s.mem:=hbm.trans ham
  refine WP.mono (tableRead_ok (s := b) (p := p) (mask := sourceMask η s) hma (by rw [hbmem]; exact hT) hbaddr
    (by rw [hbk'.rd,hbk'.wr,hbaddr]; exact (hR _ hma).1)
    (by rw [hbk'.rd,hbk'.wr,hbaddr]; exact (hR _ hma).2))
    fun c ⟨hck,hcm,hc6,hcount,hcv⟩=>?_
  have hck' : Keep [.x6,.x7,.x13] s c:=(hbk'.trans hck).mono (by decide)
  have hcmem : c.mem=s.mem:=hcm.trans hbmem
  have hvc (r : VReg) (hr : r∉bodyVecs) : c.v r=s.v r := by
    rw [hcv r (by intro he; subst r; exact hr (by decide)),hbv]
    exact hav r (by
      intro he
      apply hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl|rfl|rfl <;> decide)
  have hcn (e : Nat) (he:e<4) : vword (c.v .v1) e=nibbleWord (s.v .v0) e := by
    rw [hcv .v1 (by decide),hbv]; exact han e he
  refine valueCompact_ok hη hma
    (fun e he=>by rw [hvc .v18 (by decide)]; exact hC.thirteen e he)
    (fun e he=>by rw [hvc .v19 (by decide)]; exact hC.five e he)
    (fun e he=>by rw [hvc .v21 (by decide)]; exact hC.q e he)
    (fun e he=>by rw [hvc .v20 (by decide)]; exact hC.etaQ e he) hc6
    (fun e he=>by rw [hcn e he]; exact nibbleWord_bound _ _) fun t ht hv=>?_
  apply VG.Proof.MlKem.AArch64.wp_nil
  refine ⟨(hck'.trans ht.keep).mono (by decide),ht.mem.trans hcmem,?_,?_,?_⟩
  · rw [ht.gpr,hcount,sourceMask_count]
  · intro i hi
    have hii : i<(acceptedIndices (sourceMask η s)).length:=by rwa [sourceMask_count]
    rw [hv i hii,hcn _ (index_bound _ hma i hii)]
    change BitVec.ofNat 32 (Spec.MlDsa.ofInt (VG.Proof.MlDsa.Sample.rbC η
      (sourceNibble s ((acceptedIndices (sourceMask η s))[i]!)))).val=_
    rw [sourceValues_lane η s hii]
  · intro r hr
    rw [ht.v r (by
      intro he
      apply hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl|rfl <;> decide)]
    exact hvc r hr

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
