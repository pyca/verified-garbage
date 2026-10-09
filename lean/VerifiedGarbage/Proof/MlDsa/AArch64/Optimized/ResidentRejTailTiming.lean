import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailInspect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailAdjust
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTimingBlocks
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEnvTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

structure TailChecks (k : Nat) where
  countHint : VG.Taint.Hint VG.AArch64.Taint.T
  inspectHint : VG.Taint.Hint VG.AArch64.Taint.T
  count : (taint.check (Taint.ofRegs [.x19])
    (.block [.ldr .x .x4 .x19 (counts+8*k)]) countHint).isSome=true
  inspect : (taint.check (Taint.ofRegs [.x4,.x19,.x21])
    (.block (tailCursor k++tailRead k)) inspectHint).isSome=true

private theorem countLoad_ok {s : State} {k len : Nat} (hk : k<4)
    (hr : InRegions (s.rd++s.wr) (countAddress s k) 8)
    (hc : (s.mem.readW (countAddress s k) 64).toNat=256-len) :
    WP isa (.block [.ldr .x .x4 .x19 (counts+8*k)]) s fun t =>
      Only [.x4] s t ∧ (t.gpr .x4).toNat=256-len := by
  refine wp_ldrx (a := countAddress s k) (by unfold counts; omega) (by rfl) hr
    fun t ht et => wp_nil ⟨ht,?_⟩
  rw [et]; exact hc

/-- Cleanup's sole data-dependent decision is the masked final candidate;
its ignored overread byte is deliberately absent from this relation. -/
theorem zeroTailRaw_relCT {k len : Nat} {σ τ : State}
    (hk : k<4) (hl : len≤256) (checks : TailChecks k)
    (hsp : σ.sp=τ.sp) (h19 : σ.gpr .x19=τ.gpr .x19) (h21 : σ.gpr .x21=τ.gpr .x21)
    (crs : InRegions (σ.rd++σ.wr) (countAddress σ k) 8)
    (crt : InRegions (τ.rd++τ.wr) (countAddress τ k) 8)
    (cs : (σ.mem.readW (countAddress σ k) 64).toNat=256-len)
    (ct : (τ.mem.readW (countAddress τ k) 64).toNat=256-len)
    (rs : InRegions (σ.rd++σ.wr) (σ.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) 4)
    (rt : InRegions (τ.rd++τ.wr) (τ.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) 4)
    (hm : candidate σ.mem (σ.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005))=
      candidate τ.mem (τ.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005))) :
    RelCT isa (fun s t => s=σ ∧ t=τ) (Four.zeroTail k) (fun _ _ => True) := by
  have loadCT : RelCT isa (fun s t => s=σ ∧ t=τ)
      (.block [.ldr .x .x4 .x19 (counts+8*k)]) (fun _ _ => True) :=
    RelCT.taint (A := taint) (Taint.ofRegs [.x19])
      (fun _ _ h => by rcases h with ⟨rfl,rfl⟩; exact ⟨hsp,by simp [Taint.ofRegs,RegSet.mem_ofList,h19]⟩)
      checks.count
  unfold Four.zeroTail
  refine RelCT.seq (loadCT.wp (fun _ _ h => by
    rcases h with ⟨rfl,rfl⟩
    exact ⟨countLoad_ok hk crs cs,countLoad_ok hk crt ct⟩)) ?_
  apply RelCT.ite
  · intro s t h
    have he : s.gpr .x4=t.gpr .x4 := BitVec.eq_of_toNat_eq (h.2.1.2.trans h.2.2.2.symm)
    rw [eval_zero,eval_zero,he]
  · exact RelCT.block_nil (fun _ _ _ => True.intro)
  · intro s t tr ur s' t' h es et
    have ha := h.1.2.1.1
    have hb := h.1.2.2.1
    have hc := h.1.2.1.2
    have hd := h.1.2.2.2
    have sp : s.sp=t.sp := ha.sp.trans (hsp.trans hb.sp.symm)
    have e19 : s.gpr .x19=t.gpr .x19 := by rw [ha.get .x19,hb.get .x19]; exact h19
    have e21 : s.gpr .x21=t.gpr .x21 := by rw [ha.get .x21,hb.get .x21]; exact h21
    have e4 : s.gpr .x4=t.gpr .x4 := BitVec.eq_of_toNat_eq (hc.trans hd.symm)
    have wpS := tailInspect_ok hk hl hc (by rw [ha.rd,ha.wr,ha.get .x19]; exact rs)
    have wpT := tailInspect_ok hk hl hd (by rw [hb.rd,hb.wr,hb.get .x19]; exact rt)
    have inspectCT : RelCT isa (fun a b => a=s ∧ b=t)
        (.block (tailCursor k++tailRead k)) (fun _ _ => True) :=
      RelCT.taint (A := taint) (Taint.ofRegs [.x4,.x19,.x21])
        (fun _ _ h => by rcases h with ⟨rfl,rfl⟩; exact ⟨sp,by simp [Taint.ofRegs,RegSet.mem_ofList,e4,e19,e21]⟩)
        checks.inspect
    have result : RelCT isa (fun a b => a=s ∧ b=t)
        (.seq (.block (tailCursor k++tailRead k++tailAdjust))
          (.ite (.zero .x .x4) (.block [])
            (.loop (.block [.str .w .x9 .x3 0,.addImm .x .x3 .x3 4,.subImm .x .x4 .x4 1])
              (.nonzero .x .x4)))) (fun _ _ => True) := by
      apply blockPrefix
      refine RelCT.seq (inspectCT.wp (fun _ _ h => by rcases h with ⟨rfl,rfl⟩; exact ⟨wpS,wpT⟩)) ?_
      exact RelCT.taint (A := taint) (Taint.ofRegs [.x3,.x4,.x6,.x7])
        (fun a b hh => by
          obtain ⟨_,⟨ka,a3,a6,a7⟩,⟨kb,b3,b6,b7⟩⟩ := hh
          refine ⟨ka.sp.trans (sp.trans kb.sp.symm),?_⟩
          simp only [Taint.ofRegs,RegSet.mem_ofList,List.mem_cons,List.not_mem_nil,or_false]
          intro r hr
          rcases hr with rfl | rfl | rfl | rfl
          · rw [a3,b3,e21]
          · rw [ka.get .x4,kb.get .x4,e4]
          · apply BitVec.eq_of_toNat_eq
            rw [a6,b6,ha.mem,hb.mem,ha.get .x19,hb.get .x19]
            exact hm
          · exact BitVec.eq_of_toNat_eq (a7.trans b7.symm)) (by taint_decide)
    exact result _ _ _ _ _ _ ⟨rfl,rfl⟩ es et

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
