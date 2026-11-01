module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.GatherSplit.View
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: the shared split-seal contract follows from the gather layout.
/-! # Buffer separation for the split-seal call -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.GatherSplit
open VG VG.PPC64LE
open VG.Proof.AesGcm.PPC64LE.Gather


theorem callee_stack_sub {s : State} (h : Layout s) :
    Region.Sub (below (Pf s) 2800) (below s.sp 2960) := by
  rw [← h.base.pf_eq]
  exact below_body' s.sp 160 2800


theorem outgoing_sub (s : State) : Region.Sub (outgoingRegion s) (stkR s) := by
  change Region.Sub ⟨Pf s+BitVec.ofNat 64 96,24⟩ ⟨Bs s,2832⟩
  rw [pf_off]
  exact stk_sub s _ _ (by decide)


theorem callee_outgoing (s : State) : (below (Pf s) 2800).Disjoint (outgoingRegion s) := by
  have ha : Pf s+BitVec.ofNat 64 96=(Pf s-BitVec.ofNat 64 2800)+BitVec.ofNat 64 2896 := by
    rw [show 2896=2800+96 by decide,← Offset.add_ofNat_add_ofNat,BitVec.sub_add_cancel]
  change Region.Disjoint ⟨Pf s-BitVec.ofNat 64 2800,2800⟩ ⟨Pf s+BitVec.ofNat 64 96,24⟩
  rw [ha]
  exact (Offset.disjoint_base _ (by decide) (by decide)).symm


theorem frame_sp_nat {s : State} (h : Gather.Lay s) : (Pf s).toNat+160=s.sp.toNat := by
  have hn := h.hBn
  have hs := congrArg BitVec.toNat h.hB
  rw [BitVec.toNat_add,BitVec.toNat_ofNat] at hs
  rw [h.pf_toNat]
  omega


theorem prepared_layout {s e c : State} (h : Layout s) (he : Gather.Entered s e)
    (hc : 0<Cnt s) (hp : Prepared s e c) : CallLayout (callView s e c) := by
  obtain ⟨rd,wr,cd,ct,nd,nt,ad,at_,dsd,dst,lsdt,dt,darg,targ,bc,bn,ba,bds,bl,barg,bd,bt,
    oc,on,oa,ods,ol,od,ot,w₁,w₂,hR,hgl⟩ := h.base.pre
  obtain ⟨rc,rn,ra,rs,rD,rt,rargs⟩ := hp.view_regions
  have hsp : (callView s e c).sp=Pf s := hp.sp
  have hsn := frame_sp_nat h.base
  have hspace := h.space
  have hsource := source_listed h.base he hc
  have apart {r : Region}
      (hr : r∈[cR s,nR s,aR s,dsR s]++lsR s++[dR s,tgR s,argR s]) :
      (below (Pf s) 2800).Disjoint r := (h.stack r hr).sub_left (callee_stack_sub h)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hsp]
    omega
  · rw [hsp]
    omega
  · change callRead s e=_
    rw [rc,rn,ra,rs,rargs]
    rfl
  · change callWrite s=_
    rw [rD,rt]
    rfl
  · rw [rc,rn,ra,rs,rD]
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    exacts [cd,nd,ad,(lsdt _ hsource).1]
  · rw [rc,rn,ra,rs,rD,rt]
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl
    exacts [ct,nt,at_,(lsdt _ hsource).2,dt]
  · rw [rD,rt,rargs]
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    exacts [h.base.bd.symm.sub_right (outgoing_sub s),h.base.bt.symm.sub_right (outgoing_sub s)]
  · rw [rc,rn,ra,rs,rD,rt,rargs,hsp]
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact apart (by simp)
    · exact apart (by simp)
    · exact apart (by simp)
    · exact apart (by simp [hsource])
    · exact apart (by simp)
    · exact apart (by simp)
    · exact callee_outgoing s
  · rw [rc,rn,ra,rs,rD,rt]
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
    exacts [oc,on,oa,ol _ hsource,od,ot]
  · rw [hp.view_gpr (by decide)]
    exact hR
  · change (c.callEntry.gpr .r10).toNat≤(stackArg (callView s e c) 1).toNat
    rw [State.callEntry_gpr c (by decide),hp.length,hp.view_arg (by decide)]
    exact first_bound (gatherPre_of h.base he) hc

end VG.Proof.AesGcm.PPC64LE.GatherSplit
