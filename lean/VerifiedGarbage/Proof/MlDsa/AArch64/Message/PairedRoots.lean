import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.PairedPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsFrame

namespace VG.Proof.MlDsa.AArch64.Message.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots PairedRoots StaticTable pairedSignRootConsts)
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Impl.MlDsa.AArch64.Message

/-- The wrapper's hash workspace and stack cannot change either root table. -/
theorem roots_ctx {p : Params} {s t : State} {g : Reg → BitVec 64} {v : VReg → BitVec 128}
    (h : SPre p s) (hc : Ctx (slay p s) g v s.mem t) (hy : t.syms=s.syms) :
    StaticRoots 16 t := by
  have transfer {nm : String} {ws : List (BitVec 64)} (hr : StaticTable 16 nm ws s) : StaticTable 16 nm ws t := by
    refine hr.frame hc.frame ?_ hc.rd hc.wr hc.sp hy
    intro r hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl
    · exact (hr.writable _ (by rw [h.wr]; simp)).sub_right (slay_X p s).sub
    · exact hr.stack
  exact ⟨transfer h.roots.forward,transfer h.roots.inverse⟩

/-- A constants-aware ABI precondition is the ordinary buffer precondition
plus explicit roots, with their read permissions retained at the call. -/
theorem sign_pre_extend {p : Params} {s : State}
    (h : (signContract p abi 16).pre (s.withRegions
      [⟨s.gpr .x0,p.skLen⟩,⟨s.gpr .x1,64⟩,⟨s.gpr .x2,32⟩] s.wr))
    (hr : StaticRoots 16 s) (rp : PairedRoots 16 s)
    (hd : s.rd=[⟨s.gpr .x0,p.skLen⟩,⟨s.gpr .x1,64⟩,⟨s.gpr .x2,32⟩]++rootRegions s) :
    (signContract p (abi.withConsts pairedSignRootConsts) 16).pre s := by
  sig_pre [signContract,signSig,abi,argRegs,List.range,List.range.loop] at h
  sig_pre [signContract,signSig,abi,argRegs,Abi.withConsts,
    VG.Proof.MlDsa.AArch64.Sign.pairedSignRootConsts_eq,Abi.constRegions,Abi.constsHeld,
    TableConstants.staticNttWords_length,InverseTable.expandedWords_length,PairedTable.expandedWords_length,stackBelow,
    List.range,List.range.loop]
  obtain ⟨sp,wr,d1,d2,h⟩ := h
  obtain ⟨d3,d4,d5,d6,d7,h⟩ := h
  obtain ⟨k1,k2,k3,k4,k5,n1,n2,n3,n4,n5⟩ := h
  exact ⟨sp,by rw [hd]; rfl,hr.forward.held,hr.inverse.held,rp.held,hr.forward.fit,hr.forward.writable,
    hr.forward.stack,hr.inverse.fit,hr.inverse.writable,hr.inverse.stack,rp.fit,rp.writable,rp.stack,by rw [hd]; rfl,
    wr,d1,d2,d3,d4,d5,d6,d7,k1,k2,k3,k4,k5,n1,n2,n3,n4,n5⟩

/-- Reborrowing for the inner signer retains both tables and narrows only
writable buffers; the immutable addresses remain those of the symbol map. -/
theorem roots_reborrow {s : State} {rd wr : List Region} (h : StaticRoots 16 s)
    (hr : rootRegions s⊆rd) (hw : Covers wr s.wr) :
    StaticRoots 16 (s.callEntry.withRegions rd wr) := by
  have transfer {nm : String} {ws : List (BitVec 64)} (ht : StaticTable 16 nm ws s)
      (hm : (⟨s.syms nm,3904⟩ : Region)∈rd) :
      StaticTable 16 nm ws (s.callEntry.withRegions rd wr) := by
    refine ⟨ht.held,ht.fit,?_,?_,ht.stack⟩
    · apply Covers.one
      exact ⟨⟨s.syms nm,3904⟩,List.mem_append_left _ hm,Region.contains_self _ _⟩
    · intro r hmem
      exact ht.apart_write (hw r.base r.len ⟨r,hmem,Region.contains_self _ _⟩)
  exact ⟨transfer h.forward (hr (by simp [rootRegions])),
    transfer h.inverse (hr (by simp [rootRegions]))⟩

theorem paired_ctx {p : Params} {s t : State} {g : Reg → BitVec 64} {v : VReg → BitVec 128}
    (h : SPre p s) (hc : Ctx (slay p s) g v s.mem t) (hy : t.syms=s.syms) :
    PairedRoots 16 t := by
  refine h.paired.frame hc.frame ?_ hc.rd hc.wr hc.sp hy
  intro r hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl|rfl
  · exact (h.paired.writable _ (by rw [h.wr]; simp)).sub_right (slay_X p s).sub
  · exact h.paired.stack

theorem paired_reborrow {s : State} {rd wr : List Region} (h : PairedRoots 16 s)
    (hr : rootRegions s⊆rd) (hw : Covers wr s.wr) :
    PairedRoots 16 (s.callEntry.withRegions rd wr) := by
  refine ⟨h.held,h.fit,?_,?_,h.stack⟩
  · apply Covers.one
    exact ⟨⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩,
      List.mem_append_left _ (hr (by simp [rootRegions])),Region.contains_self _ _⟩
  · intro r hm
    exact h.apart_write (hw r.base r.len ⟨r,hm,Region.contains_self _ _⟩)

end VG.Proof.MlDsa.AArch64.Message.Paired
