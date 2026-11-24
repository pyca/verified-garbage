module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.Joined
import VerifiedGarbage.Proof.Framework.Offset

/-! # Derive the fused POWER subcall permissions from the contiguous payload bounds -/

public section
namespace VG.Proof.AesGcm.PPC64LE.Contiguous
open VG VG.PPC64LE
open VG.Proof.AesGcm.PPC64LE.DirectGather (Range)

structure PayloadSpace (s : State) : Prop where
  perm : Perm (s.gpr .r29) (s.gpr .r30) (s.gpr .r31) s
  layout : Lay (s.gpr .r29) (s.gpr .r30) (s.gpr .r31)
  bounds : Range s.gpr s (s.gpr .r19) (s.gpr .r27) (datLen s)
  slabSrc : (srcRegion s).Disjoint (slab s)
  slabDst : (dat s).Disjoint (slab s)
  slabCtx : (ctxRegion s).Disjoint (slab s)
  slabSt : (⟨s.gpr .r30,80⟩ : Region).Disjoint (slab s)
  slabWrite : Covers [slab s] s.wr

theorem PayloadSpace.core {s : State} (h : PayloadSpace s) (R : roundsOf s=10 ∨ roundsOf s=12 ∨ roundsOf s=14) :
    CoreIn s := by
  have hk : 16*fusedBlocks s≤datLen s := by
    change 16*(8*(datLen s/128))≤datLen s;omega
  let st := s.gpr .r30
  have cb : Region.Sub ⟨st+48,16⟩ ⟨st,80⟩ := Offset.sub_base _ (by decide)
  have y : Region.Sub ⟨st+16,16⟩ ⟨st,80⟩ := Offset.sub_base _ (by decide)
  have area := Region.sub_prefix (base := s.gpr .r27) hk
  have sarea := Region.sub_prefix (base := s.gpr .r19) hk
  have ds := (h.bounds.dst.ok.st.sub_left area).symm
  have cp := h.layout.cs
  have fu : FusedAccess s := by
    refine ⟨h.bounds.dst.ctx.sub_right area,cp.sub_right cb,cp.sub_right y,ds.sub_left cb,ds.sub_left y,?_,?_,?_,R⟩
    · intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl
      · exact h.slabCtx
      · exact h.slabSt.sub_left cb
      · exact h.slabSt.sub_left y
      · exact h.slabDst.sub_left area
    · rcases h.bounds.buffers with eq|apart
      · exact .inl eq
      · right
        intro r hr
        simp only [fusedWrite,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl
        · exact (h.bounds.src.st.sub_left sarea).sub_right cb
        · exact (h.bounds.src.st.sub_left sarea).sub_right y
        · exact (apart.sub_left sarea).sub_right area
        · exact h.slabSrc.sub_left sarea
    · exact Nat.le_trans (Nat.add_le_add_left hk _) h.bounds.dst.ok.fit
  have write : Covers (fusedWrite s) s.wr := Covers.cons (covers_off h.perm.st (by decide) (by decide))
    (Covers.cons (covers_off h.perm.st (by decide) (by decide)) (Covers.cons (covers_prefix h.bounds.dst.wr hk) h.slabWrite))
  exact ⟨h.perm,h.layout,h.bounds,h.slabSrc,h.slabDst,h.slabCtx,fu,
    (Covers.cons h.perm.ctx (covers_prefix h.bounds.src.rd hk)).append_left write.right,write⟩

private theorem rest_sub (s : State) : (restR s).Sub (dat s) :=
  Offset.sub_base _ (Nat.le_of_eq (Nat.add_sub_of_le (DirectGather.prefixLe _)))

theorem PayloadSpace.ctx {s : State} (h : PayloadSpace s) : ∀ r∈cipherFrame s,(ctxRegion s).Disjoint r := by
  intro r hr
  simp only [cipherFrame,prefixAreas,crFrame,taFrame,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact h.layout.cs.sub_right (Lay.stSub (by decide))
  · exact h.layout.cs.sub_right (Lay.stSub (by decide))
  · exact h.bounds.dst.ctx.sub_right (Region.sub_prefix (DirectGather.prefixLe _))
  · exact h.slabCtx
  · exact h.bounds.dst.ctx.sub_right (rest_sub s)
  · exact h.layout.cs.sub_right (Lay.stSub (by decide))
  · exact h.layout.cs.sub_right (Lay.stSub (by decide))
  · exact h.layout.cs.sub_right (Lay.stSub (by decide))
  · exact h.layout.cw'.sub_right (Lay.wSub (by decide))

theorem PayloadSpace.counter {s : State} (h : PayloadSpace s) : ∀ r∈cipherFrame s,(⟨s.gpr .r30,16⟩ : Region).Disjoint r := by
  have sub : (⟨s.gpr .r30,16⟩ : Region).Sub ⟨s.gpr .r30,80⟩ := Region.sub_prefix (by decide)
  have dst := h.bounds.dst.ok.st.symm.sub_left sub
  have apart (d n : Nat) (l : 16≤d) (hi : d+n≤80) :
      (⟨s.gpr .r30,16⟩ : Region).Disjoint ⟨s.gpr .r30+BitVec.ofNat 64 d,n⟩ := by
    simpa only [BitVec.add_zero] using Lay.st_st (st:=s.gpr .r30) (a:=0) (n:=16) (d:=d) (k:=n) (.inl l) (by decide) hi
  intro r hr
  simp only [cipherFrame,prefixAreas,crFrame,taFrame,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact apart 48 16 (by decide) (by decide)
  · exact apart 16 16 (by decide) (by decide)
  · exact dst.sub_right (Region.sub_prefix (DirectGather.prefixLe _))
  · exact h.slabSt.sub_left sub
  · exact dst.sub_right (rest_sub s)
  · exact apart 48 32 (by decide) (by decide)
  · exact apart 16 16 (by decide) (by decide)
  · exact apart 32 16 (by decide) (by decide)
  · simpa only [BitVec.add_zero] using h.layout.st_w (a:=0) (n:=16) (d:=96) (k:=16) (by decide) (.inr ⟨by decide,by decide⟩)

end VG.Proof.AesGcm.PPC64LE.Contiguous
