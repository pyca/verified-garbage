module
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.BoundedLayout
public import VerifiedGarbage.Impl.AesGcm.X86_64.BoundedGather
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Open
import VerifiedGarbage.Proof.AesGcm.X86_64.Seal
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-! Descriptor normalization before the shared bounded hardware call. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.DirectGather.Layout
open VG VG.X86_64 VG.X86_64.RegUpd Gather Short VG.Impl.AesGcm.X86_64.DirectGather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
variable {M : CtxMode} {s u : State}

theorem entryFrame2 (e : Initial s u) : Frame [⟨W s,2560⟩,below (SP s) 8] s.mem u.mem :=
  e.frame.sub (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact oneR_w)

theorem countWord (p : Layout M s) (e : Initial s u) :
    u.mem.readW (SP s+16#64) 64=stackArg s 1 ∧ InRegions (u.rd++u.wr) (SP s+16#64) 8 :=
  ⟨p.stack_word (entryFrame2 e) 1 (by decide),by rw [e.rd,e.wr]; exact (p.oneCtx M.ge).args 1 (by decide)⟩

theorem secondWord (p : Layout M s) (e : Initial s u) (c : Cnt s = 2) :
    u.mem.readW (Src s+16#64) 64=sb s 1 ∧ InRegions (u.rd++u.wr) (Src s+16#64) 8 := by
  have cont : (dsR s).Contains (Src s+16#64) 8 := Offset.contains_base _ (d:=16) (by change 16+8≤Cnt s*16; omega) (by decide)
  constructor
  · refine e.frame.readW cont (fun r hr => ?_) (by decide)
    rw [List.mem_singleton] at hr; subst r
    exact p.ds_w.sub_right (Lay.wSub (by decide))
  · rw [e.rd,e.wr,p.rd]; exact ⟨_,by simp,cont⟩

abbrev HeadReady (s t : State) := Initial s t ∧ t.gpr .rax=Src s
abbrev DataReady (s t : State) := HeadReady s t ∧ t.gpr .rbx=sb s 0 ∧ t.gpr .r10=BitVec.ofNat 64 (sl s 0) ∧
  t.zf=some (decide (Cnt s=2))
abbrev ArgsReady (s t : State) := Initial s t ∧ SpanEntryArgs (sb s 0) (secondSrc s) (sl s 0) t

theorem headReady (p : Layout M s) (e : Initial s u) : WP isa (.block descriptorHead) u (HeadReady s) := by
  have d := p.stack_word (entryFrame2 e) 0 (by decide)
  have a : InRegions (u.rd++u.wr) (SP s+8#64) 8 := by rw [e.rd,e.wr]; exact (p.oneCtx M.ge).args 0 (by decide)
  refine WP.of_runBlock ⟨_,by unfold descriptorHead; xrun [e.rsp,a,d],?_,rfl⟩
  refine OneEntry.keep (p.oneCtx M.ge).lay e ?_ rfl rfl (Frame.refl _ _)
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem dataReady (p : Layout M s) (c : Cnt s=1 ∨ Cnt s=2) (h : HeadReady s u) :
    WP isa (.block descriptorData) u (DataReady s) := by
  obtain ⟨e,ptr⟩ := h
  have f := p.first_args (by omega : 0<Cnt s) (entryFrame2 e) e.rd e.wr
  obtain ⟨v,pr⟩ := p.countWord e
  refine WP.of_runBlock ⟨_,by unfold descriptorData; xrun [BitVec.add_zero,e.rsp,ptr,pr,v,f.srcR,f.src,f.sizeR,f.size],⟨?_,?_⟩,rfl,rfl,?_⟩
  · refine OneEntry.keep (p.oneCtx M.ge).lay e ?_ rfl rfl (Frame.refl _ _)
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · exact ptr
  · rcases c with one|two
    · have eq : stackArg s 1=1#64 := BitVec.eq_of_toNat_eq one
      simp only [one,eq]; rfl
    · have eq : stackArg s 1=2#64 := BitVec.eq_of_toNat_eq two
      simp only [two,eq]; rfl

theorem argsReady (p : Layout M s) (c : Cnt s=1 ∨ Cnt s=2) (e : Initial s u) :
    WP isa gatherArgs u (ArgsReady s) := by
  refine WP.seq (WP.mono (p.headReady e) fun v hv => WP.seq (WP.mono (p.dataReady c hv) fun t ht => ?_))
  obtain ⟨⟨e,ptr⟩,left,len,flag⟩ := ht
  refine WP.ite (decide (Cnt s=2)) (by simp only [eval,flag]) (fun yes => ?_) (fun no => ?_)
  · have two := of_decide_eq_true yes
    obtain ⟨v,pr⟩ := p.secondWord e two
    refine WP.of_runBlock ⟨_,by xrun [ptr,v,pr],?_,?_,?_,?_⟩
    · refine OneEntry.keep (p.oneCtx M.ge).lay e ?_ rfl rfl (Frame.refl _ _)
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
    · exact left
    · simp [secondSrc,two, gpr_setReg]
    · exact len
  · have one := of_decide_eq_false no
    refine WP.of_runBlock ⟨_,by xrun [left],?_,?_,?_,?_⟩
    · refine OneEntry.keep (p.oneCtx M.ge).lay e ?_ rfl rfl (Frame.refl _ _)
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
    · exact left
    · simp [secondSrc,one,gpr_setReg]
    · exact len

end VG.Proof.AesGcm.X86_64.DirectGather.Layout
