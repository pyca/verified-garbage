module
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.BoundedSpans
public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Post
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Mid
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Aes.KeyWords
public import VerifiedGarbage.Impl.AesGcm.X86_64.BoundedGather
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Open
import VerifiedGarbage.Proof.AesGcm.X86_64.Seal
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-! The two public gather descriptors bind the same source-span contract as the in-place entry. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.DirectGather.Layout
open VG VG.X86_64 Gather Short
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
variable {M : CtxMode} {s t : State}

def secondSrc (s : State) : Addr := if Cnt s = 2 then sb s 1 else sb s 0

private theorem one_len (h : Layout M s) (one : Cnt s = 1) : sl s 0 = L s := by
  simpa only [one,gl_succ,gl_zero,Nat.zero_add] using h.glen

private theorem two_len (h : Layout M s) (two : Cnt s = 2) : sl s 0 + sl s 1 = L s := by
  simpa only [two,gl_succ,gl_zero,Nat.zero_add] using h.glen

theorem boundedGeo (h : Layout M s) (cnt : Cnt s = 1 ∨ Cnt s = 2) :
    SpanLayout s (sb s 0) (secondSrc s) (Dst s) (W s) (SP s) (sl s 0) (L s) := by
  have m := slice_mem s (i:=0) (by omega : 0<Cnt s)
  have first : sl s 0 ≤ L s := by
    rcases cnt with c|c
    · exact Nat.le_of_eq (one_len h c)
    · have eq := two_len h c
      omega
  have depth : (below (SP s) 24).Sub (below (SP s) 56) := below_sub (by decide) (by decide)
  have tail (lt : sl s 0 < L s) : Cnt s = 2 := cnt.resolve_left (fun c => Nat.ne_of_lt lt (one_len h c))
  refine ⟨first,?_,.inr (h.ls _ m).1,(h.ls _ m).2.2,((h.b_ls _ m).sub_left depth).symm,?_,?_,?_,?_⟩
  · rw [h.rd]; exact covers_of_mem (by simp [m])
  all_goals
    intro lt
    have c := tail lt
    have eq : L s - sl s 0 = sl s 1 := by have := two_len h c; omega
    have j := slice_mem s (i:=1) (by omega : 1<Cnt s)
    simp only [secondSrc,c,ite_true,eq]
  · rw [h.rd]; exact covers_of_mem (by simp [j])
  · exact .inr (h.ls _ j).1
  · exact (h.ls _ j).2.2
  · exact ((h.b_ls _ j).sub_left depth).symm

theorem spanPlain (h : Layout M s) (cnt : Cnt s = 1 ∨ Cnt s = 2) :
    spanBytes s (sb s 0) (secondSrc s) (sl s 0) (L s) = pt s (Cnt s) := by
  have base : pt s 0 = [] := rfl
  rcases cnt with c|c
  · have eq := one_len h c
    simp only [spanBytes,←eq,Nat.sub_self,bytesAt,List.range_zero,List.map_nil,List.append_nil,c,pt_succ,base,List.nil_append]
  · have eq : L s-sl s 0=sl s 1 := by have := two_len h c; omega
    simp only [spanBytes,eq,secondSrc,c,ite_true,pt_succ,base,List.nil_append]

theorem boundedDone (h : Layout M s) (cnt : Cnt s = 1 ∨ Cnt s = 2)
    (post : SealPostFrom s (K s) (W s) (SP s) (Dst s) (L s) (R s) (AL s).toNat (hk s)
      (Spec.Gcm.j0 (hk s) (iv s)) (ad s) (spanBytes s (sb s 0) (secondSrc s) (sl s 0) (L s)) t) :
    BodyDone M s t := by
  obtain ⟨env,rd,wr,saved,frame,text,tag⟩ := post
  refine ⟨env,rd,wr,saved,frame.sub ?_,(h.spanPlain cnt) ▸ text,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact ⟨_,List.mem_cons_self ..,fun _ x => x⟩
    · exact ⟨dR s,by simp [changed],fun _ x => x⟩
    · exact ⟨below (SP s) 56,by simp [changed],below_sub (by decide) (by decide)⟩
  · rw [Proof.Gcm.fullTag_eq]
    rw [show (ad s).length=(AL s).toNat from VG.Proof.Aes.KeyWords.length_bytesAt .., VG.Proof.Aes.KeyWords.length_bytesAt]
    exact tag

end VG.Proof.AesGcm.X86_64.DirectGather.Layout

/-! Descriptor normalization before the shared bounded hardware call. -/
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
