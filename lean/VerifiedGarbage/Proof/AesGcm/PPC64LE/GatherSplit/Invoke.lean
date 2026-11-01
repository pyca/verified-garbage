module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.GatherSplit.InvokeLayout
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: call the already verified split-seal entry through its public contract.
/-! # Calling split seal -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.GatherSplit
open VG VG.PPC64LE
open VG.Proof.AesGcm.PPC64LE.Gather

abbrev SplitOk : Prop := ∀ s,(Proof.Gcm.sealSplitContract PPC64LE.abi 2800).pre s →
  ∃ t z,Exec isa Impl.AesGcm.PPC64LE.GatherSplit.sealCode s t z ∧ abiPreserved s z ∧
    (Proof.Gcm.sealSplitContract PPC64LE.abi 2800).post s z


theorem Prepared.covers {s e c : State} (h : Gather.Lay s) (he : Gather.Entered s e)
    (hc : 0<Cnt s) (hp : Prepared s e c) :
    VG.Covers (callRead s e++callWrite s) (c.rd++c.wr) ∧ VG.Covers (callWrite s) c.wr := by
  have hs := source_listed h he hc
  constructor
  · apply VG.Covers.of_sub
    intro r hr
    simp only [callRead,callWrite,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨_,List.mem_append_left _ (by rw [hp.rd,h.pre.1]; simp),0,(BitVec.add_zero _).symm,by omega⟩
    · exact ⟨_,List.mem_append_left _ (by rw [hp.rd,h.pre.1]; simp),0,(BitVec.add_zero _).symm,by omega⟩
    · exact ⟨_,List.mem_append_left _ (by rw [hp.rd,h.pre.1]; simp),0,(BitVec.add_zero _).symm,by omega⟩
    · exact ⟨_,List.mem_append_left _ (by rw [hp.rd,h.pre.1]; simp [hs]),0,(BitVec.add_zero _).symm,by omega⟩
    · refine ⟨FR s,List.mem_append_right _ (by rw [hp.wr]; exact List.mem_cons_self),64,?_,by show 64+24≤128; decide⟩
      exact (Offset.add_ofNat_add_ofNat (Pf s) 32 64).symm
    · exact ⟨_,List.mem_append_right _ (by rw [hp.wr,h.pre.2.1]; simp),0,(BitVec.add_zero _).symm,by omega⟩
    · exact ⟨_,List.mem_append_right _ (by rw [hp.wr,h.pre.2.1]; simp),0,(BitVec.add_zero _).symm,by omega⟩
  · exact Gather.covers_mem (fun r hr => by rw [hp.wr,h.pre.2.1]; exact List.mem_cons_of_mem _ hr)


theorem Prepared.originalFrame {s e c : State} (he : Gather.Entered s e) (hp : Prepared s e c) :
    Frame [FA s,dR s] s.mem c.mem := by
  have a : Frame [FA s,dR s] s.mem e.mem := by
    rw [he.mem]
    exact (frame_eMem s).mono (fun r hr => by rw [List.mem_singleton] at hr; subst r; exact List.mem_cons_self)
  refine a.trans (hp.frame.sub ?_)
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact ⟨dR s,by simp,fun _ hh => hh⟩
  · exact ⟨FA s,List.mem_cons_self,Offset.sub_base _ (by decide)⟩


theorem Prepared.encryption {s e c : State} (h : Gather.Lay s) (he : Gather.Entered s e)
    (hp : Prepared s e c) :
    Spec.Gcm.encryptWith (Spec.Gcm.ctxCiph c.mem (C s) (Rn s)) (Spec.Gcm.ctxH c.mem (C s)) 16
      (Spec.Aes.bytesAt c.mem (Nn s) (NL s))
      (Spec.Aes.bytesAt c.mem (e.mem.readW (Src s) 64) (firstLen e).toNat ++
        (Spec.Aes.bytesAt c.mem (Dst s) (L s)).drop (firstLen e).toNat)
      (Spec.Aes.bytesAt c.mem (Ad s) (AL s)) =
    Spec.Gcm.encryptWith (Spec.Gcm.ctxCiph s.mem (C s) (Rn s)) (Spec.Gcm.ctxH s.mem (C s)) 16
      (Spec.Aes.bytesAt s.mem (Nn s) (NL s)) (pt s (Cnt s)) (Spec.Aes.bytesAt s.mem (Ad s) (AL s)) := by
  rw [hp.input]
  exact h.encrypt_frame (hp.originalFrame he) _


theorem called_wp (hv : SplitOk) {s e c : State} (h : Layout s) (he : Gather.Entered s e)
    (hc : 0<Cnt s) (hp : Prepared s e c) :
    WP isa (.call "vg_aes_gcm_seal_split" Impl.AesGcm.PPC64LE.GatherSplit.sealCode) c (Gather.Called s) := by
  have hl := prepared_layout h he hc hp
  obtain ⟨hcov,hw⟩ := hp.covers h.base he hc
  refine WP.callAny (k := Proof.Gcm.sealSplitContract PPC64LE.abi 2800) hv (call_pre hl) hcov hw (fun z hrd hwr hsp hfr hpres hpost => ?_)
    (by rw [split_sdepth]; decide)
  have out := call_post hpost hl.rounds hl.bound
  have g9 : (callView s e c).gpr .r9=e.mem.readW (Src s) 64 := by
    change c.callEntry.gpr .r9=_
    rw [State.callEntry_gpr c (by decide),hp.source]
  have g10 : (callView s e c).gpr .r10=firstLen e := by
    change c.callEntry.gpr .r10=_
    rw [State.callEntry_gpr c (by decide),hp.length]
  change Spec.Gcm.encryptWith
      (Spec.Gcm.ctxCiph (callView s e c).mem ((callView s e c).gpr .r3) ((callView s e c).gpr .r4).toNat)
      (Spec.Gcm.ctxH (callView s e c).mem ((callView s e c).gpr .r3)) 16
      (Spec.Aes.bytesAt (callView s e c).mem ((callView s e c).gpr .r5) ((callView s e c).gpr .r6).toNat)
      (Spec.Aes.bytesAt (callView s e c).mem ((callView s e c).gpr .r9) ((callView s e c).gpr .r10).toNat ++
        (Spec.Aes.bytesAt (callView s e c).mem (stackArg (callView s e c) 0) (stackArg (callView s e c) 1).toNat).drop
          ((callView s e c).gpr .r10).toNat)
      (Spec.Aes.bytesAt (callView s e c).mem ((callView s e c).gpr .r7) ((callView s e c).gpr .r8).toNat) =
    (Spec.Aes.bytesAt z.mem (stackArg (callView s e c) 0) (stackArg (callView s e c) 1).toNat,
      Spec.Aes.bytesAt z.mem (stackArg (callView s e c) 2) 16) at out
  rw [hp.view_gpr (r := .r3) (by decide),hp.view_gpr (r := .r4) (by decide),
    hp.view_gpr (r := .r5) (by decide),hp.view_gpr (r := .r6) (by decide),
    hp.view_gpr (r := .r7) (by decide),hp.view_gpr (r := .r8) (by decide),g9,g10,
    hp.view_arg (j := 0) (by decide),hp.view_arg (j := 1) (by decide),hp.view_arg (j := 2) (by decide)] at out
  change Spec.Gcm.encryptWith (Spec.Gcm.ctxCiph c.mem (C s) (Rn s)) (Spec.Gcm.ctxH c.mem (C s)) 16
      (Spec.Aes.bytesAt c.mem (Nn s) (NL s))
      (Spec.Aes.bytesAt c.mem (e.mem.readW (Src s) 64) (firstLen e).toNat ++
        (Spec.Aes.bytesAt c.mem (Dst s) (L s)).drop (firstLen e).toNat)
      (Spec.Aes.bytesAt c.mem (Ad s) (AL s)) =
    (Spec.Aes.bytesAt z.mem (Dst s) (L s),Spec.Aes.bytesAt z.mem (Tg s) 16) at out
  rw [hp.encryption h.base he] at out
  have hra : z.mem.readW (slot s 6) 64=s.lr := by
    rw [← hp.ra]
    apply hfr.readW (Region.contains_self _ _) _ (by decide)
    intro r hr
    simp only [callWrite,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with (rfl|rfl)|rfl
    · exact h.base.bd.sub_left (fr_sub s (by decide))
    · exact h.base.bt.sub_left (fr_sub s (by decide))
    · rw [hp.sp,split_sdepth]
      have ha : slot s 6=(Pf s-BitVec.ofNat 64 2800)+BitVec.ofNat 64 2952 := by
        rw [show 2952=2800+152 by decide,← Offset.add_ofNat_add_ofNat,BitVec.sub_add_cancel]
      change Region.Disjoint ⟨slot s 6,8⟩ ⟨Pf s-BitVec.ofNat 64 2800,2800⟩
      rw [ha]
      exact Offset.disjoint_base _ (by decide) (by decide)
  exact ⟨hra,(h.base.gMem_encrypt).trans out,fun r hr => (hpres r hr).trans (hp.pres r hr),
    hsp.trans hp.sp,hrd.trans hp.rd,hwr.trans hp.wr⟩

end VG.Proof.AesGcm.PPC64LE.GatherSplit
