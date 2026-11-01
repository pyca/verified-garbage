module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Finish
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: join the partial-source copy to the shared whole-block and tag stages.
/-! # Split-seal text processing -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SealSplit
open VG VG.PPC64LE
open VG.Proof.AesGcm.PPC64LE.SealFused



theorem partial_env_layout {V : Reg → BitVec 64} {sp S : Addr} {count : Nat} {s t : State}
    (he : Env V sp s) (lay : Call.Layout V sp S count s) (ht : PartialCopy.Result s count t) :
    Env V sp t ∧ Call.Layout V sp S count t := by
  have heT : Env V sp t := he.keep (fun r hr => ht.keep.gpr (by
    have hp : ∀ r ∈ frozen, r ∉ PartialCopy.registers := by decide
    exact hp r hr)) ht.sp ht.keep.2.1 ht.keep.2.2
  have layT : Call.Layout V sp S count t := by
    refine ⟨lay.bound,?_,?_,?_,lay.fit,lay.st,lay.data,lay.work,?_,lay.stackFit,lay.slotFit,
      lay.slotContext,lay.slotState,lay.slotData,lay.slotWork,lay.slotSource⟩
    · rw [ht.keep.gpr (by decide : Reg.r7∉PartialCopy.registers)]; exact lay.source
    · rw [ht.keep.gpr (by decide : Reg.r8∉PartialCopy.registers)]; exact lay.countReg
    · rw [ht.keep.2.1,ht.keep.2.2]; exact lay.reads
    · rw [ht.keep.2.2]; exact lay.slotWrite
  exact ⟨heT,layT⟩

theorem partial_ok [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {V : Reg → BitVec 64} {sp S : Addr} {count R : Nat} {s : State} {a : List Byte}
    (L : Lay (V .r29) (V .r30) (V .r31)) (he : Env V sp s)
    (hd : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat)
    (lay : Call.Layout V sp S count s) (hR : V .r28=BitVec.ofNat 64 R) (hv : R=10 ∨ R=12 ∨ R=14)
    (ha : (V .r22).toNat=a.length) (hn : 0<(V .r23).toNat)
    (hab : Proof.Gcm.Absorbed s.mem (V .r30+16) (V .r30+32) (Spec.Gcm.ctxH s.mem (V .r29))
      (a++Spec.Gcm.zeros (Spec.Gcm.padLen a.length))) :
    WP isa (.seq Impl.AesGcm.PPC64LE.SealSplit.partialCopy
      (.seq Impl.AesGcm.PPC64LE.SealSplit.whole
        (.seq (.seq (.block Impl.AesGcm.PPC64LE.SealFused.tailSetup) Impl.AesGcm.PPC64LE.cryptTail)
          (.seq (Impl.AesGcm.PPC64LE.absorb 16) (Impl.AesGcm.PPC64LE.finTag 0))))) s
      (fun t => BodyOutWith V sp R (Spec.Gcm.ctxH s.mem (V .r29)) a s.mem
        (Spec.Aes.bytesAt s.mem S count ++ (Spec.Aes.bytesAt s.mem (V .r27) (V .r23).toNat).drop count)
        t [⟨sp+96,8⟩]) := by
  have cfg : PartialCopy.Config s (V .r23).toNat count := by
    refine ⟨lay.bound,(V .r23).isLt,lay.countReg,?_,?_,?_⟩
    · rw [lay.source]; exact lay.reads
    · rw [he.fr .r27 (by decide)]; exact hd.wr
    · rw [lay.source,he.fr .r27 (by decide)]; exact lay.data
  refine WP.seq (WP.mono (PartialCopy.ok s _ _ cfg) fun t ht => ?_)
  obtain ⟨heT,layT⟩ := partial_env_layout he lay ht
  have hdT := hd.of_eq ht.keep.2.1 ht.keep.2.2
  have hf : Frame [⟨V .r27+BitVec.ofNat 64 (count-count%16),count%16⟩] s.mem t.mem := by
    have hh := ht.frame
    rw [he.fr .r27 (by decide)] at hh
    exact hh
  have hsub : Region.Sub ⟨V .r27+BitVec.ofNat 64 (count-count%16),count%16⟩ ⟨V .r27,(V .r23).toNat⟩ :=
    Offset.sub_base _ (by have := lay.bound; omega)
  have hctx : ∀ r ∈ [⟨V .r27+BitVec.ofNat 64 (count-count%16),count%16⟩],
      (⟨V .r29,256⟩ : Region).Disjoint r := by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact hd.ctx.sub_right hsub
  have hciph : Spec.Gcm.ctxCiph t.mem (V .r29) R=Spec.Gcm.ctxCiph s.mem (V .r29) R := ciph_keep hf hctx hv
  have hH : Spec.Gcm.ctxH t.mem (V .r29)=Spec.Gcm.ctxH s.mem (V .r29) := ctxH_keep hf hctx
  have hst : ∀ d k, d+k≤80 →
      (⟨V .r30+BitVec.ofNat 64 d,k⟩ : Region).Disjoint ⟨V .r27+BitVec.ofNat 64 (count-count%16),count%16⟩ := by
    intro d k hb
    exact (hd.ok.st.symm.sub_left (Lay.stSub hb)).sub_right hsub
  have hb : Spec.Gcm.blockAt t.mem (V .r30+48)=Spec.Gcm.blockAt s.mem (V .r30+48) :=
    blockAt_frame hf (fun r hr => by rw [List.mem_singleton] at hr; subst r; exact hst 48 16 (by decide))
  have hj : Spec.Gcm.blockAt t.mem (V .r30)=Spec.Gcm.blockAt s.mem (V .r30) :=
    blockAt_frame hf (fun r hr => by rw [List.mem_singleton] at hr; subst r; simpa only [BitVec.add_zero] using hst 0 16 (by decide))
  have habT : Proof.Gcm.Absorbed t.mem (V .r30+16) (V .r30+32) (Spec.Gcm.ctxH t.mem (V .r29))
      (a++Spec.Gcm.zeros (Spec.Gcm.padLen a.length)) := by
    rw [hH]
    apply hab.congr
    · exact blockAt_frame hf (fun r hr => by rw [List.mem_singleton] at hr; subst r; exact hst 16 16 (by decide))
    · apply bytesAt_frame hf _ (by omega)
      intro r hr
      rw [List.mem_singleton] at hr
      subst r
      exact hst 32 _ (by omega)
  refine WP.mono (finish_ok L heT hdT layT hR hv ha hn habT) fun z hz => ?_
  have hp := Input.copied cfg ht
  rw [lay.source,he.fr .r27 (by decide)] at hp
  rw [hp,hH] at hz
  exact hz.rebase (hf.sub (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact ⟨⟨V .r27,(V .r23).toNat⟩,List.mem_append_left _ (by simp [bodyFrame]),hsub⟩)) hciph hb hj

end VG.Proof.AesGcm.PPC64LE.SealSplit
