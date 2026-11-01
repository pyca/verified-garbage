module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.CTPrelude
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.CTBody
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Cache
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb

-- separate module: retain source-cache provenance through nonce and AAD processing.
/-! # Constant time across the shared one-shot stages -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SealSplit.CTStages
open VG VG.PPC64LE
open CTPrelude


def OT (b s : State) : Prop :=
  OneT ((prepared b).gpr .r3) (stackArg b 3) (prepared b).sp ((prepared b).gpr .r4).toNat
    ((prepared b).gpr .r5) ((prepared b).gpr .r6).toNat ((prepared b).gpr .r7)
    ((prepared b).gpr .r8) ((prepared b).gpr .r9) ((prepared b).gpr .r10) (stackArg b 2) s


def EntryI (b t : State) : Prop := ∃ s, Initial b s ∧
  SO1 (stackArg (prepared s) 1) (stackArg (prepared s) 0) (prepared s) t


def AadI (b t : State) : Prop := OT b t ∧ ∃ s, Initial b s ∧ ∃ s₁,
  SO1 (stackArg (prepared s) 1) (stackArg (prepared s) 0) (prepared s) s₁ ∧
  OA s₁.gpr (prepared s).sp (Spec.Gcm.ctxH (prepared s).mem ((prepared s).gpr .r3))
    (Spec.Aes.bytesAt s₁.mem ((prepared s).gpr .r5) ((prepared s).gpr .r6).toNat)
    (Spec.Aes.bytesAt s₁.mem (s₁.gpr .r21) (s₁.gpr .r22).toNat) s₁.mem t ∧ t.rd=s₁.rd ∧ t.wr=s₁.wr


theorem entry_one {b t : State} (hb : scratchContract.pre b) (ht : EntryI b t) :
    OT b t ∧ t.gpr .r24=(prepared b).gpr .r5 ∧ t.gpr .r25=BitVec.ofNat 64 ((prepared b).gpr .r6).toNat := by
  obtain ⟨s,hs,h1⟩ := ht
  have hr := CTEntry.entry_ready (entry_access s hs.pre) h1
  obtain ⟨hsp,hg,hW,hT⟩ := prepared_public hb hs
  simp only [hsp,hg .r3 (by decide),hg .r4 (by decide),hg .r5 (by decide),hg .r6 (by decide),
    hg .r7 (by decide),hg .r8 (by decide),hg .r9 (by decide),hg .r10 (by decide),hW,hT] at hr
  exact ⟨⟨hr.1,hr.2.2.2.1,hr.2.2.2.2⟩,hr.2.1,hr.2.2.1⟩


theorem aad_ready [VG.Proof.Gcm.PPC64LE.GhashLaw] {b s₁ : State}
    (hb : scratchContract.pre b) (hs₁ : EntryI b s₁) :
    WP isa Impl.AesGcm.PPC64LE.oneAad s₁ (AadI b) := by
  have hot := (entry_one hb hs₁).1
  obtain ⟨s,hs,h1⟩ := hs₁
  refine WP.mono (WP.with_rdwr (oneAad_entry_wp (entry_access s hs.pre) h1)) fun t ⟨oa,rd,wr,_⟩ => ?_
  have he := oa.env
  rw [(prepared_public hb hs).1] at he
  exact ⟨hot.keep (fun _ _ => rfl) he rd wr,s,hs,s₁,h1,oa,rd,wr⟩


theorem body_si {b t : State} (hb : scratchContract.pre b) (ht : AadI b t) :
    CTBlocks.SI ((prepared b).gpr .r3) (stackArg b 3+BitVec.ofNat 64 16) (stackArg b 3)
      (prepared b).sp ((prepared b).gpr .r4).toNat ((prepared b).gpr .r8) ((prepared b).gpr .r9)
      ((prepared b).gpr .r10) (b.gpr .r9) (b.gpr .r10).toNat (sourceState t) := by
  obtain ⟨hot,s,hs,s₁,h1,oa,rd,wr⟩ := ht
  obtain ⟨hsp,hg,hW,_⟩ := prepared_public hb hs
  have lay := source_layout hs.pre h1 oa rd wr
  have he := source_env oa.env
  rw [hsp] at he lay
  have hR : s₁.gpr .r28=BitVec.ofNat 64 ((prepared b).gpr .r4).toNat := by
    rw [h1.r28,hg .r4 (by decide),BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have hD := hot.1
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hdata⟩ := hD
  refine ⟨s₁.gpr,?_,?_,?_,hR,?_,?_,?_,he,?_,?_⟩
  · rw [h1.r29,hg .r3 (by decide)]
  · rw [h1.r30,hW]
  · rw [h1.r31,hW]
  · rw [h1.r22,hg .r8 (by decide)]
  · rw [h1.r27,hg .r9 (by decide)]
  · rw [h1.r23,hg .r10 (by decide)]
  · exact hdata.of_eq rfl rfl
  · rw [hs.regs .r9 (by decide)] at lay
    have hc := hs.regs .r10 (by decide)
    rw [hc] at lay
    exact lay


theorem body_ready [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {b t : State} (hb : scratchContract.pre b)
    (L : Lay ((prepared b).gpr .r3) (stackArg b 3+BitVec.ofNat 64 16) (stackArg b 3))
    (hv : ((prepared b).gpr .r4).toNat=10 ∨ ((prepared b).gpr .r4).toNat=12 ∨ ((prepared b).gpr .r4).toNat=14)
    (ht : AadI b t) :
    WP isa Impl.AesGcm.PPC64LE.SealSplit.body t (CTEntry.ReturnI (stackArg b 3) (stackArg b 2) (prepared b).sp) := by
  obtain ⟨hot,s,hs,s₁,h1,oa,rd,wr⟩ := ht
  obtain ⟨hsp,hg,hW,hT⟩ := prepared_public hb hs
  have hd : DataW (s₁.gpr .r29) (s₁.gpr .r30) (s₁.gpr .r31) t (s₁.gpr .r27) (s₁.gpr .r23).toNat := by
    rw [h1.r29,h1.r30,h1.r31,h1.r27,h1.r23,hg .r3 (by decide),hg .r9 (by decide),hg .r10 (by decide),hW]
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hdata⟩ := hot.1
    exact hdata
  have hL : Lay (s₁.gpr .r29) (s₁.gpr .r30) (s₁.gpr .r31) := by
    rw [h1.r29,h1.r30,h1.r31,hg .r3 (by decide),hW]
    exact L
  have h28 : s₁.gpr .r28=BitVec.ofNat 64 ((prepared b).gpr .r4).toNat := by
    rw [h1.r28,hg .r4 (by decide),BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have hab : Proof.Gcm.Absorbed t.mem (s₁.gpr .r30+16) (s₁.gpr .r30+32)
      (Spec.Gcm.ctxH t.mem (s₁.gpr .r29))
      (Spec.Aes.bytesAt s₁.mem (s₁.gpr .r21) (s₁.gpr .r22).toNat ++
        Spec.Gcm.zeros (Spec.Gcm.padLen (Spec.Aes.bytesAt s₁.mem (s₁.gpr .r21) (s₁.gpr .r22).toNat).length)) := by
    rw [ctxH_eq,oa.hH]
    exact oa.abs
  refine WP.mono (WP.with_rdwr (body_ok hL oa.env hd (source_layout hs.pre h1 oa rd wr) h28 hv
    (length_bytesAt _ _ _).symm hab)) fun z ⟨bo,_,wz,_⟩ => ?_
  have he := bo.env
  rw [hsp] at he
  refine ⟨s₁.gpr,?_,?_,he,?_⟩
  · rw [h1.r31,hW]
  · rw [h1.r20,hT]
  · rw [wz]; exact hot.2.2


theorem stages_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {b : State} (hb : scratchContract.pre b) :
    CT (PreparedI b) (Impl.AesGcm.PPC64LE.sealWith Impl.AesGcm.PPC64LE.SealSplit.body) := by
  have lay := layout_pre b hb
  have L : Lay ((prepared b).gpr .r3) (stackArg b 3+BitVec.ofNat 64 16) (stackArg b 3) := by
    rw [prepared_gpr b .r3 (by decide)]
    exact oneLay (lay.fits (contextR b) (by simp)) (lay.fits (workR b) (by simp))
      (lay.workApart (contextR b) (by simp))
  have hv : ((prepared b).gpr .r4).toNat=10 ∨ ((prepared b).gpr .r4).toNat=12 ∨ ((prepared b).gpr .r4).toNat=14 := by
    rw [prepared_gpr b .r4 (by decide)]
    exact lay.rounds
  refine CT.seq (J := EntryI b)
    (CTEntry.entry_ct (I := PreparedI b) (v := (prepared b).gpr) (sp := (prepared b).sp) (W := stackArg b 3)
      (fun s ⟨o,ho,hs⟩ => by subst s; exact entry_access o ho.pre)
      (fun s ⟨o,ho,hs⟩ => by subst s; exact ⟨(prepared_public hb ho).1,(prepared_public hb ho).2.1,(prepared_public hb ho).2.2.1⟩))
    (fun s ⟨o,ho,hs⟩ => ?_) ?_
  · subst s
    exact WP.mono (CTEntry.entry_wp (entry_access o ho.pre)) fun t ht => ⟨o,ho,ht⟩
  · refine CT.seq (J := AadI b) ((oneAad_ct L).mono (fun s hs =>
      ⟨(entry_one hb hs).1.1,(entry_one hb hs).2.1,(entry_one hb hs).2.2⟩))
      (fun _ => aad_ready hb) ?_
    exact CT.seq (CTBlocks.body_ct L hv (AadI b) (fun _ hs => hs.1.1) (fun _ => body_si hb))
      (fun _ => body_ready hb L hv)
      (CTEntry.return_ct ((lay.workApart (tagR b) (by simp)).sub_right (Region.sub_prefix (by decide))))


end VG.Proof.AesGcm.PPC64LE.SealSplit.CTStages
