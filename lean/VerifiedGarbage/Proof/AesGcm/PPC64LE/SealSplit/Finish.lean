module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Whole
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: reuse the in-place seal's partial-text and tag proofs.
/-! # Finish split seal after setting up its outgoing argument -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SealSplit
open VG VG.PPC64LE
open VG.Proof.AesGcm.PPC64LE.SealFused


theorem finish_ok [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {V : Reg → BitVec 64} {sp S : Addr} {count R : Nat} {s : State} {a : List Byte}
    (L : Lay (V .r29) (V .r30) (V .r31)) (he : Env V sp s)
    (hd : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat)
    (lay : Call.Layout V sp S count s) (hR : V .r28=BitVec.ofNat 64 R) (hv : R=10 ∨ R=12 ∨ R=14)
    (ha : (V .r22).toNat=a.length) (hn : 0<(V .r23).toNat)
    (hab : Proof.Gcm.Absorbed s.mem (V .r30+16) (V .r30+32) (Spec.Gcm.ctxH s.mem (V .r29))
      (a++Spec.Gcm.zeros (Spec.Gcm.padLen a.length))) :
    WP isa (.seq Impl.AesGcm.PPC64LE.SealSplit.whole
      (.seq (.seq (.block Impl.AesGcm.PPC64LE.SealFused.tailSetup) Impl.AesGcm.PPC64LE.cryptTail)
        (.seq (Impl.AesGcm.PPC64LE.absorb 16) (Impl.AesGcm.PPC64LE.finTag 0)))) s
      (fun t => BodyOutWith V sp R (Spec.Gcm.ctxH s.mem (V .r29)) a s.mem
        ((Input.blocks s.mem S (V .r27) (V .r23).toNat count).flatMap Spec.Gcm.toBytes ++
          Spec.Aes.bytesAt s.mem (V .r27+BitVec.ofNat 64 (16*((V .r23).toNat/16))) ((V .r23).toNat%16))
        t [⟨sp+96,8⟩]) := by
  let u := Call.argsState s
  have hk := Call.args_keep s (by rw [he.sp]; exact lay.slotWrite)
  have hdU : DataW (V .r29) (V .r30) (V .r31) u (V .r27) (V .r23).toNat := hd.of_eq hk.2.1 hk.2.2
  have hf : Frame [⟨sp+96,8⟩] s.mem u.mem := by
    have hh := Call.args_frame s
    rw [he.sp] at hh
    exact hh
  have hctx : ∀ r ∈ [⟨sp+96,8⟩], (⟨V .r29,256⟩ : Region).Disjoint r := by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact lay.slotContext.symm
  have hciph : Spec.Gcm.ctxCiph u.mem (V .r29) R=Spec.Gcm.ctxCiph s.mem (V .r29) R :=
    ciph_keep hf hctx hv
  have hH : Spec.Gcm.ctxH u.mem (V .r29)=Spec.Gcm.ctxH s.mem (V .r29) := ctxH_keep hf hctx
  have hst : ∀ d k, d+k≤80 →
      (⟨V .r30+BitVec.ofNat 64 d,k⟩ : Region).Disjoint ⟨sp+96,8⟩ := by
    intro d k hb
    exact lay.slotState.symm.sub_left (Lay.stSub hb)
  have hb : Spec.Gcm.blockAt u.mem (V .r30+48)=Spec.Gcm.blockAt s.mem (V .r30+48) :=
    blockAt_frame hf (fun r hr => by rw [List.mem_singleton] at hr; subst r; exact hst 48 16 (by decide))
  have hj : Spec.Gcm.blockAt u.mem (V .r30)=Spec.Gcm.blockAt s.mem (V .r30) :=
    blockAt_frame hf (fun r hr => by rw [List.mem_singleton] at hr; subst r; simpa only [BitVec.add_zero] using hst 0 16 (by decide))
  have habU : Proof.Gcm.Absorbed u.mem (V .r30+16) (V .r30+32) (Spec.Gcm.ctxH u.mem (V .r29))
      (a++Spec.Gcm.zeros (Spec.Gcm.padLen a.length)) := by
    rw [hH]
    apply hab.congr
    · exact blockAt_frame hf (fun r hr => by rw [List.mem_singleton] at hr; subst r; exact hst 16 16 (by decide))
    · apply bytesAt_frame hf _ (by omega)
      intro r hr
      rw [List.mem_singleton] at hr
      subst r
      exact hst 32 _ (by omega)
  have hdata : ∀ r ∈ [⟨sp+96,8⟩], (⟨V .r27,16*((V .r23).toNat/16)⟩ : Region).Disjoint r := by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact lay.slotData.symm.sub_left (Region.sub_prefix (by omega))
  have hsource : ∀ r ∈ [⟨sp+96,8⟩], (⟨S,16*(count/16)⟩ : Region).Disjoint r := by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact lay.slotSource.symm.sub_left (Region.sub_prefix (by omega))
  have hp : Input.blocks u.mem S (V .r27) (V .r23).toNat count=
      Input.blocks s.mem S (V .r27) (V .r23).toNat count := by
    rw [Input.blocks,Input.blocks,Input.blocksAt_frame hf hsource,Input.blocksAt_frame hf hdata]
  have htail : Spec.Aes.bytesAt u.mem (V .r27+BitVec.ofNat 64 (16*((V .r23).toNat/16))) ((V .r23).toNat%16)=
      Spec.Aes.bytesAt s.mem (V .r27+BitVec.ofNat 64 (16*((V .r23).toNat/16))) ((V .r23).toNat%16) := by
    apply bytesAt_frame hf _ (by omega)
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact lay.slotData.symm.sub_left (Offset.sub_base _ (by omega))
  refine WP.seq (WP.mono (WP.with_rdwr (whole_ok L he hd lay hR hv)) fun t ⟨hw,rdt,wrt,_⟩ => ?_)
  have mid := whole_done L hdU lay.bound hv hw habU
  refine WP.mono (finishWhole_ok L mid (hd.of_eq rdt wrt) hR hv ha hn) fun z hz => ?_
  have hz' : BodyOutWith V sp R (Spec.Gcm.ctxH s.mem (V .r29)) a u.mem
      ((Input.blocks s.mem S (V .r27) (V .r23).toNat count).flatMap Spec.Gcm.toBytes ++
        Spec.Aes.bytesAt s.mem (V .r27+BitVec.ofNat 64 (16*((V .r23).toNat/16))) ((V .r23).toNat%16)) z [⟨sp+96,8⟩] := by
    rw [hH,hp,htail] at hz
    exact ⟨hz.env,hz.ciphertext,hz.tag,hz.frame.mono (fun _ hr => List.mem_append_left _ hr)⟩
  exact hz'.rebase (hf.mono (fun _ hr => List.mem_append_right _ hr)) hciph hb hj

end VG.Proof.AesGcm.PPC64LE.SealSplit
