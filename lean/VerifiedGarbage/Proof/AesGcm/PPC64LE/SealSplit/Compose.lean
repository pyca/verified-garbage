module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Cache
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: the split body supplies the plaintext to the shared seal stages.
/-! # Compose split seal with the shared one-shot stages -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SealSplit
open VG VG.PPC64LE


def plaintext (s : State) : List Byte :=
  Spec.Aes.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat ++
    (Spec.Aes.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat).drop (s.gpr .r10).toNat


theorem prepared_ok [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {s : State} (hs : scratchContract.pre s) :
    WP isa (Impl.AesGcm.PPC64LE.sealWith Impl.AesGcm.PPC64LE.SealSplit.body) (prepared s)
      (fun t => abiPreserved (prepared s) t ∧
        Spec.Gcm.encryptWith (Spec.Gcm.ctxCiph (prepared s).mem ((prepared s).gpr .r3) ((prepared s).gpr .r4).toNat)
          (Spec.Gcm.ctxH (prepared s).mem ((prepared s).gpr .r3)) 16
          (Spec.Aes.bytesAt (prepared s).mem ((prepared s).gpr .r5) ((prepared s).gpr .r6).toNat)
          (plaintext s) (Spec.Aes.bytesAt (prepared s).mem ((prepared s).gpr .r7) ((prepared s).gpr .r8).toNat)=
          (Spec.Aes.bytesAt t.mem ((prepared s).gpr .r9) ((prepared s).gpr .r10).toNat,
            Spec.Aes.bytesAt t.mem (stackArg (prepared s) 0) 16)) := by
  have lay := layout_pre s hs
  refine sealStages_wp (entry_access s hs) (extra := [⟨(prepared s).sp+96,8⟩]) ?_
    (fun s₁ s₂ h1 oa rd wr L hd h28 hv hab => ?_)
  · intro r hr
    rw [List.mem_singleton] at hr
    subst r
    rw [prepared_work]
    exact ((lay.stackApart (workR s) (by simp)).symm.sub_left (Lay.wSub (d := 128) (n := 120) (by decide))).sub_right
      (Offset.sub_base _ (by decide))
  · refine WP.mono (body_ok L oa.env hd (source_layout hs h1 oa rd wr) h28 hv
      (length_bytesAt _ _ _).symm hab) fun t ht => ?_
    have hf : Frame [stackR s,workR s] s.mem s₂.mem := by
      apply (prepared_frame s).trans
      have hh := h1.aadFrame oa
      rw [prepared_work] at hh
      exact hh.mono (by simp [workR])
    have hsource : Spec.Aes.bytesAt s₂.mem (s.gpr .r9) (s.gpr .r10).toNat=
        Spec.Aes.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat := by
      apply bytesAt_frame hf _ (by have := (s.gpr .r10).isLt; omega)
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact (lay.stackApart (sourceR s) (by simp)).symm
      · exact lay.workApart (sourceR s) (by simp)
    have hdata : Spec.Aes.bytesAt s₂.mem (s₁.gpr .r27) (s₁.gpr .r23).toNat=
        Spec.Aes.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat := by
      rw [h1.r27,h1.r23,prepared_destination s hs,prepared_length s hs]
      apply bytesAt_frame hf _ (by have := (stackArg s 1).isLt; omega)
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact (lay.stackApart (dataR s) (by simp)).symm
      · exact lay.workApart (dataR s) (by simp)
    simpa only [plaintext,hsource,hdata] using ht

end VG.Proof.AesGcm.PPC64LE.SealSplit
