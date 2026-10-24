module
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeTiming
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverStages

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverBlocksTiming
import VerifiedGarbage.Proof.Rsa.X86.PrivSetupTiming
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverReleaseTiming
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverStatus
import VerifiedGarbage.Proof.Rsa.X86.PrivReleaseTiming
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.RandomFinish

/-! # The padding check never branches on the precomputed RSA call's status -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Recover VG.Proof.Dsa.X86
open VG.Impl.RsaPkcs1Sig.X86.Verify (test0)
open VG.Proof.Rsa.X86.PrivChecked (sp_agree pair_seq_ct)

theorem compareReady_agree {g : Geometry} {bs : Fin 4 → List Byte} {s t : State}
    (hs : CompareReady g bs s) (ht : CompareReady g bs t) : VG.X86.Taint.Agree compareTaint s t := by
  apply agree_regs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hs.dst.trans ht.dst.symm
  · exact hs.src.trans ht.src.symm
  · exact hs.count.trans ht.count.symm

theorem compareThenRelease_relCT {g : Geometry} {bs : Fin 4 → List Byte} :
    RelCT isa (fun s t => Context g bs s ∧ Context g bs t)
      (.seq (.block cmpArgs) (.seq VG.Impl.RsaPkcs1Sig.X86.compare release)) (fun _ _ => True) := by
  apply pair_seq_ct (cmpArgs_relCT.mono
    (fun _ _ h => sp_agree (h.1.sp.trans h.2.sp.symm)) (fun _ _ _ => trivial))
    (fun _ h => cmpArgs_ready h) (fun _ h => cmpArgs_ready h)
  apply pair_seq_ct (compare_relCT.mono (fun _ _ h => compareReady_agree h.1 h.2) (fun _ _ _ => trivial))
    (fun _ h => compare_done h) (fun _ h => compare_done h)
  exact release_relCT

structure Compared (g : Geometry) (bs : Fin 4 → List Byte) (s : State) : Prop extends EncodeDone g bs s where
  flag : s.zf = some (s.gpr .eax == 0)

theorem compare_ready {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : EncodeDone g bs s) :
    WP isa (.block test0) s (Compared g bs) := by
  unfold test0
  refine wp_cmpS rfl fun t F Z => WP.block_nil ?_
  refine ⟨⟨h.context.after (by rw [F.mem]; exact Frame.refl _ _) (F.keeps []) (congrFun F.gpr .esp), ?_⟩, ?_⟩
  · simpa only [Encoded, digestBytes, F.gpr, F.mem] using h.encoded
  · rw [Z, F.gpr]
    exact congrArg some (by change (s.gpr .eax - 0#32 == 0#32) = _; rw [BitVec.sub_zero]; rfl)

theorem tail_relCT {g : Geometry} {bs : Fin 4 → List Byte} :
    RelCT isa (fun s t => EncodeDone g bs s ∧ EncodeDone g bs t) tail (fun _ _ => True) := by
  unfold tail
  apply pair_seq_ct (cmp_relCT.mono (fun s t h => agree_regs (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.context.sp.trans h.2.context.sp.symm
    · exact encoded_status h.1 h.2)) (fun _ _ _ => trivial))
    (fun _ h => compare_ready h) (fun _ h => compare_ready h)
  apply RelCT.ite
  · intro s t h
    change s.zf = t.zf
    rw [h.1.flag, h.2.flag, encoded_status h.1.toEncodeDone h.2.toEncodeDone]
  · exact zeroOut_relCT.mono
      (fun _ _ h => ⟨h.1.1.context, h.1.2.context⟩) (fun _ _ _ => trivial)
  · exact compareThenRelease_relCT.mono (fun _ _ h => ⟨h.1.1.context, h.1.2.context⟩) (fun _ _ _ => trivial)

theorem encodeReady_agree {g : Geometry} {bs : Fin 4 → List Byte} {s t : State}
    (hs : EncodeReady g bs s) (ht : EncodeReady g bs t) : VG.X86.Taint.Agree encodeTaint s t := by
  apply agree_regs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hs.dst.trans ht.dst.symm
  · exact hs.len.trans ht.len.symm
  · exact hs.hash.trans ht.hash.symm
  · exact hs.src.trans ht.src.symm
  · exact hs.count.trans ht.count.symm

theorem afterPub_relCT {g : Geometry} {bs : Fin 4 → List Byte} :
    RelCT isa (fun s t => Context g bs s ∧ Context g bs t) afterPub (fun _ _ => True) := by
  unfold afterPub
  apply pair_seq_ct (save_relCT.mono
    (fun _ _ h => sp_agree (h.1.sp.trans h.2.sp.symm)) (fun _ _ _ => trivial))
    (fun _ h => WP.mono (save_ok h) (fun _ x => x.1))
    (fun _ h => WP.mono (save_ok h) (fun _ x => x.1))
  apply pair_seq_ct (encArgs_relCT.mono
    (fun _ _ h => sp_agree (h.1.sp.trans h.2.sp.symm)) (fun _ _ _ => trivial))
    (fun _ h => encArgs_ready h) (fun _ h => encArgs_ready h)
  exact pair_seq_ct (encode_relCT.mono (fun _ _ h => encodeReady_agree h.1 h.2) (fun _ _ _ => trivial))
    (fun _ h => encode_done h) (fun _ h => encode_done h) tail_relCT

end VG.Proof.RsaPkcs1Sig.X86.Rcv
