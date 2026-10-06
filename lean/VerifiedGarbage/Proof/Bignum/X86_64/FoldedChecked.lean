import VerifiedGarbage.Proof.Bignum.X86_64.FoldedDispatch

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Checked
open VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.MlKem.X86_64

theorem expCheck_entryR {s : State} (g : Geom s) :
    WP isa expCheck s fun t => t.zf = some (eValid s) ∧ Same s t ∧
      t.gpr .r11 = BitVec.ofNat 64 (sat (Spec.Rsa.os2ip (eBytes s))) ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.mxcsr = s.mxcsr :=
  WP.mono_mx (by decide +kernel) (expCheckR_ok rfl (ofNat_toNat _).symm g.L1 g.L2 g.e rfl)
    fun t ⟨hz,hm,h11,k⟩ hmx => ⟨hz,Same.of_keep k hm,h11,fun r hr => k.gpr (by
      simp only [calleeSaved,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),hmx⟩

theorem checked_correct (M : Mont)
    (hmx : (Folded.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (hmxOld : (Precomputed.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : pdContract.pre s) :
    ∃ tr t, Exec isa (Folded.checked M.mm) s tr t ∧ abiPreserved s t ∧ pdChkContract.post s t := by
  have g := pdGeom h
  unfold Folded.checked guarded
  refine WP.seq (WP.mono (expCheck_entryR g) fun a ⟨za,sa,h11,cs,mx⟩ => ?_)
  refine WP.ite (!eValid s) (by simp [eval,za]) (fun hz => ?_) (fun hz => ?_)
  · have invalid : eValid s = false := by simpa using hz
    refine WP.mono_mx (by decide +kernel) (failOut_ok (s := a) (op := s.gpr .rdi)
      (k := (s.gpr .rsi).toNat) sa.rdi (by rw [sa.rsi,ofNat_toNat]) g.k1 g.k2
      (fun j hj => by rw [sa.wr]; exact g.out j hj))
      fun t ⟨bytes,rax,frame,keep⟩ mxt => ⟨⟨?_,?_,by rw [mxt,mx]⟩,?_⟩
    · intro r hr
      rw [keep.gpr (by
        simp only [calleeSaved,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),cs r hr]
    · refine Mem.readW_congr fun b hb => ?_
      rw [frame _ (fun j hj => g.ret b hb j hj),sa.mem]
    · intro nB _ _
      simp only [eValid,eBytes] at invalid
      simp only [Spec.Rsa.publicOpChecked,invalid,Bool.false_eq_true,ite_false,
        Spec.Rsa.written,rax]
      exact ⟨rfl,bytes⟩
  · have valid : eValid s = true := by simpa using hz
    have ha : pdContract.pre a := (pdPre_same sa).symm ▸ h
    have ea : a.gpr .r11 = BitVec.ofNat 64 (sat (Spec.Rsa.os2ip (eBytes a))) := by
      simpa only [eBytes,sa.mem,sa.r8,sa.r9] using h11
    obtain ⟨tr,t,exec,abi,post⟩ := dispatch_correct M hmx hmxOld a ha ea
    refine ⟨tr,t,exec,⟨fun r hr => (abi.1 r hr).trans (cs r hr),?_,?_⟩,?_⟩
    · rw [← sa.rsp,← sa.mem]; exact abi.2.1
    · rw [abi.2.2,mx]
    · intro nB hl hp
      simp only [pdContract,stackArg_same sa,sa.rdi,sa.rsi,sa.rdx,sa.rcx,sa.r8,sa.r9,sa.mem] at post
      simp only [eValid,eBytes] at valid
      simp only [Spec.Rsa.publicOpChecked,valid,↓reduceIte]
      exact post nB hl hp

end VG.Proof.Bignum.X86_64.FoldedPublic
