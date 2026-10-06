import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTDispatch

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Checked
open VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

theorem public_bytes {s t : State} (h : pdContract.pub s t) : eBytes s = eBytes t := h.2.2.2.2.2.2

theorem checked_ct (M : Mont)
    (hfinal : RelCT isa (Two GoodL) (M.mm aY aX aY) (fun _ _ => True)) :
    ConstantTime isa pdContract.pre pdContract.pub (Folded.checked M.mm) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold Folded.checked guarded
  have headCT := (RelCT.taint (A := taint) (c := expCheck) (Taint.ofRegs [.r8,.r9])
    (P := fun s t => pdContract.pre s ∧ pdContract.pre t ∧ pdContract.pub s t)
    (fun s t ⟨_,_,hp⟩ => Taint.agree_ofRegs fun r hr => hp.1 r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
      rcases hr with rfl | rfl <;> simp)) (by taint_decide)).wpDep
    (F := fun (s t : State) => t.zf = some (eValid s) ∧ Same s t ∧
      t.gpr .r11 = BitVec.ofNat 64 (sat (Spec.Rsa.os2ip (eBytes s))))
    (fun s t ⟨ps,pt,_⟩ =>
      ⟨WP.mono (expCheck_entryR (pdGeom ps)) (fun _ ⟨hz,hs,h11,_⟩ => ⟨hz,hs,h11⟩),
       WP.mono (expCheck_entryR (pdGeom pt)) (fun _ ⟨hz,hs,h11,_⟩ => ⟨hz,hs,h11⟩)⟩)
  refine RelCT.seq headCT (RelCT.ite ?_ ?_ ?_)
  · rintro a b ⟨_,s,t,⟨_,_,hp⟩,⟨za,_⟩,⟨zb,_⟩⟩
    simp only [eval,za,zb,eValid,public_bytes hp]
  · refine (RelCT.taint (A := taint) (Taint.ofRegs [.rdi,.rsi])
      (fun a b h => ?_) (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)
    obtain ⟨⟨_,s,t,⟨_,_,hp⟩,⟨_,sa,_⟩,⟨_,sb,_⟩⟩,_⟩ := h
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · rw [sa.rdi,sb.rdi]; exact hp.1 _ (by simp)
    · rw [sa.rsi,sb.rsi]; exact hp.1 _ (by simp)
  · refine (relCT_of_ct (dispatch_ct M hfinal)).mono ?_ (fun _ _ _ => trivial)
    rintro a b ⟨⟨_,s,t,⟨ps,pt,hp⟩,⟨_,sa,h11a⟩,⟨_,sb,h11b⟩⟩,_⟩
    exact ⟨(pdPre_same sa).symm ▸ ps,(pdPre_same sb).symm ▸ pt,
      pdPub_same sa sb hp,by rw [h11a,h11b,public_bytes hp]⟩

theorem checked_verified (M : Mont)
    (hmx : (Folded.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (hmxOld : (Precomputed.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (hfinal : RelCT isa (Two GoodL) (M.mm aY aX aY) (fun _ _ => True)) :
    Verified target (Folded.checked M.mm) (Spec.Rsa.publicPrecomputedCheckedContract abi) :=
  Verified.of_correct (k := pdChkContract) (checked_correct M hmx hmxOld)
    (checked_ct M hfinal) precomputedChecked_implies

end VG.Proof.Bignum.X86_64.FoldedPublic
