import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledChoice

namespace VG.Proof.Bignum.X86_64.AdxTiledProduct
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.Adx
open VG.Proof.Bignum.X86_64

theorem aligned_ct {o a b : Nat} (ho : o<8) (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    {h₁ h₂ h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (setup b)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a b)) h₂).isSome=true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (finishBases o)) h₃).isSome=true) :
    RelCT isa (Two fun L s => AdxSquare.GW L s ∧ L.w%8=0)
      (AdxTiledProduct.montMul o a b) (fun _ _ => True) := by
  intro s t ts tt s' t' ⟨L,⟨⟨⟨mi,gs,hZ⟩,sz⟩,h8⟩,⟨⟨⟨mj,gt,_⟩,_⟩,_⟩⟩ es et
  have hw := sz.lt
  have hp := sz.2.1
  let R : Layout := ⟨L.B,L.Z,L.w,L.w/8,hZ,hw,by omega,by omega⟩
  exact montMul_ct (ps := [(o,o),(a,a),(b,b)]) (.head _) (.tail _ (.head _)) (.tail _ (.tail _ (.head _))) ha hb ha1 ha2 hb1 hb2 hS hR hF
    _ _ _ _ _ _ ⟨R,⟨⟨mi,gs⟩,gs.hdr.ops3 ho ha hb⟩,⟨mj,gt⟩,gt.hdr.ops3 ho ha hb⟩ es et

theorem alignedChoice_ct {o a b : Nat} (ho : o<8) (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    {h₀ h₁ h₂ h₃ h₄ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hM : (taint.check (Taint.ofRegs [.rdi]) (.block (bases o a b aN aAcc aTmp)) h₀).isSome=true)
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (setup b)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (rowBase a)) h₂).isSome=true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (finishBases o)) h₃).isSome=true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a b)) h₄).isSome=true) :
    RelCT isa (Two AdxSquare.GW) (AdxTiledProduct.alignedChoice o a b) (fun _ _ => True) := by
  unfold AdxTiledProduct.alignedChoice
  refine RelCT.seq (two_piece (Ψ := fun L s => AdxSquare.GW L s ∧ s.zf=some (decide (L.w%8=0)))
    [.rdi] AdxSquare.pins_gw (by taint_decide) ?_) ?_
  · intro L s ⟨⟨mi,hg,hZ⟩,sz⟩
    exact WP.mono (AdxSquare.redcTest_ok hg.scr hg.rdi hg.hdr hZ (by have := sz.lt; omega))
      fun _ ⟨z,m,k⟩ => ⟨⟨⟨mi,⟨hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,m ▸ hg.hdr⟩,hZ⟩,sz⟩,z⟩
  refine two_ite (fun L s t hs ht => by simp only [eval,hs.2,ht.2]) ?_ ?_
  · refine two_map id (fun L s ⟨⟨h,z⟩,e⟩ => ⟨h,?_⟩) (aligned_ct ho ha hb ha1 ha2 hb1 hb2 hS hT hF)
    simp only [eval,z,Option.some.injEq,decide_eq_true_eq] at e
    exact e
  · exact two_map id (fun _ _ h => h.1.1.1) (montMulAdx_ct ho ha hb ha1 ha2 hb1 hb2 hM hS hR hF)

theorem choice_ct {o a b : Nat} (ho : o<8) (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    {h₀ h₁ h₂ h₃ h₄ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hM : (taint.check (Taint.ofRegs [.rdi]) (.block (bases o a b aN aAcc aTmp)) h₀).isSome=true)
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (setup b)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (rowBase a)) h₂).isSome=true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (finishBases o)) h₃).isSome=true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a b)) h₄).isSome=true) :
    RelCT isa (Two GoodW) (AdxTiledProduct.choice o a b) (fun _ _ => True) := by
  unfold AdxTiledProduct.choice
  refine RelCT.seq (two_piece (Ψ := fun L s => GoodW L s ∧ s.zf=some (decide (SizeOk L.w)))
    [.rdi] pins_goodW (by taint_decide) ?_) ?_
  · intro L s ⟨mi,hg,hZ⟩
    exact WP.mono (sizeTest_ok hg.scr hg.rdi hg.hdr hZ) fun _ ⟨z,m,k⟩ =>
      ⟨⟨mi,⟨hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,m ▸ hg.hdr⟩,hZ⟩,z⟩
  refine two_ite (fun L s t hs ht => by simp only [eval,hs.2,ht.2]) ?_ ?_
  · refine two_map id (fun L s ⟨⟨h,z⟩,e⟩ => ⟨h,?_⟩) (alignedChoice_ct ho ha hb ha1 ha2 hb1 hb2 hM hS hR hF hT)
    simp only [eval,z,Option.some.injEq,decide_eq_true_eq] at e
    exact e
  · exact two_map id (fun _ _ h => h.1.1) (montMulAdx_ct ho ha hb ha1 ha2 hb1 hb2 hM hS hR hF)

end VG.Proof.Bignum.X86_64.AdxTiledProduct
