import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareDispatch
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareMontCT

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.Adx
open VG.Proof.Bignum.X86_64

theorem aligned_ct {o a : Nat} (ho : o<8) (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {h₁ h₂ h₃ h₄ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (setup a)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a a)) h₂).isSome=true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (finishBases o)) h₃).isSome=true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup a)) h₄).isSome=true) :
    RelCT isa (Two fun L s => AdxSquare.GW L s ∧ L.w%8=0)
      (AdxTiledSquare.montSquare o a) (fun _ _ => True) := by
  intro s t ts tt s' t' ⟨L,⟨⟨⟨mi,gs,hZ⟩,sz⟩,h8⟩,⟨⟨⟨mj,gt,_⟩,_⟩,_⟩⟩ es et
  have hw := sz.lt
  have hp := sz.2.1
  let R : AdxTiledProduct.Layout := ⟨L.B,L.Z,L.w,L.w/8,hZ,hw,by omega,by omega⟩
  exact montSquare_ct (ps := [(o,o),(a,a),(a,a)]) (.head _) (.tail _ (.head _)) ha ha1 ha2 hS hR hF hT
    _ _ _ _ _ _ ⟨R,⟨⟨mi,gs⟩,gs.hdr.ops3 ho ha ha⟩,⟨mj,gt⟩,gt.hdr.ops3 ho ha ha⟩ es et

theorem alignedChoice_ct {o a : Nat} (ho : o<8) (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {h₁ h₂ h₃ h₄ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (setup a)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a a)) h₂).isSome=true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (finishBases o)) h₃).isSome=true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup a)) h₄).isSome=true) :
    RelCT isa (Two AdxSquare.GW) (AdxTiledSquare.alignedChoice o a) (fun _ _ => True) := by
  unfold AdxTiledSquare.alignedChoice
  refine RelCT.seq (two_piece (Ψ := fun L s => AdxSquare.GW L s ∧ s.zf=some (decide (L.w%8=0)))
    [.rdi] AdxSquare.pins_gw (by taint_decide) ?_) ?_
  · intro L s ⟨⟨mi,hg,hZ⟩,sz⟩
    exact WP.mono (AdxSquare.redcTest_ok hg.scr hg.rdi hg.hdr hZ (by have := sz.lt; omega))
      fun _ ⟨z,m,k⟩ => ⟨⟨⟨mi,⟨hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,m ▸ hg.hdr⟩,hZ⟩,sz⟩,z⟩
  refine two_ite (fun L s t hs ht => by simp only [eval,hs.2,ht.2]) ?_ ?_
  · refine two_map id (fun L s ⟨⟨h,z⟩,e⟩ => ⟨h,?_⟩) (aligned_ct ho ha ha1 ha2 hS hR hF hT)
    simp only [eval,z,Option.some.injEq,decide_eq_true_eq] at e
    exact e
  · exact two_map id (fun _ _ h => h.1.1) (AdxSquare.montSquare_ct ho ha ha1 ha2 hS hF)

theorem choice_ct {o a : Nat} (ho : o<8) (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {h₀ h₁ h₂ h₃ h₄ h₅ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hM : (taint.check (Taint.ofRegs [.rdi]) (.block (bases o a a aN aAcc aTmp)) h₀).isSome=true)
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (setup a)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (rowBase a)) h₂).isSome=true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (finishBases o)) h₃).isSome=true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a a)) h₄).isSome=true)
    (hTri : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup a)) h₅).isSome=true) :
    RelCT isa (Two GoodW) (AdxTiledSquare.choice o a) (fun _ _ => True) := by
  unfold AdxTiledSquare.choice
  refine RelCT.seq (two_piece (Ψ := fun L s => GoodW L s ∧ s.zf=some (decide (SizeOk L.w)))
    [.rdi] pins_goodW (by taint_decide) ?_) ?_
  · intro L s ⟨mi,hg,hZ⟩
    exact WP.mono (sizeTest_ok hg.scr hg.rdi hg.hdr hZ) fun _ ⟨z,m,k⟩ =>
      ⟨⟨mi,⟨hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,m ▸ hg.hdr⟩,hZ⟩,z⟩
  refine two_ite (fun L s t hs ht => by simp only [eval,hs.2,ht.2]) ?_ ?_
  · refine two_map id (fun L s ⟨⟨h,z⟩,e⟩ => ⟨h,?_⟩) (alignedChoice_ct ho ha ha1 ha2 hS hT hF hTri)
    simp only [eval,z,Option.some.injEq,decide_eq_true_eq] at e
    exact e
  · exact two_map id (fun _ _ h => h.1.1) (montMulAdx_ct ho ha ha ha1 ha2 ha1 ha2 hM hS hR hF)

end VG.Proof.Bignum.X86_64.AdxTiledSquare
