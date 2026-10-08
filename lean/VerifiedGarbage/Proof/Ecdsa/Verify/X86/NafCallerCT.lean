import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafCallerKeep

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Impl.Ecdsa.Verify.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Ecdsa.X86 VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass
open Spec.Weierstrass

theorem vNaf_rel (hc : CfgOk p256Comb) (hC : Law p256Comb.C) (ham3 : AM3 p256Comb.C)
    {s₀ t₀ : State} {extra₁ extra₂ : List Region}
    (hp : VPre p256Comb s₀ extra₁) (hq : VPre p256Comb t₀ extra₂)
    (he : s₀.gpr .esp=t₀.gpr .esp) (ha : ∀ j<4,arg s₀ j=arg t₀ j)
    (hv : VInputEq p256Comb s₀ t₀) :
    RelCT isa (fun s t => VPointInput s₀ (ptr s₀ 3) s ∧ VPointInput t₀ (ptr t₀ 3) t)
      vNafCode (fun _ _ => True) := by
  intro s t ts tt u v ⟨hs,ht⟩ es et
  have pub := vKeepNafPublic hp hq hs.1 ht.1 he ha
  have hb : ptr s₀ 3=ptr t₀ 3 := congrArg (BitVec.setWidth 64) (ha 3 (by decide))
  have ht' := ht
  rw [←hb] at ht'
  have si := vPointInput_naf hc hC hs
  have ti := vValues_naf hc hC ht'.1 (ht'.2.rebase hv)
  have hk : vScalar p256Comb s₀<2^256 := by
    rw [←si.scalar]
    exact wordsVal_lt s.mem (ptr s₀ 3) (p256Comb.sl V) 4
  exact windowMulQ_relCT hc hC ham3 hk (Ecdh.X86.peerPt_onCurve hc _ _ _)
    _ _ _ _ _ _ ⟨si,ti,pub⟩ es et

theorem vPointTail_rel (hc : CfgOk p256Comb) (hC : Law p256Comb.C) (ham3 : AM3 p256Comb.C)
    {s₀ t₀ : State} {extra₁ extra₂ : List Region}
    (hp : VPre p256Comb s₀ extra₁) (hq : VPre p256Comb t₀ extra₂)
    (he : s₀.gpr .esp=t₀.gpr .esp) (ha : ∀ j<4,arg s₀ j=arg t₀ j)
    (hv : VInputEq p256Comb s₀ t₀) :
    RelCT isa (fun s t => VPointInput s₀ (ptr s₀ 3) s ∧ VPointInput t₀ (ptr t₀ 3) t)
      vPointTailCode (fun _ _ => True) := by
  have save := vSave_rel.mono
    (P':=fun s t => VPointInput s₀ (ptr s₀ 3) s ∧ VPointInput t₀ (ptr t₀ 3) t)
    (fun _ _ ⟨hs,ht⟩ => vKeepScratchAgree hp hq hs.1 ht.1 he ha) (fun _ _ h => h)
  have save' := save.wp (fun _ _ ⟨hs,ht⟩ => ⟨vSave_input hc hs,vSave_input hc ht⟩)
  have mult := (vNaf_rel hc hC ham3 hp hq he ha hv).mono
    (P':=fun s t => True ∧ VPointInput s₀ (ptr s₀ 3) s ∧ VPointInput t₀ (ptr t₀ 3) t)
    (fun _ _ h => h.2) (fun _ _ h => h)
  have mult' := mult.wp (fun _ _ ⟨_,hs,ht⟩ => ⟨vNaf_keep hc hC ham3 hs,vNaf_keep hc hC ham3 ht⟩)
  exact save'.seq (mult'.seq (vSum_rel.mono
    (fun _ _ h => vKeepScratchAgree hp hq h.2.1 h.2.2 he ha) (fun _ _ _ => trivial)))

end VG.Proof.Ecdsa.Verify.X86
