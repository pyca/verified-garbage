import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZStoredField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedMaskSemantic

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem hLane_norm {m : Mem} {work challenge secret out : Addr} {u e B : Nat}
    (hu : u<8) (he : e<4) (i : Fin 2 × Fin 8) (c : CheckConstants)
    (hlower : vword c.lower e=BitVec.ofNat 32 (B-1))
    (hwidth : vword c.width e=BitVec.ofNat 32 (2*B-1))
    (hB : 1≤B) (hB' : B≤524288)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (hp : pairedProductsReduced m challenge secret) :
    passMask true work out c (firstPassMem m work challenge secret 8) u i e=0 ↔
      normZq (pairedProduct m challenge secret i.1.val)[4*u+32*i.2.val+e]!<B := by
  have hr := rawFinal_field hu hc hs i.1 (Inverse.positiveReduced_is hp.1)
    (Inverse.positiveReduced_is (hp.2 i.1.val i.1.isLt)) i.2 he
  simp only [passMask,checkMask,ite_true,hlower,hwidth]
  rw [hMask_zero ⟨hr.1,hr.2.1⟩ hB hB',hr.2.2]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired
