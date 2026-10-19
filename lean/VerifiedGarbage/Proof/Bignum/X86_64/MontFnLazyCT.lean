module

public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxCT
public import VerifiedGarbage.Impl.Bignum.X86_64.MontFnLazy
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledLazyCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBackend
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMontCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRawCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxCT
meta import VerifiedGarbage.Impl.Bignum.X86_64.MontFnLazy
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledLazyCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBackend
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMontCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRawCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# `vg_rsa_lazy_mont_mul_adx`: constant time

`vg_rsa_mont_mul_adx`'s proof, with the lazy reduction of the tiles
(`AdxTiledProduct.redcLazy_ct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.MontFn
open VG.Proof.MlKem.X86_64

/-- The tiles, with the lazy reduction. -/
theorem tiledLazy_ct : RelCT isa (Two fun d s => (AdxMid d s ∧ s.zf = some (decide (AlignOk d.w))) ∧
    isa.eval .e s = some true) tiledLazy fun _ _ => True := by
  unfold tiledLazy
  refine RelCT.seq (two_piece (Ψ := fun d s => (AdxMid d s ∧ AlignOk d.w) ∧ s.zf = some (decide (d.a = d.b)))
    [.rcx, .r8] (fun d s₁ s₂ h₁ h₂ r hr => pins_adxMid d s₁ s₂ h₁.1.1 h₂.1.1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp))
    (by taint_decide) ?_) ?_
  · rintro d s ⟨⟨hm, hz⟩, he⟩
    have hA : AlignOk d.w := by simpa only [eval, hz, Option.some.injEq, decide_eq_true_eq] using he
    have ha := hm.1.2.2.2.2.1.2.1
    have hb := hm.1.2.2.2.2.1.2.2.1
    have hcx := hm.1.2.2.2.2.2.2.1
    have h8 := hm.1.2.2.2.2.2.2.2
    exact WP.mono (cmpIdx_ok ha hb hcx h8) fun t ⟨hz', hm', hc', k⟩ =>
      ⟨⟨⟨AdxIn.of_keep hm.1 hm' k hc' (by decide), hm' ▸ hm.2⟩, hA⟩, hz'⟩
  refine RelCT.seq (R := Two TiledMid)
    (two_ite (fun d s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_)
    (AdxTiledProduct.redcLazy_ct (P := fun x : TiledData => adxOps x.1.o x.1.a x.1.b)
      (L := fun x => adxLayout x.1 x.2.1 x.2.2) (O := fun x => x.1.o) (fun x => mem_adxOps_o _ _ _)
      (by taint_decide))
  · rintro s₁ s₂ t₁ t₂ s₁' s₂' ⟨d, ⟨⟨⟨h₁, hA⟩, z₁⟩, e₁⟩, ⟨⟨h₂, -⟩, -⟩, -⟩ e₁' e₂'
    have hab : d.a = d.b := by simpa only [eval, z₁, Option.some.injEq, decide_eq_true_eq] using e₁
    have hZ := h₁.1.2.2.2.1
    obtain ⟨-, ha, -, -, -, ha1, ha2, -⟩ := h₁.1.2.2.2.2.1
    obtain ⟨ht, -, u₁, u₂⟩ := two_post (α := Unit)
      (two_map (fun _ => adxLayout d hZ hA) (fun _ _ h => h)
        (AdxTiledSquare.rawBare_ct (ps := adxOps d.o d.a d.b) (mem_adxOps_a _ _ _) ha ha1 ha2
          (by taint_decide) (by taint_decide) (by taint_decide)))
      (fun _ s h => AdxTiledSquare.rawBare_fw (mem_adxOps_a _ _ _) ha ha1 ha2 (adxLayout d hZ hA) s h)
      _ _ _ _ _ _ ⟨(), goodV_of_mid h₁ hZ hA, goodV_of_mid h₂ hZ hA⟩ e₁' e₂'
    exact ⟨ht, ⟨d, hZ, hA⟩, u₁, u₂⟩
  · rintro s₁ s₂ t₁ t₂ s₁' s₂' ⟨d, ⟨⟨⟨h₁, hA⟩, -⟩, -⟩, ⟨⟨h₂, -⟩, -⟩, -⟩ e₁' e₂'
    have hZ := h₁.1.2.2.2.1
    obtain ⟨-, ha, hb, -, -, ha1, ha2, hb1, hb2⟩ := h₁.1.2.2.2.2.1
    obtain ⟨ht, -, u₁, u₂⟩ := two_post (α := Unit)
      (two_map (fun _ => adxLayout d hZ hA) (fun _ _ h => h)
        (AdxTiledProduct.rawBare_ct (ps := adxOps d.o d.a d.b) (mem_adxOps_a _ _ _) (mem_adxOps_b _ _ _) ha hb
          ha1 ha2 hb1 hb2 (by taint_decide) (by taint_decide)))
      (fun _ s h => AdxTiledProduct.rawBare_fw (mem_adxOps_a _ _ _) (mem_adxOps_b _ _ _) ha hb ha1 ha2 hb1 hb2
        (adxLayout d hZ hA) s h)
      _ _ _ _ _ _ ⟨(), goodV_of_mid h₁ hZ hA, goodV_of_mid h₂ hZ hA⟩ e₁' e₂'
    exact ⟨ht, ⟨d, hZ, hA⟩, u₁, u₂⟩

theorem adxBodyLazy_ct : RelCT isa (Two AdxMid) adxBodyLazy fun _ _ => True := by
  unfold adxBodyLazy
  refine RelCT.seq (two_piece (Ψ := fun d s => AdxMid d s ∧ s.zf = some (decide (AlignOk d.w))) [.rdi]
    (fun d s₁ s₂ h₁ h₂ r hr => pins_adxMid d s₁ s₂ h₁ h₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; simp [hr])) (by taint_decide) ?_)
    (two_ite (fun d s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) tiledLazy_ct fallback_ct)
  rintro d s ⟨hm, hv⟩
  obtain ⟨hs, hdi, ⟨mi, hH⟩, hZ, -⟩ := id hm
  exact WP.mono (alignTest_ok hs hdi hH hZ) fun t ⟨hz, hm', k⟩ =>
    ⟨⟨AdxIn.of_keep hm hm' k (k.gpr (by decide)) (by decide), hm' ▸ hv⟩, hz⟩

/-- `vg_rsa_lazy_mont_mul_adx` after the head. -/
theorem adxTailLazy_ct : RelCT isa (Two AdxMid) (.seq adxBodyLazy (.block restore)) fun _ _ => True :=
  RelCT.seq (RelCT.keepRdi (f := CallData.B) adxBodyLazy_ct (by rw [← Code.allInstrs_eq]; decide +kernel)
    fun _ _ h => h.1.2.1)
    (two_taint [.rdi] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [h₁, h₂]) (by taint_decide))

/-- `vg_rsa_lazy_mont_mul_adx` after `zext`. -/
theorem adxCoreLazy_ct : RelCT isa (Two AdxIn)
    (.seq (.block (saves ++ slotsIn)) (.seq adxBodyLazy (.block restore)))
    fun _ _ => True :=
  RelCT.seq (two_piece _ pins_adxIn (by taint_decide) head_fw) adxTailLazy_ct

end VG.Proof.Bignum.X86_64
