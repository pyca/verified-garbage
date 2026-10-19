module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTRegion
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PubVec
public import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTChecked
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTMain
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTCode
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedExp
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PubMain
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PubExp
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedIOCT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTRegion
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PubVec
meta import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTChecked
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTCode
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PubMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PubExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedIOCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# `vg_rsa_public_precomputed_checked_ifma`: constant time

The vector code's addresses and branches depend on `rdi` alone (`pubT`, by
the taint analysis); whether it runs depends on `e` and the modulus' size,
which are public.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma.Pub
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.FoldedPublic
open VG.Proof.MlKem.X86_64 (Keep)

/-- The vector code's addresses and branches depend on `rdi` alone. -/
theorem pubT {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay} (hl : PubOk l) : TOk [.rdi] (PubIfma.exp65537 l) := by
  rcases hl with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

theorem daw_rdi : Pins (fun (q : DPub × BitVec 64) t => DAw q t) [.rdi] := fun _ _ _ ⟨_, _, _, h₁, _⟩ ⟨_, _, _, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rdi, h₂.rdi]

/-- `is65537`, from `DAw`. -/
theorem is65537_ct : RelCT isa (Two DAw) Folded.is65537
    (Two fun q t => DAw q t ∧ t.zf = some (decide (Spec.Rsa.os2ip q.1.eb = 65537))) := by
  unfold Folded.is65537
  refine RelCT.seq (two_piece (Ψ := fun q t => DAw q t ∧ t.gpr .r8 = q.1.ep ∧
      t.gpr .r9 = BitVec.ofNat 64 q.1.len) [.rdi] daw_rdi (by taint_decide) ?_)
    (two_piece [.r8, .r9] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2, h₂.2.2]) (by taint_decide) ?_)
  · rintro q s h
    have h' := h
    obtain ⟨xb, σ, g, hg, _⟩ := h'
    exact WP.mono (is65537Load_ok hg g.1.z (by rw [g.fixed sE (by decide)]; exact g.1.hE)
      (by rw [g.fixed sElen (by decide)]; exact g.1.hL)) fun a ⟨h8, h9, ma, ka⟩ =>
      ⟨DAw.regs h ma ka (by decide), h8, h9⟩
  · rintro q s ⟨h, h8, h9⟩
    have h' := h
    obtain ⟨xb, σ, g, _⟩ := h'
    have hs := g.1.e.congrK g.inScr g.2.2.1
    exact WP.mono (is65537Check_ok h8 h9 hs g.1.el g.1.L1
      (by have := g.1.L2; have := g.1.k2; show q.1.len < 2^31; omega)) fun a ⟨za, ma, ka⟩ =>
        ⟨DAw.regs h ma ka (by decide), za⟩

/-- `cmp w, n`, with a public condition `P` carried. -/
theorem cmpW_ct (n : Nat) (hn : n < 2 ^ 31) (P : DPub × BitVec 64 → Prop) (hT : TOk [.rdi] (PubIfma.cmpW n)) :
    RelCT isa (Two fun q t => DAw q t ∧ P q) (PubIfma.cmpW n)
      (Two fun q t => (DAw q t ∧ P q) ∧ t.zf = some (decide ((q.1.k + 7) / 8 = n))) := by
  obtain ⟨_, hT⟩ := hT
  refine two_post (two_taint [.rdi] (fun q s₁ s₂ h₁ h₂ => daw_rdi q s₁ s₂ h₁.1 h₂.1) hT) ?_
  rintro q s ⟨h, hp⟩
  have h' := h
  obtain ⟨xb, σ, g, hg, _⟩ := h'
  have hk2 := g.1.k2
  exact WP.mono (cmpW_ok n hg g.1.z hn (by omega)) fun t ⟨z, m, k⟩ => ⟨⟨DAw.regs h m k (by decide), hp⟩, z⟩

/-- The vector code, for a layout of the modulus' size and `e = 65537`. -/
theorem vec_ct {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay} (hl : PubOk l) :
    RelCT isa (Two fun q t => DAw q t ∧ Spec.Rsa.os2ip q.1.eb = 65537 ∧ (q.1.k + 7) / 8 = l.W)
      (PubIfma.exp65537 l) (Two DD) := by
  obtain ⟨_, hT⟩ := pubT hl
  refine two_post (two_taint [.rdi] (fun q s₁ s₂ h₁ h₂ => daw_rdi q s₁ s₂ h₁.1 h₂.1) hT) ?_
  rintro q s ⟨⟨xb, σ, g, hg, hN, hinv, hX, -, hR⟩, he, hw⟩
  rw [hw] at hg hN hinv hX hR
  have hz := g.1.z
  rw [hw] at hz
  refine WP.mono (exp65537_ok hl hg hN hinv hX hz hR g.1.rlt g.1.odd (by rw [← hw]; exact g.1.big) he)
    fun d ⟨gd, _, fd, kd, _⟩ => ⟨xb, σ, g.step (by rw [hw]; exact fd.mono (expAll_sub _)) kd ?_, by rw [hw]; exact gd⟩
  exact fd.word_eq (mask_not_expAll _) (by unfold sMask sFn; have := hg.scr.nowrap; omega)

/-- The ADX code's exponentiation, from `DAw`. -/
theorem adx_ct (M : Mont) (hfinal : RelCT isa (Two GoodL) (M.mm aY aX aY) (fun _ _ => True))
    (Φ : DPub × BitVec 64 → State → Prop) (hΦ : ∀ q t, Φ q t → DAw q t) :
    RelCT isa (Two Φ) (PubIfma.adxExp M.mm) (Two DD) :=
  two_map id hΦ (RelCT.seq pdMm_ctw (RelCT.seq (exp_ct M) (pdFinal_ct hfinal)))

/-- `pubExp`: leaks the same in runs with the same public data. -/
theorem pubExp_ct (M : Mont) (hfinal : RelCT isa (Two GoodL) (M.mm aY aX aY) (fun _ _ => True)) :
    RelCT isa (Two DA) (PubIfma.pubExp M.mm) (Two DD) := by
  unfold PubIfma.pubExp
  refine RelCT.seq (two_map id (fun _ _ h => h.weak) is65537_ct)
    (two_ite (fun _ _ _ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_
      (adx_ct M hfinal _ fun _ _ h => h.1.1))
  have e65 : ∀ q t, (DAw q t ∧ t.zf = some (decide (Spec.Rsa.os2ip q.1.eb = 65537))) ∧ isa.eval .e t = some true →
      DAw q t ∧ Spec.Rsa.os2ip q.1.eb = 65537 := fun q t ⟨⟨h, z⟩, hb⟩ => ⟨h, by simpa [eval, z] using hb⟩
  refine two_map id e65 (RelCT.seq (cmpW_ct 32 (by decide) (fun q => Spec.Rsa.os2ip q.1.eb = 65537) ⟨_, by taint_decide⟩)
    (two_ite (fun _ _ _ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_))
  · exact two_map id (fun q t ⟨⟨⟨h, he⟩, z⟩, hb⟩ => ⟨h, he, (by simpa [eval, z] using hb : (q.1.k + 7) / 8 = 32)⟩) (vec_ct (.inl rfl))
  refine two_map id (fun q t ⟨⟨h, _⟩, _⟩ => h) (RelCT.seq (cmpW_ct 48 (by decide) (fun q => Spec.Rsa.os2ip q.1.eb = 65537) ⟨_, by taint_decide⟩)
    (two_ite (fun _ _ _ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_))
  · exact two_map id (fun q t ⟨⟨⟨h, he⟩, z⟩, hb⟩ => ⟨h, he, (by simpa [eval, z] using hb : (q.1.k + 7) / 8 = 48)⟩) (vec_ct (.inr (.inl rfl)))
  refine two_map id (fun q t ⟨⟨h, _⟩, _⟩ => h) (RelCT.seq (cmpW_ct 64 (by decide) (fun q => Spec.Rsa.os2ip q.1.eb = 65537) ⟨_, by taint_decide⟩)
    (two_ite (fun _ _ _ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ (adx_ct M hfinal _ fun _ _ h => h.1.1.1)))
  exact two_map id (fun q t ⟨⟨⟨h, he⟩, z⟩, hb⟩ => ⟨h, he, (by simpa [eval, z] using hb : (q.1.k + 7) / 8 = 64)⟩) (vec_ct (.inr (.inr rfl)))

/-- `rest` with `pubExp`: leaks the same in runs with the same public data. -/
theorem rest_ct (M : Mont) (hfinal : RelCT isa (Two GoodL) (M.mm aY aX aY) (fun _ _ => True)) :
    RelCT isa (Two DRel) (PubIfma.rest M.mm) (fun _ _ => True) := by
  rw [rest_eq]
  refine RelCT.seqs_append (by simp [wordIn]) (by simp) (RelCT.seq wordSetup_ct ?_)
  refine RelCT.seqs_append (by simp) (by simp [wordOutStepsArr]) (RelCT.seq (R := Two DD)
    (show RelCT isa (Two DA) (seqs [PubIfma.pubExp M.mm]) (Two DD) from pubExp_ct M hfinal) ?_)
  exact two_map (fun q => (⟨DPub.L q,q.1.k,q.1.op⟩ : OPub)) (fun _ _ h => dd_wordOPre h) wordOut_ct

/-- `vg_rsa_public_precomputed_checked_ifma` is constant time. -/
theorem checked_ct (M : Mont) (hfinal : RelCT isa (Two GoodL) (M.mm aY aX aY) (fun _ _ => True)) :
    ConstantTime isa pdContract.pre pdContract.pub (PubIfma.checked M.mm) :=
  guardedPd_ct (codeWith_constantTime (PubIfma.rest M.mm) (rest_ct M hfinal))

end VG.Proof.Bignum.X86_64.Ifma.Pub
