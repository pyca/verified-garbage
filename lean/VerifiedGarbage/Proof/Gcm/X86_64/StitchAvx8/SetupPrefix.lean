import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Metadata
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Env
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Counter

/-! # Establishing the batch environment from the saved entry state -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Gcm.X86_64.StitchAvx8 (setupC)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame)
open VG.Spec.Gcm (Block blockAt)

theorem setupPrefix_ok {s₀ : State} (hp : SPre s₀) (s : State) (P : Nat → Block)
    (hg : ∀ r, r ≠ .rax → s.gpr r = s₀.gpr r)
    (hm : Frame [pR s₀] s₀.mem s.mem) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (h0 : s.lane .xmm0 0 = revMask) (h1 : s.lane .xmm1 0 = poly)
    (hP : ∀ k < 8, s.mem.readW (pp s₀ + BitVec.ofNat 64 (128 + 16 * k)) 128 = P k) :
    WP isa (.block (setupC ++ metaCode ++ counterHead)) s fun t =>
      Env s₀ P t ∧ Frame [pR s₀] s₀.mem t.mem ∧
      t.gpr .rdx = dp s₀ ∧ t.gpr .r9 = s₀.gpr .r9 ∧
      (t.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 ∧
      XBinOp.eval .pshufb (t.lane .xmm7 0) revMask = cb s₀ ∧ t.lane .xmm2 0 = y₀ s₀ := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (setupC_ok s h0 (by rw [hwr, hg _ (by decide)]; exact hp.y_in))
    fun u ⟨hyu, hu10, hax, hdx, hgu, hxu, hmu, hrdu, hwru⟩ => ?_
  have gu : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → u.gpr r = s₀.gpr r :=
    fun r hax hdx h10 => (hgu r hax hdx h10).trans (hg r hax)
  have gu11 : u.gpr .r11 = pp s₀ := gu _ (by decide) (by decide) (by decide)
  have gu10 : u.gpr .r10 = kp s₀ + BitVec.ofNat 64 (16 * nr s₀) := by
    rw [hu10, hg _ (by decide), hg _ (by decide)]
  have guax : u.gpr .rax = cp s₀ := hax.trans (hg _ (by decide))
  have gudx : u.gpr .rdx = dp s₀ := hdx.trans (hg _ (by decide))
  have hmu0 : Frame [pR s₀] s₀.mem u.mem := hmu ▸ hm
  rw [WP.block_append_iff]
  refine WP.mono (meta_ok u
    (by rw [hwru, hwr, gu11]; exact in_sub hp.p_in (off := 768) (by decide))
    (by rw [hwru, hwr, gu11]; exact in_sub hp.p_in (off := 784) (by decide))
    (by rw [hwru, hwr, gu11]; exact in_sub hp.p_in (off := 808) (by decide))
    (by rw [hwru, hwr, gu11]; exact in_sub hp.p_in (off := 800) (by decide)))
    fun v ⟨hmv, hgv, hxv, hrdv, hwrv⟩ => ?_
  have fm : Frame [metaR u] u.mem v.mem := hmv ▸ meta_frame u
  have fmv : Frame [pR s₀] s₀.mem v.mem := hmu0.trans (fm.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨pR s₀, List.mem_singleton_self _, by
      simpa only [metaR, gu11] using (Offset.sub_base (pp s₀) (d := 768) (n := 48) (k := 1024) (by decide))⟩)
  have gvax : v.gpr .rax = cp s₀ := by rw [hgv]; exact guax
  have vcb : blockAt v.mem (cp s₀) = cb s₀ := blockAt_frame fmv (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hp.p_c.symm)
  refine WP.mono (counterHead_ok v (by
    rw [hrdv, hwrv, hrdu, hwru, hrd, hwr, gvax, BitVec.add_zero]
    exact in_rdwr hp.c_in) (by
    rw [hrdv, hwrv, hrdu, hwru, hrd, hwr, gvax]
    exact in_rdwr (in_sub hp.c_in (off := 12) (by decide))))
    fun t ⟨hti, ht8, ht7, hgt, hxt, hmt, hrdt, hwrt⟩ => ?_
  have gt : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → r ≠ .rsi → r ≠ .r8 →
      t.gpr r = s₀.gpr r := by
    intro r hax hdx h10 hsi h8
    rw [hgt r hsi h8, hgv]; exact gu r hax hdx h10
  have ft : Frame [pR s₀] s₀.mem t.mem := hmt ▸ fmv
  have ep : Env s₀ P t := by
    constructor
    · exact gt _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [hti, gvax]
    · exact gt _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact gt _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [hgt _ (by decide) (by decide), hgv]; exact gu10
    · intro r hax hdx h8 h9 h10 hsi; exact gt r hax hdx h10 hsi h8
    · exact ft.mono (by simp)
    · intro k hk
      rw [hmt]
      have he : v.mem.readW (pp s₀ + BitVec.ofNat 64 (128 + 16 * k)) 128 =
          u.mem.readW (pp s₀ + BitVec.ofNat 64 (128 + 16 * k)) 128 :=
        fm.readW (r := ⟨pp s₀ + BitVec.ofNat 64 (128 + 16 * k), 16⟩)
          (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
          (by intro r hr; simp only [List.mem_singleton] at hr; subst r
              rw [metaR, gu11]
              exact Offset.disjoint (pp s₀) (by omega) (by omega) (by decide)) (by decide)
      rw [he, hmu]; exact hP k hk
    · rw [hmt, hmv, ← gu11]
      exact (meta_mask u).trans ((hxu _ (by decide) 0 (by decide)).trans h0)
    · rw [hmt, hmv, ← gu11]
      exact (meta_poly u).trans ((hxu _ (by decide) 0 (by decide)).trans h1)
    · rw [hmt, hmv, ← gu11]
      exact (meta_rounds u).trans (gu _ (by decide) (by decide) (by decide))
    · rw [hmt, hmv, ← gu11]
      exact (meta_data u).trans gudx
    · exact hrdt.trans (hrdv.trans (hrdu.trans hrd))
    · exact hwrt.trans (hwrv.trans (hwru.trans hwr))
  refine ⟨ep, ft, ?_, gt _ (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, ?_⟩
  · rw [hgt _ (by decide) (by decide), hgv]; exact gudx
  · rw [ht8, gvax, VG.Proof.Aes.X86_64.icb_lo, vcb]
  · rw [ht7, gvax, BitVec.add_zero, ← blockAt_eq]; exact vcb
  · rw [hxt _ (by decide), hxv, hyu, hg _ (by decide)]
    exact blockAt_frame hm (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hp.p_y.symm)

end VG.Proof.Gcm.X86_64.StitchAvx8
