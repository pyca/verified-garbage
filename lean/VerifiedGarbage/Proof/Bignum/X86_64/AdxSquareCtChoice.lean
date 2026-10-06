import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareCtRedc
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcChoice
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8CT

/-! Reduction dispatch depends only on the public word count. -/
namespace VG.Proof.Bignum.X86_64.AdxSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

theorem rotate_gw_ct : RelCT isa (Two fun L s => GW L s ∧ L.w % 8 = 0)
    AdxRotate8.redc (Two GW) := by
  intro s t ts tt s' t' h es et
  obtain ⟨L, ⟨hs, h8⟩, ⟨ht, _⟩⟩ := h
  have hn : 0 < L.w / 8 := by have := hs.2.2.1; omega
  let W : AdxRotate8.W8 := ⟨L, L.w / 8, by omega, hn⟩
  obtain ⟨he, ⟨_, _, _⟩⟩ := AdxRotate8.redc_ct _ _ _ _ _ _ ⟨W, hs.1, ht.1⟩ es et
  have fw : ∀ u, GW L u → WP isa AdxRotate8.redc u (GW L) := by
    intro u ⟨⟨mi, hg, hZ⟩, hsz⟩
    refine WP.mono (AdxRotate8.redc_ok hg.scr hg.rdi hg.hdr hZ W.hw W.hn) fun v ⟨_, ot, kt⟩ => ?_
    exact ⟨⟨mi, ⟨hg.scr.congr kt.2.2, (kt.gpr (by decide)).trans hg.rdi,
      hg.hdr.of_outside ot (by unfold slot; omega)⟩, hZ⟩, hsz⟩
  obtain ⟨_, _, e1, h1⟩ := fw s hs
  obtain ⟨_, _, e2, h2⟩ := fw t ht
  obtain ⟨_, rfl⟩ := Exec.det es e1
  obtain ⟨_, rfl⟩ := Exec.det et e2
  exact ⟨he, L, h1, h2⟩

theorem redcChoice_ct : RelCT isa (Two GW) AdxSquare.redcChoice (Two GW) := by
  unfold AdxSquare.redcChoice
  refine RelCT.seq (two_piece (Ψ := fun L s => GW L s ∧ s.zf = some (decide (L.w % 8 = 0)))
    [.rdi] pins_gw (by taint_decide) ?_) ?_
  · intro L s ⟨⟨mi, hg, hZ⟩, hsz⟩
    refine WP.mono (redcTest_ok hg.scr hg.rdi hg.hdr hZ (by have := hsz.lt; omega))
      fun t ⟨hz, hm, kt⟩ => ?_
    exact ⟨⟨⟨mi, ⟨hg.scr.congr kt.2.2, (kt.gpr (by decide)).trans hg.rdi,
      hm ▸ hg.hdr⟩, hZ⟩, hsz⟩, hz⟩
  refine two_ite (fun L s t hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
  · refine two_map id (fun L s ⟨⟨h, hz⟩, he⟩ => ⟨h, ?_⟩) rotate_gw_ct
    simp only [eval, hz, Option.some.injEq, decide_eq_true_eq] at he
    exact he
  · exact two_map id (fun L s h => h.1.1) redc_ct
end VG.Proof.Bignum.X86_64.AdxSquare
