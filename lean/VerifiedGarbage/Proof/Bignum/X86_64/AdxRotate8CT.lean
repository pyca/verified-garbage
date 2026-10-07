import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8CtEdges
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8CtLoop
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Redc

/-! Constant time of the complete register-tiled Montgomery reduction. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

theorem redc_ct : RelCT isa (Two fun L : W8 => GoodW L.ws) AdxRotate8.redc
    (Two fun L : W8 => GoodW L.ws) := by
  apply two_post ?_ ?_
  · unfold AdxRotate8.redc
    refine RelCT.seq (two_post (Ψ := fun L s => RW L 0 s) (two_map W8.ws (fun _ _ h => h) setup_ct) ?_) ?_
    · intro L s ⟨mi, hg, hZ⟩
      refine WP.mono (setup_ok hg.scr hg.rdi hg.hdr hZ) fun t ⟨hc, _, ot, kt⟩ => ?_
      exact ⟨⟨mi, ⟨hg.scr.congr kt.2.2, (kt.gpr (by decide)).trans hg.rdi,
        hg.hdr.of_outside ot (by unfold slot; omega)⟩, hZ⟩,
        by simpa only [Nat.mul_zero, Nat.add_zero] using hc⟩
    refine RelCT.seq outer_ct ?_
    refine two_map W8.ws ?_ finish_ct
    intro L s ⟨hg, hc⟩
    exact ⟨hg, by rw [hc]; congr 1; have := L.hw; unfold slot aAcc aTmp; omega⟩
  · intro L s ⟨mi, hg, hZ⟩
    refine WP.mono (redc_ok hg.scr hg.rdi hg.hdr hZ L.hw L.hn) fun t ⟨_, ot, kt⟩ => ?_
    exact ⟨mi, ⟨hg.scr.congr kt.2.2, (kt.gpr (by decide)).trans hg.rdi,
      hg.hdr.of_outside ot (by unfold slot; omega)⟩, hZ⟩
end VG.Proof.Bignum.X86_64.AdxRotate8
