import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Edges
import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT

/-! Public header loads establish the pointers used by the edge blocks. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (WP.keep)

theorem setupBases_fw (L : Ws) (s : State) (h : GoodW L s) :
    WP isa (.block AdxRotate8.setupBases) s fun t => t.gpr .rcx = off L.B (slot L.w aAcc + 16) := by
  obtain ⟨mi, hg, hZ⟩ := h
  have hl := hg.scr.ld (show 8 * sArr aAcc + 8 ≤ L.Z by
    have := hdr_lt_slot L.w 8 (show sArr aAcc < 32 by decide); omega)
  unfold AdxRotate8.setupBases
  xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hg.hdr.harr aAcc (by decide), off_add16]

theorem setup_ct : RelCT isa (Two GoodW) (.block AdxRotate8.setup) (fun _ _ => True) := by
  unfold AdxRotate8.setup
  apply VG.RelCT.block_append
  refine RelCT.seq (two_piece [.rdi] pins_goodW (by taint_decide) setupBases_fw) ?_
  exact two_taint [.rcx] (fun L s t hs ht r hr => by
    have he : r = .rcx := List.mem_singleton.mp hr
    subst r; exact hs.trans ht.symm) (by taint_decide)

def EndW (L : Ws) (s : State) : Prop := GoodW L s ∧ s.gpr .rcx = off L.B (slot L.w aTmp)

theorem finish_ct : RelCT isa (Two EndW) (.block AdxRotate8.finish) (fun _ _ => True) := by
  unfold AdxRotate8.finish
  apply VG.RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun L s => s.gpr .r8 = off L.B (slot L.w aTmp) ∧
    s.gpr .rbp = BitVec.ofNat 64 L.w) [.rdi, .rcx] ?_ (by taint_decide) ?_) ?_
  · intro L s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact pins_goodW L s t hs.1 ht.1 .rdi (by simp)
    · rw [hs.2, ht.2]
  · intro L s ⟨⟨mi, hg, hZ⟩, hc⟩
    exact WP.mono (finishSetup_ok hg.scr hg.rdi hg.hdr hZ hc) fun _ h => ⟨h.1, h.2.1⟩
  · refine two_taint [.r8, .rbp] ?_ (by taint_decide)
    intro L s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hs.1, ht.1]
    · rw [hs.2, ht.2]
end VG.Proof.Bignum.X86_64.AdxRotate8
