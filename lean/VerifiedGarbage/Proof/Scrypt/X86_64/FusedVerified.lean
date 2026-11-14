module
public import VerifiedGarbage.Impl.Scrypt.X86_64.BlockMixFused
public import VerifiedGarbage.Proof.Scrypt.X86_64.Common
import VerifiedGarbage.Proof.Scrypt.X86_64.FusedCT
public import VerifiedGarbage.Proof.Scrypt.X86_64.FusedInvariant
import VerifiedGarbage.Proof.Scrypt.X86_64.FusedBody
import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Proof.Scrypt.X86_64.FusedSetup
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Scrypt.X86_64.FusedCorrect`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Scrypt.X86_64.BlockMix.Fused
open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Proof.Scrypt.Memory (InRegions.of_mem)
theorem loop_ok {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv s₀ 0 s) : WP isa (.loop fusedBody .ne) s (Inv s₀ (rr s₀)) := by
  refine WP.loop (M := isa) (fun n s => ∃ k, n = rr s₀ - k ∧ k < rr s₀ ∧ Inv s₀ k s) ?_ (rr s₀) s
    ⟨0, rfl, hp.pos, h⟩
  rintro n s ⟨k, rfl, hk, hi⟩
  refine WP.mono (body_ok hp hk hi) fun s' ⟨hi', hz⟩ => ?_
  rw [eval_ne hp hk hz]
  by_cases hl : k + 1 = rr s₀
  · exact .inl ⟨by simp [hl], hl ▸ hi'⟩
  · exact .inr ⟨by simp [hl], rr s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hk, hl], hi'⟩

/-! ## The epilogue -/

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv s₀ (rr s₀) s) :
    WP isa (.block (bmSaved.map fun (r, d) => .mov r (.mem (at_ .rsi d)))) s fun s' => s'.mem = s.mem ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) := by
  refine WP.mono (Spill.restore_ok .rsi bmSaved s₀.gpr s (by decide) (fun p hp' => ?_)
    (by rw [h.words.rsi]; exact h.saved)) fun s' ⟨h₁, h₂, hm, _⟩ =>
    ⟨hm, Spill.calleeSaved_ok h₁ h₂ (by decide) h.rsp⟩
  have := saved_bound p hp'
  rw [h.words.rsi, h.rd, h.wr, hp.rd, hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ (by omega_using [this]))

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa blockMixFused s₀ fun s' =>
      gprPreserved s₀ s' ∧ Proof.Scrypt.blockMixX86_64.post s₀ s' := by
  unfold blockMixFused
  refine WP.seq (WP.mono (prologue_ok hp) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (loop_ok hp h₂) fun s₃ h₃ => ?_)
  refine WP.mono (restore_ok hp h₃) fun s' ⟨hm', hg'⟩ => ?_
  refine ⟨⟨hg', ?_⟩, ?_⟩
  · rw [hm']
    refine h₃.frame.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_y
    · exact hp.ret_s
    · exact ret_stk s₀
  · show Spec.Scrypt.bytesAt s'.mem (yP s₀) (128 * rr s₀) = Spec.Scrypt.blockMix (rr s₀) (B s₀)
    rw [hm']
    exact post_of fun i hi => h₃.done i hi
end VG.Proof.Scrypt.X86_64.BlockMix.Fused

end

end


@[expose] public section

namespace VG.Proof.Scrypt.X86_64.BlockMix.Fused
open VG VG.X86_64
theorem blockMix_correct (s : State) (hs : Proof.Scrypt.blockMixX86_64.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.X86_64.blockMixFused s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.blockMixX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem blockMix_ct : ConstantTime isa Proof.Scrypt.blockMixX86_64.pre
    Proof.Scrypt.blockMixX86_64.pub Impl.Scrypt.X86_64.blockMixFused := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  exact (blockMix_rel (pre_of h₁) (pre_of h₂) (pubEq_of hpub) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Scrypt.X86_64.BlockMix.Fused
