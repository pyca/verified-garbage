module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorLoopCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorLoopCT
import VerifiedGarbage.Proof.Framework.Omega

/-! # Timing of complete native generator selection from an input tape -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64

def GeneratorSearchStart (len : Nat) (p : GeneratorSearchPlan) (s : State) : Prop :=
  (∃ W, GeneratorSearchMemory p W s) ∧ p.core.len = len

def GeneratorSearchPlan.start (p : GeneratorSearchPlan) : GeneratorSearchPublic := ⟨p, 0, Nat.zero_le _⟩

theorem generatorSearch_reset {len : Nat} {p : GeneratorSearchPlan} {s : State}
    (h : GeneratorSearchStart len p s) :
    WP isa (.block (tapeReset generatorTape)) s (GeneratorSearchBefore len p.start) := by
  obtain ⟨⟨W, hm⟩, he⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  refine WP.mono (tapeReset_frame_ok hm.layout R generatorTape (by decide) (by decide))
    fun t ⟨Lt, Rt, ft, kt⟩ => ?_
  have ff : Frame p.core.changed s.mem t.mem := by
    intro a ha
    apply ft a
    right
    have hn := ha ⟨p.core.F, frameBytes⟩ (by simp [GeneratorPlan.changed])
    change ¬ ofs p.core.F a < frameBytes at hn
    change 168 ≤ ofs p.core.F a
    unfold frameBytes at hn
    omega
  refine ⟨⟨upd W 20 0, hm.frame Lt ⟨V, Rt⟩ ?_ ff kt.rd kt.wr, by simp [upd, GeneratorSearchPlan.start]⟩, he⟩
  intro k hk
  simp only [generatorSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem nativeGenerator_ct (M : Mont)  (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorSearchStart len)) (generatorSearch M.mm len) (fun _ _ => True) := by
  unfold generatorSearch tapeLoop
  refine RelCT.seq (two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide))
    (fun _ _ h => generatorSearch_reset h)) ?_
  exact two_map GeneratorSearchPlan.start (fun _ _ h => h) (generatorLoop_ct M len hl)

end VG.Proof.Dsa.AArch64.Generation
