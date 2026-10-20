module
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorSearch
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorSearchCTState

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorLoopCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeState
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorSearch
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorSearchCTState
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorLoopCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeState
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr

/-! # Timing of complete native generator selection from an input tape -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64

def GeneratorSearchStart (len : Nat) (p : GeneratorSearchPlan) (s : State) : Prop :=
  (∃ W, GeneratorSearchMemory p W s) ∧ p.core.len = len

def GeneratorSearchPlan.start (p : GeneratorSearchPlan) : GeneratorSearchPublic := ⟨p, 0, Nat.zero_le _⟩

theorem generatorSearch_reset {len : Nat} {p : GeneratorSearchPlan} {s : State}
    (h : GeneratorSearchStart len p s) :
    WP isa (.block (tapeReset generatorTape)) s (GeneratorSearchBefore len p.start) := by
  obtain ⟨⟨W, hm⟩, he⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  refine WP.mono (tapeReset_ok hm.layout R generatorTape (by decide) (by decide))
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
  refine ⟨⟨upd W 20 0, hm.frame Lt ⟨V, Rt⟩ ?_ ff kt.2.1 kt.2.2, by simp [upd, GeneratorSearchPlan.start]⟩, he⟩
  intro k hk
  simp only [generatorSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem nativeGenerator_ct (M : Mont) (Sq : MontS) (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorSearchStart len)) (generatorSearch Sq.mm M.mm len) (fun _ _ => True) := by
  unfold generatorSearch tapeLoop
  refine RelCT.seq (two_piece [.rsp] ?_ (by taint_decide)
    (fun _ _ h => generatorSearch_reset h)) ?_
  · intro p s t ⟨⟨Ws, hs⟩, _⟩ ⟨⟨Wt, ht⟩, _⟩ r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.layout.rsp.trans ht.layout.rsp.symm
  · exact two_map GeneratorSearchPlan.start (fun _ _ h => h) (generatorLoop_ct M Sq len hl)

end VG.Proof.Dsa.X86_64.Generation
