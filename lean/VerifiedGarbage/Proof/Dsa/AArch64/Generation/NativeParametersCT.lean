module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ParameterCTState

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ParameterLoopCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TapeState
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextFrame
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ParameterCTState
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ParameterLoopCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TapeState
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextFrame
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Timing of the complete native DSA parameter search -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.MillerRabin.AArch64

def ParameterStart (pLen qLen : Nat) (p : ParameterPublic) (s : State) : Prop :=
  (∃ W, GenerationMemory p.context W s ∧ W 16 = BitVec.ofNat 64 p.randUsed) ∧
  p.context.geo.pLen = pLen ∧ p.context.geo.qLen = qLen

def ParameterPublic.start (p : ParameterPublic) : ParameterPublic :=
  { p with seedUsed := 0, seedBound := Nat.zero_le _ }

theorem parameter_reset {pLen qLen : Nat} {p : ParameterPublic} {s : State}
    (h : ParameterStart pLen qLen p s) :
    WP isa (.block (tapeReset seedTape)) s (ParameterBefore pLen qLen p.start) := by
  obtain ⟨⟨W, hm, hu⟩, hp, hq⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  refine WP.mono (tapeReset_frame_ok hm.layout R seedTape (by decide) (by decide))
    fun t ⟨Lt, Rt, ft, kt⟩ => ?_
  have ff : Frame p.context.changed s.mem t.mem := by
    apply GenerationContext.frame_single
    intro a ha
    apply ft a
    right
    have hn := ha ⟨p.context.geo.F, frameBytes⟩ (by simp)
    change ¬ ofs p.context.geo.F a < frameBytes at hn
    change 88 ≤ ofs p.context.geo.F a
    unfold frameBytes at hn
    omega
  have ht := hm.frame Lt ⟨V, Rt⟩ (by
    intro k hk
    simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    ff kt.rd kt.wr
  exact ⟨⟨_, ht, by simp [seedTape, upd, ParameterPublic.start], by simpa [seedTape, upd, ParameterPublic.start] using hu⟩,
    hp, hq⟩

theorem nativeParameters_ct (H : GenerationHashes) (M : Mont)  (K : Kernel)
    (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (ParameterStart pLen qLen))
      (parameterSearch H.sha1 H.sha256 M.mm K.run pLen qLen) (fun _ _ => True) := by
  unfold parameterSearch tapeLoop
  refine RelCT.seq (two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide))
    (fun _ _ h => parameter_reset h)) ?_
  exact two_map ParameterPublic.start (fun _ _ h => h) (parameterLoop_ct H M K pLen qLen sizes)

end VG.Proof.Dsa.AArch64.Generation
