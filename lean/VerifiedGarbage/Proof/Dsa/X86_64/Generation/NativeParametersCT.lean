module
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterCTState

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterLoopCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeState
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.TCB.Registration
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterCTState
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterLoopCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeState
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.Registration

/-! # Timing of the complete native DSA parameter search -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Proof.MillerRabin.X86_64


variable {checkName : String}

def ParameterStart (n pLen qLen : Nat) (p : ParameterPublic) (s : State) : Prop :=
  (∃ W, GenerationMemory p.context W s ∧ W 16 = BitVec.ofNat 64 p.randUsed) ∧
  FrV n p.context.geo.F p.ws s ∧ s.wr = p.wr ∧ p.context.geo.pLen = pLen ∧ p.context.geo.qLen = qLen

def ParameterPublic.start (p : ParameterPublic) : ParameterPublic :=
  { p with seedUsed := 0, seedBound := Nat.zero_le _ }

theorem parameter_reset {n pLen qLen : Nat} {p : ParameterPublic} {s : State}
    (h : ParameterStart n pLen qLen p s) :
    WP isa (.block (tapeReset seedTape)) s (ParameterBefore n pLen qLen p.start) := by
  obtain ⟨⟨W, hm, hu⟩, hf, hw, hp, hq⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  refine WP.mono (tapeReset_ok hm.layout R seedTape (by decide) (by decide))
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
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    ff kt.2.1 kt.2.2
  exact ⟨⟨_, ht, by simp [seedTape, upd, ParameterPublic.start], by simpa [seedTape, upd, ParameterPublic.start] using hu⟩,
    hf.congr (kt.gpr (by decide)) kt.2.2, kt.2.2.trans hw, hp, hq⟩

theorem nativeParameters_ct (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    (n : Nat) (hn : n = 2 ∨ n = 3) (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (ParameterStart n pLen qLen))
      (parameterSearch (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run pLen qLen) (fun _ _ => True) := by
  unfold parameterSearch tapeLoop
  refine RelCT.seq (two_piece [.rsp] ?_ (by taint_decide)
    (fun _ _ h => parameter_reset h)) ?_
  · intro p s t ⟨⟨Ws, hs, _⟩, _⟩ ⟨⟨Wt, ht, _⟩, _⟩ r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.layout.rsp.trans ht.layout.rsp.symm
  · exact two_map ParameterPublic.start (fun _ _ h => h) (parameterLoop_ct (checkName := checkName) H M Sq T n hn pLen qLen sizes)

end VG.Proof.Dsa.X86_64.Generation
