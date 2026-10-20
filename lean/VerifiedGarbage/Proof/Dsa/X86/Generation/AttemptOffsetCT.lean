module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.PAttemptControl
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchState
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PAttempt
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchStatus
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate
import VerifiedGarbage.Proof.Dsa.X86.Generation.PAttemptControl

/-! # Move the public p-search offset from its controller into the search frame -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Dsa.X86.Generation

def PAttemptAt (P : PSearchPlan) (counter used : Nat) (s : State) : Prop :=
  (∃ W, PSearchMemory P W s ∧ W 16 = BitVec.ofNat 32 used) ∧
  SearchControl (off P.context.geometry.base VG.Impl.Dsa.Generation.Layout.control) counter
    (P.context.geometry.contributionCount + 1) s

def AttemptConstructAt (P : PSearchPlan) (counter used : Nat) (s : State) : Prop :=
  ∃ W, PSearchMemory P W s ∧ W 16 = BitVec.ofNat 32 used ∧
    W 2 = BitVec.ofNat 32 (1 + counter * (P.context.geometry.contributionCount + 1))

theorem pAttemptOffset_ct (P : PSearchPlan) (counter used : Nat) :
    RelCT isa (Two fun (_ : Unit) => PAttemptAt P counter used)
      (.block pAttemptOffset) (Two fun (_ : Unit) => AttemptConstructAt P counter used) := by
  refine two_piece [.edi, .esp] ?_ (by taint_decide) ?_
  · rintro _ s t ⟨⟨Ws, Rs, _⟩, Cs⟩ ⟨⟨Wt, Rt, _⟩, Ct⟩ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (Cs.scr.edi_toNat.trans Ct.scr.edi_toNat.symm)
    · exact BitVec.eq_of_toNat_eq (Rs.context.arena.frame.esp_toNat.trans Rt.context.arena.frame.esp_toNat.symm)
  · rintro _ s ⟨⟨W, R, usedValue⟩, C⟩
    refine WP.mono (pAttemptOffset_ok R.context C) fun t ⟨Rt, _, O, K⟩ => ?_
    have F : Frame (parameterWrites P.context.geometry) s.mem t.mem := O.mono (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr; simp [parameterWrites])
    have pw := P.context.geometry.qWidth
    have room : q + P.context.geometry.qLen ≤ usedBytes P.context.geometry.pLen := by unfold q usedBytes domainCheck; omega
    refine ⟨_, ⟨Rt, R.seed.keep F P.seed.parameterApart K, R.source, ?_, R.seedUsed⟩, usedValue, rfl⟩
    rw [drawFrame_bytes O (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact (P.context.geometry.frame_part room).symm)
      (by omega), R.qval]
end VG.Proof.Dsa.X86.Generation
