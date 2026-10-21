module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTDrawRange
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTRound
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.DrawRange
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Status
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessMemory
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTDrawSample
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessState
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend

/-! A public witness prefix determines native range and primality branches. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)
open VG.Spec.Rsa.Mont (numAt)

def DrawMore (p : DrawPoint) (s : State) : Prop := DrawStart p s ∧ p.passed < p.params.checks

private structure RangeEnd (p : DrawPoint) (s : State) : Prop where
  state : WitnessState p.params (p.used + (p.params.bits + 7) / 8) p.passed s
  more : p.passed < p.params.checks
  ready : ArithmeticReady p.params.base p.params.capacity p.params.words s
  input : numAt s.mem (State.addr p.params.base) p.params.words 1 = witnessValue p.params p.used
  flag : (s.gpr .r11).toNat = if decide (1 < witnessValue p.params p.used ∧ witnessValue p.params p.used < p.params.modulus - 1) then 1 else 0

private theorem rangeEnd_ok (p : DrawPoint) (s : State) (h : DrawMore p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.drawRange s (RangeEnd p) := by
  refine WP.mono (drawRange_ok h.1.1 h.1.2) ?_
  rintro t ⟨state, ready, flag, input, _, _⟩
  refine ⟨state, h.2, ready, input, ?_⟩
  rw [flag]
  by_cases valid : 1 < witnessValue p.params p.used ∧ witnessValue p.params p.used < p.params.modulus - 1
  · simp only [ite_eq_left valid, decide_eq_true valid, ite_true]; rfl
  · simp only [ite_eq_right valid, decide_eq_false valid, Bool.false_eq_true, ite_false]; rfl

private structure DrawCompared (p : DrawPoint) (s : State) : Prop where
  state : WitnessState p.params (p.used + (p.params.bits + 7) / 8) p.passed s
  more : p.passed < p.params.checks
  ready : ArithmeticReady p.params.base p.params.capacity p.params.words s
  input : numAt s.mem (State.addr p.params.base) p.params.words 1 = witnessValue p.params p.used
  zero : s.z = !(decide (1 < witnessValue p.params p.used ∧ witnessValue p.params p.used < p.params.modulus - 1))

private theorem drawCompared_ok (p : DrawPoint) (s : State) (h : RangeEnd p s) :
    WP isa (.block [.cmp .r11 (.imm 0)]) s (DrawCompared p) := by
  refine WP.mono (cmpWord_ok .r11 h.flag) ?_
  rintro t ⟨⟨zero, mem⟩, rest⟩
  exact ⟨h.state.after_memory mem rest, h.more,
    h.ready.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ready.ptr), by rw [mem]; exact h.input, zero⟩

theorem draw_ct (v : RoundImpl) : RelCT isa (Two DrawMore)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.draw v.name v.code) (fun _ _ => True) := by
  have range : RelCT isa (Two DrawMore) VG.Impl.Ffdh.Arm.ParameterCandidate.drawRange (Two RangeEnd) :=
    two_post (drawRange_ct.mono (fun _ _ h => two_mono (fun _ _ h => h.1) h) (fun _ _ h => h)) rangeEnd_ok
  have compare : RelCT isa (Two RangeEnd) (.block [.cmp .r11 (.imm 0)]) (Two DrawCompared) :=
    two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) drawCompared_ok
  have choice : RelCT isa (Two DrawCompared)
      (.ite .eq (.block [.mov .r3 (.imm 4), .cmp .r3 (.imm 4)])
        (VG.Impl.Ffdh.Arm.ParameterCandidate.round v.name v.code)) (fun _ _ => True) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left.zero, right.zero]
    · exact (stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)
    · exact two_map (fun p => (⟨p.params, p.used + (p.params.bits + 7) / 8, p.passed, witnessValue p.params p.used⟩ : RoundPoint))
        (fun _ _ h => ⟨h.1.state, h.1.more, h.1.ready, h.1.input⟩) (round_ct v)
  exact range.seq (compare.seq (choice.seq (RelCT.block_nil (fun _ _ _ => trivial))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
