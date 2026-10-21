module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTDraw
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTStackBlocks
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Room
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessMemory
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTDrawSample
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend

/-! A witness iteration branches on public entropy availability. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

def WitnessLoopStart (p : DrawPoint) (s : State) : Prop :=
  WitnessState p.params p.used p.passed s ∧ p.passed < p.params.checks

private structure WitnessRoomEnd (p : DrawPoint) (s : State) : Prop where
  state : WitnessState p.params p.used p.passed s
  more : p.passed < p.params.checks
  zero : s.z = decide (p.params.bytes.length - p.used < (p.params.bits + 7) / 8)

private theorem witnessRoomEnd_ok (p : DrawPoint) (s : State) (h : WitnessLoopStart p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.witnessRoom) s (WitnessRoomEnd p) := by
  have lengthWord : s.mem.readW (State.addr (s.sp + 20#32)) 32 = BitVec.ofNat 32 p.params.bytes.length := by
    simpa only [witnessValues] using h.1.saved.saved 20 (by simp [witnessSlots])
  have usedWord : s.mem.readW (State.addr (s.sp + 40#32)) 32 = BitVec.ofNat 32 p.used := by
    simpa only [witnessValues] using h.1.saved.saved 40 (by simp [witnessSlots])
  have widthWord : s.mem.readW (State.addr (s.sp + 48#32)) 32 = BitVec.ofNat 32 ((p.params.bits + 7) / 8) := by
    simpa only [witnessValues] using h.1.saved.saved 48 (by simp [witnessSlots])
  refine WP.mono (witnessRoom_ok h.1.saved.space h.1.tapeCount
    (by have := h.1.bitsBound; omega) h.1.usedBound lengthWord usedWord widthWord) ?_
  rintro t ⟨⟨zero, mem⟩, rest⟩
  exact ⟨h.1.after_memory mem rest, h.2, zero⟩

theorem witnessStep_ct (v : RoundImpl) : RelCT isa (Two WitnessLoopStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.witnessStep v.name v.code) (fun _ _ => True) := by
  have room : RelCT isa (Two WitnessLoopStart)
      (.block VG.Impl.Ffdh.Arm.ParameterCandidate.witnessRoom) (Two WitnessRoomEnd) :=
    two_post (witnessRoom_ct.mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) witnessRoomEnd_ok
  have choice : RelCT isa (Two WitnessRoomEnd)
      (.ite .eq (.block [.mov .r3 (.imm 0), .cmp .r3 (.imm 4)])
        (VG.Impl.Ffdh.Arm.ParameterCandidate.draw v.name v.code)) (fun _ _ => True) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left.zero, right.zero]
    · exact (stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)
    · refine two_map id ?_ (draw_ct v)
      intro p s h
      have enough : p.used + (p.params.bits + 7) / 8 ≤ p.params.bytes.length := by
        have notShort : ¬ p.params.bytes.length - p.used < (p.params.bits + 7) / 8 := by
          have go := h.2
          change some s.z = some false at go
          rw [h.1.zero] at go
          exact of_decide_eq_false (Option.some.inj go)
        have := h.1.state.usedBound
        omega
      exact ⟨⟨h.1.state, enough⟩, h.1.more⟩
  exact room.seq (choice.seq (RelCT.block_nil (fun _ _ _ => trivial)))

end VG.Proof.Ffdh.Arm.ParameterCandidate
