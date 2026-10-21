module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTRoundKernel
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.RoundKernel
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTOnPass
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Status
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTRoundPrepare

/-! Public witness values synchronize primality results and native success counters. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)
open VG.Spec.Rsa.Mont (numAt)

structure RoundPoint where
  params : WitnessParams
  used : Nat
  passed : Nat
  witness : Nat

structure RoundStart (p : RoundPoint) (s : State) : Prop where
  state : WitnessState p.params p.used p.passed s
  more : p.passed < p.params.checks
  ready : ArithmeticReady p.params.base p.params.capacity p.params.words s
  input : numAt s.mem (State.addr p.params.base) p.params.words 1 = p.witness

private def roundKernelData (p : RoundPoint) : RoundKernelData :=
  ⟨⟨p.params.base, p.params.capacity, p.params.words⟩, p.params.modulus⟩

private theorem roundStart_kernel (p : RoundPoint) (s : State) (h : RoundStart p s) :
    RoundKernelStart (roundKernelData p) s :=
  ⟨h.ready, h.state.data, h.state.saved.space, h.state.stackScratch,
    by simpa only [witnessValues, roundKernelData] using h.state.saved.saved 36 (by simp [witnessSlots]),
    h.state.stackBelow, h.state.belowScratch⟩

private structure RoundReturned (p : RoundPoint) (s : State) : Prop where
  state : WitnessState p.params p.used p.passed s
  more : p.passed < p.params.checks
  result : (s.gpr .r0).toNat = if Spec.MillerRabin.round p.params.modulus p.witness then 1 else 0

private theorem roundReturned_ok (v : RoundImpl) (p : RoundPoint) (s : State) (h : RoundStart p s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.roundKernel v.name v.code) s (RoundReturned p) := by
  have saved : s.mem.readW (State.addr (s.sp + 36#32)) 32 = BitVec.ofNat 32 p.params.capacity := by
    simpa only [witnessValues] using h.state.saved.saved 36 (by simp [witnessSlots])
  refine WP.mono (roundKernel_ok v h.ready h.state.data h.state.saved.space h.state.stackScratch
    saved h.state.stackBelow h.state.belowScratch h.input) ?_
  rintro t ⟨data, result, frame, rest⟩
  exact ⟨h.state.after_round data frame rest, h.more, result⟩

private structure RoundCompared (p : RoundPoint) (s : State) : Prop where
  state : WitnessState p.params p.used p.passed s
  more : p.passed < p.params.checks
  zero : s.z = !(Spec.MillerRabin.round p.params.modulus p.witness)

private theorem roundCompared_ok (p : RoundPoint) (s : State) (h : RoundReturned p s) :
    WP isa (.block [.cmp .r0 (.imm 0)]) s (RoundCompared p) := by
  refine WP.mono (cmpResult_ok h.result) ?_
  rintro t ⟨⟨zero, mem⟩, rest⟩
  exact ⟨h.state.after_memory mem rest, h.more, zero⟩

theorem round_ct (v : RoundImpl) : RelCT isa (Two RoundStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.round v.name v.code) (fun _ _ => True) := by
  have kernel : RelCT isa (Two RoundStart)
      (VG.Impl.Ffdh.Arm.ParameterCandidate.roundKernel v.name v.code) (Two RoundReturned) :=
    two_post (two_map roundKernelData roundStart_kernel (roundKernel_ct v)) (roundReturned_ok v)
  have compare : RelCT isa (Two RoundReturned) (.block [.cmp .r0 (.imm 0)]) (Two RoundCompared) :=
    two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) roundCompared_ok
  have choice : RelCT isa (Two RoundCompared)
      (.ite .eq (.block [.mov .r3 (.imm 2), .cmp .r3 (.imm 4)]) VG.Impl.Ffdh.Arm.ParameterCandidate.onPass)
      (fun _ _ => True) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left.zero, right.zero]
    · exact (stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)
    · refine two_map (fun p => (⟨p.passed, p.params.checks⟩ : PassData)) ?_ onPass_ct
      intro p s h
      exact ⟨h.1.state.saved.space, h.1.more, h.1.state.checksBound,
        by simpa only [witnessValues] using h.1.state.saved.saved 56 (by simp [witnessSlots]),
        by simpa only [witnessValues] using h.1.state.saved.saved 52 (by simp [witnessSlots])⟩
  exact kernel.seq (compare.seq (choice.seq (RelCT.block_nil (fun _ _ _ => trivial))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
