module

public import VerifiedGarbage.Proof.Sha3.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lazy.Sequence
public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Unrolled
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.VectorCoreExec
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Wrap
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
import VerifiedGarbage.Proof.Framework.Bitslice.Anf
import VerifiedGarbage.Proof.Framework.RegSet
meta import VerifiedGarbage.Proof.Sha3.Contract
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Lazy
import Mathlib.Tactic.ToExpr
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import Mathlib.Tactic.ToExpr
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector
public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lazy.Round

@[expose] public section
namespace VG.Proof.Sha3.AArch64.Scalar.Lazy
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar
open VG.Impl.Sha3.AArch64.Scalar.Lazy
open VG.Proof.Sha3.AArch64.Scalar

/-- All 24 rounds followed by the one-time canonical lane restoration. -/
theorem core_ok (A : Spec.Sha3.State) (s : State)
    (hs : ∀ (i : Nat) (hi : i < 25), s.gpr (laneReg i) = A[i]) :
    WP isa (.block permutationCore) s fun t =>
      (∀ (i : Nat) (hi : i < 25), t.gpr (laneReg i) = (Spec.Sha3.keccakF A)[i]) ∧ Keep s t := by
  have hl0 : (stageLayout 0).length = 25 := by decide +kernel
  have hcanon : ∀ i < 25, (stageLayout 0).getD i (.x0, 0) = (laneReg i, 0) := by decide +kernel
  have hin : LayoutHolds (stageLayout 0) (logicalState A) (machineFile s) := by
    apply layout_of_at
    intro i hi
    have hi25 : i < 25 := by omega
    simp only [hcanon i hi25, logicalState_lane _ i hi25,
      VG.Bitslice.Anf.rotateRight_zero]
    exact hs i hi25
  unfold permutationCore
  rw [WP.block_append_iff]
  refine (roundPrefix_ok 24 (by decide) A s hin).mono fun t ht => ?_
  let f := machineFile t
  obtain ⟨u, hu, hru, hm, hrd, hwr, hsp, hv⟩ :=
    vector_list_ok normalize normalize_good f t ⟨fun _ => rfl, fun _ _ => rfl⟩
  refine WP.of_runBlock ⟨u, hu, ?_⟩
  refine ⟨fun i hi => (hru.regs (laneReg i)).trans (normalize_math _ f ht.1 i hi),
    ht.2.trans ⟨hm, hrd, hwr, hsp, hv⟩⟩

theorem core_state_keep (orig : State) (A : Spec.Sha3.State) (s : State)
    (hs : Boundary.CoreState orig A s) :
    WP isa (.block permutationCore) s fun t =>
      Boundary.CoreState orig (Spec.Sha3.keccakF A) t ∧ RoundKeep s t := by
  refine (core_ok A s hs.lanes).mono fun t ⟨hl, hk⟩ => ?_
  refine ⟨?_, ⟨hk.mem, hk.vec⟩⟩
  refine ⟨⟨hk.rd.trans hs.keep.rd, hk.wr.trans hs.keep.wr, hk.sp.trans hs.keep.sp⟩,
    ?_, ?_, ?_, hl⟩
  · simpa only [Boundary.Ptrs, hk.vec .v30 (by decide) (by decide) (by decide) (by decide),
      hk.vec .v31 (by decide) (by decide) (by decide) (by decide)] using hs.ptrs
  · intro i hi
    have hn := savedVec_not_temps i hi
    rw [hk.vec _ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2]
    exact hs.saved i hi
  · intro q hq
    have hn := preservedV_not_temps q hq
    rw [hk.vec _ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2]
    exact hs.vec q hq

theorem core_state (orig : State) (A : Spec.Sha3.State) (s : State)
    (hs : Boundary.CoreState orig A s) :
    WP isa (.block permutationCore) s (Boundary.CoreState orig (Spec.Sha3.keccakF A)) :=
  (core_state_keep orig A s hs).mono fun _ h => h.1

theorem permute_correct (s : State) (hs : VG.Proof.Sha3.permuteAArch64.pre s) :
    ∃ t s', Exec isa permute s t s' ∧ abiPreserved s s' ∧
      VG.Proof.Sha3.permuteAArch64.post s s' :=
  Boundary.wrap_correct (.block permutationCore) (fun orig A s _ hs => core_state orig A s hs)
    s (VG.Proof.Sha3.AArch64.pre_of s hs)

theorem permute_noCalls : permute.noCalls = true := by lit_decide

theorem permute_noFrames : permute.noFrames = true := by lit_decide

theorem permute_ct : ConstantTime isa VG.Proof.Sha3.permuteAArch64.pre
    VG.Proof.Sha3.permuteAArch64.pub permute := by
  refine VG.Taint.constantTime (A := VectorTaint.taint) (VectorTaint.ofRegs [.x0, .x1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, hsp⟩
  refine ⟨⟨hsp, fun r hr => ?_⟩, ?_⟩
  · simp only [VectorTaint.ofRegs, Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> with_reducible assumption
  · intro r hr
    simp [VectorTaint.ofRegs, RegSet.mem_ofList] at hr

theorem permute_verified :
    Verified AArch64.target permute (Proof.Sha3.permuteContract AArch64.abi) :=
  Verified.of_correct permute_correct permute_ct (by
    sig_implies [Proof.Sha3.permuteContract, Proof.Sha3.permuteSig, VG.Proof.Sha3.permuteAArch64,
      AArch64.abi, AArch64.argRegs] [VG.Proof.Sha3.AArch64.satState]
      using VG.Proof.Sha3.AArch64.satState)

end VG.Proof.Sha3.AArch64.Scalar.Lazy
