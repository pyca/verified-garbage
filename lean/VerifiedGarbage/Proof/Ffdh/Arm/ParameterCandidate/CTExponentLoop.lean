module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTMontOne
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyReady
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTExponentStep
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ExponentStep
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! The exponent halving loop follows its public countdown in both runs. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Keys (num)
open VG.Proof.Ffdh.Arm.KeySearch (Two)

structure ExponentCountData where
  math : MontMathData
  count : Nat

structure ExponentCountState (p : ExponentCountData) (s : State) : Prop where
  workspace : Workspace s p.math.base (8 * p.math.capacity)
  ready : KeyReady p.math.base p.math.capacity p.math.words s
  data : MontData p.math.base p.math.capacity p.math.words s.mem
  stack : Workspace s s.sp 72
  separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.math.base, 8 * p.math.capacity⟩
  positive : 0 < p.count
  bound : p.count ≤ 4
  saved : s.mem.readW (State.addr (s.sp + 64#32)) 32 = BitVec.ofNat 32 p.count

private structure ExponentCountAfter (p : ExponentCountData) (s : State) : Prop where
  workspace : Workspace s p.math.base (8 * p.math.capacity)
  ready : KeyReady p.math.base p.math.capacity p.math.words s
  data : MontData p.math.base p.math.capacity p.math.words s.mem
  stack : Workspace s s.sp 72
  separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.math.base, 8 * p.math.capacity⟩
  saved : s.mem.readW (State.addr (s.sp + 64#32)) 32 = BitVec.ofNat 32 (p.count - 1)
  zero : s.z = decide (p.count = 1)

private theorem exponentCountAfter_ok (p : ExponentCountData) (s : State) (h : ExponentCountState p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.exponentHalf s (ExponentCountAfter p) := by
  refine WP.mono (exponentHalfStep_ok h.workspace h.ready h.data h.stack h.positive h.bound h.saved h.separate) ?_
  rintro t ⟨ready, data, _, saved, zero, _, _, _, rest⟩
  exact ⟨h.workspace.congr rest.wr, ready, data, by rw [rest.sp]; exact h.stack.congr rest.wr,
    by rw [rest.sp]; exact h.separate, saved, zero⟩

private theorem exponentCountPair_keyRegs {p : ExponentCountData} {s t : State}
    (left : ExponentCountState p s) (right : ExponentCountState p t) (sp : s.sp = t.sp) : KeyRegEq s t := by
  refine ⟨?_, sp⟩
  intro r hr
  simp only [keyRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact left.ready.r7.trans right.ready.r7.symm
  · exact left.ready.r8.trans right.ready.r8.symm
  · exact left.ready.r9.trans right.ready.r9.symm

private theorem exponentCountStep_fixed (p : ExponentCountData) :
    RelCT isa (fun s t => ExponentCountState p s ∧ ExponentCountState p t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.ParameterCandidate.exponentHalf
      (fun s t => ExponentCountAfter p s ∧ ExponentCountAfter p t ∧ s.sp = t.sp) := by
  intro s t trS trT u v h runS runT
  have leak := (exponentHalf_ct _ _ _ _ _ _ (exponentCountPair_keyRegs h.1 h.2.1 h.2.2) runS runT).1
  obtain ⟨_, u', execS, postS⟩ := exponentCountAfter_ok p s h.1
  obtain ⟨_, v', execT, postT⟩ := exponentCountAfter_ok p t h.2.1
  obtain ⟨_, rfl⟩ := Exec.det runS execS
  obtain ⟨_, rfl⟩ := Exec.det runT execT
  exact ⟨leak, postS, postT, (Exec.rdwr runS).2.2.trans (h.2.2.trans (Exec.rdwr runT).2.2.symm)⟩

private def ExponentLoopPair (remaining : Nat) (s t : State) : Prop :=
  ∃ p : ExponentCountData, p.count = remaining ∧ ExponentCountState p s ∧ ExponentCountState p t ∧ s.sp = t.sp

private theorem ExponentCountAfter.continue {p : ExponentCountData} {s : State}
    (h : ExponentCountAfter p s) (positive : 0 < p.count) (bound : p.count ≤ 4)
    (go : isa.eval .ne s = some true) : ExponentCountState ⟨p.math, p.count - 1⟩ s := by
  have notLast : p.count ≠ 1 := by
    change some (!s.z) = some true at go
    rw [h.zero] at go
    simpa using go
  have nextPositive : 0 < p.count - 1 := by omega
  have nextBound : p.count - 1 ≤ 4 := by omega
  exact ⟨h.workspace, h.ready, h.data, h.stack, h.separate, nextPositive, nextBound, h.saved⟩

theorem exponentHalfLoop_ct : RelCT isa (Two ExponentCountState)
    (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.exponentHalf .ne) (fun _ _ => True) := by
  have step : ∀ n, RelCT isa (ExponentLoopPair n) VG.Impl.Ffdh.Arm.ParameterCandidate.exponentHalf
      (fun u v => isa.eval .ne u = isa.eval .ne v ∧
        (isa.eval .ne u = some false → True) ∧
        (isa.eval .ne u = some true → ∃ m, m < n ∧ ExponentLoopPair m u v)) := by
    intro n s t trS trT u v h runS runT
    obtain ⟨p, remaining, left, right, sp⟩ := h
    obtain ⟨leak, postU, postV, spUV⟩ := exponentCountStep_fixed p _ _ _ _ _ _ ⟨left, right, sp⟩ runS runT
    refine ⟨leak, ?_, by intro _; trivial, ?_⟩
    · change some (!u.z) = some (!v.z)
      rw [postU.zero, postV.zero]
    · intro go
      have goV : isa.eval .ne v = some true := by
        change some (!v.z) = some true
        change some (!u.z) = some true at go
        rw [postV.zero, ← postU.zero]
        exact go
      exact ⟨p.count - 1, by rw [← remaining]; have := left.positive; omega,
        ⟨p.math, p.count - 1⟩, rfl, postU.continue left.positive left.bound go,
        postV.continue right.positive right.bound goV, spUV⟩
  intro s t trS trT u v h runS runT
  obtain ⟨p, left, right, sp⟩ := h
  exact RelCT.loop ExponentLoopPair step p.count _ _ _ _ _ _ ⟨p, rfl, left, right, sp⟩ runS runT

end VG.Proof.Ffdh.Arm.ParameterCandidate
