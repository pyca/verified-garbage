module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTMontOne
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyReady
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCountStep
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CountStep
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Native factor-of-two decomposition follows the same public modulus in both runs. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Keys (num)
open VG.Proof.Ffdh.Arm.KeySearch (Two)

structure CountData where
  math : MontMathData
  number : Nat
  count : Nat

structure CountState (p : CountData) (s : State) : Prop where
  workspace : Workspace s p.math.base (8 * p.math.capacity)
  ready : KeyReady p.math.base p.math.capacity p.math.words s
  data : MontData p.math.base p.math.capacity p.math.words s.mem
  stack : Workspace s s.sp 72
  separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.math.base, 8 * p.math.capacity⟩
  number : num s.mem (p.math.base + 96#32) (2 * p.math.words + 2) 29 = p.number
  positive : 0 < p.number
  even : p.number % 2 = 0
  saved : s.mem.readW (State.addr (s.sp + 60#32)) 32 = BitVec.ofNat 32 p.count

private structure CountAfter (p : CountData) (s : State) : Prop where
  workspace : Workspace s p.math.base (8 * p.math.capacity)
  ready : KeyReady p.math.base p.math.capacity p.math.words s
  data : MontData p.math.base p.math.capacity p.math.words s.mem
  stack : Workspace s s.sp 72
  separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.math.base, 8 * p.math.capacity⟩
  number : num s.mem (p.math.base + 96#32) (2 * p.math.words + 2) 29 = p.number / 2
  saved : s.mem.readW (State.addr (s.sp + 60#32)) 32 = BitVec.ofNat 32 (p.count + 1)
  zero : s.z = decide (p.number / 2 % 2 = 0)

private theorem countAfter_ok (p : CountData) (s : State) (h : CountState p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.halfCountStep s (CountAfter p) := by
  refine WP.mono (halfCountStep_ok h.workspace h.ready h.data h.stack h.saved h.separate) ?_
  rintro t ⟨ready, data, number, saved, zero, _, _, _, rest⟩
  rw [h.number] at number zero
  exact ⟨h.workspace.congr rest.wr, ready, data, by rw [rest.sp]; exact h.stack.congr rest.wr,
    by rw [rest.sp]; exact h.separate, number, saved, zero⟩

private theorem countPair_keyRegs {p : CountData} {s t : State}
    (left : CountState p s) (right : CountState p t) (sp : s.sp = t.sp) : KeyRegEq s t := by
  refine ⟨?_, sp⟩
  intro r hr
  simp only [keyRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact left.ready.r7.trans right.ready.r7.symm
  · exact left.ready.r8.trans right.ready.r8.symm
  · exact left.ready.r9.trans right.ready.r9.symm

private theorem countStep_fixed (p : CountData) :
    RelCT isa (fun s t => CountState p s ∧ CountState p t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.ParameterCandidate.halfCountStep
      (fun s t => CountAfter p s ∧ CountAfter p t ∧ s.sp = t.sp) := by
  intro s t trS trT u v h runS runT
  have leak := (halfCountStep_ct _ _ _ _ _ _ (countPair_keyRegs h.1 h.2.1 h.2.2) runS runT).1
  obtain ⟨_, u', execS, postS⟩ := countAfter_ok p s h.1
  obtain ⟨_, v', execT, postT⟩ := countAfter_ok p t h.2.1
  obtain ⟨_, rfl⟩ := Exec.det runS execS
  obtain ⟨_, rfl⟩ := Exec.det runT execT
  exact ⟨leak, postS, postT, (Exec.rdwr runS).2.2.trans (h.2.2.trans (Exec.rdwr runT).2.2.symm)⟩

private def CountLoopPair (remaining : Nat) (s t : State) : Prop :=
  ∃ p : CountData, p.number = remaining ∧ CountState p s ∧ CountState p t ∧ s.sp = t.sp

private theorem CountAfter.continue {p : CountData} {s : State}
    (h : CountAfter p s) (positive : 0 < p.number) (even : p.number % 2 = 0)
    (go : isa.eval .eq s = some true) : CountState ⟨p.math, p.number / 2, p.count + 1⟩ s := by
  have nextEven : p.number / 2 % 2 = 0 := by
    change some s.z = some true at go
    rw [h.zero] at go
    exact of_decide_eq_true (Option.some.inj go)
  have nextPositive : 0 < p.number / 2 := by omega
  exact ⟨h.workspace, h.ready, h.data, h.stack, h.separate, h.number, nextPositive, nextEven, h.saved⟩

theorem halfCountLoop_ct : RelCT isa (Two CountState)
    (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.halfCountStep .eq) (fun _ _ => True) := by
  have step : ∀ n, RelCT isa (CountLoopPair n) VG.Impl.Ffdh.Arm.ParameterCandidate.halfCountStep
      (fun u v => isa.eval .eq u = isa.eval .eq v ∧
        (isa.eval .eq u = some false → True) ∧
        (isa.eval .eq u = some true → ∃ m, m < n ∧ CountLoopPair m u v)) := by
    intro n s t trS trT u v h runS runT
    obtain ⟨p, remaining, left, right, sp⟩ := h
    obtain ⟨leak, postU, postV, spUV⟩ := countStep_fixed p _ _ _ _ _ _ ⟨left, right, sp⟩ runS runT
    refine ⟨leak, ?_, by intro _; trivial, ?_⟩
    · change some u.z = some v.z
      rw [postU.zero, postV.zero]
    · intro go
      have goV : isa.eval .eq v = some true := by change some v.z = some true; change some u.z = some true at go; rw [postV.zero, ← postU.zero]; exact go
      exact ⟨p.number / 2, by rw [← remaining]; exact Nat.div_lt_self left.positive (by decide),
        ⟨p.math, p.number / 2, p.count + 1⟩, rfl, postU.continue left.positive left.even go,
        postV.continue right.positive right.even goV, spUV⟩
  intro s t trS trT u v h runS runT
  obtain ⟨p, left, right, sp⟩ := h
  exact RelCT.loop CountLoopPair step p.number _ _ _ _ _ _ ⟨p, rfl, left, right, sp⟩ runS runT

end VG.Proof.Ffdh.Arm.ParameterCandidate
