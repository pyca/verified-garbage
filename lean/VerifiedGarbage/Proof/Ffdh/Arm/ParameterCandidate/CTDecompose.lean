module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCountLoop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCountStep
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CountInit
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTMontOne
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyReady

/-! Decomposing the public modulus minus one has a public trace. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Keys (num)
open VG.Proof.Ffdh.Arm.KeySearch

structure DecomposeData where
  math : MontMathData
  modulus : Nat

structure DecomposeStart (p : DecomposeData) (s : State) : Prop where
  workspace : Workspace s p.math.base (8 * p.math.capacity)
  ready : KeyReady p.math.base p.math.capacity p.math.words s
  data : MontData p.math.base p.math.capacity p.math.words s.mem
  stack : Workspace s s.sp 72
  separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.math.base, 8 * p.math.capacity⟩
  number : num s.mem (p.math.base + 96#32) (2 * p.math.words + 2) 0 = p.modulus
  large : 1 < p.modulus
  odd : p.modulus % 2 = 1

private def decomposeCount (p : DecomposeData) : CountData := ⟨p.math, p.modulus - 1, 0⟩

private theorem decomposeInit_ok (p : DecomposeData) (s : State) (h : DecomposeStart p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.expCountInit s (CountState (decomposeCount p)) := by
  refine WP.mono (expCountInit_ok h.workspace h.ready h.data h.stack h.separate h.number h.large h.odd) ?_
  intro t ht
  exact ⟨ht.workspace, ht.ready, ht.data, ht.stack, ht.separate, ht.number, ht.positive, ht.even, ht.saved⟩

private theorem decomposeInit_ct : RelCT isa (Two DecomposeStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.expCountInit (fun _ _ => True) := by
  refine expCountInit_ct.mono ?_ (fun _ _ _ => trivial)
  rintro s t ⟨p, left, right, sp⟩
  refine ⟨?_, sp⟩
  intro r hr
  simp only [keyRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact left.ready.r7.trans right.ready.r7.symm
  · exact left.ready.r8.trans right.ready.r8.symm
  · exact left.ready.r9.trans right.ready.r9.symm

theorem expDecompose_ct : RelCT isa (Two DecomposeStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.expDecompose (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.expDecompose
  exact RelCT.seq (two_post decomposeInit_ct decomposeInit_ok)
    (halfCountLoop_ct.mono
      (fun _ _ ⟨p, left, right, sp⟩ => ⟨decomposeCount p, left, right, sp⟩)
      (fun _ _ h => h))

end VG.Proof.Ffdh.Arm.ParameterCandidate
