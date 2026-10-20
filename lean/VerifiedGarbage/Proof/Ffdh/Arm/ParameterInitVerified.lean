module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterInitSpec
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.InitCT
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyInitVerified
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Inline
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Spec.Ffdh.GenerationContract
public import Init.Data.BitVec.BasicAux
public import Init.Data.List.Basic
public import VerifiedGarbage.Impl.Ffdh.Arm.Init
public import VerifiedGarbage.Spec.Ffdh.GenerationContract
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterInit

/-! Native parameter initialization implements the shared FFDH ABI. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Impl.Ffdh.Arm VG.Proof.Bignum.Arm

def parameterPost (s t : State) : Prop :=
  match Spec.Ffdh.parameterInit (s.gpr .r1).toNat (s.gpr .r2).toNat with
  | none => (t.gpr .r0).toNat = 0 ∧ Spec.Rsa.wordsAt t.mem (State.addr (s.gpr .r0)) 4 = List.replicate 4 0
  | some values => (t.gpr .r0).toNat = 1 ∧
      Spec.Rsa.wordsAt t.mem (State.addr (s.gpr .r0)) 4 = values.map (BitVec.ofNat 64)

def parameterPub (s t : State) : Prop :=
  s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2

def parameterContract : Contract isa where
  pre := keyPre
  post := parameterPost
  pub := parameterPub

theorem parameter_correct (s : State) (h : keyPre s) :
    ∃ tr t, Exec isa Generation.init s tr t ∧ abiPreserved s t ∧ parameterPost s t := by
  have ws : Workspace s (s.gpr .r0) 128 := ⟨h.2.2, by rw [h.2.1]; simp⟩
  have run := withRest [.r0, .r2, .r3, .r12] (parameterInit_ok s ws rfl) (by
    intro r hr i hi
    have checked : (instrs Generation.init).all (fun i => !(clobbers i r)) = true := by
      cases r <;> try decide +kernel
      all_goals exact False.elim (hr (by decide))
    have flag := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  obtain ⟨tr, t, exec, post, rest⟩ := run
  refine ⟨tr, t, exec, ⟨?_, rest.sp⟩, ?_⟩
  · intro r hr
    exact rest.gpr r (by revert r; decide)
  · unfold parameterPost
    rw [parameterInit_spec]
    by_cases valid : 512 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 8192 ∧ (s.gpr .r2 = 2 ∨ s.gpr .r2 = 5)
    · simp only [parameterInitPost, valid] at post
      simp only [valid]
      exact ⟨by rw [post.1]; rfl, post.2⟩
    · simp only [parameterInitPost, valid, ite_false] at post
      simp only [valid, ite_false]
      exact ⟨by rw [post.1]; rfl, post.2⟩

private def parameterSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 512 | .r2 => 2 | _ => 0
  sp := 0x3000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 128⟩]

theorem parameterInit_verified : Verified target Generation.init (Spec.Ffdh.parameterInitContract abi) := by
  refine Verified.of_correct (k := parameterContract) parameter_correct ?_ ?_
  · intro s t tr1 tr2 u v _ _ pub e1 e2
    exact (parameterInit_ct s t tr1 tr2 u v (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [pub.2.1, pub.2.2.1, pub.2.2.2]) e1 e2).1
  · refine {
      pre := by sig_implies_pre [Spec.Ffdh.parameterInitContract, Spec.Ffdh.parameterInitSig,
        parameterContract, keyPre, abi, argRegs, reduceClassify, Loc.val, State.addr]
      post := ?_
      pub := by sig_implies_pub [Spec.Ffdh.parameterInitContract, Spec.Ffdh.parameterInitSig,
        parameterContract, parameterPub, abi, argRegs, reduceClassify, Loc.val, State.addr]
      sat := by sig_implies_sat [Spec.Ffdh.parameterInitContract, Spec.Ffdh.parameterInitSig,
        abi, argRegs, reduceClassify, Loc.val, State.addr] [parameterSat] using parameterSat }
    intro s t _ post
    sig_post [Spec.Ffdh.parameterInitContract, Spec.Ffdh.parameterInitSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
    rw [BitVec.setWidth_append_eq_right]
    exact post

end VG.Proof.Ffdh.Arm
