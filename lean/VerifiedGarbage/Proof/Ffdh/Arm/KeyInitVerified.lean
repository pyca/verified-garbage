module

import VerifiedGarbage.Proof.Ffdh.Arm.Block
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Ffdh.Arm.KeyInit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
import VerifiedGarbage.Proof.Ffdh.Arm.InitCT
import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
public import Init.Data.BitVec.BasicAux
public import Init.Data.List.Basic
public import VerifiedGarbage.Impl.Ffdh.Arm.Init
public import VerifiedGarbage.Spec.Ffdh.KeyGeneration

/-! The native key initializer implements the shared public FFDH ABI. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Impl.Ffdh.Arm VG.Proof.Bignum.Arm

def keyPre (s : State) : Prop := s.rd = [] ∧
  s.wr = [⟨State.addr (s.gpr .r0), 128⟩] ∧ (s.gpr .r0).toNat + 128 ≤ 2 ^ 32

def keyPost (s t : State) : Prop :=
  match Spec.Ffdh.keyInit (s.gpr .r1).toNat with
  | none => (t.gpr .r0).toNat = 0 ∧ Spec.Rsa.wordsAt t.mem (State.addr (s.gpr .r0)) 4 = List.replicate 4 0
  | some values => (t.gpr .r0).toNat = 1 ∧
      Spec.Rsa.wordsAt t.mem (State.addr (s.gpr .r0)) 4 = values.map (BitVec.ofNat 64)

def keyPub (s t : State) : Prop := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1

def keyContract : Contract isa where
  pre := keyPre
  post := keyPost
  pub := keyPub

theorem keyInit_correct (s : State) (h : keyPre s) :
    ∃ tr t, Exec isa KeyGeneration.init s tr t ∧ abiPreserved s t ∧ keyPost s t := by
  have ws : Workspace s (s.gpr .r0) 128 := ⟨h.2.2, by rw [h.2.1]; simp⟩
  have run := withRest [.r0, .r3, .r12] (keyInit_ok s ws rfl) (by
    intro r hr i hi
    have checked : (instrs KeyGeneration.init).all (fun i => !(clobbers i r)) = true := by
      cases r <;> try decide +kernel
      all_goals exact False.elim (hr (by decide))
    have flag := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  obtain ⟨tr, t, exec, post, rest⟩ := run
  refine ⟨tr, t, exec, ⟨?_, rest.sp⟩, ?_⟩
  · intro r hr
    exact rest.gpr r (by revert r; decide)
  · by_cases valid : 64 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 1024
    · simp only [keyInitPost, valid] at post
      have accepted : Spec.Ffdh.keyInit (s.gpr .r1).toNat = some [128, 128, (s.gpr .r1).toNat, (s.gpr .r1).toNat] := by
        simp only [Spec.Ffdh.keyInit, valid.1, valid.2, decide_true, Bool.true_and, ite_true]
      simp only [keyPost, accepted, List.map_cons, List.map_nil]
      exact ⟨by rw [post.1]; rfl, post.2⟩
    · simp only [keyInitPost, valid, ite_false] at post
      have rejected : Spec.Ffdh.keyInit (s.gpr .r1).toNat = none := by
        simp only [Spec.Ffdh.keyInit]
        exact ite_eq_right (by simpa only [Bool.and_eq_true, decide_eq_true_eq] using valid)
      simp only [keyPost, rejected]
      exact ⟨by rw [post.1]; rfl, post.2⟩

private def keySat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 64 | _ => 0
  sp := 0x3000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 128⟩]

theorem keyInit_verified : Verified target KeyGeneration.init (Spec.Ffdh.keyInitContract abi) := by
  refine Verified.of_correct (k := keyContract) keyInit_correct ?_ ?_
  · intro s t tr1 tr2 u v _ _ pub e1 e2
    exact (keyInit_ct s t tr1 tr2 u v (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [pub.2.1, pub.2.2]) e1 e2).1
  · refine {
      pre := by sig_implies_pre [Spec.Ffdh.keyInitContract, Spec.Ffdh.keyInitSig,
        keyContract, keyPre, abi, argRegs, reduceClassify, Loc.val, State.addr]
      post := ?_
      pub := by sig_implies_pub [Spec.Ffdh.keyInitContract, Spec.Ffdh.keyInitSig,
        keyContract, keyPub, abi, argRegs, reduceClassify, Loc.val, State.addr]
      sat := by sig_implies_sat [Spec.Ffdh.keyInitContract, Spec.Ffdh.keyInitSig,
        abi, argRegs, reduceClassify, Loc.val, State.addr] [keySat] using keySat }
    intro s t _ post
    sig_post [Spec.Ffdh.keyInitContract, Spec.Ffdh.keyInitSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
    rw [BitVec.setWidth_append_eq_right]
    exact post

end VG.Proof.Ffdh.Arm
