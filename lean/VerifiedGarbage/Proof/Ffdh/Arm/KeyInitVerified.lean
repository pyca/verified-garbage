module

import VerifiedGarbage.Proof.Ffdh.Arm.Block
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
public import Init.Data.BitVec.BasicAux
public import Init.Data.List.Basic
public import VerifiedGarbage.Impl.Ffdh.Arm.Init
public import VerifiedGarbage.Spec.Ffdh.KeyGeneration
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Ffdh.Arm.Init
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Ffdh.Arm.InitValues
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! ### `Ffdh.Arm.KeyInit`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.Bounds`, which this module and modules that import it used -/

section

/-! Unsigned public size guards for the native controller entry points. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Impl.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)

theorem boundTest_ok (s : State) (b : BitVec 16) :
    WP isa (.block (boundTest b)) s fun t =>
      (t.z = decide ((s.gpr .r1).toNat < b.toNat) ∧ t.mem = s.mem) ∧ Rest [.r3, .r12] s t := by
  refine withRest_all [.r3, .r12] ?_ (by rfl) (by rfl)
  have bw : b.toNat < 2 ^ 32 := by have := b.isLt; omega_using []
  have hto : (b.setWidth 32).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt bw]
  unfold boundTest
  ffrun [BitVec.add_zero, BitVec.zero_add, hto]
  by_cases h : b.toNat ≤ (s.gpr .r1).toNat
  · simp [h, show ¬ (s.gpr .r1).toNat < b.toNat by omega_using [h]]
  · simp [h, show (s.gpr .r1).toNat < b.toNat by omega_using [h]]

end VG.Proof.Ffdh.Arm

end

end

/-! ARMv7 key-generation controller initialization, including invalid widths. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Impl.Ffdh.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

def keyInitPost (B : Addr) (k : BitVec 32) (t : State) : Prop :=
  if 64 ≤ k.toNat ∧ k.toNat ≤ 1024 then
    t.gpr .r0 = 1 ∧ Spec.Rsa.wordsAt t.mem B 4 = [128, 128, BitVec.ofNat 64 k.toNat, BitVec.ofNat 64 k.toNat]
  else t.gpr .r0 = 0 ∧ Spec.Rsa.wordsAt t.mem B 4 = List.replicate 4 0

theorem keyInit_ok (s : State) {base : BitVec 32}
    (h : Workspace s base 128) (ptr : s.gpr .r0 = base) :
    WP isa KeyGeneration.init s (keyInitPost (State.addr base) (s.gpr .r1)) := by
  have clear (u : State) (rest : Rest [.r3, .r12] s u)
      (invalid : ¬ (64 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 1024)) :
      WP isa clearController u (keyInitPost (State.addr base) (s.gpr .r1)) := by
    refine WP.mono (clearController_ok u (h.congr rest.wr)
      ((rest.gpr .r0 (by simp)).trans ptr)) ?_
    rintro t ⟨result, mem⟩
    simp only [keyInitPost, invalid, ite_false]
    refine ⟨result, ?_⟩
    rw [mem, controlMem_words]
    rfl
  rw [KeyGeneration.init, boundedController, WP.seq_iff]
  refine WP.mono (boundTest_ok s 64) ?_
  rintro u ⟨⟨low, _⟩, restU⟩
  by_cases lower : (s.gpr .r1).toNat < 64
  · refine WP.ite true (by simp only [eval, low, show (64 : BitVec 16).toNat = 64 from rfl,
      lower, decide_true]) (fun _ => clear u restU (by omega_using [lower])) (by intro h; cases h)
  · refine WP.ite false (by simp only [eval, low, show (64 : BitVec 16).toNat = 64 from rfl,
      lower, decide_false]) (by intro h; cases h) (fun _ => ?_)
    rw [WP.seq_iff]
    refine WP.mono (boundTest_ok u 1025) ?_
    rintro v ⟨⟨high, _⟩, restV⟩
    have rest := restU.trans restV
    have count : u.gpr .r1 = s.gpr .r1 := restU.gpr .r1 (by simp)
    rw [count] at high
    by_cases upper : (s.gpr .r1).toNat < 1025
    · refine WP.ite false (by simp only [eval, high, show (1025 : BitVec 16).toNat = 1025 from rfl,
        upper, decide_true, Bool.not_true]) (by intro h; cases h) (fun _ => ?_)
      refine WP.mono (keyInitializeState_ok v (h.congr rest.wr)
        ((rest.gpr .r0 (by simp)).trans ptr)) ?_
      rintro t ⟨result, mem⟩
      have valid : 64 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 1024 := by omega_using [lower, upper]
      simp only [keyInitPost, valid]
      refine ⟨result, ?_⟩
      rw [mem, keyInitValues_words, rest.gpr .r1 (by simp)]
    · refine WP.ite true (by simp only [eval, high, show (1025 : BitVec 16).toNat = 1025 from rfl,
        upper, decide_false, Bool.not_false]) (fun _ => clear v rest (by omega_using [upper])) (by intro h; cases h)

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.InitCT`, which this module and modules that import it used -/

section

/-! Controller initialization depends only on its public arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Impl.Ffdh.Arm

theorem keyInit_ct : RelCT isa (fun s t => ∀ r ∈ [.r0, .r1], s.gpr r = t.gpr r)
    KeyGeneration.init (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r1]) _ (by taint_decide)
  intro s t h
  exact Taint.agree_ofRegs h

theorem parameterInit_ct : RelCT isa (fun s t => ∀ r ∈ [.r0, .r1, .r2], s.gpr r = t.gpr r)
    Generation.init (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r1, .r2]) _ (by taint_decide)
  intro s t h
  exact Taint.agree_ofRegs h

end VG.Proof.Ffdh.Arm

end

end

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
  have run := withRest_all [.r0, .r3, .r12] (keyInit_ok s ws rfl) (by rfl) (by rfl)
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
