module

public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Ffdh.Arm.Bounds
import VerifiedGarbage.Proof.Ffdh.Arm.InitValues
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Ffdh.Arm.Init
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Spec.Rsa.Contract

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
      lower, decide_true]) (fun _ => clear u restU (by omega)) (by intro h; cases h)
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
      have valid : 64 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 1024 := by omega
      simp only [keyInitPost, valid]
      refine ⟨result, ?_⟩
      rw [mem, keyInitValues_words, rest.gpr .r1 (by simp)]
    · refine WP.ite true (by simp only [eval, high, show (1025 : BitVec 16).toNat = 1025 from rfl,
        upper, decide_false, Bool.not_false]) (fun _ => clear v rest (by omega)) (by intro h; cases h)

end VG.Proof.Ffdh.Arm
