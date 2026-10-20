module

import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.KeyInit
public import VerifiedGarbage.Impl.Ffdh.Arm.Init
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Spec.Ffdh.Generation
import VerifiedGarbage.Proof.Ffdh.Arm.Bounds
import VerifiedGarbage.Proof.Ffdh.Arm.InitValues
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterInitStores
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Parameter-controller guards and initialization are native on ARMv7. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Impl.Ffdh.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

def parameterValues (bits : Nat) : List (BitVec 64) :=
  [BitVec.ofNat 64 (Spec.Ffdh.parameterAttempts bits), BitVec.ofNat 64 ((bits + 7) / 8),
    BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy bits), BitVec.ofNat 64 (512 * ((bits + 7) / 8))]

def parameterInitPost (B : Addr) (bits gen : BitVec 32) (t : State) : Prop :=
  if 512 ≤ bits.toNat ∧ bits.toNat ≤ 8192 ∧ (gen = 2 ∨ gen = 5) then
    t.gpr .r0 = 1 ∧ Spec.Rsa.wordsAt t.mem B 4 = parameterValues bits.toNat
  else t.gpr .r0 = 0 ∧ Spec.Rsa.wordsAt t.mem B 4 = List.replicate 4 0

theorem generatorTest_ok (s : State) (g : BitVec 32) (enc : encodable g = true) :
    WP isa (.block [.cmp .r2 (.imm g)]) s fun t =>
      (t.z = decide (s.gpr .r2 = g) ∧ t.mem = s.mem) ∧ Rest [] s t := by
  refine withRest [] ?_ (by intro r _ i hi; simp only [instrs, List.mem_singleton] at hi; subst i; rfl) (by rfl)
  ffrun [enc]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro hz
    calc
      s.gpr .r2 = (s.gpr .r2 - g) + g := (BitVec.sub_add_cancel _ _).symm
      _ = 0#32 + g := congrArg (fun x : BitVec 32 => x + g) hz
      _ = g := BitVec.zero_add _
  · intro hz
    rw [hz, BitVec.sub_self]
    rfl

theorem parameterGenerator_ok (s : State) {base : BitVec 32}
    (h : Workspace s base 128) (ptr : s.gpr .r0 = base)
    (lo : 512 ≤ (s.gpr .r1).toNat) (hi : (s.gpr .r1).toNat ≤ 8192) :
    WP isa Generation.generator s (parameterInitPost (State.addr base) (s.gpr .r1) (s.gpr .r2)) := by
  have accept (u : State) (rest : Rest [] s u) (valid : s.gpr .r2 = 2 ∨ s.gpr .r2 = 5) :
      WP isa Generation.initializeState u (parameterInitPost (State.addr base) (s.gpr .r1) (s.gpr .r2)) := by
    refine WP.mono (parameterInitializeState_ok u (h.congr rest.wr)
      ((rest.gpr .r0 (by simp)).trans ptr)) ?_
    rintro t ⟨result, mem⟩
    have good : 512 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 8192 ∧ (s.gpr .r2 = 2 ∨ s.gpr .r2 = 5) := ⟨lo, hi, valid⟩
    simp only [parameterInitPost, good]
    refine ⟨result, ?_⟩
    rw [mem, rest.gpr .r1 (by simp), parameterInitValues_words _ _ _ hi]
    rfl
  have clear (u : State) (rest : Rest [] s u) (invalid : ¬ (s.gpr .r2 = 2 ∨ s.gpr .r2 = 5)) :
      WP isa clearController u (parameterInitPost (State.addr base) (s.gpr .r1) (s.gpr .r2)) := by
    refine WP.mono (clearController_ok u (h.congr rest.wr)
      ((rest.gpr .r0 (by simp)).trans ptr)) ?_
    rintro t ⟨result, mem⟩
    simp only [parameterInitPost, show ¬ (512 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 8192 ∧
      (s.gpr .r2 = 2 ∨ s.gpr .r2 = 5)) by intro hh; exact invalid hh.2.2, ite_false]
    refine ⟨result, ?_⟩
    rw [mem, controlMem_words]
    rfl
  rw [Generation.generator, WP.seq_iff]
  refine WP.mono (generatorTest_ok s 2 (by decide)) ?_
  rintro u ⟨⟨two, _⟩, restU⟩
  by_cases g2 : s.gpr .r2 = 2
  · exact WP.ite true (by simp only [eval, two, g2, decide_true])
      (fun _ => accept u restU (.inl g2)) (by intro h; cases h)
  · refine WP.ite false (by simp only [eval, two, g2, decide_false])
      (by intro h; cases h) (fun _ => ?_)
    rw [WP.seq_iff]
    refine WP.mono (generatorTest_ok u 5 (by decide)) ?_
    rintro v ⟨⟨five, _⟩, restV⟩
    rw [restU.gpr .r2 (by simp)] at five
    by_cases g5 : s.gpr .r2 = 5
    · exact WP.ite true (by simp only [eval, five, g5, decide_true])
        (fun _ => accept v (restU.trans restV) (.inr g5)) (by intro h; cases h)
    · exact WP.ite false (by simp only [eval, five, g5, decide_false])
        (by intro h; cases h) (fun _ => clear v (restU.trans restV) (by simp only [not_or]; exact ⟨g2, g5⟩))

theorem parameterInit_ok (s : State) {base : BitVec 32}
    (h : Workspace s base 128) (ptr : s.gpr .r0 = base) :
    WP isa Generation.init s (parameterInitPost (State.addr base) (s.gpr .r1) (s.gpr .r2)) := by
  have clear (u : State) (rest : Rest [.r3, .r12] s u)
      (invalid : ¬ (512 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 8192)) :
      WP isa clearController u (parameterInitPost (State.addr base) (s.gpr .r1) (s.gpr .r2)) := by
    refine WP.mono (clearController_ok u (h.congr rest.wr)
      ((rest.gpr .r0 (by simp)).trans ptr)) ?_
    rintro t ⟨result, mem⟩
    have bad : ¬ (512 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 8192 ∧
        (s.gpr .r2 = 2 ∨ s.gpr .r2 = 5)) := by intro hh; exact invalid ⟨hh.1, hh.2.1⟩
    simp only [parameterInitPost, bad, ite_false]
    refine ⟨result, ?_⟩
    rw [mem, controlMem_words]
    rfl
  rw [Generation.init, boundedController, WP.seq_iff]
  refine WP.mono (boundTest_ok s 512) ?_
  rintro u ⟨⟨low, _⟩, restU⟩
  by_cases lower : (s.gpr .r1).toNat < 512
  · exact WP.ite true (by simp only [eval, low, show (512 : BitVec 16).toNat = 512 from rfl,
      lower, decide_true]) (fun _ => clear u restU (by omega)) (by intro h; cases h)
  · refine WP.ite false (by simp only [eval, low, show (512 : BitVec 16).toNat = 512 from rfl,
      lower, decide_false]) (by intro h; cases h) (fun _ => ?_)
    rw [WP.seq_iff]
    refine WP.mono (boundTest_ok u 8193) ?_
    rintro v ⟨⟨high, _⟩, restV⟩
    have rest := restU.trans restV
    rw [restU.gpr .r1 (by simp)] at high
    by_cases upper : (s.gpr .r1).toNat < 8193
    · refine WP.ite false (by simp only [eval, high, show (8193 : BitVec 16).toNat = 8193 from rfl,
        upper, decide_true, Bool.not_true]) (by intro h; cases h) (fun _ => ?_)
      have lowV : 512 ≤ (v.gpr .r1).toNat := by rw [rest.gpr .r1 (by simp)]; omega
      have highV : (v.gpr .r1).toNat ≤ 8192 := by rw [rest.gpr .r1 (by simp)]; omega
      have done := parameterGenerator_ok v (h.congr rest.wr)
        ((rest.gpr .r0 (by simp)).trans ptr) lowV highV
      rw [rest.gpr .r1 (by simp), rest.gpr .r2 (by simp)] at done
      exact done
    · exact WP.ite true (by simp only [eval, high, show (8193 : BitVec 16).toNat = 8193 from rfl,
        upper, decide_false, Bool.not_false]) (fun _ => clear v rest (by omega)) (by intro h; cases h)

end VG.Proof.Ffdh.Arm
