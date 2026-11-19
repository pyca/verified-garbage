module

public import VerifiedGarbage.Spec.Ffdh.GenerationContract
public import Init.Data.BitVec.BasicAux
public import VerifiedGarbage.Spec.Ffdh.Generation
import VerifiedGarbage.Proof.EntropyRequest
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyInitVerified
import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Spec.Ffdh.GenerationContract
public import Init.Data.List.Basic
public import VerifiedGarbage.Impl.Ffdh.Arm.Init
import VerifiedGarbage.Proof.Ffdh.Arm.Block
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Ffdh.Arm.InitValues
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! ### `Ffdh.Arm.ParameterInit`, which only this module used -/

section

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
      lower, decide_true]) (fun _ => clear u restU (by omega_using [lower])) (by intro h; cases h)
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
      have lowV : 512 ≤ (v.gpr .r1).toNat := by rw [rest.gpr .r1 (by simp)]; omega_using [lower]
      have highV : (v.gpr .r1).toNat ≤ 8192 := by rw [rest.gpr .r1 (by simp)]; omega_using [upper]
      have done := parameterGenerator_ok v (h.congr rest.wr)
        ((rest.gpr .r0 (by simp)).trans ptr) lowV highV
      rw [rest.gpr .r1 (by simp), rest.gpr .r2 (by simp)] at done
      exact done
    · exact WP.ite true (by simp only [eval, high, show (8193 : BitVec 16).toNat = 8193 from rfl,
        upper, decide_false, Bool.not_false]) (fun _ => clear v rest (by omega_using [upper])) (by intro h; cases h)

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.ParameterInitSpec`, which only this module used -/

section

/-! Relate the ARMv7 guard to the shared initialization specification. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG

theorem generatorNat (g : BitVec 32) (n : Nat) (hn : n < 2 ^ 32) :
    g.toNat = n ↔ g = BitVec.ofNat 32 n := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, h]
  · intro h
    rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem parameterInit_spec (bits gen : BitVec 32) :
    Spec.Ffdh.parameterInit bits.toNat gen.toNat =
      if 512 ≤ bits.toNat ∧ bits.toNat ≤ 8192 ∧ (gen = 2 ∨ gen = 5) then
        some [Spec.Ffdh.parameterAttempts bits.toNat, (bits.toNat + 7) / 8,
          Spec.Ffdh.parameterEntropy bits.toNat]
      else none := by
  simp only [Spec.Ffdh.parameterInit, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    beq_iff_eq, generatorNat gen 2 (by decide), generatorNat gen 5 (by decide), and_assoc]
  rfl

end VG.Proof.Ffdh.Arm

end

end


/-! Native parameter initialization implements the shared FFDH ABI. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Impl.Ffdh.Arm VG.Proof.Bignum.Arm

def parameterPost (s t : State) : Prop :=
  match Spec.Ffdh.parameterInit (s.gpr .r1).toNat (s.gpr .r2).toNat with
  | none => (t.gpr .r0).toNat = 0 ∧ Spec.Rsa.wordsAt t.mem (State.addr (s.gpr .r0)) 4 = List.replicate 4 0
  | some values => (t.gpr .r0).toNat = 1 ∧ ∃ first,
      Spec.Rsa.wordsAt t.mem (State.addr (s.gpr .r0)) 4 = (values ++ [first]).map (BitVec.ofNat 64) ∧
      Spec.Entropy.RequestValid (Spec.Ffdh.parameterEntropy (s.gpr .r1).toNat) 0 first

def parameterPub (s t : State) : Prop :=
  s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2

def parameterContract : Contract isa where
  pre := keyPre
  post := parameterPost
  pub := parameterPub

theorem parameter_correct (s : State) (h : keyPre s) :
    ∃ tr t, Exec isa Generation.init s tr t ∧ abiPreserved s t ∧ parameterPost s t := by
  have ws : Workspace s (s.gpr .r0) 128 := ⟨h.2.2, by rw [h.2.1]; simp⟩
  have run := withRest_all [.r0, .r2, .r3, .r12] (parameterInit_ok s ws rfl) (by rfl) (by rfl)
  obtain ⟨tr, t, exec, post, rest⟩ := run
  refine ⟨tr, t, exec, ⟨?_, rest.sp⟩, ?_⟩
  · intro r hr
    exact rest.gpr r (by revert r; decide)
  · unfold parameterPost
    rw [parameterInit_spec]
    by_cases valid : 512 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 8192 ∧ (s.gpr .r2 = 2 ∨ s.gpr .r2 = 5)
    · simp only [parameterInitPost, valid] at post
      simp only [valid]
      exact ⟨by rw [post.1]; rfl, _, post.2, Proof.Ffdh.first_valid valid.1⟩
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
