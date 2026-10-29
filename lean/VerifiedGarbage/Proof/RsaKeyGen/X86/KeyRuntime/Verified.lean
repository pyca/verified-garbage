module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyABI
public import VerifiedGarbage.Proof.Framework.Contract

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySatisfiable
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Framed
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyFrameResult
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEncodedResult
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallValid
import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallSizes
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.TCB.X86.Target
import Init.Data.BitVec.Basic
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InputTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.OutputTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.StartPair
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.CoreReadonlyTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Derive
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.StackRange
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyScratchFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateParameters
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyBodyTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ContextWorkspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Safety
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyFrameTiming
import Init.Core
import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEnvironment
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPublicLeak
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallArgs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallSamples
/-! # Shared native key generation satisfies the existing API and timing contracts -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/FrameResult.lean`, which only this module imported.
section

/-! # The callable key operation uses the caller's original encoded inputs -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.RsaKeyGen.X86.Key (contract call_layout call_valid call_separation call_sizes
  callEnvironment EncodedResult BodyOutcome reservedRegion pushed_bytes)

theorem framed_result_ok {s : State} (h : contract.pre s) :
    WP isa VG.Impl.RsaKeyGen.X86.KeyRuntime.code s fun t =>
      abiPreserved s t ∧ EncodedResult (callEnvironment s) s.mem t := by
  have v := call_valid h
  have A := call_layout h
  have D := call_separation h
  have Z := call_sizes h
  have eBytes : Spec.Rsa.bytesAt (Compact.entered s).mem (callEnvironment s).exponentRegion.base
      (callEnvironment s).exponentRegion.len =
      Spec.Rsa.bytesAt s.mem (callEnvironment s).exponentRegion.base (callEnvironment s).exponentRegion.len :=
    pushed_bytes h D.stackExponent (by change (arg s 15).toNat < 2 ^ 64; have := (arg s 15).isLt; omega)
  have primeBytes (i : Nat) (hi : i < 7) :
      Spec.Rsa.bytesAt (Compact.entered s).mem ((callEnvironment s).outputRegion i).base ((callEnvironment s).outputRegion i).len =
        Spec.Rsa.bytesAt s.mem ((callEnvironment s).outputRegion i).base ((callEnvironment s).outputRegion i).len := by
    rw [Z.outputRegion hi]
    apply pushed_bytes h (D.stackOutput i hi)
    change (arg s (2 * i + 1)).toNat < 2 ^ 64
    have := (arg s (2 * i + 1)).isLt
    omega
  refine WP.mono (framed_ok h) fun t ⟨preserved, R⟩ => ?_
  unfold BodyOutcome at R
  rw [eBytes, primeBytes 2 (by decide), primeBytes 3 (by decide)] at R
  exact ⟨preserved, BodyOutcome.encoded v R⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/Correct.lean`, which only this module imported.
section

/-! # Complete native key generation satisfies the shared encoded cdecl contract -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86
open VG.Proof.RsaKeyGen.X86.Key (contract call_sizes keyStack EncodedResult encodedOperation
  callEnvironment Environment)

theorem correct (s : State) (h : contract.pre s) :
    ∃ trace t, Exec isa VG.Impl.RsaKeyGen.X86.KeyRuntime.code s trace t ∧
      abiPreserved s t ∧ contract.post s t := by
  have Z := call_sizes h
  obtain ⟨trace, t, run, preserved, R⟩ := framed_result_ok h
  refine ⟨trace, t, run, preserved, ?_⟩
  sig_post [contract, keyStack, Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig,
    abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  unfold EncodedResult encodedOperation at R
  simp only [callEnvironment, Environment.exponentRegion, Environment.outputRegion, Environment.outputLength,
    List.range_succ, List.range_zero, List.map_nil, List.map_cons, List.nil_append, List.cons_append,
    Nat.reduceMul, Nat.reduceLT, ite_true, ite_false] at R
  rw [← Z.modulus] at R
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at R
  generalize result : Spec.RsaKeyGen.keyOp (arg s 5).toNat
    (Spec.Rsa.bytesAt s.mem ((arg s 14).setWidth 64) (arg s 15).toNat)
    (Spec.Rsa.bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat)
    (Spec.Rsa.bytesAt s.mem ((arg s 6).setWidth 64) (arg s 5).toNat) = value at R ⊢
  cases value with
  | inl answer => cases answer <;> exact R
  | inr u => cases u; exact R

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/FrontTiming.lean`, which only this module imported.
section

/-! # Shared derivation and the outputs publish only the specified retry bit -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (Environment stage_scratch_frame deriveArrays prepareArrays keyPartArrays)
open VG.Proof.RsaKeyGen.X86.KeyArgs (argsRegion)

theorem deriveArgs_trace (E : Environment) (sp : BitVec 32) (e p q p' q' : Nat)
    (apart : ∀ i < 7, (argsRegion sp).Disjoint (E.outputRegion i))
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p' q' = .inr ())) :
    RelCT isa (RuntimeImported E sp e p q p' q') deriveLoaded (OutputStart E sp) := by
  intro s t tr ur u v P A C
  obtain ⟨trace, out⟩ := deriveOutput_trace E sp e p q p' q' release _ _ _ _ _ _ P A C
  have valid := P.imported.inputs.left.valid
  have widths := valid.widths
  have apart' : ∀ i < 7, (argsRegion sp).Disjoint (E.outputs.region i) := fun i hi => by
    rw [valid.outputRegion hi]
    exact apart i hi
  have frame {a b : State} {tr' : List Leak} (H : Ws a E.base E.size E.n 32)
      (L : VG.Proof.RsaKeyGen.X86.Key.CoreStart E.base E.size E.n E.k e p q a ∨
        VG.Proof.RsaKeyGen.X86.Key.CoreStart E.base E.size E.n E.k e p' q' a)
      (X : Exec isa deriveLoaded a tr' b) :
      ∃ rs : List Reg, Keeps rs a b ∧ .edi ∉ rs ∧ .esp ∉ rs ∧
        Frame [E.workspaceRegion, below (a.gpr .esp) 52] a.mem b.mem := by
    have go {e₁ p₁ q₁ : Nat} (L : VG.Proof.RsaKeyGen.X86.Key.CoreStart E.base E.size E.n E.k e₁ p₁ q₁ a) :
        ∃ rs : List Reg, Keeps rs a b ∧ .edi ∉ rs ∧ .esp ∉ rs ∧
          Frame [E.workspaceRegion, below (a.gpr .esp) 52] a.mem b.mem := by
      obtain ⟨_, O, _, K⟩ := wp_result (deriveLoaded_ok H widths.2.2.1 widths.2.2.2.1 widths.2.2.2.2.1
        widths.1 widths.2.1 L.pBound L.qBound L.zero L.one (L.loaded.trans L.exponent.symm)) X
      exact ⟨_, K, by decide, by decide, O.toFrame fun _ _ O =>
        stage_scratch_frame H.old (by simp [deriveArrays, prepareArrays, keyPartArrays]; decide) O⟩
    rcases L with L | L <;> exact go L
  obtain ⟨rs, KS, ediS, espS, FS⟩ := frame P.left (Or.inl P.imported.left) A
  obtain ⟨rt, KT, ediT, espT, FT⟩ := frame P.right (Or.inr P.imported.right) C
  rw [P.leftArgs.sp] at FS
  rw [P.rightArgs.sp] at FT
  exact ⟨trace, out, ⟨valid, P.leftArgs.keepBelow KS FS ediS espS, apart'⟩,
    ⟨valid, P.rightArgs.keepBelow KT FT ediT espT, apart'⟩⟩

theorem front_trace (E : Environment) (sp : BitVec 32) (e p q p' q' : Nat)
    (apart : ∀ i < 7, (argsRegion sp).Disjoint (E.outputRegion i))
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p' q' = .inr ())) :
    RelCT isa (RuntimeStart E sp e p q p' q') front
      (VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint true)) := by
  unfold front
  exact RelCT.seq (runtime_input_trace E sp e p q p' q')
    (RelCT.seq (deriveArgs_trace E sp e p q p' q' apart release) (writeOutputs_trace E sp))

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/BodyTiming.lean`, which only this module imported.
section

/-! # The shared body retains exactly the declared exponent and retry observations -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.RsaKeyGen.X86.Key (Environment BodyPair)

theorem enterInput_trace (E : Environment) (valid : E.Valid) (sp : BitVec 32) (e p q p' q' : Nat) :
    RelCT isa (BodyPair E sp e p q p' q') VG.Impl.RsaKeyGen.X86.Key.enter
      (RuntimeStart E sp e p q p' q') := by
  intro s t tr ur u v P A C
  obtain ⟨trace, start⟩ := VG.Proof.RsaKeyGen.X86.Key.enterInput_trace E valid sp e p q p' q'
    _ _ _ _ _ _ P A C
  obtain ⟨CS, _, _, _⟩ := wp_result (VG.Proof.RsaKeyGen.X86.KeyArgs.enter_ok P.left.arguments) A
  obtain ⟨CT, _, _, _⟩ := wp_result (VG.Proof.RsaKeyGen.X86.KeyArgs.enter_ok P.right.arguments) C
  exact ⟨trace, start, context_workspace valid CS start.inputs.left.ws,
    context_workspace valid CT start.inputs.right.ws, CS, CT⟩

theorem body_trace (E : Environment) (valid : E.Valid) (sp : BitVec 32) (e p q p' q' : Nat)
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p' q' = .inr ())) :
    RelCT isa (BodyPair E sp e p q p' q') VG.Impl.RsaKeyGen.X86.KeyRuntime.body
      (VG.X86.Taint.Agree (τr [.esp])) := by
  intro s t tr ur u v P A C
  have raw := RelCT.seq (enterInput_trace E valid sp e p q p' q')
    (front_trace E sp e p q p' q' P.left.argsOutput release)
  refine ⟨(raw _ _ _ _ _ _ P A C).1, agree_regs ?_⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  rw [Exec.gpr body_noSp A, Exec.gpr body_noSp C]
  exact P.left.arguments.sp.trans P.right.arguments.sp.symm

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/FrameTiming.lean`, which only this module imported.
section

/-! # The outer native key frame preserves trace equivalence -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.RsaKeyGen.X86.Key (Environment FramedPair)

theorem framed_trace (E : Environment) (v : E.Valid) (sp : BitVec 32) (e p q p' q' : Nat)
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p' q' = .inr ())) :
    RelCT isa (FramedPair E sp e p q p' q') VG.Impl.RsaKeyGen.X86.KeyRuntime.code (fun _ _ => True) := by
  have restore : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block VG.Impl.Mont.X86.Compact.restoreRegs)
      (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl
  unfold VG.Impl.RsaKeyGen.X86.KeyRuntime.code
  apply VG.X86.RelCT.frame (rs := Compact.savedRegisters) (R := VG.X86.Taint.Agree (τr [.esp])) (fun _ _ P => P.2)
  exact (RelCT.seq (body_trace E v sp e p q p' q' release) restore).mono
    (by rintro _ _ ⟨s, t, P, rfl, rfl⟩; exact P.1) (fun _ _ P => P)

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/ConstantTime.lean`, which only this module imported.
section

/-! # Native key assembly is constant time under exactly the shared API's declared observations -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86
open VG.Proof.RsaKeyGen.X86.Key (contract public_inputs entry_input callSp entered_exponent entered_prime
  callEnvironment inputExponent inputPrime call_valid)

theorem constantTime : ConstantTime isa contract.pre contract.pub VG.Impl.RsaKeyGen.X86.KeyRuntime.code := by
  apply RelCT.constantTime
  intro s t tr ur u z ⟨HS, HT, HP⟩ A B
  have P := public_inputs HP
  have I := entry_input HS
  have J := entry_input HT
  have stack : callSp s = callSp t := by unfold callSp; rw [P.stack]
  rw [← P.environment, ← stack] at J
  have rightExponent := entered_exponent HT
  have rightP := entered_prime HT (by decide : 2 < 7)
  have rightQ := entered_prime HT (by decide : 3 < 7)
  rw [← P.environment] at rightExponent rightP rightQ
  exact framed_trace (callEnvironment s) (call_valid HS) (callSp s)
    (inputExponent (callEnvironment s) s.mem)
    (inputPrime (callEnvironment s) s.mem 2) (inputPrime (callEnvironment s) s.mem 3)
    (inputPrime (callEnvironment s) t.mem 2) (inputPrime (callEnvironment s) t.mem 3)
    (P.release HS) _ _ _ _ _ _
    ⟨⟨I, J, entered_exponent HS, rightExponent.trans P.exponentValue.symm,
      entered_prime HS (by decide : 2 < 7), entered_prime HS (by decide : 3 < 7), rightP, rightQ⟩, P.stack⟩ A B

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86

theorem verified : Verified target VG.Impl.RsaKeyGen.X86.KeyRuntime.code VG.Proof.RsaKeyGen.X86.Key.contract :=
  ⟨correct, constantTime, VG.Proof.RsaKeyGen.X86.Key.satisfiable⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
