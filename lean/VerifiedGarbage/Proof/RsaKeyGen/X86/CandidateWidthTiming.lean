module

public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Code
public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.TCB.X86.State
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.Impl.RsaKeyGen.X86.FrontRt
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingBranch
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveLoopTiming
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateFinish
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEnvironment
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinState
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFrontRt
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.RsaKeyGen.X86.WorkspaceDisjoint
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareRt.R2Timing
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Loop
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.Load
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateShape
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateArrays
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishReady
import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateParameters
public import VerifiedGarbage.Proof.RsaKeyGen.CandLeak
public import VerifiedGarbage.Proof.RsaKeyGen.TrialFilter
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestCoreTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportWorkspace
import VerifiedGarbage.Proof.RsaKeyGen.FrameOutside
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentImport
import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
import VerifiedGarbage.Proof.Bignum.X86.PublicDataTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinStep
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePreparedResult
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateResultTiming
import VerifiedGarbage.Proof.MillerRabin.Contract

/-! ### `RsaKeyGen.X86.CandidateFrontRtTiming`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.CandidateExponentStageTiming`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.CandidateFilterTiming`, which only this module used -/

section

/-! # Live candidate inputs satisfy the timing preconditions of every prefilter -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ExponentFilterTiming.lean`, which only this module imported.
section

/-! # Complete exponent filtering branches only on the public exponent -/

section
namespace VG.Proof.RsaKeyGen.X86.ExponentFilter
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.ExponentFilter
open VG.Impl.RsaKeyGen.X86.ExponentRt (fast general filter)

def TimingPair (workspace p : BitVec 32) (size w c d exponent : Nat) (s t : State) : Prop :=
  TimingInput workspace p size w c exponent s ∧ TimingInput workspace p size w d exponent t

theorem timing_agree {workspace p : BitVec 32} {size w c d exponent : Nat} {s t : State}
    (H : TimingPair workspace p size w c d exponent s t) : VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
  apply agree_regs
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact H.1.stack.trans H.2.stack.symm
  · exact H.1.workspace.trans H.2.workspace.symm

def Classified (P : State → State → Prop) (b : Bool) (s t : State) : Prop :=
  P s t ∧ isa.eval .e s = some b ∧ isa.eval .e t = some b

theorem choice {P : State → State → Prop} {b : Bool} {left right : Prog isa}
    (L : b = true → RelCT isa P left (fun _ _ => True))
    (R : b = false → RelCT isa P right (fun _ _ => True)) :
    RelCT isa (Classified P b) (.ite .e left right) (fun _ _ => True) := by
  refine VG.RelCT.ite (fun _ _ H => H.2.1.trans H.2.2.symm) ?_ ?_
  · intro s t tr ur u z ⟨H, yes⟩ E G
    have hb : b = true := by have same := H.2.1.symm.trans yes; exact Option.some.inj same
    exact L hb _ _ _ _ _ _ H.1 E G
  · intro s t tr ur u z ⟨H, no⟩ E G
    have hb : b = false := by have same := H.2.1.symm.trans no; exact Option.some.inj same
    exact R hb _ _ _ _ _ _ H.1 E G

theorem classify {workspace p : BitVec 32} {size w c d exponent : Nat} {is : List Instr} {b : Bool}
    (raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block is) (VG.X86.Taint.Agree (τr [.esp, .edi])))
    (run : ∀ {candidate : Nat} {s : State}, TimingInput workspace p size w candidate exponent s →
      WP isa (.block is) s fun t => isa.eval .e t = some b ∧ t.mem = s.mem ∧ Keeps [.eax] s t) :
    RelCT isa (TimingPair workspace p size w c d exponent) (.block is)
      (Classified (TimingPair workspace p size w c d exponent) b) := by
  intro s t tr ur u z H E G
  obtain ⟨Zu, Mu, Ku⟩ := wp_result (run H.1) E
  obtain ⟨Zz, Mz, Kz⟩ := wp_result (run H.2) G
  exact ⟨(raw _ _ _ _ _ _ (timing_agree H) E G).1,
    ⟨H.1.keepReadonly Mu Ku, H.2.keepReadonly Mz Kz⟩, Zu, Zz⟩

theorem equal_trace {workspace p : BitVec 32} {size w c d exponent value : Nat} (bound : value < 2 ^ 32) :
    RelCT isa (TimingPair workspace p size w c d exponent) (.block (equal value))
      (Classified (TimingPair workspace p size w c d exponent) (decide (exponent = value))) := by
  refine classify ?_ ?_
  · exact erased_relCT _ (.block (equal 0)) (.block []) rfl rfl rfl (by decide +kernel)
  · intro candidate s S
    refine WP.mono (equal_ok S.input.scratch S.input.header bound) fun t ⟨Z, M, K⟩ => ⟨?_, M, K⟩
    change t.zf = _
    rw [Z, S.input.exponentEq]

theorem parity_trace {workspace p : BitVec 32} {size w c d exponent : Nat} :
    RelCT isa (TimingPair workspace p size w c d exponent) (.block parity)
      (Classified (TimingPair workspace p size w c d exponent) (decide (exponent % 2 = 0))) := by
  refine classify (checkedBlockInvariant rfl rfl) ?_
  intro candidate s S
  refine WP.mono (parity_ok S.input.scratch S.input.header) fun t ⟨Z, M, K⟩ => ⟨?_, M, K⟩
  change t.zf = _
  rw [Z, S.input.exponentEq]

theorem literal_trace {workspace p : BitVec 32} {size w c d exponent : Nat} (value : Nat) :
    RelCT isa (TimingPair workspace p size w c d exponent)
      (.block [.mov .eax (.imm (BitVec.ofNat 32 value))]) (fun _ _ => True) := by
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
      (.block [.mov .eax (.imm (BitVec.ofNat 32 value))]) (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
    erased_relCT _ (.block [.mov .eax (.imm 0)]) (.block []) rfl rfl rfl (by decide +kernel)
  exact raw.mono (fun _ _ H => timing_agree H) (fun _ _ _ => trivial)

theorem fast_pair_trace {workspace p : BitVec 32} {size w c d exponent : Nat} :
    RelCT isa (TimingPair workspace p size w c d exponent) fast (fun _ _ => True) :=
  ExponentRt.fast_trace.mono (fun _ _ H => ⟨H.1.framed, H.2.framed⟩) (fun _ _ _ => trivial)

theorem general_pair_trace {workspace p : BitVec 32} {size w c d exponent : Nat} (odd : exponent % 2 = 1) :
    RelCT isa (TimingPair workspace p size w c d exponent) general (fun _ _ => True) :=
  (ExponentRt.general_trace (c := c) (d := d) odd).mono (fun _ _ H => ⟨H.1.general odd, H.2.general odd⟩)
    (fun _ _ _ => trivial)

theorem nontrivial_trace {workspace p : BitVec 32} {size w c d exponent : Nat} (odd : exponent % 2 = 1) :
    RelCT isa (TimingPair workspace p size w c d exponent)
      (.seq (.block (equal 65537)) (.ite .e fast general)) (fun _ _ => True) :=
  RelCT.seq (equal_trace (by decide)) (choice (fun _ => fast_pair_trace) (fun _ => general_pair_trace odd))

theorem odd_trace {workspace p : BitVec 32} {size w c d exponent : Nat} (odd : exponent % 2 = 1) :
    RelCT isa (TimingPair workspace p size w c d exponent)
      (.seq (.block (equal 1)) (.ite .e (.block [.mov .eax (.imm 1)])
        (.seq (.block (equal 65537)) (.ite .e fast general)))) (fun _ _ => True) :=
  RelCT.seq (equal_trace (by decide)) (choice (fun _ => literal_trace 1) (fun _ => nontrivial_trace odd))

theorem code_trace {workspace p : BitVec 32} {size w c d exponent : Nat} :
    RelCT isa (TimingPair workspace p size w c d exponent) filter (fun _ _ => True) := by
  unfold filter
  refine RelCT.seq parity_trace (choice (fun _ => literal_trace 0) ?_)
  intro odd
  have notEven : ¬ exponent % 2 = 0 := of_decide_eq_false odd
  exact odd_trace (by omega)

end VG.Proof.RsaKeyGen.X86.ExponentFilter
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ExponentImportTiming.lean`, which only this module imported.
section

/-! # Exponent import exposes only its public pointer and byte count -/

section
namespace VG.Proof.RsaKeyGen.X86.ExponentImport
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86

open VG.Impl.RsaKeyGen.X86.ExponentImport

theorem args_ok {s : State} {base : Addr} {size : Nat} (S : Scr s base size) (header : 20 ≤ size) :
    WP isa (.block args) s fun t =>
      t.gpr .esi = s.mem.readW (off base 12) 32 ∧ t.gpr .ecx = s.mem.readW (off base 16) 32 := by
  unfold args
  refine wp_movS (readSrc_sc S (by omega)) fun a A _ =>
    wp_movS (readSrc_sc (S.of_keeps A.keeps (by decide)) (d := 16) (by omega)) fun t T _ => WP.block_nil ?_
  exact ⟨(T.other .esi (by decide)).trans A.gpr, by rw [T.gpr, A.mem]⟩

def InputPair (base : Addr) (size : Nat) (s t : State) : Prop :=
  Scr s base size ∧ Scr t base size ∧ VG.X86.Taint.Agree (roundTaint [.edi]) s t ∧
    s.mem.readW (off base 12) 32 = t.mem.readW (off base 12) 32 ∧
    s.mem.readW (off base 16) 32 = t.mem.readW (off base 16) 32

theorem args_pair {base : Addr} {size : Nat} (header : 20 ≤ size) :
    RelCT isa (InputPair base size) (.block args) (VG.X86.Taint.Agree VG.Proof.Bignum.X86.loadTaint) := by
  have raw : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block args)
      (VG.X86.Taint.Agree (roundTaint [.edi])) := checkedBlockInvariant rfl rfl
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := raw _ _ _ _ _ _ H.2.2.1 E G
  obtain ⟨sourceU, countU⟩ := wp_result (args_ok H.1 header) E
  obtain ⟨sourceZ, countZ⟩ := wp_result (args_ok H.2.1 header) G
  have regs : ∀ r ∈ ([.edi, .esi, .ecx] : List Reg), u.gpr r = z.gpr r := by
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    · exact round_regs agree (by decide)
    · rw [sourceU, sourceZ]; exact H.2.2.2.1
    · rw [countU, countZ]; exact H.2.2.2.2
  have full := round_add_regs (round_forget agree) regs
  exact ⟨trace, taint.le_sound (by decide +kernel) full⟩

theorem code_trace {base : Addr} {size : Nat} (header : 20 ≤ size) :
    RelCT isa (InputPair base size) VG.Impl.RsaKeyGen.X86.ExponentImport.code
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  unfold VG.Impl.RsaKeyGen.X86.ExponentImport.code
  refine RelCT.seq (args_pair header) ?_
  apply erased_relCT (VG.Impl.Bignum.X86.loadBE 1 128) (VG.Impl.Bignum.X86.loadBE 1 0)
    (VG.Taint.hintOf taint VG.Proof.Bignum.X86.loadTaint (VG.Impl.Bignum.X86.loadBE 1 0)) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)
  kernel_rfl

end VG.Proof.RsaKeyGen.X86.ExponentImport
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateExponentTiming.lean`, which only this module imported.
section

/-! # Candidate saving, public exponent import, and filtering have one composed timing proof -/

section
namespace VG.Proof.RsaKeyGen.X86.CandidateExponent
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86.PublicContext

def InitialPair (workspace p e : BitVec 32) (size w c d len exponent : Nat) (s t : State) : Prop :=
  Initial workspace p e size w c len exponent s ∧ Initial workspace p e size w d len exponent t

theorem save_pair {workspace p e : BitVec 32} {size w c d len exponent : Nat} :
    RelCT isa (InitialPair workspace p e size w c d len exponent) VG.Impl.RsaKeyGen.X86.ExponentRt.save
      (ExponentImport.InputPair (workspace.setWidth 64) size) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := ExponentRt.save_trace _ _ _ _ _ _ ⟨H.1.spaceRt, H.2.spaceRt⟩ E G
  obtain ⟨Su, Ou, Ku⟩ := wp_result H.1.save_ok E
  obtain ⟨Sz, Oz, Kz⟩ := wp_result H.2.save_ok G
  have savedLo := H.1.savedLo
  refine ⟨trace, Su, Sz, agree, ?_, ?_⟩
  · rw [BitVec.eq_of_toNat_eq (Ou.w32 (d := 12) (by omega) (by decide)),
      BitVec.eq_of_toNat_eq (Oz.w32 (d := 12) (by omega) (by decide)), H.1.pointer, H.2.pointer]
  · apply BitVec.eq_of_toNat_eq
    change w32 u.mem (workspace.setWidth 64) 16 = w32 z.mem (workspace.setWidth 64) 16
    rw [Ou.w32 (d := 16) (by omega) (by decide), Oz.w32 (d := 16) (by omega) (by decide), H.1.length, H.2.length]

theorem prepare_trace {workspace p e : BitVec 32} {size w c d len exponent : Nat} :
    RelCT isa (InitialPair workspace p e size w c d len exponent)
      (.seq VG.Impl.RsaKeyGen.X86.ExponentRt.save VG.Impl.RsaKeyGen.X86.ExponentImport.code)
      (ExponentFilter.TimingPair workspace p size w c d exponent) := by
  intro s t tr ur u z H E G
  have raw : RelCT isa (InitialPair workspace p e size w c d len exponent)
      (.seq VG.Impl.RsaKeyGen.X86.ExponentRt.save VG.Impl.RsaKeyGen.X86.ExponentImport.code)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
    RelCT.seq save_pair (ExponentImport.code_trace (size := size) (by have := H.1.header; omega))
  exact ⟨(raw _ _ _ _ _ _ H E G).1, wp_result H.1.prepare_ok E, wp_result H.2.prepare_ok G⟩

theorem code_trace {workspace p e : BitVec 32} {size w c d len exponent : Nat} :
    RelCT isa (InitialPair workspace p e size w c d len exponent)
      VG.Impl.RsaKeyGen.X86.ExponentRt.code (fun _ _ => True) := by
  unfold VG.Impl.RsaKeyGen.X86.ExponentRt.code
  exact RelCT.assoc (RelCT.seq prepare_trace ExponentFilter.code_trace)

end VG.Proof.RsaKeyGen.X86.CandidateExponent
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem exponent_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte} :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
      VG.Impl.RsaKeyGen.X86.ExponentRt.code (fun _ _ => True) :=
  CandidateExponent.code_trace.mono (fun _ _ P => ⟨P.left.exponentInitial v, P.right.exponentInitial v⟩) (fun _ _ _ => trivial)

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! # Publicly released coprimality decisions select equally timed candidate continuations -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateIterationLeak.lean`, which only this module imported.
section

/-! # The released primality-result shape determines iterations and the final status -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.RsaKeyGen

theorem iterations_eq {E : Environment} (v : E.Valid) {rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length)
    (shape : shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E rBytes) (rBytes.drop E.length)) =
      shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E sBytes) (sBytes.drop E.length))) :
    (E.parameters rBytes).iterations = (E.parameters sBytes).iterations := by
  rw [MillerRabinLoop.Parameters.iterations, MillerRabinLoop.Parameters.iterations, v.test_eq, v.test_eq]
  change itersOf (8 * E.width) rBytes.length
      (shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E rBytes) (rBytes.drop (8 * E.width)))) (8 * E.width) - 1 =
    itersOf (8 * E.width) sBytes.length
      (shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E sBytes) (sBytes.drop (8 * E.width)))) (8 * E.width) - 1
  rw [v.length_eq, length, shape]

theorem result_status_eq {E : Environment} (v : E.Valid) {rBytes sBytes : List Byte} {s t : State}
    (left : MillerRabinLoop.Result (E.parameters rBytes) s)
    (right : MillerRabinLoop.Result (E.parameters sBytes) t)
    (shape : shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E rBytes) (rBytes.drop E.length)) =
      shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E sBytes) (sBytes.drop E.length))) :
    s.mem.readW (off E.base 168) 32 = t.mem.readW (off E.base 168) 32 := by
  apply BitVec.eq_of_toNat_eq
  rw [MillerRabinLoop.Result, v.test_eq] at left
  change (match Spec.RsaKeyGen.primalityTest (candidateValue E rBytes) (rBytes.drop (8 * E.width)) with
    | none => w32 s.mem E.base 168 = 0
    | some (prime, rest) => w32 s.mem E.base 168 = (if prime then 1 else 3) ∧
      w32 s.mem E.base 152 = rBytes.length - rest.length) at left
  rw [MillerRabinLoop.Result, v.test_eq] at right
  change (match Spec.RsaKeyGen.primalityTest (candidateValue E sBytes) (sBytes.drop (8 * E.width)) with
    | none => w32 t.mem E.base 168 = 0
    | some (prime, rest) => w32 t.mem E.base 168 = (if prime then 1 else 3) ∧
      w32 t.mem E.base 152 = sBytes.length - rest.length) at right
  rw [v.length_eq] at left right
  cases a : Spec.RsaKeyGen.primalityTest (candidateValue E rBytes) (rBytes.drop E.length) with
  | none =>
    cases b : Spec.RsaKeyGen.primalityTest (candidateValue E sBytes) (sBytes.drop E.length) with
    | none => rw [a] at left; rw [b] at right; exact left.trans right.symm
    | some pr => simp only [a, b, shapeOf, Option.map_none, Option.map_some, reduceCtorEq] at shape
  | some pr =>
    obtain ⟨prime, rest⟩ := pr
    cases b : Spec.RsaKeyGen.primalityTest (candidateValue E sBytes) (sBytes.drop E.length) with
    | none => simp only [a, b, shapeOf, Option.map_none, Option.map_some, reduceCtorEq] at shape
    | some other =>
      obtain ⟨other, remaining⟩ := other
      have equal : prime = other := by
        simp only [a, b, shapeOf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at shape
        exact shape.1
      rw [a] at left
      rw [b] at right
      exact left.1.trans (by rw [equal]; exact right.1.symm)

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidatePreparedTiming.lean`, which only this module imported.
section

/-! # Complete prepared testing and export release only the declared primality shape -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.RsaKeyGen VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86

theorem test_status_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (enough : E.length ≤ E.randLength)
    (shape : shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E rBytes) (rBytes.drop E.length)) =
      shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E sBytes) (sBytes.drop E.length))) :
    RelCT isa (TestPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.CandidateFrame.code
        (VG.Impl.RsaKeyGen.X86.Candidate.testBody montName mont roundName round))
      (StatusPair E (candidateValue E rBytes) (candidateValue E sBytes)) := by
  intro s t tr ur u z H A B
  have trace := (test_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v
    (iterations_eq v length shape) enough _ _ _ _ _ _ H A B).1
  obtain ⟨VU, RU, WU, FU, KU⟩ := wp_result (test_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack
    v H.left H.savedLeft enough) A
  obtain ⟨VZ, RZ, WZ, FZ, KZ⟩ := wp_result (test_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack
    v H.right H.savedRight enough) B
  refine ⟨trace, ⟨H.left.finishReady_after_test v VU WU FU KU, H.right.finishReady_after_test v VZ WZ FZ KZ, ?_⟩,
    result_status_eq v RU RZ shape⟩
  rw [KU.1 .esp (by unfold WitnessStep.clob; decide), KZ.1 .esp (by unfold WitnessStep.clob; decide),
    H.left.input.stack, H.right.input.stack]

theorem prepared_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (enough : E.length ≤ E.randLength)
    (shape : shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E rBytes) (rBytes.drop E.length)) =
      shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E sBytes) (sBytes.drop E.length))) :
    RelCT isa (TestPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.Candidate.tested montName mont roundName round) (fun _ _ => True) := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.tested
  rw [mrResult_zero E.width]
  exact RelCT.seq (test_status_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v length enough shape)
    (result_trace v)

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Proof.RsaKeyGen

theorem drawn_used_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte} (status : Nat) :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.CandidateFinish.used status) (fun _ _ => True) := by
  exact (CandidateFinish.used_trace (base := E.base) (size := E.size)
    (by have H : 256 ≤ E.size := v.geometry.headerFit; omega_using [H]) status).mono (fun _ _ P =>
      ⟨P.left.input.scratch, P.right.input.scratch, P.left.input.usedPointer.trans P.right.input.usedPointer.symm⟩) (fun _ _ _ => trivial)

theorem exponent_pair_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (same : decide (Nat.gcd (candidateValue E rBytes - 1) (Spec.Rsa.os2ip eBytes) = 1) =
      decide (Nat.gcd (candidateValue E sBytes - 1) (Spec.Rsa.os2ip eBytes) = 1)) :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
      VG.Impl.RsaKeyGen.X86.ExponentRt.code
      (WithFlag (TestPair E eBytes pBytes qBytes rBytes sBytes)
        (decide (Nat.gcd (candidateValue E rBytes - 1) (Spec.Rsa.os2ip eBytes) = 1))) := by
  intro s t tr ur u z P A B
  have trace := (exponent_trace v _ _ _ _ _ _ P A B).1
  obtain ⟨DU, flagU, saveU, _, _⟩ := wp_result (exponent_ok v P.left) A
  obtain ⟨DZ, flagZ, saveZ, _, _⟩ := wp_result (exponent_ok v P.right) B
  exact ⟨trace, ⟨⟨DU, DZ⟩, saveU, saveZ⟩, flagU, by rw [same]; exact flagZ⟩

theorem tested_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (enough : E.length ≤ E.randLength)
    (shape : shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E rBytes) (rBytes.drop E.length)) =
      shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E sBytes) (sBytes.drop E.length))) :
    RelCT isa (TestPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.Candidate.tested montName mont roundName round) (fun _ _ => True) := by
  exact prepared_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v length enough shape

theorem exponent_stage_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (enough : E.length ≤ E.randLength)
    (same : decide (Nat.gcd (candidateValue E rBytes - 1) (Spec.Rsa.os2ip eBytes) = 1) =
      decide (Nat.gcd (candidateValue E sBytes - 1) (Spec.Rsa.os2ip eBytes) = 1))
    (shape : Nat.gcd (candidateValue E rBytes - 1) (Spec.Rsa.os2ip eBytes) = 1 →
      shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E rBytes) (rBytes.drop E.length)) =
        shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E sBytes) (sBytes.drop E.length))) :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.Candidate.exponentCheck montName mont roundName round) (fun _ _ => True) := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.exponentCheck
  by_cases good : Nat.gcd (candidateValue E rBytes - 1) (Spec.Rsa.os2ip eBytes) = 1
  · have initialTrace := exponent_pair_trace (pBytes := pBytes) (qBytes := qBytes) v same
    rw [decide_eq_true good] at initialTrace
    refine RelCT.seq initialTrace (RelCT.seq ((cmp_flag_trace true (fun _ _ _ _ P U Z => P.keepFlags v U Z)).mono
      (fun _ _ P => P) (fun _ _ P => P.1)) ?_)
    exact branch_false (tested_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v length enough
      (shape good))
  · have initialTrace := exponent_pair_trace (pBytes := pBytes) (qBytes := qBytes) v same
    rw [decide_eq_false good] at initialTrace
    refine RelCT.seq initialTrace (RelCT.seq ((cmp_flag_trace false (fun _ _ _ _ P U Z => P.keepFlags v U Z)).mono
      (fun _ _ P => P) (fun _ _ P => P.1)) ?_)
    exact branch_true ((drawn_used_trace v 3).mono (fun _ _ P => P.toDrawnPair) (fun _ _ _ => trivial))

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! ### `RsaKeyGen.X86.FrontRt.LoadTiming`, which only this module used -/

section

/-! # The run-time width's imports and candidate load read the same addresses in every run -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.FrontRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.FrontRt
open VG.Impl.Mont.X86 (sc at_)

/-- The public registers' values: `esp`, `edi` and those `extra` gives. -/
def regs (W : Addr) (q : BitVec 32) (extra : Reg → BitVec 32) (r : Reg) : BitVec 32 :=
  if r = .esp then q else if r = .edi then BitVec.ofNat 32 W.toNat else extra r

theorem Space.edi_value {W : Addr} {L w : Nat} {s : State} (S : Space W L w s) :
    s.gpr .edi = BitVec.ofNat 32 W.toNat := by
  apply BitVec.eq_of_toNat_eq
  have := S.scratch.nowrap
  have := S.header
  rw [S.edi_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]

theorem Base.vals {W : Addr} {L w : Nat} {q : BitVec 32} {s : State} (B : Base W L w q s)
    (extra : Reg → BitVec 32) : ∀ r ∈ [Reg.esp, .edi], s.gpr r = regs W q extra r := by
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact B.2
  · exact B.1.edi_value

/-- About to import array `j` from the octets at `src`, `esi` at them. -/
structure SourceIn (W : Addr) (L w : Nat) (q src : BitVec 32) (s : State) : Prop where
  base : Base W L w q s
  esi : s.gpr .esi = src
  sourceFit : src.toNat + 8 * w ≤ 2 ^ 32
  readable : InRegions (s.rd ++ s.wr) (src.setWidth 64) (8 * w)
  separate : (⟨src.setWidth 64, 8 * w⟩ : Region).Disjoint ⟨W, L⟩

/-- The import's arguments set. -/
structure ImportIn (W : Addr) (L w : Nat) (q src : BitVec 32) (j : Nat) (s : State) : Prop where
  base : Base W L w q s
  context : VG.Proof.RsaKeyGen.X86.Import.Context (importGeometry src (BitVec.ofNat 32 W.toNat) w j) s
  esi : s.gpr .esi = (importGeometry src (BitVec.ofNat 32 W.toNat) w j).sourcePtr 0
  ebx : s.gpr .ebx = (importGeometry src (BitVec.ofNat 32 W.toNat) w j).destPtr 0
  ecx : s.gpr .ecx = BitVec.ofNat 32 (importGeometry src (BitVec.ofNat 32 W.toNat) w j).count

theorem importArgs_trace {W : Addr} {L w : Nat} {q src : BitVec 32} (j : Nat) (index : j < 32)
    (fit : slot w j + 8 * w ≤ L)
    (raw : (VG.Taint.check taint (τr [.esp, .edi]) (.block (importArgs j)) (.block [])).map
      (taint.le (τr [])) = some true) :
    RelCT isa (fun s t => SourceIn W L w q src s ∧ SourceIn W L w q src t) (.block (importArgs j))
      (fun u z => ImportIn W L w q src j u ∧ ImportIn W L w q src j z) := by
  refine seg [.esp, .edi] (regs W q fun _ => 0) (fun s S => S.base.vals _) (rawBlock raw) fun s S => ?_
  have Sp := S.base.1
  have width := Sp.width
  have sourceFit := S.sourceFit
  have below : slot w j < L := Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by omega_using [width])) fit
  have C : VG.Proof.RsaKeyGen.X86.Import.Context (importGeometry src (s.gpr .edi) w j) s :=
    VG.Proof.RsaKeyGen.X86.Import.context_workspace Sp.scratch (out := slot w j) (n := 2 * w) (by omega_using [width]) (by omega_using [fit])
      (by omega_using [sourceFit])
      (by rw [show 4 * (2 * w) = 8 * w by omega_using []]; exact S.readable)
      (by rw [show 4 * (2 * w) = 8 * w by omega_using []]; exact S.separate)
  rw [Sp.edi_value] at C
  refine WP.mono (importArgs_ok Sp j index below src) fun u ⟨M, K, Pd, Pc⟩ => ?_
  rw [Sp.edi_value] at Pd Pc
  refine ⟨⟨Sp.keepMem K (by decide) (by decide) M, (K.1 .esp (by decide)).trans S.base.2⟩,
    ⟨C.positive, C.sourceFit, C.destFit, fun i index => by rw [K.2.1, K.2.2]; exact C.readable i index,
      fun i index => by rw [K.2.2]; exact C.writable i index, C.separate⟩, ?_, Pd, Pc⟩
  rw [K.1 .esi (by decide), S.esi]
  simp only [VG.Proof.RsaKeyGen.X86.Import.Geometry.sourcePtr, importGeometry, Nat.mul_zero, BitVec.add_zero]

theorem import_trace {W : Addr} {L w : Nat} {q src : BitVec 32} (j : Nat) (fit : slot w j + 8 * w ≤ L)
    (header : 8 ≤ slot w j) :
    RelCT isa (fun s t => ImportIn W L w q src j s ∧ ImportIn W L w q src j t) VG.Impl.RsaKeyGen.X86.Import.code
      (fun u z => Base W L w q u ∧ Base W L w q z) := by
  refine seg [.esp, .edi, .esi, .ebx, .ecx]
    (regs W q fun r => if r = .esi then (importGeometry src (BitVec.ofNat 32 W.toNat) w j).sourcePtr 0
      else if r = .ebx then (importGeometry src (BitVec.ofNat 32 W.toNat) w j).destPtr 0
      else BitVec.ofNat 32 (importGeometry src (BitVec.ofNat 32 W.toNat) w j).count) (fun s S => by
        intro r mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl | rfl | rfl | rfl
        · exact S.base.2
        · exact S.base.1.edi_value
        · exact S.esi
        · exact S.ebx
        · exact S.ecx)
    (VG.Proof.RsaKeyGen.X86.Import.code_trace.mono (fun _ _ h => h) (fun _ _ _ => trivial)) fun s S => ?_
  have Sp := S.base.1
  have nowrap := Sp.scratch.nowrap
  have width := Sp.width
  refine WP.mono (VG.Proof.RsaKeyGen.X86.Import.code_ok S.context S.esi S.ebx S.ecx) fun t T => ?_
  have frame := T.frame
  have dstAddr : ((BitVec.ofNat 32 W.toNat) + BitVec.ofNat 32 (slot w j)).setWidth 64 = off W (slot w j) := by
    have below : slot w j < L := by omega_using [fit, width]
    rw [← Sp.edi_value]; exact Sp.scratch.ea below
  simp only [VG.Proof.RsaKeyGen.X86.Import.Geometry.destRegion, importGeometry] at frame
  rw [dstAddr] at frame
  have O : Outside W (slot w j) (4 * (2 * w)) s.mem t.mem := VG.Proof.RsaKeyGen.frame_outside frame (by omega_using [fit, nowrap])
  have len : t.mem.readW (off W 4) 32 = s.mem.readW (off W 4) 32 :=
    BitVec.eq_of_toNat_eq (O.w32 (d := 4) (Or.inl (by omega_using [header])) (by omega_using []))
  exact ⟨Sp.keep T.keeps (by decide) (by decide) len, (T.keeps.1 .esp (by decide)).trans S.base.2⟩

/-- Array `j` imported from the octets at `src`. -/
theorem importAt_trace {W : Addr} {L w : Nat} {q src : BitVec 32} (j : Nat) (index : j < 32)
    (fit : slot w j + 8 * w ≤ L) (header : 8 ≤ slot w j)
    (raw : (VG.Taint.check taint (τr [.esp, .edi]) (.block (importArgs j)) (.block [])).map
      (taint.le (τr [])) = some true) :
    RelCT isa (fun s t => SourceIn W L w q src s ∧ SourceIn W L w q src t) (importAt j)
      (fun u z => Base W L w q u ∧ Base W L w q z) :=
  RelCT.seq (importArgs_trace j index fit raw) (import_trace j fit header)

def bitsHead : List Instr :=
  VG.Impl.RsaKeyGen.X86.CandidateBits.forceWord 256 1 ++ [.mov .ebx (.mem (sc 4)), .alu .add .ebx (.reg .edi)]

def bitsTail : List Instr :=
  [.mov .eax (.mem (at_ .ebx 252)), .alu .or .eax (.imm 0xc0000000), .store (at_ .ebx 252) .eax]

theorem bits_split : bits ++ count = bitsHead ++ (bitsTail ++ count) := by
  simp only [bits, bitsHead, bitsTail, List.append_assoc, List.cons_append, List.nil_append]

theorem bitsHead_ok {W : Addr} {L w : Nat} {q : BitVec 32} {s : State} (B : Base W L w q s) :
    WP isa (.block bitsHead) s fun c => Base W L w q c ∧ PtrAt c W .ebx (8 * w) := by
  have S := B.1
  have head := S.header
  have nowrap := S.scratch.nowrap
  have width := S.width
  unfold bitsHead
  refine WP.block_append (WP.mono (VG.Proof.RsaKeyGen.X86.CandidateBits.forceWord_ok 1 S.scratch (by omega_using [head]))
    fun a ⟨_, Oa, Ka⟩ => ?_)
  have Sa := S.keep Ka (by decide) (by decide)
    (BitVec.eq_of_toNat_eq (Oa.w32 (d := 4) (Or.inl (by omega_using [])) (by omega_using [])))
  refine wp_movS Sa.lenRead fun b B' _ => wp_addS rfl fun c C _ => WP.block_nil ?_
  have Kc : Keeps [.eax, .ebx] s c := (Ka.mono (by decide)).trans ((B'.keeps.trans C.keeps).mono (by decide))
  refine ⟨⟨Sa.keepMem ((B'.keeps.trans C.keeps).mono (by decide) : Keeps [.ebx] a c) (by decide) (by decide)
    (by rw [C.mem, B'.mem]), (Kc.1 .esp (by decide)).trans B.2⟩, ?_⟩
  rw [PtrAt, C.gpr, B'.gpr, BitVec.toNat_add, BitVec.toNat_ofNat, B'.other .edi (by decide), Sa.edi_toNat]
  omega_using []

theorem bitsTail_ok {W : Addr} {L w : Nat} {s : State} (S : Space W L w s) (P : PtrAt s W .ebx (8 * w)) :
    WP isa (.block (bitsTail ++ count)) s fun _ => True := by
  have head := S.header
  have nowrap := S.scratch.nowrap
  have width := S.width
  have hw := S.ws
  unfold bitsTail
  refine WP.block_append (wp_movS (readSrc_ptr hw P (d := 252) (by omega_using [head])) fun d D _ => wp_orS rfl fun e E => ?_)
  have Ke : Keeps [.eax] s e := (D.keeps.trans E.keeps).mono (by decide)
  have Pe : PtrAt e W .ebx (8 * w) := by
    rw [PtrAt, E.other .ebx (by decide), D.other .ebx (by decide)]; exact P
  have hwe := hw.of_keeps Ke
  refine wp_storeS (ea_ptr hwe Pe (d := 252) (by omega_using [head])) (ws_write hwe (y := 8 * w + 252) (n := 4) (by omega_using [head]))
    fun t T => WP.block_nil ?_
  have Ot : Outside W (8 * w + 252) 4 s.mem t.mem := by
    rw [T.mem, E.mem, D.mem]; exact writeW32_outside _ _ _ (by omega_using [head, nowrap])
  have St := S.keep (Ke.widen (T.keeps [])) (by decide) (by decide)
    (BitVec.eq_of_toNat_eq (Ot.w32 (d := 4) (Or.inl (by omega_using [])) (by omega_using [])))
  exact WP.mono (count_ok St) fun _ _ => trivial

theorem load_trace {W : Addr} {L w : Nat} {q rand : BitVec 32} (width : 4 ≤ w) (space : slot w 5 ≤ L) :
    RelCT isa (fun s t => LoadIn W L w q rand s ∧ LoadIn W L w q rand t) load (fun _ _ => True) := by
  unfold load
  have source := seg (X := LoadIn W L w q rand) (Y := SourceIn W L w q rand) (c := .block [.mov .esi (.mem (sc 28))]) [.esp, .edi] (regs W q fun _ => 0)
    (fun s S => S.base.vals _) (rawBlock (by decide +kernel)) fun s S => by
      have head := S.base.1.header
      refine wp_movS (readSrc_sc S.base.1.scratch (d := 28) (by omega)) fun t T _ => WP.block_nil ?_
      refine ⟨⟨S.base.1.keepMem T.keeps (by decide) (by decide) T.mem, (T.other .esp (by decide)).trans S.base.2⟩,
        T.gpr.trans S.source, S.sourceFit, by rw [T.keeps.2.1, T.keeps.2.2]; exact S.readable, S.separate⟩
  have head := seg (X := Base W L w q) (Y := fun c => Base W L w q c ∧ PtrAt c W .ebx (8 * w)) (c := .block bitsHead)
    [.esp, .edi]
    (regs W q fun _ => 0) (fun s S => S.vals _) (rawBlock (by decide +kernel)) fun s S => bitsHead_ok S
  have tail := seg (X := fun c => Base W L w q c ∧ PtrAt c W .ebx (8 * w)) (Y := fun _ => True)
    (c := .block (bitsTail ++ count)) [.esp, .edi, .ebx]
    (regs W q fun _ => BitVec.ofNat 32 (W.toNat + 8 * w)) (fun s S => by
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl
      · exact S.1.2
      · exact S.1.1.edi_value
      · exact ptr_value S.2) (rawBlock (by decide +kernel)) fun s S => bitsTail_ok S.1.1 S.2
  have fit : slot w 0 + 8 * w ≤ L := by unfold slot stride VG.Impl.Bignum.hdrBytes at space ⊢; omega_using [space]
  refine RelCT.seq source (RelCT.seq (importAt_trace 0 (by decide) fit
    (by unfold slot VG.Impl.Bignum.hdrBytes; omega_using []) (by decide +kernel)) ?_)
  rw [bits_split]
  exact (RelCT.block_append (RelCT.seq head tail)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.RsaKeyGen.X86.FrontRt

end

end

/-! ### `RsaKeyGen.X86.CandidateSchedule`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.SievePattern`, which this module and modules that import it used -/

section

/-! # Timing may relate different passing candidates or equal rejected candidates -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.Proof.RsaKeyGen

theorem samePattern_refl (g : Geometry) (c : Nat) : SamePattern g c c := fun _ _ => rfl

theorem samePattern_clear {g : Geometry} {c d : Nat}
    (C : trialPrefix c g.limit = false) (D : trialPrefix d g.limit = false) : SamePattern g c d := by
  intro i index
  have clearC := List.any_eq_false.mp C i (List.mem_range.mpr index)
  have clearD := List.any_eq_false.mp D i (List.mem_range.mpr index)
  have cbit : dividesAt c i = false := Bool.eq_false_iff.mpr clearC
  have dbit : dividesAt d i = false := Bool.eq_false_iff.mpr clearD
  rw [cbit, dbit]

theorem samePattern_passing {g : Geometry} {c d : Nat}
    (length : g.limit = VG.Impl.RsaKeyGen.X86.Sieve.tableCount g.w)
    (cLarge : 8161 < c) (dLarge : 8161 < d)
    (C : Spec.RsaKeyGen.obviouslyComposite (64 * g.w) c = false)
    (D : Spec.RsaKeyGen.obviouslyComposite (64 * g.w) d = false) : SamePattern g c d := by
  apply samePattern_clear
  · rw [length]
    exact (trialPrefix_spec cLarge).trans C
  · rw [length]
    exact (trialPrefix_spec dLarge).trans D

end VG.Proof.RsaKeyGen.X86.Sieve

end

end

/-! # The candidate contract's existing leak determines every permitted branch schedule -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.Proof.RsaKeyGen

def schedule (E : Environment) (eBytes pBytes entropy : List Byte) : Sched :=
  schedOf E.length (Spec.Rsa.os2ip eBytes) (Spec.RsaKeyGen.otherPrime pBytes) entropy

def SameLeak (E : Environment) (eBytes pBytes qBytes rBytes sBytes : List Byte) : Prop :=
  Spec.RsaKeyGen.candidateLeak E.length eBytes pBytes rBytes = Spec.RsaKeyGen.candidateLeak E.length eBytes qBytes sBytes

theorem schedule_eq {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (enough : E.length ≤ rBytes.length)
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes) : schedule E eBytes pBytes rBytes = schedule E eBytes qBytes sBytes := by
  have L : 0 < E.length := by have := v.length; unfold Spec.RsaKeyGen.primeLenValid at this; omega_using [this]
  exact schedOf_eq L length enough (by
    unfold SameLeak at leak
    simpa only [candidateLeak_eq, Spec.RsaKeyGen.candidateOp] using leak)

theorem schedule_close (E : Environment) (eBytes pBytes entropy : List Byte) :
    (schedule E eBytes pBytes entropy).close = Spec.RsaKeyGen.tooClose (8 * E.length)
      (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E entropy) := sched_close _ _ _ _

theorem schedule_composite {E : Environment} {eBytes pBytes entropy : List Byte}
    (close : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E entropy) = false) :
    (schedule E eBytes pBytes entropy).comp = Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy) := sched_comp close

theorem schedule_exponent {E : Environment} {eBytes pBytes entropy : List Byte}
    (close : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E entropy) = false)
    (composite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy) = false) :
    (schedule E eBytes pBytes entropy).gbad = !(Nat.gcd (candidateValue E entropy - 1) (Spec.Rsa.os2ip eBytes) == 1) :=
  sched_gbad close composite

theorem schedule_mr {E : Environment} {eBytes pBytes entropy : List Byte}
    (close : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E entropy) = false)
    (composite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy) = false)
    (gcd : Nat.gcd (candidateValue E entropy - 1) (Spec.Rsa.os2ip eBytes) = 1) :
    (schedule E eBytes pBytes entropy).mr = shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E entropy) (entropy.drop E.length)) :=
  sched_mr close composite (by
    change (!(Nat.gcd (candidateValue E entropy - 1) (Spec.Rsa.os2ip eBytes) == 1)) = false
    rw [gcd]
    decide)

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! ### `RsaKeyGen.X86.FrontRt.CloseTiming`, which only this module used -/

section

/-! # The distance to `p` at the run-time width reads the same addresses in every run -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.FrontRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.FrontRt
open VG.Impl.Mont.X86 (sc at_)

theorem Framed.base {W : Addr} {L w : Nat} {q : BitVec 32} {s : State} (F : Framed W L w q s) : Base W L w q s :=
  ⟨F.space, F.stack.sp⟩

/-- The subtraction's loop and `edi` restored, with its pointers and count public. -/
theorem subRest_raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .ebp, .ebx, .edi, .edx]))
    (.seq subLoop (.block [.mov .edi (.mem (at_ .esp 0))])) (fun _ _ => True) :=
  (erased_relCT (σ := τr [.esp]) (.seq subLoop (.block [.mov .edi (.mem (at_ .esp 0))]))
    (.seq subLoop (.block [.mov .edi (.mem (at_ .esp 0))]))
    (VG.Taint.hintOf taint (τr [.esp, .ebp, .ebx, .edi, .edx])
      (Code.erase (.seq subLoop (.block [.mov .edi (.mem (at_ .esp 0))]))))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem selectRest_raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .ebp, .ebx, .edi]))
    (.seq selectLoop (.block [.mov .edi (.mem (at_ .esp 0))])) (fun _ _ => True) :=
  (erased_relCT (σ := τr [.esp]) (.seq selectLoop (.block [.mov .edi (.mem (at_ .esp 0))]))
    (.seq selectLoop (.block [.mov .edi (.mem (at_ .esp 0))]))
    (VG.Taint.hintOf taint (τr [.esp, .ebp, .ebx, .edi])
      (Code.erase (.seq selectLoop (.block [.mov .edi (.mem (at_ .esp 0))]))))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem orLoop_raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .ebp, .ecx]))
    (.loop (.block [.alu .or .ebx (.mem (at_ .ebp 0)), .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 1)]) .ne)
    (fun _ _ => True) :=
  (erased_relCT (σ := τr [.esp])
    (.loop (.block [.alu .or .ebx (.mem (at_ .ebp 0)), .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 1)]) .ne)
    (.loop (.block [.alu .or .ebx (.mem (at_ .ebp 0)), .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 1)]) .ne)
    (VG.Taint.hintOf taint (τr [.esp, .ebp, .ecx]) (Code.erase
      (.loop (.block [.alu .or .ebx (.mem (at_ .ebp 0)), .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 1)]) .ne)))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

/-- `[out] := [a] − [b]`, its borrow a mask in `ecx`; `E` holds of `esi` throughout. -/
theorem sub_trace {W : Addr} {L w : Nat} {q : BitVec 32} (E : BitVec 32 → Prop) {out a b : Nat}
    (Io : Arrays out) (Ia : Arrays a) (Ib : Arrays b) (oa : out ≠ a) (ob : out ≠ b)
    (raw : (VG.Taint.check taint (τr [.esp, .edi]) (.block (lenPtr .ebp .edx a ++ lenPtr .ebx .edx b ++
      lenPtr .eax .edx out ++ ([.mov .edx (.mem (sc 4)), .mov .edi (.reg .eax), .mov .ecx (.imm 0)] : List Instr)))
      (.block [])).map
      (taint.le (τr [])) = some true) :
    RelCT isa (fun s t => (Framed W L w q s ∧ E (s.gpr .esi)) ∧ (Framed W L w q t ∧ E (t.gpr .esi))) (sub out a b)
      (fun u z => (Framed W L w q u ∧ E (u.gpr .esi) ∧ ∃ c : Bool, u.gpr .ecx = cmask c) ∧
        (Framed W L w q z ∧ E (z.gpr .esi) ∧ ∃ c : Bool, z.gpr .ecx = cmask c)) := by
  unfold sub
  have setup := seg (X := fun s => Framed W L w q s ∧ E (s.gpr .esi))
    (Y := fun u => (∃ s₀, SubSet W L w q out a b s₀ u) ∧ E (u.gpr .esi))
    (c := .block (lenPtr .ebp .edx a ++ lenPtr .ebx .edx b ++ lenPtr .eax .edx out ++
      [.mov .edx (.mem (sc 4)), .mov .edi (.reg .eax), .mov .ecx (.imm 0)]))
    [.esp, .edi] (regs W q fun _ => 0) (fun s S => S.1.base.vals _) (rawBlock raw) fun s S =>
      WP.mono (subSetup_ok S.1 Io Ia Ib) fun u ⟨Pa, Pb, Po, cnt, ecx0, Mu, Ku⟩ =>
        ⟨⟨s, S.1, Pa, Pb, Po, cnt, ecx0, Mu, Ku⟩, by rw [Ku.1 .esi (by decide)]; exact S.2⟩
  have rest := seg (X := fun u => (∃ s₀, SubSet W L w q out a b s₀ u) ∧ E (u.gpr .esi))
    (Y := fun u => Framed W L w q u ∧ E (u.gpr .esi) ∧ ∃ c : Bool, u.gpr .ecx = cmask c)
    (c := .seq subLoop (.block [.mov .edi (.mem (at_ .esp 0))])) [.esp, .ebp, .ebx, .edi, .edx]
    (fun r => if r = .esp then q else if r = .ebp then BitVec.ofNat 32 (W.toNat + slot w a)
      else if r = .ebx then BitVec.ofNat 32 (W.toNat + slot w b)
      else if r = .edi then BitVec.ofNat 32 (W.toNat + slot w out) else BitVec.ofNat 32 (4 * (2 * w)))
    (fun u ⟨⟨s₀, H⟩, _⟩ => by
      have bound := H.framed.space.widthBound
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl | rfl
      · exact (H.keeps.1 .esp (by decide)).trans H.framed.stack.sp
      · exact ptr_value H.aPtr
      · exact ptr_value H.bPtr
      · exact ptr_value H.outPtr
      · change u.gpr .edx = BitVec.ofNat 32 (4 * (2 * w))
        apply BitVec.eq_of_toNat_eq
        rw [H.count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [bound])]) subRest_raw fun u ⟨⟨s₀, H⟩, e⟩ =>
      WP.mono (subRest_ok H Io Ia Ib oa ob) fun t ⟨⟨c, mask, _⟩, _, Kt, Ft⟩ =>
        ⟨Ft, by rw [Kt.1 .esi (by decide), ← H.keeps.1 .esi (by decide)]; exact e, c, mask⟩
  exact RelCT.seq setup rest

/-- A mask: all ones or zero. -/
def IsMask (x : BitVec 32) : Prop := ∃ k : Bool, x = cmask k

theorem difference_trace {W : Addr} {L w : Nat} {q : BitVec 32} :
    RelCT isa (fun s t => Framed W L w q s ∧ Framed W L w q t) difference
      (fun u z => Framed W L w q u ∧ Framed W L w q z) := by
  unfold difference
  have first := sub_trace (W := W) (L := L) (w := w) (q := q) (fun _ => True) arrays2 arrays0 arrays4 (by decide)
    (by decide) (by decide +kernel)
  have save := seg (X := fun s => Framed W L w q s ∧ True ∧ ∃ c : Bool, s.gpr .ecx = cmask c)
    (Y := fun u => Framed W L w q u ∧ IsMask (u.gpr .esi)) (c := .block [.mov .esi (.reg .ecx)]) []
    (fun _ => 0) (fun _ _ _ mem => nomatch mem) (rawBlock (by decide +kernel)) fun s S =>
      wp_movS rfl fun u U _ => WP.block_nil ⟨S.1.keepMem U.keeps (by decide) (by decide) U.mem,
        by obtain ⟨c, mask⟩ := S.2.2; exact ⟨c, by rw [U.gpr, mask]⟩⟩
  have second := sub_trace (W := W) (L := L) (w := w) (q := q) IsMask arrays3 arrays4 arrays0 (by decide)
    (by decide) (by decide +kernel)
  have selectSetup := seg (X := fun s => Framed W L w q s ∧ IsMask (s.gpr .esi) ∧ ∃ c : Bool, s.gpr .ecx = cmask c)
    (Y := fun u => ∃ s₀ k, SelectSet W L w q k s₀ u)
    (c := .block (lenPtr .ebp .edx 3 ++ lenPtr .ebx .edx 2 ++ [.mov .edi (.mem (sc 4)), .mov .ecx (.reg .esi)]))
    [.esp, .edi] (regs W q fun _ => 0) (fun s S => S.1.base.vals _) (rawBlock (by decide +kernel)) fun s S => by
      obtain ⟨k, mask⟩ := S.2.1
      exact WP.mono (selectSetup_ok S.1 mask) fun u H => ⟨s, k, H⟩
  have selectRest := seg (X := fun u => ∃ s₀ k, SelectSet W L w q k s₀ u) (Y := Framed W L w q)
    (c := .seq selectLoop (.block [.mov .edi (.mem (at_ .esp 0))])) [.esp, .ebp, .ebx, .edi]
    (fun r => if r = .esp then q else if r = .ebp then BitVec.ofNat 32 (W.toNat + slot w 3)
      else if r = .ebx then BitVec.ofNat 32 (W.toNat + slot w 2) else BitVec.ofNat 32 (4 * (2 * w)))
    (fun u ⟨s₀, k, H⟩ => by
      have bound := H.framed.space.widthBound
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl
      · exact (H.keeps.1 .esp (by decide)).trans H.framed.stack.sp
      · exact ptr_value H.fromPtr
      · exact ptr_value H.toPtr
      · change u.gpr .edi = BitVec.ofNat 32 (4 * (2 * w))
        apply BitVec.eq_of_toNat_eq
        rw [H.count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [bound])]) selectRest_raw fun u ⟨s₀, k, H⟩ =>
      WP.mono (selectRest_ok H) fun _ H' => H'.2.2.2
  exact (RelCT.seq (first.mono (fun _ _ ⟨S, T⟩ => ⟨⟨S, trivial⟩, ⟨T, trivial⟩⟩) (fun _ _ h => h))
    (RelCT.seq save (RelCT.seq second (RelCT.seq selectSetup selectRest))))

/-- Scanning array 2's low words: `ebp` at them and their count in `ecx`. -/
structure Scanning (W : Addr) (L w : Nat) (q : BitVec 32) (u : State) : Prop where
  ws : Ws u W L
  sp : u.gpr .esp = q
  ptr : PtrAt u W .ebp (slot w 2)
  count : (u.gpr .ecx).toNat = 2 * w - 4
  zero : u.gpr .ebx = 0#32

/-- At array 2's top four words. -/
structure Scanned (W : Addr) (L w : Nat) (q : BitVec 32) (u : State) : Prop where
  ws : Ws u W L
  sp : u.gpr .esp = q
  ptr : PtrAt u W .ebp (slot w 2 + 4 * (2 * w - 4))

theorem near_trace {W : Addr} {L w : Nat} {q : BitVec 32} (width : 4 ≤ w) (bound : w ≤ 64)
    (space : slot w 5 ≤ L) :
    RelCT isa (fun s t => Base W L w q s ∧ Base W L w q t) near (fun _ _ => True) := by
  have fit : slot w 2 + 8 * w ≤ L := by unfold slot stride VG.Impl.Bignum.hdrBytes at space ⊢; omega_using [space]
  unfold near orScan
  have setup := seg (X := Base W L w q) (Y := Scanning W L w q)
    (c := .block ([.mov .ebx (.imm 0)] ++ lenPtr .ebp .edx 2 ++
      [.mov .ecx (.mem (sc 4)), .shift .shr .ecx 2, .alu .sub .ecx (.imm 4)]))
    [.esp, .edi] (regs W q fun _ => 0) (fun s S => S.vals _) (rawBlock (by decide +kernel)) fun s S =>
      WP.mono (orScanSetup_ok S.1) fun u ⟨P, cnt, zero, _, K⟩ =>
        ⟨S.1.ws.of_keeps K, (K.1 .esp (by decide)).trans S.2, P, cnt, zero⟩
  have loop := seg (X := Scanning W L w q) (Y := Scanned W L w q)
    (c := .loop (.block [.alu .or .ebx (.mem (at_ .ebp 0)), .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 1)]) .ne)
    [.esp, .ebp, .ecx]
    (fun r => if r = .esp then q else if r = .ebp then BitVec.ofNat 32 (W.toNat + slot w 2)
      else BitVec.ofNat 32 (2 * w - 4)) (fun u U => by
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl
      · exact U.sp
      · exact ptr_value U.ptr
      · change u.gpr .ecx = BitVec.ofNat 32 (2 * w - 4)
        apply BitVec.eq_of_toNat_eq
        rw [U.count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [bound])]) orLoop_raw fun u U =>
      WP.mono (orLoop_ok U.ws (by omega_using [width]) (by omega_using [fit]) U.ptr U.count U.zero) fun t ⟨_, _, P, K⟩ =>
        ⟨U.ws.of_keeps K, (K.1 .esp (by decide)).trans U.sp, P⟩
  have last := seg (X := Scanned W L w q) (Y := fun _ => True) (c := .block (top ++ VG.Impl.RsaKeyGen.X86.Near.finish))
    [.esp, .ebp] (fun r => if r = .esp then q else BitVec.ofNat 32 (W.toNat + (slot w 2 + 4 * (2 * w - 4))))
    (fun u U => by
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · exact U.sp
      · exact ptr_value U.ptr) (rawBlock (by decide +kernel)) fun u U =>
      WP.block_append (WP.mono (topAt_ok U.ws U.ptr (by omega_using [width, fit])) fun b ⟨C, _⟩ =>
        WP.mono (VG.Proof.RsaKeyGen.X86.Near.finish_ok b (by rw [C]; exact VG.Proof.RsaKeyGen.X86.Near.nibble_bound _))
          fun _ _ => trivial)
  exact (RelCT.seq (RelCT.seq setup loop) last).mono (fun _ _ h => h) (fun _ _ _ => trivial)

/-- The workspace pointer saved at the bottom of the distance check's frame. -/
theorem frameStore_ok {W : Addr} {L w : Nat} {q : BitVec 32} {s : State} (B : Base W L w q s)
    (fit : 40 ≤ q.toNat) (separateStack : q.toNat ≤ W.toNat ∨ W.toNat + L + 40 ≤ q.toNat) :
    WP isa (.block [.store (at_ .esp 0) .edi]) (allocFrame 20 s) (Framed W L w (q - 20#32)) := by
  have Sb := B.1
  have spB := B.2
  have nowrap := Sb.scratch.nowrap
  have head := Sb.header
  have St := FilterStack.allocated_context (s := s) (by rw [spB]; omega_using [fit])
  rw [spB] at St
  have apartQ : (⟨W, L⟩ : Region).Disjoint ⟨(q - 20#32).setWidth 64, 20⟩ := by
    have H := FilterStack.allocated_apart (s := s) (bytes := 20) (by rw [spB]; omega_using [fit]) nowrap
      (by rw [spB]; rcases separateStack with h | h; exact Or.inl h; exact Or.inr (by omega_using [h]))
    rw [spB] at H
    exact H
  have Sc : Space W L w (allocFrame 20 s) :=
    ⟨FilterStack.allocated_scratch Sb.scratch (by rw [spB]; omega_using [fit])
      (by rw [spB]; rcases separateStack with h | h; exact Or.inl h; exact Or.inr (by omega_using [h])),
      Sb.width, Sb.widthBound, Sb.space, Sb.len⟩
  refine WP.mono (St.store 0 (by decide) .edi) fun c ⟨Mc, Oc, Kc, Stc⟩ => ?_
  have Fc := VG.Proof.Bignum.outside_frame Oc (by decide)
  have Wc : VG.Proof.MillerRabin.X86.WorkspaceFrame ⟨W, L, w⟩ [] (allocFrame 20 s).mem c.mem :=
    VG.Proof.RsaKeyGen.X86.workspace_of_frame (g := ⟨W, L, w⟩) Fc nowrap (by
      intro r mem
      obtain rfl := List.mem_singleton.mp mem
      exact apartQ.sub_right (Offset.sub_base _ (by decide)))
  refine ⟨Sc.keep Kc (by decide) (by decide) (Wc.read32 (d := 4) (by change 4 + 4 ≤ L; omega_using [head]) (fun _ mem => nomatch mem)),
    Stc, apartQ, ?_⟩
  rw [Mc, Mem.readW_writeW_self32, allocFrame_gpr _ _ (by decide), Sb.edi_value]

theorem other_trace {W : Addr} {L w : Nat} {q p : BitVec 32} (width : 4 ≤ w) (bound : w ≤ 64)
    (space : slot w 5 ≤ L) (fit : 40 ≤ q.toNat)
    (separateStack : q.toNat ≤ W.toNat ∨ W.toNat + L + 40 ≤ q.toNat) :
    RelCT isa (fun s t => OtherIn W L w q p s ∧ OtherIn W L w q p t) other (fun _ _ => True) := by
  unfold other
  have source := seg (X := OtherIn W L w q p) (Y := SourceIn W L w q p) (c := .block [.mov .esi (.mem (sc 20))])
    [.esp, .edi] (regs W q fun _ => 0) (fun s S => S.base.vals _) (rawBlock (by decide +kernel)) fun s S => by
      have head := S.base.1.header
      refine wp_movS (readSrc_sc S.base.1.scratch (d := 20) (by omega_using [head])) fun t T _ => WP.block_nil ?_
      refine ⟨⟨S.base.1.keepMem T.keeps (by decide) (by decide) T.mem, (T.other .esp (by decide)).trans S.base.2⟩,
        T.gpr.trans S.pointer, S.sourceFit, by rw [T.keeps.2.1, T.keeps.2.2]; exact S.readable, S.separate⟩
  have f4 : slot w 4 + 8 * w ≤ L := by unfold slot stride VG.Impl.Bignum.hdrBytes at space ⊢; omega_using [space]
  have store := seg (X := fun a => ∃ s, Base W L w q s ∧ a = allocFrame 20 s) (Y := Framed W L w (q - 20#32))
    (c := .block [.store (at_ .esp 0) .edi]) [.esp, .edi] (regs W (q - 20#32) fun _ => 0) (fun a ⟨s, S, e⟩ => by
      subst e
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · rw [allocFrame_esp, S.2]; rfl
      · rw [allocFrame_gpr _ _ (by decide)]; exact S.1.edi_value) (rawBlock (by decide +kernel))
    fun a ⟨s, S, e⟩ => by subst e; exact frameStore_ok S fit separateStack
  refine RelCT.seq source (RelCT.seq (importAt_trace 4 (by decide) f4
    (by unfold slot stride VG.Impl.Bignum.hdrBytes; omega_using []) (by decide +kernel)) ?_)
  refine RelCT.frameAlloc (R := fun _ _ => True) ?_
  refine (RelCT.seq store (RelCT.seq difference_trace ((near_trace width bound space).mono
    (fun _ _ ⟨U, Z⟩ => ⟨U.base, Z.base⟩) (fun _ _ h => h)))).mono ?_ (fun _ _ h => h)
  rintro a b ⟨s₁, s₂, ⟨S₁, S₂⟩, e₁, e₂⟩
  exact ⟨⟨s₁, S₁, e₁⟩, ⟨s₂, S₂, e₂⟩⟩

theorem close_trace {W : Addr} {L w : Nat} {q p plen : BitVec 32} (width : 4 ≤ w) (bound : w ≤ 64)
    (space : slot w 5 ≤ L) (fit : 40 ≤ q.toNat)
    (separateStack : q.toNat ≤ W.toNat ∨ W.toNat + L + 40 ≤ q.toNat) :
    RelCT isa (fun s t => CloseIn W L w q p plen s ∧ CloseIn W L w q p plen t) close (fun _ _ => True) := by
  unfold close
  have check := seg (X := CloseIn W L w q p plen)
    (Y := fun u => CloseIn W L w q p plen u ∧ isa.eval .e u = some (decide (plen = 0#32)))
    (c := .block [.mov .eax (.mem (sc 24)), .alu .cmp .eax (.imm 0)]) [.esp, .edi] (regs W q fun _ => 0)
    (fun s S => S.base.vals _) (rawBlock (by decide +kernel)) fun s S => by
      have head := S.base.1.header
      refine wp_movS (readSrc_sc S.base.1.scratch (d := 24) (by omega_using [head])) fun a A _ =>
        wp_cmpS rfl fun b B Z => WP.block_nil ?_
      have K : Keeps [.eax] s b := A.keeps.widen (B.keeps [])
      have M : b.mem = s.mem := B.mem.trans A.mem
      refine ⟨⟨⟨S.base.1.keepMem K (by decide) (by decide) M, (K.1 .esp (by decide)).trans S.base.2⟩,
        by rw [M]; exact S.pointer, by rw [M]; exact S.length,
        fun h => by rw [K.2.1, K.2.2]; exact S.source h⟩, ?_⟩
      change b.zf = _
      rw [Z, A.gpr, S.length]
      change some (plen - 0#32 == 0#32) = _
      rw [BitVec.sub_zero]
      rfl
  refine RelCT.seq check (VG.RelCT.ite (fun _ _ ⟨U, Z⟩ => U.2.trans Z.2.symm) ?_ ?_)
  · exact (rawBlock (rs := []) (by decide +kernel)).mono (fun _ _ _ => agree_regs (by intro r mem; cases mem))
      (fun _ _ h => h)
  · refine (other_trace (p := p) width bound space fit separateStack).mono ?_ (fun _ _ h => h)
    rintro u z ⟨⟨⟨U, cu⟩, ⟨Z, _⟩⟩, no⟩
    rw [cu] at no
    have nonzero : plen ≠ 0#32 := fun h => by simp [h] at no
    obtain ⟨fu, ru, su⟩ := U.source nonzero
    obtain ⟨fz, rz, sz⟩ := Z.source nonzero
    exact ⟨⟨U.base, U.pointer, fu, ru, su⟩, ⟨Z.base, Z.pointer, fz, rz, sz⟩⟩

end VG.Proof.RsaKeyGen.X86.FrontRt

end

end

/-! ### `RsaKeyGen.X86.CandidateSieveLeak`, which only this module used -/

section

/-! # Rejected-candidate leakage permits the sieve pattern and passing candidates hide their values -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.Proof.RsaKeyGen

theorem candidate_op_composite {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte}
    (enough : E.length ≤ entropy.length)
    (close : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E entropy) = false)
    (composite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy) = true) :
    Spec.RsaKeyGen.candidateOp E.length eBytes pBytes entropy = some (.rejected, entropy.drop E.length) := by
  unfold Spec.RsaKeyGen.candidateOp
  rw [candidateStep_eq E.length _ _ _ (by have := v.length; unfold Spec.RsaKeyGen.primeLenValid at this; omega_using [this]), ite_t enough]
  change afterDraw (8 * E.length) (Spec.Rsa.os2ip eBytes) (Spec.RsaKeyGen.otherPrime pBytes)
    (candidateValue E entropy) (entropy.drop E.length) = _
  simp only [afterDraw, close, composite, Bool.false_eq_true, Bool.not_true, Bool.false_and, ↓reduceIte]

theorem composite_candidates_eq {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (rEnough : E.length ≤ rBytes.length) (sEnough : E.length ≤ sBytes.length)
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes)
    (rClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes) = false)
    (sClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime qBytes) (candidateValue E sBytes) = false)
    (rComposite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes) = true)
    (sComposite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E sBytes) = true) :
    candidateValue E rBytes = candidateValue E sBytes := by
  unfold SameLeak at leak
  rw [candidateLeak_eq, candidateLeak_eq, candidate_op_composite v rEnough rClose rComposite,
    candidate_op_composite v sEnough sClose sComposite] at leak
  have rCount : rBytes.length - (rBytes.drop E.length).length = E.length := by rw [List.length_drop]; omega_using [rEnough]
  have sCount : sBytes.length - (sBytes.drop E.length).length = E.length := by rw [List.length_drop]; omega_using [sEnough]
  change 3 :: (rBytes.take (rBytes.length - (rBytes.drop E.length).length)).map (·.toNat) =
    3 :: (sBytes.take (sBytes.length - (sBytes.drop E.length).length)).map (·.toNat) at leak
  rw [rCount, sCount] at leak
  have bytes := map_toNat_inj (List.cons.inj leak).2
  unfold candidateValue
  rw [bytes]

theorem sieve_pattern {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (rEnough : E.length ≤ rBytes.length) (sEnough : E.length ≤ sBytes.length)
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes)
    (rClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes) = false)
    (sClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime qBytes) (candidateValue E sBytes) = false)
    (same : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes) =
      Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E sBytes)) :
    Sieve.SamePattern E.sieveGeometry (candidateValue E rBytes) (candidateValue E sBytes) := by
  cases composite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes)
  · have right := same.symm.trans composite
    have left := composite
    have bits : 64 * E.sieveGeometry.w = 8 * E.length := by change 64 * E.width = _; have := v.length_eq; omega_using [this]
    apply Sieve.samePattern_passing rfl (candidate_large v rBytes) (candidate_large v sBytes)
    · rw [bits]; exact left
    · rw [bits]; exact right
  · rw [composite_candidates_eq v rEnough sEnough leak rClose sClose composite (same.symm.trans composite)]
    exact Sieve.samePattern_refl _ _

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! # The candidate drawn and filtered at its run-time width hides the filtered values -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateSieveStageTiming.lean`, which only this module imported.
section

/-! # The shared leak controls sieve rejection and the complete remaining candidate path -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Proof.RsaKeyGen

/-- After the code for the width: both runs wrote the same status, or both go
on with `eax = 4`, the drawn candidates neither too close nor divisible. -/
def FrontPair (E : Environment) (eBytes pBytes qBytes rBytes sBytes : List Byte) (s t : State) : Prop :=
  (s.gpr .eax = t.gpr .eax ∧ s.gpr .eax ≠ 4) ∨
  (s.gpr .eax = 4 ∧ t.gpr .eax = 4 ∧ DrawnPair E eBytes pBytes qBytes rBytes sBytes s t ∧
    Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes) = false ∧
    Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime qBytes) (candidateValue E sBytes) = false ∧
    Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes) = false ∧
    Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E sBytes) = false)

/-- A status written by both runs. -/
theorem drawn_done_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (status : Nat) (small : status < 4) :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.CandidateFinish.used status) (FrontPair E eBytes pBytes qBytes rBytes sBytes) := by
  refine ((drawn_used_trace v status).wp (F₁ := fun (u : State) => u.gpr .eax = BitVec.ofNat 32 status)
    (F₂ := fun (u : State) => u.gpr .eax = BitVec.ofNat 32 status) fun s t P =>
    ⟨WP.mono (finish_used_ok (status := status) v (P.left.finishReady v)) fun _ H => H.1.1,
      WP.mono (finish_used_ok (status := status) v (P.right.finishReady v)) fun _ H => H.1.1⟩).mono
    (fun _ _ P => P) ?_
  rintro u z ⟨_, U, Z⟩
  refine Or.inl ⟨U.trans Z.symm, ?_⟩
  rw [U]
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by omega_using [small])] at this
  change status = 4 at this
  omega_using [small, this]

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/FrontRt/SieveTiming.lean`, which only this module imported.
section

/-! # Trial division at the run-time width releases only the trial divisors' pattern -/

section
namespace VG.Proof.RsaKeyGen.X86.FrontRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Proof.RsaKeyGen.X86.Sieve
open VG.Impl.RsaKeyGen.X86.FrontRt
open VG.Impl.RsaKeyGen.X86.Sieve (tableCount tableAddress stackSlots)

theorem enter_ok {g : Geometry} {c : Nat} {s : State} (S : SieveIn g c s) :
    WP isa (.block [.mov .edx (.mem (VG.Impl.Mont.X86.sc 4)), .alu .add .edi (.imm 256)]) s (BodyIn g c) := by
  obtain ⟨C, pointer, symbol, lenRead⟩ := S
  refine wp_movS lenRead fun a A _ => wp_addS rfl fun b B _ => WP.block_nil ?_
  have Kb : Keeps [.edx, .edi] s b := (A.keeps.mono (by decide)).widen B.keeps
  have Mb : b.mem = s.mem := B.mem.trans A.mem
  refine ⟨⟨C.stack.keep Kb (by decide), ?_, ?_, ?_, ?_⟩, by rw [B.gpr, A.other .edi (by decide)]; exact pointer,
    by rw [B.other .edx (by decide), A.gpr], by rw [B.syms, A.syms]; exact symbol⟩
  · intro i index; rw [Kb.2.1, Kb.2.2]; exact C.candidateRead i index
  · intro i index d mem; rw [Kb.2.1, Kb.2.2]; exact C.tableRead i index d mem
  · intro i index; rw [Mb]; exact C.tableWords i index
  · rw [Mb]; exact C.candidateValue

theorem enter_trace {g : Geometry} {c d : Nat} :
    RelCT isa (fun s t => SieveIn g c s ∧ SieveIn g d t)
      (.block [.mov .edx (.mem (VG.Impl.Mont.X86.sc 4)), .alu .add .edi (.imm 256)])
      (fun u z => BodyIn g c u ∧ BodyIn g d z) := by
  intro s t tr ur u z ⟨S, T⟩ E G
  have A : VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
    apply agree_regs
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact S.1.stack.sp.trans T.1.stack.sp.symm
    · have H := congrArg (fun x : BitVec 32 => x - 256#32) (S.2.1.trans T.2.1.symm)
      simpa only [BitVec.add_sub_cancel] using H
  exact ⟨((rawBlock (rs := [.esp, .edi]) (by decide +kernel)) _ _ _ _ _ _ A E G).1,
    wp_result (enter_ok S) E, wp_result (enter_ok T) G⟩

theorem setup_trace {g : Geometry} (v : g.Valid) {c d : Nat} (low : 4 ≤ g.sp.toNat)
    (length : g.limit = tableCount g.w) (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) :
    RelCT isa (fun s t => BodyIn g c s ∧ BodyIn g d t)
      (.seq (.block candidateSlots) (.seq tableAddress (.block tableSlots)))
      (fun s t => StateAt g c 0 g.limit s ∧ StateAt g d 0 g.limit t) := by
  have first : RelCT isa (fun s t => BodyIn g c s ∧ BodyIn g d t) (.block candidateSlots)
      (fun s t => s.gpr .esp = g.sp ∧ t.gpr .esp = g.sp) := by
    intro s t tr ur u z ⟨S, T⟩ E G
    have A : VG.X86.Taint.Agree (τr [.esp]) s t :=
      agree_regs (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact S.1.stack.sp.trans T.1.stack.sp.symm)
    have trace := ((rawBlock (rs := [.esp]) (code := candidateSlots) (by decide +kernel)) _ _ _ _ _ _ A E G).1
    have U := wp_result (candidateSlots_ok v S.1 S.2.1 S.2.2.1) E
    have Z := wp_result (candidateSlots_ok v T.1 T.2.1 T.2.2.1) G
    exact ⟨trace, U.1.context.stack.sp, Z.1.context.stack.sp⟩
  have middle : RelCT isa (fun s t => s.gpr .esp = g.sp ∧ t.gpr .esp = g.sp)
      tableAddress (VG.X86.Taint.Agree (τr [.esp])) := by
    intro s t tr ur u z ⟨S, T⟩ E G
    have Ls : 4 ≤ (s.gpr .esp).toNat := by rw [S]; exact low
    have Lt : 4 ≤ (t.gpr .esp).toNat := by rw [T]; exact low
    have U := wp_result (symFrame_ok VG.Impl.RsaKeyGen.TrialTable32.symbol s Ls) E
    have Z := wp_result (symFrame_ok VG.Impl.RsaKeyGen.TrialTable32.symbol t Lt) G
    refine ⟨?_, agree_regs (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact
      (U.gpr .esp (by decide)).trans (S.trans (T.symm.trans (Z.gpr .esp (by decide)).symm)))⟩
    rw [symFrame_trace Ls E, symFrame_trace Lt G, S, T]
  have raw : RelCT isa (fun s t => BodyIn g c s ∧ BodyIn g d t)
      (.seq (.block candidateSlots) (.seq tableAddress (.block tableSlots))) (fun _ _ => True) :=
    RelCT.seq first (RelCT.seq middle (rawBlock (by decide +kernel)))
  intro s t tr ur u z ⟨S, T⟩ E G
  exact ⟨(raw _ _ _ _ _ _ ⟨S, T⟩ E G).1,
    (wp_result (setup_ok v S.1 S.2.1 S.2.2.1 length S.2.2.2 low candidateFar tableFar) E).1,
    (wp_result (setup_ok v T.1 T.2.1 T.2.2.1 length T.2.2.2 low candidateFar tableFar) G).1⟩

theorem body_trace {g : Geometry} (v : g.Valid) {c d : Nat} (pattern : SamePattern g c d)
    (length : g.limit = tableCount g.w) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) :
    RelCT isa (fun s t => BodyIn g c s ∧ BodyIn g d t) sieveBody (VG.X86.Taint.Agree (τr [.esp])) := by
  have setup := setup_trace (c := c) (d := d) v low length candidateFar tableFar
  intro s t tr ur u z H E G
  cases E with
  | seq A E =>
    cases E with
    | seq B E =>
      cases E with
      | seq C L =>
        cases G with
        | seq D G =>
          cases G with
          | seq F G =>
            cases G with
            | seq K N =>
              have R := RelCT.seq setup (loop_trace v pattern) _ _ _ _ _ _ H
                (.seq (.seq A (.seq B C)) L) (.seq (.seq D (.seq F K)) N)
              simpa only [List.append_assoc] using R

theorem sieve_trace {g : Geometry} (v : g.Valid) {c d : Nat} (pattern : SamePattern g c d)
    (length : g.limit = tableCount g.w) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) :
    RelCT isa (fun s t => SieveIn g c (allocFrame 20 s) ∧ SieveIn g d (allocFrame 20 t)) sieve (fun _ _ => True) := by
  unfold sieve
  apply RelCT.frameAlloc
  refine (RelCT.seq enter_trace (RelCT.seq (body_trace v pattern length low candidateFar tableFar)
    (rawBlock (by decide +kernel)))).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, H, rfl, rfl⟩
  exact H

end VG.Proof.RsaKeyGen.X86.FrontRt
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Proof.RsaKeyGen

structure ClearedPair (E : Environment) (eBytes pBytes qBytes rBytes sBytes : List Byte) (s t : State) : Prop
    extends InputPair E eBytes pBytes qBytes rBytes sBytes s t where
  zerosLeft : Spec.Rsa.bytesAt s.mem (E.out.setWidth 64) E.length = List.replicate E.length 0
  zerosRight : Spec.Rsa.bytesAt t.mem (E.out.setWidth 64) E.length = List.replicate E.length 0

theorem load_rt_pair_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (enough : E.length ≤ E.randLength) :
    RelCT isa (ClearedPair E eBytes pBytes qBytes rBytes sBytes) VG.Impl.RsaKeyGen.X86.FrontRt.load
      (DrawnPair E eBytes pBytes qBytes rBytes sBytes) := by
  intro s t tr ur u z P A B
  have five := v.slotFit (j := 5) (by decide)
  have trace := (FrontRt.load_trace v.width_bounds.1 (by omega_using [five]) _ _ _ _ _ _
    ⟨P.left.loadIn v enough, P.right.loadIn v enough⟩ A B).1
  obtain ⟨DU, _, _⟩ := wp_result (load_rt_ok v P.left P.zerosLeft enough) A
  obtain ⟨DZ, _, _⟩ := wp_result (load_rt_ok v P.right P.zerosRight enough) B
  exact ⟨trace, DU, DZ⟩

theorem close_rt_pair_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (same : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes) =
      Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime qBytes) (candidateValue E sBytes)) :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes) VG.Impl.RsaKeyGen.X86.FrontRt.close
      (WithFlag (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
        (Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes))) := by
  intro s t tr ur u z P A B
  have five := v.slotFit (j := 5) (by decide)
  have trace := (FrontRt.close_trace v.width_bounds.1 v.width_bounds.2 (by omega_using [five]) (by have := v.low; omega_using [this])
    v.stackApart _ _ _ _ _ _ ⟨P.left.closeIn v, P.right.closeIn v⟩ A B).1
  obtain ⟨DU, flagU, _, _⟩ := wp_result (close_rt_ok v P.left) A
  obtain ⟨DZ, flagZ, _, _⟩ := wp_result (close_rt_ok v P.right) B
  exact ⟨trace, ⟨DU, DZ⟩, flagU, by rw [same]; exact flagZ⟩

theorem sieve_rt_pair_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (pattern : Sieve.SamePattern E.sieveGeometry (candidateValue E rBytes) (candidateValue E sBytes))
    (same : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes) =
      Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E sBytes)) :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes) VG.Impl.RsaKeyGen.X86.FrontRt.sieve
      (WithFlag (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
        (Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes))) := by
  have privateSub : (below E.sieveGeometry.sp 4).Sub (below E.p 136) := below_inner (by decide) v.low
  have workspaceFar : E.workspaceRegion.Disjoint (below E.p 136) := v.stackFar E.workspaceRegion
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have tableFar : E.tableRegion.Disjoint (below E.p 136) := v.stackFar E.tableRegion
    (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  intro s t tr ur u z P A B
  have trace := (FrontRt.sieve_trace v.sieve_valid pattern rfl
    (by change 4 ≤ (E.p - 20#32).toNat; rw [sub_toNat (by have := v.low; omega_using [this])]; have := v.low; omega_using [this])
    ((workspaceFar.sub_left v.sieveCandidateSub).sub_right privateSub) (tableFar.sub_right privateSub)
    _ _ _ _ _ _ ⟨P.left.sieveIn v, P.right.sieveIn v⟩ A B).1
  obtain ⟨DU, flagU, _, _⟩ := wp_result (sieve_rt_ok v P.left) A
  obtain ⟨DZ, flagZ, _, _⟩ := wp_result (sieve_rt_ok v P.right) B
  exact ⟨trace, ⟨DU, DZ⟩, flagU, by rw [same]; exact flagZ⟩

theorem sieve_front_rt_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (rEnough : E.length ≤ rBytes.length)
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes)
    (rClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes) = false)
    (sClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime qBytes) (candidateValue E sBytes) = false) :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
      (.seq VG.Impl.RsaKeyGen.X86.FrontRt.sieve (.seq (.block [.alu .cmp .eax (.imm 0)])
        (.ite .ne (VG.Impl.RsaKeyGen.X86.CandidateFinish.used 3) (.block [.mov .eax (.imm 4)]))))
      (FrontPair E eBytes pBytes qBytes rBytes sBytes) := by
  have schedules := schedule_eq v length rEnough leak
  have same : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes) =
      Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E sBytes) := by
    have H := congrArg Sched.comp schedules
    rw [schedule_composite rClose, schedule_composite sClose] at H
    exact H
  have pattern := sieve_pattern v rEnough (by rw [← length]; exact rEnough) leak rClose sClose same
  have initialTrace := sieve_rt_pair_trace (eBytes := eBytes) (pBytes := pBytes) (qBytes := qBytes) v pattern same
  cases composite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes)
  · have right := same.symm.trans composite
    rw [composite] at initialTrace
    refine RelCT.seq initialTrace (RelCT.seq ((cmp_flag_trace false (fun _ _ _ _ P U Z => P.keepFlags v U Z)).mono
      (fun _ _ P => P) (fun _ _ P => P.2)) (branch_false ?_))
    have raw : RelCT isa (VG.X86.Taint.Agree (τr [])) (.block [.mov .eax (.imm 4)]) (VG.X86.Taint.Agree (τr [])) :=
      checkedBlockInvariant rfl rfl
    have four {e p r : List Byte} {x : State} (D : Drawn E e p r x) :
        WP isa (.block [.mov .eax (.imm 4)]) x fun u => u.gpr .eax = 4 ∧ Drawn E e p r u :=
      wp_movS rfl fun u U _ => WP.block_nil ⟨U.gpr, D.keepMem v U.mem U.keeps (by decide) (by decide) U.syms⟩
    refine ((raw.mono (fun _ _ _ => agree_regs (by intro r mem; cases mem)) (fun _ _ _ => trivial)).wp
      (fun _ _ P => ⟨four P.left, four P.right⟩)).mono (fun _ _ P => P) ?_
    rintro u z ⟨_, ⟨U, DU⟩, ⟨Z, DZ⟩⟩
    exact Or.inr ⟨U, Z, ⟨DU, DZ⟩, rClose, sClose, composite, right⟩
  · rw [composite] at initialTrace
    refine RelCT.seq initialTrace (RelCT.seq ((cmp_flag_trace true (fun _ _ _ _ P U Z => P.keepFlags v U Z)).mono
      (fun _ _ P => P) (fun _ _ P => P.2)) ?_)
    exact branch_true (drawn_done_trace v 3 (by decide))

theorem front_rt_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (rEnough : E.length ≤ rBytes.length) (enough : E.length ≤ E.randLength)
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes) :
    RelCT isa (ClearedPair E eBytes pBytes qBytes rBytes sBytes)
      VG.Impl.RsaKeyGen.X86.FrontRt.code (FrontPair E eBytes pBytes qBytes rBytes sBytes) := by
  have schedules := schedule_eq v length rEnough leak
  have same : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes) =
      Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime qBytes) (candidateValue E sBytes) := by
    have H := congrArg Sched.close schedules
    rw [schedule_close, schedule_close] at H
    exact H
  have initialTrace := close_rt_pair_trace (eBytes := eBytes) v same
  unfold VG.Impl.RsaKeyGen.X86.FrontRt.code
  refine RelCT.seq (load_rt_pair_trace v enough) ?_
  cases close : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes)
  · rw [close] at initialTrace
    refine RelCT.seq initialTrace (RelCT.seq ((cmp_flag_trace false (fun _ _ _ _ P U Z => P.keepFlags v U Z)).mono
      (fun _ _ P => P) (fun _ _ P => P.2)) ?_)
    exact branch_false (sieve_front_rt_trace v length rEnough leak close (same.symm.trans close))
  · rw [close] at initialTrace
    refine RelCT.seq initialTrace (RelCT.seq ((cmp_flag_trace true (fun _ _ _ _ P U Z => P.keepFlags v U Z)).mono
      (fun _ _ P => P) (fun _ _ P => P.2)) ?_)
    exact branch_true (drawn_done_trace v 2 (by decide))

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! # Public width comparisons retain the candidate's input relation -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Dsa.X86

theorem ClearedPair.keepMem {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    {s t u z : State} (P : ClearedPair E eBytes pBytes qBytes rBytes sBytes s t)
    (MU : u.mem = s.mem) (MZ : z.mem = t.mem) {regs : List Reg} (KU : Keeps regs s u) (KZ : Keeps regs t z)
    (base : .edi ∉ regs) (sp : .esp ∉ regs) (SU : u.syms = s.syms) (SZ : z.syms = t.syms) :
    ClearedPair E eBytes pBytes qBytes rBytes sBytes u z := by
  refine ⟨⟨P.left.keepMem v MU KU base sp SU, P.right.keepMem v MZ KZ base sp SZ⟩, ?_, ?_⟩
  · rw [MU]; exact P.zerosLeft
  · rw [MZ]; exact P.zerosRight

end VG.Proof.RsaKeyGen.X86.Candidate
