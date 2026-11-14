module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingBranch
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingInput
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestTiming
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEnvironment
public import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentTimingInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentClass
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentImport
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks
import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
import VerifiedGarbage.Proof.Bignum.X86.PublicDataTiming
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateExponentInitial
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.SaveTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateExponentInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinOutcome
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateParameters
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePreparedResult
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateResultTiming
import VerifiedGarbage.Proof.RsaKeyGen.CandLeak
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput
import VerifiedGarbage.Proof.MillerRabin.Contract

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
