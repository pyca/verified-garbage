module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingInput
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
