module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Trial
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialPointer
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! ### `RsaKeyGen.X86.TrialReadControl`, which this module and modules that import it used -/

section

/-! # Only pointers and the fixed word count control a single divisor's trace -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/TrialControl.lean`, which only this module imported.
section

/-! # Trial-reduction pointer control is independent of candidate arithmetic -/

section
namespace VG.Proof.RsaKeyGen.X86.Trial
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Trial

theorem wordStep_control (s : State) (endOffset : Nat) (endPtr : BitVec 32)
    (candidateRead : InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) 0) 4)
    (endRead : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) endOffset) 4)
    (endValue : s.mem.readW (addr (s.gpr .esp) endOffset) 32 = endPtr) :
    WP isa (.block (wordStep endOffset)) s fun t => t.mem = s.mem ∧
      Keeps [.eax, .edx, .ecx, .ebp, .edi] s t ∧ t.gpr .edi = s.gpr .edi + 4 ∧
      t.zf = some (s.gpr .edi + 4 - endPtr == 0) := by
  unfold wordStep
  rw [WP.block_append_iff, WP.block_append_iff]
  refine wp_movS (readSrc_mem rfl candidateRead) fun a A _ => WP.block_nil ?_
  refine WP.mono (redc32_code a) fun b ⟨M, K, _⟩ => ?_
  have Kb : Keeps [.eax, .edx, .ecx, .ebp] s b := (A.keeps.mono (by decide)).trans K
  have Mb : b.mem = s.mem := M.trans A.mem
  refine wp_addS rfl fun c C _ => ?_
  have Kc : Keeps [.eax, .edx, .ecx, .ebp, .edi] s c := (Kb.mono (by decide)).trans (C.keeps.mono (by decide))
  have Mc : c.mem = s.mem := C.mem.trans Mb
  have read : readSrc c (.mem ⟨.esp, endOffset⟩) = some endPtr := by
    have ptr := Kc.1 .esp (by decide)
    have readable : InRegions (c.rd ++ c.wr) (addr (c.gpr .esp) endOffset) 4 := by
      rw [Kc.2.1, Kc.2.2, ptr]
      exact endRead
    have raw := readSrc_mem rfl readable
    rw [Mc, ptr, endValue] at raw
    exact raw
  refine wp_cmpS read fun t T Z => WP.block_nil ?_
  have Kt : Keeps [.eax, .edx, .ecx, .ebp, .edi] s t := Kc.trans (T.keeps _)
  have ptr : c.gpr .edi = s.gpr .edi + 4 := by rw [C.gpr, Kb.1 .edi (by decide)]
  refine ⟨T.mem.trans Mc, Kt, (congrFun T.gpr .edi).trans ptr, ?_⟩
  rw [ptr] at Z
  exact Z

end VG.Proof.RsaKeyGen.X86.Trial
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

structure ReadControl (g : Geometry) (j : Nat) (s : State) : Prop where
  stack : StackContext g.sp s
  candidateRead : ∀ k < 2 * g.w, InRegions (s.rd ++ s.wr) (off (g.candidate.setWidth 64) (4 * k)) 4
  ending : s.mem.readW (off (g.sp.setWidth 64) 4) 32 = g.ending
  pointer : s.gpr .edi = g.candidate + BitVec.ofNat 32 (4 * j)

theorem ReadControl.agree {g : Geometry} {j : Nat} {s t : State}
    (S : ReadControl g j s) (T : ReadControl g j t) : VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
  apply agree_regs
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact S.stack.sp.trans T.stack.sp.symm
  · exact S.pointer.trans T.pointer.symm

theorem StateAt.readControl {g : Geometry} {c i q : Nat} {s : State}
    (S : StateAt g c i q s) (pointer : s.gpr .edi = g.candidate) : ReadControl g 0 s := by
  refine ⟨S.context.stack, S.context.candidateRead, S.ending, ?_⟩
  simpa only [Nat.mul_zero, show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero] using pointer

theorem ReadControl.step_bounded {g : Geometry} (widthBound : g.w ≤ 128)
    (candidateFit : g.candidate.toNat + 8 * g.w ≤ 2 ^ 32) {j : Nat} {s : State}
    (S : ReadControl g j s) (index : j < 2 * g.w) :
    WP isa (.block (VG.Impl.RsaKeyGen.X86.Trial.wordStep 4)) s fun t =>
      ReadControl g (j + 1) t ∧ t.zf = some (decide (j + 1 = 2 * g.w)) := by
  have read : InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) 0) 4 := by
    rw [S.pointer, Trial.word_address g.candidate (by omega_using [candidateFit]) index]
    exact S.candidateRead j index
  have ending : s.mem.readW (addr (s.gpr .esp) 4) 32 = g.ending := by
    change s.mem.readW (s.ea (VG.Impl.RsaKeyGen.X86.Sieve.slot 4)) 32 = _
    rw [S.stack.address 4 (by decide)]
    exact S.ending
  refine WP.mono (Trial.wordStep_control s 4 g.ending read (S.stack.access 4 (by decide)) ending)
    fun t ⟨M, K, P, Z⟩ => ?_
  have next : t.gpr .edi = g.candidate + BitVec.ofNat 32 (4 * (j + 1)) := by
    rw [P, S.pointer, BitVec.add_assoc]
    change g.candidate + (BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 4) = _
    rw [← BitVec.ofNat_add]
    congr 2 <;> omega
  refine ⟨⟨S.stack.keep K (by decide), ?_, ?_, next⟩, ?_⟩
  · intro k bound
    rw [K.2.1, K.2.2]
    exact S.candidateRead k bound
  · rw [M]; exact S.ending
  · rw [Z, S.pointer]
    have pointer : g.candidate + BitVec.ofNat 32 (4 * j) + 4 = g.candidate + BitVec.ofNat 32 (4 * (j + 1)) := by
      rw [BitVec.add_assoc]
      change g.candidate + (BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 4) = _
      rw [← BitVec.ofNat_add]
      congr 2 <;> omega
    rw [pointer]
    rw [Geometry.ending, show 8 * g.w = 4 * (2 * g.w) by omega_using []]
    rw [Trial.pointer_zf g.candidate (by omega_using [widthBound]) index]

end VG.Proof.RsaKeyGen.X86.Sieve

end

end

/-! # Every divisor scans a fixed public number of candidate words -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.Trial

theorem wordStep_trace : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block (wordStep 4))
    (VG.X86.Taint.Agree (τr [.esp, .edi])) := checkedBlockInvariant rfl rfl

theorem wordLoop_trace_bounded {g : Geometry} (positive : 0 < g.w) (widthBound : g.w ≤ 128)
    (candidateFit : g.candidate.toNat + 8 * g.w ≤ 2 ^ 32) :
    RelCT isa (fun s t => ReadControl g 0 s ∧ ReadControl g 0 t)
      (words 4) (VG.X86.Taint.Agree (τr [.esp, .edi])) := by
  unfold words
  refine (RelCT.loop (M := isa) (body := .block (wordStep 4)) (c := .ne)
    (I := fun q s t => ∃ j, q = 2 * g.w - j ∧ j < 2 * g.w ∧ ReadControl g j s ∧ ReadControl g j t)
    (Q := VG.X86.Taint.Agree (τr [.esp, .edi])) ?_ (2 * g.w)).mono
    (fun _ _ H => ⟨0, rfl, by omega_using [positive], H⟩) (fun _ _ H => H)
  rintro q s t tr ur u z ⟨j, rfl, index, S, T⟩ E G
  obtain ⟨trace, _⟩ := wordStep_trace _ _ _ _ _ _ (S.agree T) E G
  obtain ⟨U, Zu⟩ := wp_result (S.step_bounded widthBound candidateFit index) E
  obtain ⟨Z, Zz⟩ := wp_result (T.step_bounded widthBound candidateFit index) G
  have eu : isa.eval .ne u = some (!decide (j + 1 = 2 * g.w)) := by
    change u.zf.map Bool.not = _
    rw [Zu]
    rfl
  have ez : isa.eval .ne z = some (!decide (j + 1 = 2 * g.w)) := by
    change z.zf.map Bool.not = _
    rw [Zz]
    rfl
  refine ⟨trace, eu.trans ez.symm, fun _ => U.agree Z, ?_⟩
  intro next
  have more : j + 1 ≠ 2 * g.w := by
    intro done
    rw [eu, decide_eq_true done] at next
    cases next
  exact ⟨2 * g.w - (j + 1), by omega_using [index], j + 1, rfl, by omega_using [index, more], U, Z⟩

theorem wordLoop_trace {g : Geometry} (v : g.Valid) :
    RelCT isa (fun s t => ReadControl g 0 s ∧ ReadControl g 0 t)
      (words 4) (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  wordLoop_trace_bounded v.positive v.widthBound v.candidateFit

theorem finish_trace : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block finish)
    (VG.X86.Taint.Agree (τr [.esp, .edi])) := checkedBlockInvariant rfl rfl

theorem divisor_trace {g : Geometry} (v : g.Valid) :
    RelCT isa (fun s t => ReadControl g 0 s ∧ ReadControl g 0 t)
      (divisor 4) (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  RelCT.seq (wordLoop_trace v) finish_trace

theorem divisor_trace_bounded {g : Geometry} (positive : 0 < g.w) (widthBound : g.w ≤ 128)
    (candidateFit : g.candidate.toNat + 8 * g.w ≤ 2 ^ 32) :
    RelCT isa (fun s t => ReadControl g 0 s ∧ ReadControl g 0 t)
      (divisor 4) (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  RelCT.seq (wordLoop_trace_bounded positive widthBound candidateFit) finish_trace

end VG.Proof.RsaKeyGen.X86.Sieve
