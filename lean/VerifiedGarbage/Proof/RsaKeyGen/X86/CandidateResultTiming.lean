module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePrimeTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishReady

/-! # Equal released primality statuses select the same finish branch -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Mont.X86

structure StatusPair (E : Environment) (c d : Nat) (s t : State) : Prop extends PrimePair E c d s t where
  status : s.mem.readW (off E.base 168) 32 = t.mem.readW (off E.base 168) 32

def ControlPair (E : Environment) (c d : Nat) (s t : State) : Prop :=
  PrimePair E c d s t ∧ s.gpr .eax = t.gpr .eax ∧ isa.eval .e s = isa.eval .e t

def statusArgs : List Instr := [.mov .eax (.mem (sc 168)), .alu .cmp .eax (.imm 1)]

theorem statusArgs_ok {s : State} {base : Addr} {size : Nat} (S : Scr s base size) (space : 172 ≤ size) :
    WP isa (.block statusArgs) s fun t =>
      t.gpr .eax = s.mem.readW (off base 168) 32 ∧
      isa.eval .e t = some (s.mem.readW (off base 168) 32 - 1#32 == 0#32) ∧ t.mem = s.mem ∧ Keeps [.eax] s t := by
  unfold statusArgs
  refine wp_movS (readSrc_sc S space) fun a A _ => wp_cmpS rfl fun t T Z => WP.block_nil ?_
  refine ⟨(T.keeps []).1 .eax (by decide) |>.trans A.gpr, ?_, T.mem.trans A.mem, A.keeps.widen (T.keeps [])⟩
  change t.zf = _
  rw [Z, A.gpr]
  rfl

theorem statusArgs_trace {E : Environment} (v : E.Valid) {c d : Nat} :
    RelCT isa (StatusPair E c d) (.block statusArgs) (ControlPair E c d) := by
  intro s t tr ur u z P A B
  have space : 172 ≤ E.size := by have H : 256 ≤ E.size := v.geometry.headerFit; omega
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block statusArgs)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := checkedBlockInvariant rfl rfl
  obtain ⟨valueU, flagU, memU, KU⟩ := wp_result (statusArgs_ok P.left.1.scratch space) A
  obtain ⟨valueZ, flagZ, memZ, KZ⟩ := wp_result (statusArgs_ok P.right.1.scratch space) B
  refine ⟨(raw _ _ _ _ _ _ P.toPrimePair.agree A B).1,
    ⟨P.left.keepMem memU KU (by decide) (by decide), P.right.keepMem memZ KZ (by decide) (by decide), ?_⟩,
    valueU.trans (P.status.trans valueZ.symm), ?_⟩
  · rw [KU.1 .esp (by decide), KZ.1 .esp (by decide)]; exact P.stack
  · rw [flagU, flagZ, P.status]

theorem compareZero_ok {s : State} : WP isa (.block [.alu .cmp .eax (.imm 0)]) s fun t =>
    Fupd s t ∧ isa.eval .e t = some (s.gpr .eax - 0#32 == 0#32) :=
  wp_cmpS rfl fun _ T Z => WP.block_nil ⟨T, Z⟩

theorem compareZero_trace {E : Environment} {c d : Nat} :
    RelCT isa (ControlPair E c d) (.block [.alu .cmp .eax (.imm 0)]) (ControlPair E c d) := by
  intro s t tr ur u z P A B
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi, .eax])) (.block [.alu .cmp .eax (.imm 0)])
      (VG.X86.Taint.Agree (τr [.esp, .edi, .eax])) := checkedBlockInvariant rfl rfl
  have agree : VG.X86.Taint.Agree (τr [.esp, .edi, .eax]) s t := by
    apply agree_regs
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    · exact P.1.stack
    · exact BitVec.eq_of_toNat_eq (P.1.left.1.scratch.edi_toNat.trans P.1.right.1.scratch.edi_toNat.symm)
    · exact P.2.1
  obtain ⟨U, flagU⟩ := wp_result compareZero_ok A
  obtain ⟨Z, flagZ⟩ := wp_result compareZero_ok B
  refine ⟨(raw _ _ _ _ _ _ agree A B).1,
    ⟨P.1.left.keepMem U.mem (U.keeps []) (by decide) (by decide),
      P.1.right.keepMem Z.mem (Z.keeps []) (by decide) (by decide), ?_⟩, ?_, ?_⟩
  · rw [U.gpr, Z.gpr]; exact P.1.stack
  · rw [U.gpr, Z.gpr]; exact P.2.1
  · rw [flagU, flagZ, P.2.1]

theorem result_trace {E : Environment} (v : E.Valid) {c d : Nat} :
    RelCT isa (StatusPair E c d) (VG.Impl.RsaKeyGen.X86.CandidateFinish.mrResult E.width) (fun _ _ => True) := by
  have finish {s t : State} (P : ControlPair E c d s t) : CandidateFinish.FinishPair E.base E.size s t :=
    ⟨P.1.left.1.scratch, P.1.right.1.scratch, P.1.left.1.usedEq.trans P.1.right.1.usedEq.symm⟩
  have space : 156 ≤ E.size := by have H : 256 ≤ E.size := v.geometry.headerFit; omega
  unfold VG.Impl.RsaKeyGen.X86.CandidateFinish.mrResult
  refine RelCT.seq (statusArgs_trace v) (VG.RelCT.ite (fun _ _ P => P.2.2) ?_ ?_)
  · exact (prime_trace v).mono (fun _ _ P => P.1.1) (fun _ _ _ => trivial)
  · refine RelCT.seq (compareZero_trace.mono (fun _ _ P => P.1) (fun _ _ P => P))
      (VG.RelCT.ite (fun _ _ P => P.2.2) ?_ ?_)
    · exact (CandidateFinish.none_trace space).mono (fun _ _ P => finish P.1) (fun _ _ _ => trivial)
    · exact (CandidateFinish.used_trace space 3).mono (fun _ _ P => finish P.1) (fun _ _ _ => trivial)

end VG.Proof.RsaKeyGen.X86.Candidate
