module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePrime
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishTiming
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishInput

import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishReady
import VerifiedGarbage.Proof.Bignum.X86.ExportBE
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86.PublicDataTiming
/-! # Equal released primality statuses select the same finish branch -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidatePrimeExport.lean`, which only this module imported.
section

/-! # Prime export retains the workspace header needed to write entropy consumption -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateFinish
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PublicContext VG.Impl.Mont.X86

def primeArgs : List Instr := [.mov .ebx (.mem (sc 0)), .mov .ecx (.mem (sc 4))]

theorem primeArgs_ok {s : State} {base : Addr} {size : Nat} (S : Scr s base size) (header : 8 ≤ size) :
    WP isa (.block primeArgs) s fun t =>
      t.gpr .ebx = s.mem.readW (off base 0) 32 ∧ t.gpr .ecx = s.mem.readW (off base 4) 32 ∧
      t.mem = s.mem ∧ Keeps [.ebx, .ecx] s t := by
  unfold primeArgs
  refine wp_movS (readSrc_sc S (d := 0) (by omega)) fun a A _ =>
    wp_movS (readSrc_sc (S.of_keeps A.keeps (by decide)) (d := 4) header) fun t T _ => WP.block_nil ?_
  exact ⟨(T.other .ebx (by decide)).trans A.gpr, by rw [T.gpr, A.mem], T.mem.trans A.mem, (A.keeps.mono (by decide)).widen T.keeps⟩

theorem PrimeInput.keepMem {s t : State} {base : Addr} {size w candidate : Nat} {out usedPtr count : BitVec 32}
    (S : PrimeInput base size w candidate out usedPtr count s) (M : t.mem = s.mem)
    {regs : List Reg} (K : Keeps regs s t) (baseReg : .edi ∉ regs) (sp : .esp ∉ regs) :
    PrimeInput base size w candidate out usedPtr count t := by
  refine ⟨S.scratch.of_keeps K baseReg sp, S.positive, S.space, S.header, ?_, ?_, ?_, ?_, ?_, S.outFit, ?_,
    S.usedWrite.of_keeps K, S.workspaceFar, S.usedFar⟩
  · rw [M]; exact S.outEq
  · rw [M]; exact S.lengthEq
  · rw [M]; exact S.usedEq
  · rw [M]; exact S.countEq
  · rw [M]; exact S.candidateEq
  · rw [K.2.2]; exact S.outWrite

theorem export_header_ok {s : State} {base : Addr} {size w candidate : Nat} {out usedPtr count : BitVec 32}
    (S : PrimeInput base size w candidate out usedPtr count s)
    (destination : s.gpr .ebx = out) (length : s.gpr .ecx = BitVec.ofNat 32 (8 * w)) :
    WP isa (VG.Impl.Bignum.X86.storeBE (slot w 0)) s fun t =>
      Scr t base size ∧ t.mem.readW (off base 44) 32 = usedPtr ∧ Keeps [.eax, .ebx, .ecx, .esi] s t := by
  refine WP.mono (VG.Proof.Bignum.X86.storeBE_ok S.scratch (by have := S.positive; omega) (Nat.le_refl _) S.space length
    (by rw [wordsVal_eq_val32, show 8 * (8 * w) = 32 * (2 * w) by omega]; exact val32_lt _ _ _ _)
    (by rw [destination]; exact S.outFit) (by rw [destination]; exact S.outWrite)
    (by rw [destination]; exact S.workspaceFar.sub_left (Offset.sub_base base S.space))) fun t ⟨_, F, K⟩ => ?_
  rw [destination] at F
  have header := F.readW (r := (⟨base, size⟩ : Region)) (a := off base 44) (w := 32)
    (Offset.contains_base _ (by have := S.header; omega) (by decide))
    (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact S.workspaceFar) (by decide)
  exact ⟨S.scratch.of_keeps K (by decide), header.trans S.usedEq, K.mono (by decide)⟩

end VG.Proof.RsaKeyGen.X86.CandidateFinish
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidatePrimeTiming.lean`, which only this module imported.
section

/-! # Prime export and its entropy count have a trace independent of the prime -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86

structure PrimePair (E : Environment) (c d : Nat) (s t : State) : Prop where
  left : FinishReady E c s
  right : FinishReady E d t
  stack : s.gpr .esp = t.gpr .esp

structure StorePair (E : Environment) (c d : Nat) (s t : State) : Prop extends PrimePair E c d s t where
  outLeft : s.gpr .ebx = E.out
  outRight : t.gpr .ebx = E.out
  lengthLeft : s.gpr .ecx = BitVec.ofNat 32 (8 * E.width)
  lengthRight : t.gpr .ecx = BitVec.ofNat 32 (8 * E.width)

theorem PrimePair.agree {E : Environment} {c d : Nat} {s t : State} (P : PrimePair E c d s t) :
    VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
  apply agree_regs
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact P.stack
  · exact BitVec.eq_of_toNat_eq (P.left.1.scratch.edi_toNat.trans P.right.1.scratch.edi_toNat.symm)

theorem primeArgs_trace {E : Environment} (v : E.Valid) {c d : Nat} :
    RelCT isa (PrimePair E c d) (.block CandidateFinish.primeArgs) (StorePair E c d) := by
  intro s t tr ur u z P A B
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block CandidateFinish.primeArgs)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := checkedBlockInvariant rfl rfl
  have space : 8 ≤ E.size := by have H : 256 ≤ E.size := v.geometry.headerFit; omega
  obtain ⟨outU, lenU, memU, KU⟩ := wp_result (CandidateFinish.primeArgs_ok P.left.1.scratch space) A
  obtain ⟨outZ, lenZ, memZ, KZ⟩ := wp_result (CandidateFinish.primeArgs_ok P.right.1.scratch space) B
  refine ⟨(raw _ _ _ _ _ _ P.agree A B).1, ⟨P.left.keepMem memU KU (by decide) (by decide),
    P.right.keepMem memZ KZ (by decide) (by decide), ?_⟩, outU.trans P.left.1.outEq,
    outZ.trans P.right.1.outEq, lenU.trans P.left.1.lengthEq, lenZ.trans P.right.1.lengthEq⟩
  rw [KU.1 .esp (by decide), KZ.1 .esp (by decide)]
  exact P.stack

theorem export_trace {E : Environment} {c d : Nat} :
    RelCT isa (StorePair E c d) (VG.Impl.Bignum.X86.storeBE (VG.Impl.Bignum.X86.PublicContext.slot E.width 0))
      (CandidateFinish.FinishPair E.base E.size) := by
  intro s t tr ur u z P A B
  have agree : VG.X86.Taint.Agree storeTaint s t := by
    apply agree_regs
    intro r mem
    change r ∈ [.edi, .esp, .ebx, .ecx] at mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl
    · exact BitVec.eq_of_toNat_eq (P.left.1.scratch.edi_toNat.trans P.right.1.scratch.edi_toNat.symm)
    · exact P.stack
    · exact P.outLeft.trans P.outRight.symm
    · exact P.lengthLeft.trans P.lengthRight.symm
  obtain ⟨SU, ptrU, _⟩ := wp_result (CandidateFinish.export_header_ok P.left.1 P.outLeft P.lengthLeft) A
  obtain ⟨SZ, ptrZ, _⟩ := wp_result (CandidateFinish.export_header_ok P.right.1 P.outRight P.lengthRight) B
  exact ⟨(storeBE_relCT _ _ _ _ _ _ _ agree A B).1, SU, SZ, ptrU.trans ptrZ.symm⟩

theorem prime_trace {E : Environment} (v : E.Valid) {c d : Nat} :
    RelCT isa (PrimePair E c d) (VG.Impl.RsaKeyGen.X86.CandidateFinish.prime E.width) (fun _ _ => True) := by
  unfold VG.Impl.RsaKeyGen.X86.CandidateFinish.prime
  exact RelCT.seq (primeArgs_trace v) (RelCT.seq export_trace
    (CandidateFinish.used_trace (by have H : 256 ≤ E.size := v.geometry.headerFit; omega) 1))

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

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
