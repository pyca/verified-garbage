module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEnvironment
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Framework.Offset

/-! # Candidate work frames preserve all caller inputs and the read-only sieve table -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Environment.Valid.readFit {E : Environment} (v : E.Valid) {r : Region} (mem : r ∈ E.readRegions) : r.len ≤ 2 ^ 64 := by
  simp only [Environment.readRegions, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl
  · change E.exponentLength ≤ 2 ^ 64
    have := v.exponentFit; omega
  · change E.otherLength ≤ 2 ^ 64
    have := v.otherFit; omega
  · change E.randLength ≤ 2 ^ 64
    have := v.randLengthFit; omega
  · change 8192 ≤ 2 ^ 64
    decide

theorem Environment.Valid.readWorkFar {E : Environment} (v : E.Valid) {R : Region} (mem : R ∈ E.readRegions) :
    ∀ r ∈ [E.workspaceRegion, below E.p 136], R.Disjoint r := by
  intro r member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact v.readWorkspace mem
  · exact v.stackFar R (List.mem_append_right _ mem)

theorem WorkFrame.bytes {E : Environment} (v : E.Valid) {m m' : Mem} (F : WorkFrame E m m')
    {r : Region} (mem : r ∈ E.readRegions) : Spec.Rsa.bytesAt m' r.base r.len = Spec.Rsa.bytesAt m r.base r.len :=
  VG.Proof.RsaKeyGen.frame_bytesAt F (v.readWorkFar mem) (v.readFit mem)

theorem Environment.Valid.readMutableFar {E : Environment} (v : E.Valid) {R : Region} (mem : R ∈ E.readRegions) :
    ∀ r ∈ E.writeRegions ++ [below E.p 136], R.Disjoint r := by
  intro r member
  rcases List.mem_append.mp member with member | member
  · exact v.readWrite R mem r member
  · obtain rfl := List.mem_singleton.mp member
    exact v.stackFar R (List.mem_append_right _ mem)

theorem WorkFrame.mutable {E : Environment} {m m' : Mem} (F : WorkFrame E m m') : MutableFrame E m m' :=
  F.mono (by
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · exact List.mem_append_right _ (List.mem_singleton_self _))

theorem MutableFrame.bytes {E : Environment} (v : E.Valid) {m m' : Mem} (F : MutableFrame E m m')
    {r : Region} (mem : r ∈ E.readRegions) : Spec.Rsa.bytesAt m' r.base r.len = Spec.Rsa.bytesAt m r.base r.len :=
  VG.Proof.RsaKeyGen.frame_bytesAt F (v.readMutableFar mem) (v.readFit mem)

theorem MemoryFacts.keepMutable {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s t : State}
    (M : MemoryFacts E eBytes pBytes entropy s) {regs : List Reg} (K : Keeps regs s t) (F : MutableFrame E s.mem t.mem)
    (symbol : t.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol) :
    MemoryFacts E eBytes pBytes entropy t := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, symbol.trans M.symbol⟩
  · rw [K.2.1, K.2.2]; exact M.exponentRead
  · rw [K.2.1, K.2.2]; exact M.otherRead
  · rw [K.2.1, K.2.2]; exact M.randRead
  · rw [K.2.1, K.2.2]; exact M.tableRead
  · exact (F.bytes v (r := E.exponentRegion) List.mem_cons_self).trans M.exponentBytes
  · exact (F.bytes v (r := E.otherRegion) (List.mem_cons_of_mem _ List.mem_cons_self)).trans M.otherBytes
  · exact (F.bytes v (r := E.randRegion) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))).trans M.entropy
  · intro i index
    have tableMem : E.tableRegion ∈ E.readRegions :=
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    rw [F.readW (r := E.tableRegion)
      (Offset.contains_base _ (by change 8 * i + 8 ≤ 8192; omega) (by omega)) (v.readMutableFar tableMem) (by decide)]
    exact M.table i index

theorem MemoryFacts.keep {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s t : State}
    (M : MemoryFacts E eBytes pBytes entropy s) {regs : List Reg} (K : Keeps regs s t) (F : WorkFrame E s.mem t.mem)
    (symbol : t.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol) :
    MemoryFacts E eBytes pBytes entropy t := M.keepMutable v K F.mutable symbol

theorem Input.keep {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s t : State}
    (I : Input E eBytes pBytes entropy s) {regs : List Reg} (K : Keeps regs s t)
    (base : .edi ∉ regs) (sp : .esp ∉ regs) (F : WorkFrame E s.mem t.mem)
    (header : ∀ i < 11, t.mem.readW (off E.base (4 * i)) 32 = E.argument i)
    (used : t.mem.readW (off E.base 44) 32 = E.used)
    (symbol : t.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol) :
    Input E eBytes pBytes entropy t :=
  ⟨I.scratch.of_keeps K base sp, (K.1 .esp sp).trans I.stack, header, used,
    by rw [K.2.2]; exact I.outWrite, I.usedWrite.of_keeps K, I.memory.keep v K F symbol⟩

theorem Input.keepMutable {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s t : State}
    (I : Input E eBytes pBytes entropy s) {regs : List Reg} (K : Keeps regs s t)
    (base : .edi ∉ regs) (sp : .esp ∉ regs) (F : MutableFrame E s.mem t.mem)
    (header : ∀ i < 11, t.mem.readW (off E.base (4 * i)) 32 = E.argument i)
    (used : t.mem.readW (off E.base 44) 32 = E.used)
    (symbol : t.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol) :
    Input E eBytes pBytes entropy t :=
  ⟨I.scratch.of_keeps K base sp, (K.1 .esp sp).trans I.stack, header, used,
    by rw [K.2.2]; exact I.outWrite, I.usedWrite.of_keeps K, I.memory.keepMutable v K F symbol⟩

theorem WorkFrame.output {E : Environment} (v : E.Valid) {m m' : Mem} (F : WorkFrame E m m') :
    Spec.Rsa.bytesAt m' (E.out.setWidth 64) E.length = Spec.Rsa.bytesAt m (E.out.setWidth 64) E.length := by
  apply VG.Proof.RsaKeyGen.frame_bytesAt F
  · intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact v.outWorkspace
    · exact v.stackFar E.outRegion (List.mem_append_left _ List.mem_cons_self)
  · have := v.outFit; omega

end VG.Proof.RsaKeyGen.X86.Candidate
