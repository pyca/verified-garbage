module

public import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEnvironment
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `RsaKeyGen.X86.CandidateMemory`, which this module and modules that import it used -/

section

/-! # Candidate work frames preserve all caller inputs and the read-only sieve table -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Environment.Valid.readFit {E : Environment} (v : E.Valid) {r : Region} (mem : r ∈ E.readRegions) : r.len ≤ 2 ^ 64 := by
  simp only [Environment.readRegions, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl
  · change E.exponentLength ≤ 2 ^ 64
    have := v.exponentFit; omega_using [this]
  · change E.otherLength ≤ 2 ^ 64
    have := v.otherFit; omega_using [this]
  · change E.randLength ≤ 2 ^ 64
    have := v.randLengthFit; omega_using [this]
  · change 8192 ≤ 2 ^ 64
    decide

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
      (Offset.contains_base _ (by change 8 * i + 8 ≤ 8192; omega_using [index]) (by omega_using [index])) (v.readMutableFar tableMem) (by decide)]
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
  · have := v.outFit; omega_using [this]

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! # The candidate header keeps native public arguments across every prefilter -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

theorem Input.out_eq {E : Environment} {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) : s.mem.readW (off E.base 0) 32 = E.out := I.header 0 (by decide)

theorem Input.exponent_eq {E : Environment} {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) : s.mem.readW (off E.base 12) 32 = E.exponent := I.header 3 (by decide)

theorem Input.other_eq {E : Environment} {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) : s.mem.readW (off E.base 20) 32 = E.other := I.header 5 (by decide)

theorem Input.rand_eq {E : Environment} {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) : s.mem.readW (off E.base 28) 32 = E.rand := I.header 7 (by decide)

theorem native_word {m : Mem} {base : Addr} {offset value : Nat}
    (H : m.readW (off base offset) 32 = BitVec.ofNat 32 value) (bound : value < 2 ^ 32) :
    w32 m base offset = value := by rw [w32, H, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]

theorem Input.exponentLength_eq {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) : w32 s.mem E.base 16 = E.exponentLength :=
  native_word (I.header 4 (by decide)) (by have := v.exponentLength; omega_using [this])

theorem Input.randLength_eq {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) : w32 s.mem E.base 32 = E.randLength :=
  native_word (I.header 8 (by decide)) v.randLengthFit

theorem Input.capacity_eq {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) : w32 s.mem E.base 40 = E.capacity :=
  native_word (I.header 10 (by decide)) v.capacityFit

theorem Input.keepWorkspace {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s t : State}
    (I : Input E eBytes pBytes entropy s) {regs : List Reg} (K : Keeps regs s t)
    (base : .edi ∉ regs) (sp : .esp ∉ regs) (F : WorkFrame E s.mem t.mem)
    {ranges : List (Nat × Nat)} (W : WorkspaceFrame E.geometry ranges s.mem t.mem)
    (headerFar : ∀ r ∈ ranges, 48 ≤ r.1)
    (symbol : t.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol) :
    Input E eBytes pBytes entropy t := by
  have space : 256 ≤ E.size := v.geometry.headerFit
  refine I.keep v K base sp F ?_ ?_ symbol
  · intro i index
    exact (W.read32 (by change 4 * i + 4 ≤ E.size; omega_using [space, index])
      (fun r mem => Or.inl (by have := headerFar r mem; omega_using [index, this]))).trans (I.header i index)
  · exact (W.read32 (by change 44 + 4 ≤ E.size; omega_using [space])
      (fun r mem => Or.inl (by have := headerFar r mem; omega_using [this]))).trans I.usedPointer

theorem count_low {E : Environment} (v : E.Valid) {m : Mem}
    (H : word m E.base 152 = BitVec.ofNat 64 E.length) : w32 m E.base 152 = E.length := by
  have lengthBound : E.length < 2 ^ 32 := CandidateGeometry.native_length_bound v.length
  have pair := word_eq_w32 m E.base 152
  rw [H, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans lengthBound (by decide : 2 ^ 32 < 2 ^ 64))] at pair
  have lo : w32 m E.base 152 < 2 ^ 32 := (m.readW _ 32).isLt
  omega_using [lengthBound, pair]

end VG.Proof.RsaKeyGen.X86.Candidate
