module

import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Load
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Width
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieve
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.RsaKeyGen.X86.WorkspaceDisjoint
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.Syms
public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Memory
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Enter

/-! # Trial division of the imported candidate -/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Dsa.X86.ProbablePrime VG.Impl.Bignum.X86.PublicContext
open VG.Proof.RsaKeyGen.X86

def Environment.sieveGeometry (E : Environment) : Sieve.Geometry :=
  ⟨E.p - 20#32, E.workspace + 256#32, E.table, E.width, VG.Impl.RsaKeyGen.X86.Sieve.tableCount E.width⟩

theorem Environment.Valid.candidateRoom {E : Environment} (v : E.Valid) : 256 + 8 * E.width ≤ E.size := by
  have := v.slotFit (j := 0) (by decide)
  have := v.room
  have e0 : slot E.width 0 = 256 := by unfold slot VG.Impl.Bignum.hdrBytes; omega
  omega

theorem Environment.Valid.candidateAddress {E : Environment} (v : E.Valid) :
    (E.workspace + 256#32).setWidth 64 = off E.base 256 := by
  have room := v.candidateRoom
  have width := v.width_low
  have fit := v.workspaceFit
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, off, Environment.base]
  have := E.workspace.isLt
  omega

theorem Environment.Valid.sieveCandidateSub {E : Environment} (v : E.Valid) :
    E.sieveGeometry.candidateRegion.Sub E.workspaceRegion := by
  change (⟨(E.workspace + 256#32).setWidth 64, 8 * E.width⟩ : Region).Sub E.workspaceRegion
  rw [v.candidateAddress]
  exact Offset.sub_base E.base v.candidateRoom

theorem Environment.Valid.sieveStackSub {E : Environment} (v : E.Valid) :
    E.sieveGeometry.stackRegion.Sub (below E.p 136) :=
  below_sub (by decide) v.low

theorem Environment.Valid.sieve_valid {E : Environment} (v : E.Valid) : E.sieveGeometry.Valid := by
  have width := v.width_low
  have high := v.width_high
  have room := v.candidateRoom
  have fit := v.workspaceFit
  have candidateNat : (E.workspace + 256#32).toNat = E.workspace.toNat + 256 := by
    rw [BitVec.toNat_add]
    change (E.workspace.toNat + 256) % 2 ^ 32 = E.workspace.toNat + 256
    omega
  refine ⟨by change 0 < E.width; exact Nat.lt_of_lt_of_le (by decide) width, by change E.width ≤ 128; omega, ?_, ?_, ?_, v.tableFit, ?_, ?_⟩
  · change 0 < VG.Impl.RsaKeyGen.X86.Sieve.tableCount E.width
    unfold VG.Impl.RsaKeyGen.X86.Sieve.tableCount
    split <;> decide
  · change VG.Impl.RsaKeyGen.X86.Sieve.tableCount E.width ≤ 1024
    unfold VG.Impl.RsaKeyGen.X86.Sieve.tableCount
    split <;> decide
  · change (E.workspace + 256#32).toNat + 8 * E.width ≤ 2 ^ 32
    rw [candidateNat]
    omega
  · exact ((v.stackFar E.workspaceRegion List.mem_cons_self).sub_left v.sieveCandidateSub).sub_right
      v.sieveStackSub
  · exact (v.stackFar E.tableRegion (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))).sub_right v.sieveStackSub

theorem sieve_context {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s : State}
    (L : Loaded E c entropy s) :
    Sieve.Context E.sieveGeometry c (allocFrame 20 s) := by
  have fit : 20 ≤ (s.gpr .esp).toNat := by rw [L.input.stack]; have := v.low; omega
  have stack := FilterStack.allocated_context fit
  rw [L.input.stack] at stack
  have room := v.candidateRoom
  refine ⟨stack, ?_, ?_, ?_, ?_⟩
  · intro i index
    change i < 2 * E.width at index
    change InRegions ((allocFrame 20 s).rd ++ (allocFrame 20 s).wr)
      (off ((E.workspace + 256#32).setWidth 64) (4 * i)) 4
    rw [v.candidateAddress, off, Offset.add_add]
    obtain ⟨r, mem, contains⟩ := L.input.scratch.read (d := 256 + 4 * i) (n := 4) (by omega)
    refine ⟨r, ?_, contains⟩
    simp only [allocFrame_rd, allocFrame_wr, List.mem_append, List.mem_cons]
    exact (List.mem_append.mp mem).elim Or.inl (fun h => Or.inr (Or.inr h))
  · intro i index d mem
    have native := v.sieve_valid
    have dBound : d = 0 ∨ d = 4 := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using mem
    have address : addr (E.sieveGeometry.cursor i) d = off (E.table.setWidth 64) (8 * i + d) := by
      rw [addr_eq (by have := native.cursor_fit index; rcases dBound with rfl | rfl <;> omega),
        native.cursor_addr index]
      exact Offset.add_add _ _ _
    rw [address]
    obtain ⟨r, member, contains⟩ := Candidate.read_offset L.input.memory.tableRead (d := 8 * i + d) (n := 4)
      (by rcases dBound with rfl | rfl <;> omega) (by rcases dBound with rfl | rfl <;> omega)
    refine ⟨r, ?_, contains⟩
    simp only [allocFrame_rd, allocFrame_wr, List.mem_append, List.mem_cons]
    exact (List.mem_append.mp member).elim Or.inl (fun h => Or.inr (Or.inr h))
  · intro i index
    exact L.input.memory.table i index
  · change val32 s.mem ((E.workspace + 256#32).setWidth 64) 0 (2 * E.width) = c
    rw [v.candidateAddress, ← VG.Proof.Bignum.read_eq_val32, ← L.value, ← VG.Proof.Bignum.read_eq_val32]
    congr 2
    change off (off E.base 256) 0 = off E.base (Proof.Rsa.Mont.arrAt E.width 0)
    simp only [off, BitVec.add_zero, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero]

/-- A stage that writes only the stack below the saved registers keeps the
input. -/
theorem Loaded.keepStack {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s t : State}
    (L : Loaded E c entropy s) (F : Frame [below E.p 136] s.mem t.mem) {regs : List Reg} (K : Keeps regs s t)
    (edi : .edi ∉ regs) (esp : .esp ∉ regs)
    (symbol : t.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol) :
    Loaded E c entropy t ∧ WorkFrame E s.mem t.mem ∧ Tail E s.mem t.mem := by
  have fit : E.base.toNat + E.size ≤ 2 ^ 32 := by rw [v.baseNat]; exact v.workspaceFit
  have W : WorkspaceFrame E.geometry [] s.mem t.mem := workspace_of_frame F fit
    (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact v.stackFar _ List.mem_cons_self)
  have T : Tail E s.mem t.mem := fun i _ hi => W i hi (by intro r mem; cases mem)
  have WF : WorkFrame E s.mem t.mem := F.mono (by
    intro r mem; obtain rfl := List.mem_singleton.mp mem; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have header := v.header
  have read (d : Nat) (small : d + 4 ≤ E.size) : t.mem.readW (off E.base d) 32 = s.mem.readW (off E.base d) 32 :=
    W.read32 small (by intro r mem; cases mem)
  have arrays (j : Nat) (index : j < 28) :
      val32 t.mem E.base (E.geometry.array j) E.geometry.words = val32 s.mem E.base (E.geometry.array j) E.geometry.words :=
    W.val32 ((v.geometry).arrayFit index) (by intro r mem; cases mem)
  refine ⟨⟨⟨L.input.scratch.of_keeps K edi esp, (K.1 .esp esp).trans L.input.stack, ?_, ?_, ?_, ?_,
    L.input.memory.keep v K WF T symbol⟩, ?_, ?_, ?_⟩, WF, T⟩
  · rw [read 28 (by omega)]; exact L.input.randPtr
  · unfold w32; rw [read 32 (by omega)]; exact L.input.randLength
  · unfold w32; rw [read 40 (by omega)]; exact L.input.capacity
  · rw [read 44 (by omega)]; exact L.input.usedPtr
  · rw [arrays 0 (by decide)]; exact L.value
  · rw [arrays 5 (by decide)]; exact L.minusOne
  · unfold w32; rw [read 152 (by omega)]; exact L.count

theorem sieve_ok {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s : State}
    (L : Loaded E c entropy s) (large : 8161 < c) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateSieve.code E.width) s fun t =>
      Loaded E c entropy t ∧
      t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.obviouslyComposite (64 * E.width) c).toNat ∧
      WorkFrame E s.mem t.mem ∧ Tail E s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have privateSub : (below E.sieveGeometry.sp 4).Sub (below E.p 136) := below_inner (by decide) v.low
  have workspaceFar : E.workspaceRegion.Disjoint (below E.p 136) := v.stackFar _ List.mem_cons_self
  have tableFar : E.tableRegion.Disjoint (below E.p 136) := v.stackFar _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have pointer : s.gpr .edi = E.workspace := by
    apply BitVec.eq_of_toNat_eq
    rw [L.input.scratch.edi_toNat, v.baseNat]
  refine WP.mono_syms (CandidateSieve.code_ok v.sieve_valid (sieve_context v L)
    (by rw [L.input.stack]; have := v.low; omega) (by change s.gpr .edi + 256#32 = E.workspace + 256#32; rw [pointer])
    rfl L.input.memory.symbol
    (by change 4 ≤ (E.p - 20#32).toNat; rw [sub_toNat (by have := v.low; omega)]; have := v.low; omega)
    ((workspaceFar.sub_left v.sieveCandidateSub).sub_right privateSub) (tableFar.sub_right privateSub)
    large) fun t ⟨result, F, K⟩ syms => ?_
  have stackFrame : Frame [below E.p 136] s.mem t.mem := F.sub (by
    intro r mem
    simp only [Sieve.setupWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, v.sieveStackSub⟩
    · exact ⟨_, List.mem_singleton_self _, privateSub⟩)
  obtain ⟨Lt, W, T⟩ := L.keepStack v stackFrame K (by decide) (by decide) (by rw [syms])
  exact ⟨Lt, result, W, T, K⟩

end VG.Proof.Dsa.X86.ProbablePrime
