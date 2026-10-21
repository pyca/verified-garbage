module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateSieve
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieve
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveGeometry
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateShape
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateArrays
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.RsaKeyGen.X86.WorkspaceDisjoint
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateMemory
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.Offset

/-! # Native trial division preserves the entire candidate workspace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

theorem read_offset {rs : List Region} {base : Addr} {L d n : Nat}
    (R : InRegions rs base L) (bound : d + n ≤ L) (fit : d < 2 ^ 64) :
    InRegions rs (off base d) n := by
  obtain ⟨r, mem, contains⟩ := R
  refine ⟨r, mem, ?_⟩
  have distance : (off base d - r.base).toNat ≤ d + (base - r.base).toNat := by
    rw [← Offset.sub_add_sub_cancel (off base d) base r.base, BitVec.toNat_add]
    have first : (off base d - base).toNat = d := Mem.sub_ofNat_toNat base fit
    rw [first]
    exact Nat.mod_le _ _
  change (base - r.base).toNat + L ≤ r.len at contains
  change (off base d - r.base).toNat + n ≤ r.len
  omega

theorem sieve_context {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s) :
    Sieve.Context E.sieveGeometry (candidateValue E entropy) (allocFrame 20 s) := by
  have fit : 20 ≤ (s.gpr .esp).toNat := by rw [D.input.stack]; have := v.low; omega
  have stack := FilterStack.allocated_context fit
  rw [D.input.stack] at stack
  refine ⟨stack, ?_, ?_, ?_, ?_⟩
  · intro i index
    change i < 2 * E.width at index
    change InRegions ((allocFrame 20 s).rd ++ (allocFrame 20 s).wr)
      (off ((E.workspace + 256#32).setWidth 64) (4 * i)) 4
    rw [v.candidateAddress, off, Offset.add_add]
    have source := D.input.scratch.read (d := 256 + 4 * i) (n := 4) (by
      have := v.slotFit (j := 0) (by decide)
      change 256 + 0 * stride E.width + 8 * E.width ≤ E.size at this
      omega)
    obtain ⟨r, mem, contains⟩ := source
    refine ⟨r, ?_, contains⟩
    simp only [allocFrame_rd, allocFrame_wr, List.mem_append, List.mem_cons]
    exact (List.mem_append.mp mem).elim Or.inl (fun h => Or.inr (Or.inr h))
  · intro i index d mem
    have native := v.sieve_valid
    have dBound : d = 0 ∨ d = 4 := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using mem
    have address : addr (E.sieveGeometry.cursor i) d = off (E.table.setWidth 64) (8 * i + d) := by
      rw [addr_eq (by have := native.cursor_fit index; rcases dBound with rfl | rfl <;> omega), native.cursor_addr index]
      exact Offset.add_add _ _ _
    rw [address]
    obtain ⟨r, member, contains⟩ := read_offset D.input.memory.tableRead (d := 8 * i + d) (n := 4)
      (by rcases dBound with rfl | rfl <;> omega) (by rcases dBound with rfl | rfl <;> omega)
    refine ⟨r, ?_, contains⟩
    simp only [allocFrame_rd, allocFrame_wr, List.mem_append, List.mem_cons]
    exact (List.mem_append.mp member).elim Or.inl (fun h => Or.inr (Or.inr h))
  · intro i index
    exact D.input.memory.table i index
  · change val32 s.mem ((E.workspace + 256#32).setWidth 64) 0 (2 * E.width) = candidateValue E entropy
    rw [v.candidateAddress, ← VG.Proof.Bignum.read_eq_val32, ← D.candidate, ← VG.Proof.Bignum.read_eq_val32]
    congr 2
    change off (off E.base 256) 0 = off E.base (slot E.width 0)
    simp only [off, BitVec.add_zero, slot, VG.Impl.Bignum.hdrBytes, Nat.zero_mul, Nat.add_zero]

theorem sieve_ok {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateSieve.code E.width) s fun t =>
      Drawn E eBytes pBytes entropy t ∧
      t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy)).toNat ∧
      WorkFrame E s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have space : 256 ≤ E.size := v.geometry.headerFit
  have privateSub : (below E.sieveGeometry.sp 4).Sub (below E.p 96) := below_inner (by decide) v.low
  have workspaceFar : E.workspaceRegion.Disjoint (below E.p 96) :=
    v.stackFar E.workspaceRegion (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have tableFar : E.tableRegion.Disjoint (below E.p 96) :=
    v.stackFar E.tableRegion (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  have pointer : s.gpr .edi = E.workspace := by
    apply BitVec.eq_of_toNat_eq
    have H := D.input.scratch.edi_toNat
    change (s.gpr .edi).toNat = (E.workspace.setWidth 64).toNat at H
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans E.workspace.isLt (by decide))] at H
    exact H
  refine WP.mono_syms (CandidateSieve.code_ok v.sieve_valid (sieve_context v D)
    (by rw [D.input.stack]; have := v.low; omega) (by change s.gpr .edi + 256#32 = E.workspace + 256#32; rw [pointer])
    rfl D.input.memory.symbol (by change 4 ≤ (E.p - 20#32).toNat; rw [sub_toNat (by have := v.low; omega)]; have := v.low; omega)
    ((workspaceFar.sub_left v.sieveCandidateSub).sub_right privateSub) (tableFar.sub_right privateSub)
    (candidate_large v entropy)) fun t ⟨result, F, K⟩ syms => ?_
  change t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.obviouslyComposite (64 * E.width) (candidateValue E entropy)).toNat at result
  rw [show 64 * E.width = 8 * E.length by have := v.length_eq; omega] at result
  have stackFrame : Frame [below E.p 96] s.mem t.mem := F.sub (by
    intro r mem
    simp only [Sieve.setupWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, v.sieveStackSub⟩
    · exact ⟨_, List.mem_singleton_self _, privateSub⟩)
  have frame : WorkFrame E s.mem t.mem := stackFrame.mono (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have W : WorkspaceFrame E.geometry [] s.mem t.mem := workspace_of_frame stackFrame D.input.scratch.nowrap
    (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact workspaceFar)
  have I := D.input.keepWorkspace v K (by decide) (by decide) frame W (by intro r mem; cases mem) (by rw [syms])
  have value := W.val32 (d := slot E.width 0) (n := 2 * E.width)
    (by have := v.slotFit (j := 0) (by decide); change slot E.width 0 + 4 * (2 * E.width) ≤ E.size; omega)
    (by intro r mem; cases mem)
  have used := W.read32 (d := 152) (by change 152 + 4 ≤ E.size; omega) (by intro r mem; cases mem)
  exact ⟨⟨I, value.trans D.candidate, (congrArg BitVec.toNat used).trans D.used, (frame.output v).trans D.zeros⟩,
    result, frame, K⟩

end VG.Proof.RsaKeyGen.X86.Candidate
