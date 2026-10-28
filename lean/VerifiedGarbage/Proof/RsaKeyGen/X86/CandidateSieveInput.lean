module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput
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
public import VerifiedGarbage.TCB.X86.State

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

end VG.Proof.RsaKeyGen.X86.Candidate
