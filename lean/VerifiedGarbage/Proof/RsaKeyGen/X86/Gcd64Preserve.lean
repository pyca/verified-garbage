module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Check

/-! # The native gcd's working space lies below the candidate's arrays -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Gcd64

theorem ranges_below {r : Nat × Nat} (mem : r ∈ checkRanges) : r.1 + r.2 ≤ 400 := by
  simp only [checkRanges, ranges, arrays, slots, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.RsaKeyGen.X86.Gcd64
