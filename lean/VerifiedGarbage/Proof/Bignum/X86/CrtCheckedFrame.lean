module

public import VerifiedGarbage.Proof.Bignum.X86.CrtCheckedCompute

/-! # The CRT body writes around the saved cdecl register block -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.Proof.Mont VG.Impl.Mont.X86.Dynamic VG.Impl.Bignum.X86.Crt

def bodyRanges (bytes : Nat) : List (Nat × Nat) := [(0, 32), (48, bytes - 48)]

theorem checked_frame {n bytes : Nat} {base : Addr} {m m' : Mem}
    (O : Outs base (checkedRanges n) m m') (space : size n ≤ bytes) :
    Outs base (bodyRanges bytes) m m' := by
  have sz := size_eq n
  intro a ha
  have low := ha (0, 32) (by simp [bodyRanges])
  have high := ha (48, bytes - 48) (by simp [bodyRanges])
  apply O a
  intro r hr
  simp only [checkedRanges, validationRanges, computeRanges, powersRanges, arithmeticRanges, tableRange,
    recombineRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [slot, stride, contextBytes, productSlot, resultSlot, pSlot, mpSlot, multiplierOffset,
      acceptanceOffset, counterOffset] at * <;> omega

theorem body_scratch {bytes : Nat} {base : Addr} {m m' : Mem}
    (O : Outs base (bodyRanges bytes) m m') (space : 48 ≤ bytes) : Outside base 0 bytes m m' := by
  intro a ha
  apply O a
  intro r hr
  simp only [bodyRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> omega

end VG.Proof.Bignum.X86.Crt
