module

public import VerifiedGarbage.Proof.Bignum.X86.CrtCompute

/-! # Private arithmetic preserves acceptance and the saved cdecl registers -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic
open VG.Impl.Bignum.X86.Crt

theorem compute_header {n d bytes : Nat} {base : Addr} {sp : BitVec 32} {m m' : Mem}
    (O : OutsZ base sp (computeRanges n) m m') (R : CallRoom sp base bytes)
    (nw : base.toNat + bytes ≤ 2 ^ 32) (hb : 48 ≤ bytes) (lo : 8 ≤ d) (hi : d + 4 ≤ 48) :
    m'.readW (off base d) 32 = m.readW (off base d) 32 := by
  have V : val32 m' base d 1 = val32 m base d 1 := by
    apply O.val32 R nw
    · intro r hr
      simp only [computeRanges, powersRanges, arithmeticRanges, tableRange, recombineRanges,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [slot, stride, multiplierOffset, counterOffset] <;> omega
    · omega
  apply BitVec.eq_of_toNat_eq
  simpa only [val32, w32, Nat.mul_zero, Nat.add_zero] using V

end VG.Proof.Bignum.X86.Crt
