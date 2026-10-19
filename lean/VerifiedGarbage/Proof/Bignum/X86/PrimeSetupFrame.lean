module

public import VerifiedGarbage.Proof.Bignum.X86.PreparePrime

/-! # Factor preparation preserves the base and secret exponent -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic

theorem primeSetup_value {n i k : Nat} {base : Addr} {m m' : Mem}
    (O : Outs base (primeSetupRanges n) m m') (hi : i = 5 ∨ i = 6 ∨ i = 8)
    (hk : k ≤ 2 * n) (fit : contextBytes n ≤ 2 ^ 64) :
    val32 m' base (slot n i) k = val32 m base (slot n i) k := by
  have i0 := slot_sep (n := n) (i := i) (j := 0) (by omega)
  have i1 := slot_sep (n := n) (i := i) (j := 1) (by omega)
  have i2 := slot_sep (n := n) (i := i) (j := 2) (by omega)
  have i3 := slot_sep (n := n) (i := i) (j := 3) (by omega)
  have i4 := slot_sep (n := n) (i := i) (j := 4) (by omega)
  have i7 := slot_sep (n := n) (i := i) (j := 7) (by omega)
  have head := slot_header n i
  have bound := slot_bound (n := n) (i := i) (by omega)
  simp only [stride] at *
  apply O.val32
  · intro r hr
    simp only [primeSetupRanges, setupRanges, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · omega

end VG.Proof.Bignum.X86
