module

public import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Three-word scalar accumulation without wraparound -/

@[expose] public section
namespace VG.Proof.Mont.X86.StaticSquare

/-- The carry accounts for the single possible wrap of a word sum. -/
theorem word_carry {t : Nat} (ht : t<2*(2^32)) :
    t%2^32+2^32*(decide (2^32≤t)).toNat=t := by
  by_cases h : 2^32≤t
  · simp only [h,decide_true,Bool.toNat_true,Nat.mul_one]
    rw [Nat.mod_eq_sub_mod h,Nat.mod_eq_of_lt (by omega)]
    omega
  · simp only [h,decide_false,Bool.toNat_false,Nat.mul_zero,Nat.add_zero]
    exact Nat.mod_eq_of_lt (by omega)

theorem accum96 {l m h a b : Nat}
    (hl : l<2^32) (hm : m<2^32) (hh : h<2^32) (ha : a<2^32) (hb : b<2^32)
    (bound : l+2^32*m+2^64*h+a+2^32*b<2^96) :
    let c := decide (2^32≤l+a)
    let d := decide (2^32≤m+b+c.toNat)
    (l+a)%2^32+2^32*((m+b+c.toNat)%2^32)+2^64*((h+d.toNat)%2^32)=
      l+2^32*m+2^64*h+a+2^32*b := by
  intro c d
  have hc : c.toNat≤1 := Bool.toNat_le c
  have hd : d.toNat≤1 := Bool.toNat_le d
  have E₁ := word_carry (t:=l+a) (by omega)
  have E₂ := word_carry (t:=m+b+c.toNat) (by omega)
  change (l+a)%2^32+2^32*c.toNat=l+a at E₁
  change (m+b+c.toNat)%2^32+2^32*d.toNat=m+b+c.toNat at E₂
  have high : h+d.toNat<2^32 := by omega
  rw [Nat.mod_eq_of_lt high]
  omega

end VG.Proof.Mont.X86.StaticSquare
