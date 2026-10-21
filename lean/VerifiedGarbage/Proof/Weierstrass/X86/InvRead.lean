module
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Weierstrass.Unch
/-! # Reads preserved outside the divstep scratch ranges -/
@[expose] public section
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.Proof.Mont VG.Proof.Weierstrass
theorem word_unch {base : Addr} {W : List (Nat × Nat)} {m m' : Mem}
    (U : Unch base W m m') {d : Nat}
    (hd : ∀ w ∈ W, d + 4 ≤ w.1 ∨ w.1 + w.2 ≤ d) (hb : d + 4 ≤ 2 ^ 64) :
    w32 m' base d = w32 m base d := by
  have H := Outs.val32 U (d := d) (k := 1) hd hb
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using H

theorem read32_unch {base : Addr} {W : List (Nat × Nat)} {m m' : Mem}
    (U : Unch base W m m') {d : Nat}
    (hd : ∀ w ∈ W, d + 4 ≤ w.1 ∨ w.1 + w.2 ≤ d) (hb : d + 4 ≤ 2 ^ 64) :
    m'.readW (off base d) 32 = m.readW (off base d) 32 :=
  BitVec.eq_of_toNat_eq (word_unch U hd hb)

end VG.Proof.Weierstrass.X86.Inv
