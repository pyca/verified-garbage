module

public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Moving an output-range frame between its array pointer and workspace base. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Proof.Bignum VG.Proof.Bignum.AArch64

/-- The two descriptions denote the same modular-address interval. -/
theorem outside_shift_iff (B x : Addr) {d n : Nat} (hd : d<2^64) (fit : d+n≤2^64) :
 (ofs B x<d ∨ d+n≤ofs B x) ↔ n≤ofs (off B d) x := by
 have sub : ofs (off B d) x=(2^64-d+ofs B x)%2^64 :=
  Offset.toNat_sub_add x B hd
 rw [sub]
 have bound : ofs B x<2^64 := (x-B).isLt
 change (ofs B x<d ∨ d+n≤ofs B x) ↔ n≤(2^64-d+ofs B x)%2^64
 by_cases before : ofs B x<d
 · rw [Nat.mod_eq_of_lt (by omega)]
   omega
 · have eq : 2^64-d+ofs B x=2^64+(ofs B x-d) := by omega
   rw [eq,Nat.add_mod_left,Nat.mod_eq_of_lt (by omega : ofs B x-d<2^64)]
   omega

theorem outside_to_array {B : Addr} {d n : Nat} {m m' : Mem} (hd : d<2^64) (fit : d+n≤2^64)
 (frame : Outside B d n m m') : Outside (off B d) 0 n m m' := by
 intro x hx
 apply frame x
 exact (outside_shift_iff B x hd fit).mpr (by omega)

theorem outside_to_workspace {B : Addr} {d n : Nat} {m m' : Mem} (hd : d<2^64) (fit : d+n≤2^64)
 (frame : Outside (off B d) 0 n m m') : Outside B d n m m' := by
 intro x hx
 apply frame x
 exact Or.inr (by simpa only [Nat.zero_add] using (outside_shift_iff B x hd fit).mp hx)

end VG.Proof.Ffdh.AArch64.Cached
