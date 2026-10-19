module
public import VerifiedGarbage.Impl.Bignum.AArch64.WindowLazy
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

import VerifiedGarbage.Proof.Bignum.AArch64.WindowLazyTile

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowLazy
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The masked subtraction traverses each limb exactly once, independently of
its value. The mask is fixed throughout the loop. -/
theorem loop_ok {s : State} {B : Addr} {Z n eA eN eT : Nat} {bit : Bool}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B eA) (h17 : s.gpr .x17 = off B eN)
    (h5 : s.gpr .x5 = off B eT) (h14 : s.gpr .x14 = BitVec.ofNat 64 n)
    (h15 : s.gpr .x15 = if bit then -1 else 0) (hc : s.c = true)
    (hn : 0 < n) (hn' : n < 2 ^ 64)
    (hA : eA + 8*(4*n) ≤ Z) (hN : eN + 8*(4*n) ≤ Z) (hT : eT + 8*(4*n) ≤ Z)
    (sA : eT+8*(4*n) ≤ eA ∨ eA+8*(4*n) ≤ eT)
    (sN : eT+8*(4*n) ≤ eN ∨ eN+8*(4*n) ≤ eT) :
    WP isa (countLoop .x14 (VG.Impl.Bignum.AArch64.WindowLazy.words ++
      ([.addImm .x .x16 .x16 32, .addImm .x .x17 .x17 32, .addImm .x .x5 .x5 32] : List Instr))) s fun t =>
      wv t.mem B eT (4*n) + bit.toNat * wv s.mem B eN (4*n) =
        wv s.mem B eA (4*n) + 2 ^ (64*(4*n)) * (!t.c).toNat ∧
      Outside B eT (8*(4*n)) s.mem t.mem ∧
      Keep [.x3, .x4, .x5, .x14, .x16, .x17] s t := by
  have h0 : Inv s B Z eA eN eT 0 bit s :=
    ⟨hs, Keep.refl _ _, by simpa using h16, by simpa using h17,
      by simpa using h5, h15, Outside.refl _ _ _ _, by simp [wv, hc]⟩
  exact WP.mono (wp_countdown hn' hn (fun j => Inv s B Z eA eN eT (4*j) bit)
    (fun j hj t hI _ => tile_ok hA hN hT sA sN hj hI) h0 h14)
    fun _ hI => ⟨hI.val, hI.out, hI.keep⟩

end VG.Proof.Bignum.AArch64.WindowLazy
