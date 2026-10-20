module
public import VerifiedGarbage.Impl.Bignum.AArch64.WindowLazy
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

import VerifiedGarbage.Proof.Bignum.AArch64.WindowLazyLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCount
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowLazy
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- Final subtraction for a loose Montgomery residue. Its only mask is the
word above the radix; the result is below the radix and congruent modulo m. -/
theorem finish_ok {s : State} {B : Addr} {Z n eA eN eT : Nat} {bit : Bool}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eA) (h10 : s.gpr .x10 = off B eN)
    (h5 : s.gpr .x5 = off B eT) (h12 : s.gpr .x12 = BitVec.ofNat 64 (4*n))
    (h7 : s.gpr .x7 = 0) (hn : 0 < n) (hn' : 4*n < 2 ^ 31)
    (hA : eA + 8*(4*n+1) ≤ Z) (hN : eN + 8*(4*n) ≤ Z) (hT : eT + 8*(4*n) ≤ Z)
    (sA : eT+8*(4*n) ≤ eA ∨ eA+8*(4*n+1) ≤ eT)
    (sN : eT+8*(4*n) ≤ eN ∨ eN+8*(4*n) ≤ eT)
    (hbit : word s.mem B (eA+8*(4*n)) = BitVec.ofNat 64 bit.toNat)
    (hlt : wv s.mem B eA (4*n) + 2 ^ (64*(4*n)) * bit.toNat <
      2 ^ (64*(4*n)) + wv s.mem B eN (4*n)) :
    WP isa VG.Impl.Bignum.AArch64.WindowLazy.code s fun t =>
      wv t.mem B eT (4*n) % wv s.mem B eN (4*n) =
        (wv s.mem B eA (4*n) + 2 ^ (64*(4*n)) * bit.toNat) % wv s.mem B eN (4*n) ∧
      Outside B eT (8*(4*n)) s.mem t.mem ∧
      Keep [.x3, .x4, .x5, .x14, .x15, .x16, .x17] s t := by
  have hsz := hs.nowrap
  unfold VG.Impl.Bignum.AArch64.WindowLazy.code
  refine WP.seq (WP.mono (WP.keep [.x3, .x14, .x15, .x16, .x17] (Q := fun u =>
    u.gpr .x16 = off B eA ∧ u.gpr .x17 = off B eN ∧
    u.gpr .x14 = BitVec.ofNat 64 n ∧ u.gpr .x15 = (if bit then -1 else 0) ∧
    u.c = true ∧ u.mem = s.mem) ?_ rfl rfl rfl) fun u ⟨⟨h16,h17,h14,h15,hc,hm⟩,ku⟩ => ?_)
  · brun [h8, h10, h12, h7, BlockedRedc.shl3_ofNat (show 4*n < 2^64 by omega),
      Square.shr2_ofNat (show 4*n < 2^64 by omega),
      hs.ld (show eA+8*(4*n)+8 ≤ Z by omega)]
    constructor
    · congr 1; omega
    · change 0 - word s.mem B (eA+8*(4*n)) = _
      rw [hbit]
      cases bit <;> rfl
  · have hl := loop_ok (hs.congr ku.wr) h16 h17 ((ku.gpr .x5 (by decide)).trans h5)
      h14 h15 hc hn (by omega) (by omega) hN hT (by omega) sN
    refine WP.mono hl fun t ⟨hv,ho,kt⟩ => ?_
    rw [hm] at hv ho
    refine ⟨lazy_sub (wv_lt _ _ _ _) (Bool.toNat_le _) (Bool.toNat_le _) hlt hv,
      ho, (ku.trans kt).mono (by decide)⟩

end VG.Proof.Bignum.AArch64.WindowLazy
