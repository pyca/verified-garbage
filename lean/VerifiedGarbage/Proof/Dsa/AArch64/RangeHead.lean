module

public import VerifiedGarbage.Proof.Dsa.AArch64.Masks
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Public loop bounds and addresses for DSA range checks -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem rangeHead_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) :
    WP isa (.block [ldh .x12 sW, ldh .x16 (sArr aX), ldh .x17 (sArr aN), movi .x7 0, mov .x14 .x12,
      .subs .x .x3 .x7 .x7]) s fun u =>
      u.gpr .x12 = BitVec.ofNat 64 w ∧ u.gpr .x16 = off B (slot w aX) ∧
      u.gpr .x17 = off B (slot w aN) ∧ u.gpr .x14 = BitVec.ofNat 64 w ∧ u.gpr .x7 = 0 ∧ u.c = true ∧
      u.mem = s.mem ∧ Keep [.x3, .x7, .x12, .x14, .x16, .x17] s u := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (Nat.le_trans (hdr_lt_slot w 8 hi) hZ)
  refine WP.mono (WP.keep [.x3, .x7, .x12, .x14, .x16, .x17] (Q := fun u =>
    u.gpr .x12 = BitVec.ofNat 64 w ∧ u.gpr .x16 = off B (slot w aX) ∧
    u.gpr .x17 = off B (slot w aN) ∧ u.gpr .x14 = BitVec.ofNat 64 w ∧ u.gpr .x7 = 0 ∧ u.c = true ∧
    u.mem = s.mem) ?_ (by decide) (by decide) (by decide +kernel))
    fun u ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2, hk⟩
  brun [hg.x0, hdr_enc (show sW < 32 by decide), hdr_enc (sArr_lt (show aX < 8 by decide)),
    hdr_enc (sArr_lt (show aN < 8 by decide)), hl sW (by decide), hl _ (sArr_lt (show aX < 8 by decide)),
    hl _ (sArr_lt (show aN < 8 by decide)), hg.hdr.hw, hg.hdr.harr aX (by decide), hg.hdr.harr aN (by decide)]

end VG.Proof.Dsa.AArch64
