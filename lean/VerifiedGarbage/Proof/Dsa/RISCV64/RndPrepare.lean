module

public import VerifiedGarbage.Proof.Dsa.RISCV64.RndEnv
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes
import VerifiedGarbage.Proof.Dsa.RISCV64.RndMath
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA sampling on RISC-V: the scan of q

As on PPC64LE (`Proof/Dsa/PPC64LE/Random/Prepare.lean`). `prepare_ok`: with
q's `q_len` octets at `s7` (`q_len` in `s8`), `s8 :=` its significant
octets, `s7 :=` the address of the first, `s9 :=` the mask of its bits, and
`a0 ≠ 0` exactly when `q > 1`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.Rnd

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Bignum.RISCV64
open VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Proof.Mont
open VG.Proof.Dsa (significant)

/-- The registers `prepare` writes. -/
def prepRegs : List Reg := [.s0, .a0, .a1, .t3, .t4, .t5, .s7, .s8, .s9, .a2]

theorem prepare_ok {s : State} {Q : Addr} {ql : Nat} (h7 : s.gpr .s7 = Q) (h8 : s.gpr .s8 = BitVec.ofNat 64 ql)
    (hql : 1 ≤ ql) (hql' : ql ≤ 32) (hrd : ∀ i ≤ ql, InRegions (s.rd ++ s.wr) (off Q i) 1) :
    WP isa prepare s fun t =>
      (t.gpr .s8 = BitVec.ofNat 64 (significant (Spec.Rsa.bytesAt s.mem Q ql)).1 ∧
        t.gpr .s7 = off Q (ql - (significant (Spec.Rsa.bytesAt s.mem Q ql)).1) ∧
        (t.gpr .a0 = 0 ↔ ¬ 1 < Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem Q ql)) ∧
        (1 < Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem Q ql) →
          t.gpr .s9 = BitVec.ofNat 64 (maskOf (significant (Spec.Rsa.bytesAt s.mem Q ql)).2.toNat)) ∧
        t.mem = s.mem) ∧ Keep prepRegs s t := by
  refine WP.keep prepRegs ?_ (by decide) (by rfl)
  unfold prepare
  generalize hqb : Spec.Rsa.bytesAt s.mem Q ql = qb
  have hlen : qb.length = ql := by rw [← hqb, VG.Proof.Bignum.bytesAt_length]
  have hfit := Dsa.significant_fits qb
  refine WP.seq (WP.mono (sigLen_ok h7 h8 hql (by omega) fun i hi => hrd i (by omega))
    fun s₁ ⟨⟨a16, m1⟩, k1⟩ => ?_)
  rw [hqb] at a16
  generalize hW : (significant qb).1 = W at a16 hfit
  have hrd' : InRegions (s₁.rd ++ s₁.wr) (off Q (ql - W)) 1 := by rw [k1.2.1, k1.2.2]; exact hrd _ (by omega)
  generalize ht : s₁.mem (off Q (ql - W)) = tb
  have htl := tb.isLt
  have e27 : off Q ql - BitVec.ofNat 64 W = off Q (ql - W) := VG.Offset.add_ofNat_sub Q (by omega)
  have hor : BitVec.ofNat 64 W >>> 1 ||| BitVec.ofNat 64 tb.toNat >>> 1 =
      BitVec.ofNat 64 (W >>> 1 ||| tb.toNat >>> 1) := by
    rw [ofNat_shr (by omega), ofNat_shr (by omega), ofNat_or (by have := shr_lt (k := 1) (show W < 256 by omega); omega)
      (by have := shr_lt (k := 1) htl; omega)]
  have hor' : (W >>> 1 ||| tb.toNat >>> 1) < 256 := or_lt (shr_lt (by omega)) (shr_lt htl)
  brun [(k1.gpr (r := .s7) (by decide)).trans h7, (k1.gpr (r := .s8) (by decide)).trans h8, a16, off_add, e27,
    hrd', BitVec.add_zero, read_byte64, ht, exec_li_zero]
  rw [show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, hor, nz_eq (x := W >>> 1 ||| tb.toNat >>> 1) (by omega),
    nz_eq (x := W) (by omega), valid_eq (w := W) (t := tb.toNat) (by omega) htl]
  have hq1 : 1 < Spec.Dsa.decodeBE qb → W ≠ 0 := fun h => by
    have := (Dsa.random_valid_scan qb).mp h; rw [hW] at this; exact this.1
  have htb : W ≠ 0 → tb = (significant qb).2 := fun hw => by
    have e1 := significant_get qb (by rw [hW]; exact hw)
    rw [hlen, hW, ← hqb, bytesAt_get s.mem Q (show ql - W < ql by omega), hqb] at e1
    rw [← ht, m1]
    exact Option.some.inj e1
  refine ⟨?_, fun hq => ?_, m1⟩
  · by_cases hw : W = 0
    · rw [ite_eq_right (by omega)]
      exact ⟨fun _ hq => hq1 hq hw, fun _ => rfl⟩
    · rw [htb hw, ← hW] at *
      have hv := Dsa.random_valid_scan_ge qb
      by_cases hc : 2 ≤ (significant qb).1 ∨ 2 ≤ (significant qb).2.toNat
      · rw [ite_eq_left ⟨by rw [hW]; exact hw, hc⟩]
        exact ⟨fun h => absurd h (by decide), fun h => absurd (hv.mpr hc) h⟩
      · rw [ite_eq_right (fun h => hc h.2)]
        exact ⟨fun _ h => hc (hv.mp h), fun _ => rfl⟩
  · have hw := hq1 hq
    have e := htb hw
    subst e
    have hpos : 0 < (significant qb).2.toNat := by
      have hn : (significant qb).2 ≠ 0 := fun h0 => hw (by rw [← hW]; exact (Dsa.significant_nonzero qb).mpr h0)
      exact Nat.pos_of_ne_zero fun h0 => hn (BitVec.eq_of_toNat_eq h0)
    exact smear_eq (significant qb).2.isLt hpos

end VG.Proof.Dsa.RISCV64.Rnd
