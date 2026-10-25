module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFinS
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvCorrect
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvStores
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFinD
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFinG
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFinY
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCand
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCandSet
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFF
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvLoads

/-!
# `vg_rsa_recover_primes` on PPC64LE: the finish

`fin_ok`: after the last candidate, `p = max(g, n / g)` and
`q = min(g, n / g)` for `g = gcd(y - 1, n)`, or zeros, as `ok` says, and
`ok` returned.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa
open VG.Impl.Rsa.PPC64LE.Recover (fin finY gcdSet divide order stores nArr)
open VG.Impl.Rsa.PPC64LE.Keys (seqs inverse)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- The bytes of a factor. -/
abbrev outB (b : Bool) (v k : Nat) : List Byte := if b then Spec.Rsa.i2osp v k else List.replicate k 0

theorem nV_lt256 (s0 : State) : nV s0 < 256 ^ kK s0 := by
  have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s0.mem (s0.gpr .r7) (kK s0))
  rwa [VG.Proof.Bignum.bytesAt_length] at this

/-- `fin`. -/
theorem fin_ok {s0 u : State} (hn : NOk s0) (h : CP s0 (jL s0) u) :
    WP isa fin u fun t => RFin s0 t ∧ t.gpr .r3 = BitVec.ofNat 64 (b2n (okB s0)) ∧
      ∃ x, (1 ≤ yV s0 → x = yV s0 - 1) ∧
        Spec.Rsa.bytesAt t.mem (s0.gpr .r3) (kK s0) =
          outB (okB s0) (max (Nat.gcd x (nV s0)) (nV s0 / Nat.gcd x (nV s0))) (kK s0) ∧
        Spec.Rsa.bytesAt t.mem (s0.gpr .r5) (kK s0) =
          outB (okB s0) (min (Nat.gcd x (nV s0)) (nV s0 / Nat.gcd x (nV s0))) (kK s0) := by
  have hn0 : 0 < nV s0 := by have := hn.big; omega_arith
  unfold fin
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (finY_ok hn h) fun u1 ⟨f1, y1⟩ => ?_
  rw [CrtValues.wp_seqs_pair (List.cons_ne_nil _ _)]
  refine WP.mono (gcd_ok hn f1 y1) fun u2 ⟨f2, x, g2, hx⟩ => ?_
  rw [CrtValues.wp_seqs_pair (List.cons_ne_nil _ _)]
  have p0 : 0 < Nat.gcd x (nV s0) := Nat.gcd_pos_of_pos_right _ hn0
  refine WP.mono (divOrder_ok f2 g2 p0) fun u3 ⟨f3, v5, v6⟩ => ?_
  rw [show seqs [stores] = stores from rfl]
  refine WP.mono (stores_ok (f3.base.fin f3.ws.r30) f3.ws f3.r21 f3.r23 f3.r25 f3.mask) fun t ⟨ft, r3, bp, bq⟩ => ?_
  have hk : kK s0 ≤ 4 * ww (kK s0) := by simp only [ww]; omega_arith
  have pl : Nat.gcd x (nV s0) ≤ nV s0 := Nat.le_of_dvd hn0 (Nat.gcd_dvd_right _ _)
  have ql : nV s0 / Nat.gcd x (nV s0) ≤ nV s0 := Nat.div_le_self _ _
  have nl := nV_lt256 s0
  refine ⟨ft, r3, x, hx, ?_, ?_⟩
  · cases hb : okB s0
    · rw [hb] at bp; exact CrtValues.bytes_zero fun c hc => by rw [bp c hc]; rfl
    · rw [hb] at bp
      have e : (2 : Nat) ^ (8 * kK s0) = 256 ^ kK s0 := by rw [Nat.pow_mul]
      rw [CrtValues.bytes_of hk bp, v5, e, Nat.mod_eq_of_lt (by omega_arith)]
      rfl
  · cases hb : okB s0
    · rw [hb] at bq; exact CrtValues.bytes_zero fun c hc => by rw [bq c hc]; rfl
    · rw [hb] at bq
      have e : (2 : Nat) ^ (8 * kK s0) = 256 ^ kK s0 := by rw [Nat.pow_mul]
      rw [CrtValues.bytes_of hk bq, v6, e, Nat.mod_eq_of_lt (by omega_arith)]
      rfl

end VG.Proof.Rsa.PPC64LE.Recover
