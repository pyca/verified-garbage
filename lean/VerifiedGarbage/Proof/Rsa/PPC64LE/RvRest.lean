module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFin
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvMont
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvHalving
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Rsa.RecoverMath
import VerifiedGarbage.Proof.Rsa.RecoverTries
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCF
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvSqStart
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCand
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCandSet
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFF
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvLoads
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvNumbers

/-!
# `vg_rsa_recover_primes` on PPC64LE: once `m = d e - 1` is known even and positive

`par_of`: the sizes the candidates need (`Par`); `res_eq`: what
`recoverPrimes` returns, from the last candidate; `rest_ok`: the halvings,
the Montgomery setup, the candidates and the finish.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa
open VG.Spec.Rsa (recoverPrimes recoverStep recoverTries splitTwos)
open VG.Impl.Rsa.PPC64LE.Recover (rest halving mont candLoop fin)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)

theorem mV_eq {s0 : State} (odd : dV s0 * eV s0 % 2 = 1) : mV s0 = dV s0 * eV s0 - 1 := by
  simp only [mV]; omega_arith

/-- The sizes, from the contract. -/
theorem par_of {s0 : State} (h : rvP.pre s0) (odd : dV s0 * eV s0 % 2 = 1) (two : 2 ≤ dV s0 * eV s0) : Par s0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hk, hk'⟩, -, -, e1, e2, d1, d2,
    -⟩ := id h
  have bD : dV s0 < 2 ^ (8 * (PPC64LE.stackArg s0 1).toNat) := by
    have := os2ip_lt8 (dB s0); simp only [dB, Spec.Rsa.bytesAt, List.length_map, List.length_range] at this
    exact this
  have bE : eV s0 < 2 ^ (8 * (s0.gpr .r10).toNat) := by
    have := os2ip_lt8 (eB s0); simp only [eB, Spec.Rsa.bytesAt, List.length_map, List.length_range] at this
    exact this
  have hm : mV s0 < 2 ^ cB s0 := by
    have : dV s0 * eV s0 < 2 ^ cB s0 :=
      calc dV s0 * eV s0 < 2 ^ (8 * (PPC64LE.stackArg s0 1).toNat) * 2 ^ (8 * (s0.gpr .r10).toNat) :=
            Nat.mul_lt_mul'' bD bE
        _ = 2 ^ cB s0 := by rw [← Nat.pow_add]; congr 1; simp only [cB]; omega_arith
    simp only [mV]; omega_arith
  have hm0 : 0 < mV s0 := by simp only [mV]; omega_arith
  have hme : mV s0 % 2 = 0 := by simp only [mV]; omega_arith
  obtain ⟨e, ro⟩ := splitTwos_spec hm0
  refine ⟨by simp only [cB]; omega_arith, by simp only [cB]; omega_arith, ?_, ?_, Nat.le_of_lt (splitTwos_lt hm0 hm)⟩
  · have : rR s0 ≤ mV s0 := by
      have := Nat.le_mul_of_pos_left (rR s0) (Nat.two_pow_pos (tT s0)); rw [← e] at this; exact this
    omega_arith
  · show 1 ≤ (splitTwos (mV s0)).1
    rw [splitTwos_even (by omega_arith) hme]; omega_arith

/-- What `recoverPrimes` returns, from the last candidate. -/
theorem res_eq {s0 : State} (hn : NOk s0) (hp : Par s0)
    (hg : gos s0 recoverTries = gos s0 (recoverTries - jL s0)) :
    (gos s0 recoverTries).1 = (if okB s0 then some (max (Nat.gcd (yV s0 - 1) (nV s0)) (nV s0 / Nat.gcd (yV s0 - 1) (nV s0)),
      min (Nat.gcd (yV s0 - 1) (nV s0)) (nV s0 / Nat.gcd (yV s0 - 1) (nV s0))) else none) ∧
      (okB s0 = true → 1 ≤ yV s0) := by
  have n1 := nt_pos s0; have n2 := nt_le s0
  have hn1 : 1 < nV s0 := by have := hn.big; omega_arith
  have hJ : jL s0 < recoverTries := by unfold recoverTries; simp only [jL]; omega_arith
  have ge := VG.Proof.Rsa.go_eq (nV s0) (tT s0) (rR s0) hJ
  have hsq := VG.Proof.Rsa.sq_result (n := nV s0) (r := rR s0) (g := jL s0 + 2) hp.t1 hp.tc
  change sqRes (sqst s0 (jL s0) (cB s0)) = _ at hsq
  cases hb : okB s0
  · -- Not found: the last candidate is the 100th.
    have hs : recoverStep (nV s0) (tT s0) (rR s0) (jL s0 + 2) = none := by
      rw [← hsq]; simp only [sqRes, okB] at hb ⊢; rw [hb]; rfl
    rw [hs] at ge; simp only at ge
    refine ⟨?_, fun h => by cases h⟩
    rw [hg]; show (recoverPrimes.go _ _ _ _).1 = none
    rw [ge]
    by_cases h100 : jL s0 + 1 = recoverTries
    · rw [h100, Nat.sub_self, recoverPrimes.go]
    · exfalso
      have := VG.Proof.Rsa.go_ge1 (nV s0) (tT s0) (rR s0) (k := recoverTries - (jL s0 + 1) - 1)
        (by unfold recoverTries at *; omega_arith)
      rw [show recoverTries - (jL s0 + 1) - 1 + 1 = recoverTries - (jL s0 + 1) by unfold recoverTries at *; omega_arith,
        ← ge, ← (show recoverPrimes.go (nV s0) (tT s0) (rR s0) recoverTries =
          recoverPrimes.go (nV s0) (tT s0) (rR s0) (recoverTries - jL s0) from hg)] at this
      change _ ≤ nt s0 at this
      unfold recoverTries at *; simp only [jL] at *; omega_arith
  · -- Found.
    have hs : recoverStep (nV s0) (tT s0) (rR s0) (jL s0 + 2) = some (yV s0) := by
      rw [← hsq]; simp only [sqRes, okB] at hb ⊢; rw [hb]; rfl
    have y1 := VG.Proof.Rsa.recoverStep_some hs
    refine ⟨?_, fun _ => ?_⟩
    · rw [hg]; show (recoverPrimes.go _ _ _ _).1 = _
      rw [ge, hs]; rfl
    · rcases Nat.eq_zero_or_pos (yV s0) with e | e
      · rw [e] at y1; simp at y1
      · exact e

/-- The halvings, the Montgomery setup, the candidates and the finish. -/
theorem rest_ok {s0 t : State} (h : NumS s0 t) (hgo : t.gpr .r0 = 0)
    (hmv : Spec.Rsa.modulusValid (nV s0) (kK s0) = true) :
    WP isa rest t fun u => RFin s0 u ∧ u.gpr .r3 = BitVec.ofNat 64 (b2n (okB s0)) ∧
      Spec.Rsa.bytesAt u.mem (s0.gpr .r3) (kK s0) =
        outB (okB s0) (max (Nat.gcd (yV s0 - 1) (nV s0)) (nV s0 / Nat.gcd (yV s0 - 1) (nV s0))) (kK s0) ∧
      Spec.Rsa.bytesAt u.mem (s0.gpr .r5) (kK s0) =
        outB (okB s0) (min (Nat.gcd (yV s0 - 1) (nV s0)) (nV s0 / Nat.gcd (yV s0 - 1) (nV s0))) (kK s0) ∧
      (gos s0 recoverTries).1 = (if okB s0 then some (max (Nat.gcd (yV s0 - 1) (nV s0))
        (nV s0 / Nat.gcd (yV s0 - 1) (nV s0)), min (Nat.gcd (yV s0 - 1) (nV s0))
        (nV s0 / Nat.gcd (yV s0 - 1) (nV s0))) else none) := by
  have hn := NOk.of_valid hmv
  obtain ⟨odd, two⟩ := h.go.mp hgo
  have hp := par_of h.base.pre odd two
  unfold rest
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (halving_ok h hgo) fun u1 h1 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (mont_ok h1 hmv) fun u2 h2 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (candLoop_ok hn hp h2.cf) fun u3 ⟨h3, hg⟩ => ?_
  rw [show seqs [fin] = fin from rfl]
  obtain ⟨res, y1⟩ := res_eq hn hp hg
  refine WP.mono (fin_ok hn h3) fun u ⟨fu, r3, x, hx, bp, bq⟩ => ⟨fu, r3, ?_, ?_, res⟩
  · cases hb : okB s0
    · rw [hb] at bp; exact bp
    · rw [hb] at bp; rw [← hx (y1 hb)]; exact bp
  · cases hb : okB s0
    · rw [hb] at bq; exact bq
    · rw [hb] at bq; rw [← hx (y1 hb)]; exact bq

end VG.Proof.Rsa.PPC64LE.Recover
