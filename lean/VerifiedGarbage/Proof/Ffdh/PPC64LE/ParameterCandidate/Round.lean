module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.RoundCall
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Omega

/-!
# An FFDH parameter candidate on PPC64LE: a witness's round

`roundCount_ok`: the round of a witness `a` (`roundCall_ok`), then `hStat`
2 if it failed, else the passing witnesses `hIdx` counted and `hStat` 1 once
there are `hChecks` of them, 4 before.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (arr RoundImpl)
open VG.Proof.Mont (word off)

theorem stat_eq {i K : Nat} (hi : i < 2 ^ 62) (hK : K < 2 ^ 62) :
    BitVec.ofNat 64 4 - (BitVec.ofNat 64 K - BitVec.ofNat 64 (i + 1) - BitVec.ofNat 64 1) >>> 63 * BitVec.ofNat 64 3 =
      BitVec.ofNat 64 (if i + 1 < K then 4 else 1) := by
  have e1 : BitVec.ofNat 64 K - BitVec.ofNat 64 (i + 1) - BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (if i + 1 < K then K - (i + 2) else 2 ^ 64 - (i + 2 - K)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    split <;> omega_arith
  have e2 : ∀ n, n < 2 ^ 64 → BitVec.ofNat 64 n >>> 63 = BitVec.ofNat 64 (n / 2 ^ 63) := fun n hn => by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega_arith)]
  rw [e1]
  split
  · rw [e2 _ (by omega_arith), Nat.div_eq_of_lt (by omega_arith)]; rfl
  · rw [e2 _ (by omega_arith), show (2 ^ 64 - (i + 2 - K)) / 2 ^ 63 = 1 by omega_arith]; rfl

/-- What `round` leaves: the round's state `u` (`RcPost`), and the status
and count stored over it. -/
def RdPost (s : State) (B : Addr) (L w c a i K : Nat) (t : State) : Prop :=
  ∃ u, RcPost s B L w c a u ∧ (t.mem = if Proof.MillerRabin.Round.round c a then
      (u.mem.writeW (B + BitVec.ofNat 64 176) (BitVec.ofNat 64 (i + 1))).writeW (B + BitVec.ofNat 64 160)
        (BitVec.ofNat 64 (if i + 1 < K then 4 else 1))
    else u.mem.writeW (B + BitVec.ofNat 64 160) (BitVec.ofNat 64 2)) ∧ Keep [.r3, .r4, .r5] u t

theorem roundCount_ok (R : RoundImpl) {s : State} {B : Addr} {L w c a i K : Nat} (h : Prep s B L w c)
    (ha : arr s.mem B w 4 = a) (hac : a < c)
    (hsp : 176 ≤ s.sp.toNat) (hstk : (below s.sp 176).Disjoint ⟨B, 8 * L⟩)
    (hI : word s.mem B 176 = BitVec.ofNat 64 i) (hK : word s.mem B 168 = BitVec.ofNat 64 K)
    (hi : i < 2 ^ 62) (hK' : K < 2 ^ 62) :
    WP isa (round R.name R.code) s (RdPost s B L w c a i K) := by
  have hnw := h.env.hs.nowrap
  have hZ := h.env.hZ
  have es : ∀ j, VG.Proof.Bignum.slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have hZ' : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := by rw [← es]; exact hZ
  unfold round
  refine WP.seq (WP.mono (roundCall_ok R h ha hac hsp hstk) fun u hu => ?_)
  have hs : Scr u B (8 * L) := hu.prep.env.hs
  have h31 : u.gpr .r31 = B := hu.prep.env.h31
  have l160 : InRegions u.wr (B + BitVec.ofNat 64 160) 8 := hs.st (d := 160) (by omega_arith)
  refine WP.ite (decide ((if Proof.MillerRabin.Round.round c a then 1 else 0) = 0))
    (eval_zero_ofNat u .r3 (by split <;> decide) hu.r3) (fun hb => ?_) (fun hb => ?_)
  · have hf : Proof.MillerRabin.Round.round c a = false := by
      cases hr : Proof.MillerRabin.Round.round c a <;> simp_all
    refine WP.mono (WP.keep [.r3] (Q := fun t => t.mem = u.mem.writeW (B + BitVec.ofNat 64 160)
      (BitVec.ofNat 64 2)) ?_ (by decide)) fun t ⟨tm, kt⟩ => ⟨u, hu, by rw [tm, hf]; rfl, kt.mono (by decide)⟩
    simp only [sth, hStat]
    prun [h31, l160]
  · have ht : Proof.MillerRabin.Round.round c a = true := by
      cases hr : Proof.MillerRabin.Round.round c a <;> simp_all
    have rI : u.mem.readW (B + BitVec.ofNat 64 176) 64 = BitVec.ofNat 64 i :=
      (keeps_word hu.keeps (d := 176) (by omega_arith) (by kept_tac)).trans hI
    have rK : u.mem.readW (B + BitVec.ofNat 64 168) 64 = BitVec.ofNat 64 K :=
      (keeps_word hu.keeps (d := 168) (by omega_arith) (by kept_tac)).trans hK
    have l176 : InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 176) 8 := hs.ld (d := 176) (by omega_arith)
    have l168 : InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 168) 8 := hs.ld (d := 168) (by omega_arith)
    have s176 : InRegions u.wr (B + BitVec.ofNat 64 176) 8 := hs.st (d := 176) (by omega_arith)
    refine WP.mono (WP.keep [.r3, .r4, .r5] (Q := fun t => t.mem =
      (u.mem.writeW (B + BitVec.ofNat 64 176) (BitVec.ofNat 64 (i + 1))).writeW (B + BitVec.ofNat 64 160)
        (BitVec.ofNat 64 (if i + 1 < K then 4 else 1))) ?_ (by decide))
      fun t ⟨tm, kt⟩ => ⟨u, hu, by rw [tm, ht]; rfl, kt⟩
    simp only [ldh, sth, hStat, hIdx, hChecks]
    prun [h31, l160, l176, l168, s176, rI, rK, ← BitVec.ofNat_add, stat_eq hi hK']

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
