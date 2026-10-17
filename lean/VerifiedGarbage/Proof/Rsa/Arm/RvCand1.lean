module

public import VerifiedGarbage.Proof.Rsa.Arm.RvSt2
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `vg_rsa_recover_primes` on ARMv7: a candidate set up (`candSet_vp`)

The candidate `j` (`g = j + 2`): `[mG] := g R mod n` (`g` in Montgomery
form), `[mY] := R mod n` (1), `r`'s copy, and the count `c` of its bits: the
stage `Xs j 0` of the exponentiation (`Xs j i`: `i` bits done).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

/-- `r` and `t`. -/
abbrev rv (P : RP) (σ : State) : Nat := (hvs P σ P.c).1
abbrev tv (P : RP) (σ : State) : Nat := (hvs P σ P.c).2

/-- The header words of the candidate `j` with the count `k`. -/
def Vc (P : RP) (σ : State) (j k : Nat) : Nat → Nat := upd (upd (upd (fun _ => 0) sTc (tv P σ)) sCand j) sCnt k

/-- `g^e` in Montgomery form, `g = j + 2`. -/
abbrev gR (P : RP) (j e : Nat) : Nat := (j + 2) ^ e * Rm P % P.n

/-- The arrays after `i` bits: `y = g^(r mod 2^i)` and `g^(2^i)`. -/
def Ae (P : RP) (σ : State) (j i : Nat) : Nat → Nat :=
  upd (upd (AM P) mY (gR P j (rv P σ % 2 ^ i))) mG (gR P j (2 ^ i))
abbrev Le : List Nat := mY :: mG :: liveM

/-- `r`'s copy after `i` bits. -/
def AWe (P : RP) (σ : State) (i : Nat) : Nat → Nat := upd (AWh P σ P.c) wRc (rv P σ / 2 ^ i)
abbrev LWe : List Nat := [wRc, wR]
abbrev LSe : List Nat := [sCnt, sCand, sTc]

/-- The start of the candidate `j`. -/
abbrev Cs (P : RP) (E : State → Prop) (j : Nat) : State → State → Prop :=
  St P E (fun _ => AM P) liveM (fun σ => AWh P σ P.c) [wR] (fun σ => Vc P σ j 0) [sCand, sTc] P.w nArr

/-- The candidate `j` after `i` bits of `r`. -/
abbrev Xs (P : RP) (E : State → Prop) (j i : Nat) : State → State → Prop :=
  St P E (fun σ => Ae P σ j i) Le (fun σ => AWe P σ i) LWe (fun σ => Vc P σ j (P.c - i)) LSe P.w nArr

section
variable {P : RP}

theorem gR1_mont (j : Nat) : gR P j 1 * Rm P % P.n = (j + 2) * R2v P % P.n := by
  rw [Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.pow_one, Nat.mul_assoc, ← Nat.pow_add,
    show 64 * P.w6 + 64 * P.w6 = 128 * P.w6 by omega]

theorem candSet_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) (h101 : 101 < P.n) {E : State → Prop} {j : Nat} (hj : j < 100) :
    VP (Cs P E j) (.seq candSet (seqs (mmul iG iG iR2))) (Xs P E j 0) := by
  have hn0 : 0 < P.n := by omega
  simp only [candSet, seqs]
  refine VP.assoc' (VP.seq (St.pcopy gZ_taint (o := mG) (a := aZ) (by decide) (by decide) (by decide) (by decide)
    (by decide)) ?_)
  refine VP.assoc' (VP.seq (St.pstoreG (by decide) (by decide) (fun σ _ => ⟨?_, ?_⟩) (by decide)) ?_)
  · have : Vc P σ j 0 sCand = j := by simp [Vc, upd, sCnt, sCand]
    omega
  · simp [AM, upd, aZ, mG, aOne, mR2, aO, aNg]
  refine VP.assoc' (VP.seq (St.pcopy yO_taint (o := mY) (a := aO) (by decide) (by decide) (by decide) (by decide)
    (by decide)) ?_)
  refine VP.assoc' (VP.seq St.pctxW ?_)
  refine VP.assoc' (VP.seq (St.pcopyW rcR_taint (o := wRc) (a := wR) (by decide) (by decide) (by decide)
    (by decide) (by decide)) ?_)
  rw [cntBits_eq]
  refine VP.seq (VP.block_append (VP.block_append St.pldrLens St.pcntTail) St.pctxw) ?_
  · refine (St.pmmul (o := iG) (a := iG) (b := iR2) (by decide) hn.1 (T := fun _ => gR P j 1) (by decide) (by decide)
      (by decide) (by decide) (by decide) fun σ _ => ?_).mono (fun _ _ h => h) fun σ s h => h.mono ?_ ?_ ?_
    · have e1 : Vc P σ j 0 sCand = j := by simp [Vc, upd, sCnt, sCand]
      have eG : (upd (upd (upd (AM P) mG (AM P aZ)) mG (Vc P σ j 0 sCand + 2)) mY
          (upd (upd (AM P) mG (AM P aZ)) mG (Vc P σ j 0 sCand + 2) aO)) (mBase + iG) = j + 2 := by
        simp [upd, e1, mG, mY, mBase, iG]
      have eR : (upd (upd (upd (AM P) mG (AM P aZ)) mG (Vc P σ j 0 sCand + 2)) mY
          (upd (upd (AM P) mG (AM P aZ)) mG (Vc P σ j 0 sCand + 2) aO)) (mBase + iR2) = R2v P := by
        simp [upd, AM, mG, mY, mBase, iR2, mR2, aO, aNg]
      rw [eG, eR]
      exact ⟨by omega, Nat.mod_lt _ hn0, Nat.mod_lt _ hn0, gR1_mont j⟩
    · intro x hx
      simp only [Le, liveM, List.mem_cons, List.not_mem_nil, or_false] at hx
      refine ⟨by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega, ?_⟩
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Ae, AM, upd, mG, mY, mBase, iG, aZ, aO, aN, aOne, aNg, mR2, gR, Ov, Nat.mod_one]
    · intro x hx
      simp only [LWe, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp [AWe, AWh, upd]
    · intro x hx
      simp only [LSe, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [Vc, upd, sCnt, sCand, sTc]

end

end VG.Proof.Rsa.Arm.Recover
