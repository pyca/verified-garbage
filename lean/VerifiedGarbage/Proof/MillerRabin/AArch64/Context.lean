module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSq
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.MontFnVerified
import VerifiedGarbage.Proof.Bignum.CrtExp
import VerifiedGarbage.Proof.Rsa.Ranges

/-! # The callable precondition supplies the shared round's context -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.AArch64
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum.AArch64.MontFn (numAt_eq)

theorem initial_ctx {s : State} (h : roundPre s) :
    let B := s.gpr .x0
    let Z := (s.gpr .x1).toNat * 8
    let w := Proof.Rsa.Mont.wOf s.mem B
    let c := Proof.Rsa.Mont.numAt s.mem B w 0
    4 ≤ w ∧ w ≤ 128 ∧ slot w aE + 8 * (w + 2) ≤ Z ∧
      ∃ bm, MrCtx s B Z w c bm ∧ ECtx s.mem B w c ∧
        c % 2 = 1 ∧ 3 ≤ c ∧ wv s.mem B (slot w aXm) w < c := by
  rcases h with ⟨hrd, hwr, hn, hL, hp⟩
  dsimp only [Proof.MillerRabin.Round.Layout, Proof.MillerRabin.Round.compact] at hL
  rcases hL with ⟨-, hm, h4, h128, hspace, hstride⟩
  rcases hm with ⟨h2, h31, h8, harr⟩
  dsimp only [Proof.MillerRabin.Round.Prepared, Proof.MillerRabin.Round.compact] at hp
  rcases hp with ⟨h3, hodd, hinv, hxm, hr1, hrm1, he, hl⟩
  dsimp only
  let B := s.gpr .x0
  let Z := (s.gpr .x1).toNat * 8
  let w := Proof.Rsa.Mont.wOf s.mem B
  let c := Proof.Rsa.Mont.numAt s.mem B w 0
  have hw128 : w ≤ 128 := h128
  have hs : Scr s B Z := Scr.of_mem (by rw [hwr]; simp [B, Z]) hn
  have h28 : slot w 28 ≤ Z := by
    change slot w 28 ≤ 8 * (s.gpr .x1).toNat at hspace
    simpa only [Z, Nat.mul_comm] using hspace
  have h16 : slot w 16 ≤ Z := Nat.le_trans (VG.Proof.Bignum.slot_mono w (by decide : 16 ≤ 28)) h28
  have hEZ : slot w aE + 8 * (w + 2) ≤ Z := by
    change slot w 27 + 8 * (w + 2) ≤ Z
    rw [← VG.Proof.Bignum.slot_succ w 27]
    exact h28
  have hws : Ws s B Z w := by
    refine ⟨hs, rfl, ?_, hstride, ?_, h16, h2, by omega_arith⟩
    · simp only [w, Proof.Rsa.Mont.wOf, Proof.Rsa.Mont.wordAt, Proof.Rsa.Mont.wWord, word, sW, off]
      simp
    · intro j hj
      exact harr j hj
  refine ⟨h4, h128, hEZ, wv s.mem B (slot w aB) w, ⟨hws, ?_, ?_, rfl, ?_, ?_⟩,
    ⟨?_, ?_⟩, hodd, h3, ?_⟩
  · exact hinv
  · exact (numAt_eq s.mem B w 0).symm
  · rw [← numAt_eq s.mem B w aR1]
    exact hr1
  · rw [← numAt_eq s.mem B w aRm1]
    exact hrm1
  · rw [← numAt_eq s.mem B w aE]
    simpa only [Proof.MillerRabin.Round.exponent, Proof.MillerRabin.Round.shift, mrE, mrSig, sigOf, mrA, aE, B, w, c] using he
  · exact hl
  · rw [← numAt_eq s.mem B w aXm]
    exact hxm

end VG.Proof.MillerRabin.AArch64
