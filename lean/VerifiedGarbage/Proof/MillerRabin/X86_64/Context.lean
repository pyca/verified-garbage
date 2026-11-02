module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSq
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnVerified
import VerifiedGarbage.Proof.Bignum.CrtExp
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # A prepared x86-64 workspace supplies the shared round's context -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Impl.Bignum VG.Impl.Bignum.Public
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum.X86_64.MontFn (numAt_eq)

theorem initial_ctx {s : State} (h : roundPre s) :
    let B := s.gpr .rdi
    let Z := (s.gpr .rsi).toNat * 8
    let w := Proof.Rsa.Mont.wOf s.mem B
    let c := Proof.Rsa.Mont.numAt s.mem B w 0
    MrDims B Z w ∧ ∃ bm, MrCtx s B Z w (word s.mem B (8 * sMinv)) c bm ∧
      ECtx s.mem B w c ∧ c % 2 = 1 ∧ 3 ≤ c ∧ wv s.mem B (slot w aXm) w < c := by
  rcases h with ⟨-, hwr, hn, -, -, -, hL, hp⟩
  dsimp only [Proof.MillerRabin.Round.Layout, Proof.MillerRabin.Round.extended] at hL
  rcases hL with ⟨-, hm, h4, h128, hspace, -⟩
  rcases hm with ⟨-, -, -, harr⟩
  dsimp only [Proof.MillerRabin.Round.Prepared, Proof.MillerRabin.Round.extended] at hp
  rcases hp with ⟨h3, hodd, hinv, hxm, hr1, hrm1, he, hl⟩
  dsimp only
  let B := s.gpr .rdi
  let Z := (s.gpr .rsi).toNat * 8
  let w := Proof.Rsa.Mont.wOf s.mem B
  let c := Proof.Rsa.Mont.numAt s.mem B w 0
  have hs : Scr s B Z := Scr.of_mem (by rw [hwr]; simp [B, Z]) hn
  have h27 : slot w 27 ≤ Z := by
    change slot w 27 ≤ 8 * (s.gpr .rsi).toNat at hspace
    simpa only [Z, Nat.mul_comm] using hspace
  have hz : slot w 8 ≤ Z := Nat.le_trans (VG.Proof.Bignum.slot_mono w (by decide : 8 ≤ 27)) h27
  have hd : MrDims B Z w := ⟨hz, by
    change slot w 26 + 8 * (w + 2) ≤ Z
    rw [← VG.Proof.Bignum.slot_succ w 26]
    exact h27, h4, h128⟩
  have hg : Good s B Z w (word s.mem B (8 * sMinv)) := by
    refine ⟨hs, rfl, ?_, rfl, ?_⟩
    · simp only [w, Proof.Rsa.Mont.wOf, Proof.Rsa.Mont.wordAt, Proof.Rsa.Mont.wWord, VG.Proof.Bignum.word, sW, off]
      simp
    · intro j hj
      exact harr j hj
  refine ⟨hd, wv s.mem B (slot w aB) w, ⟨hg, hinv, ?_, rfl, ?_, ?_⟩,
    ⟨?_, ?_⟩, hodd, h3, ?_⟩
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

end VG.Proof.MillerRabin.X86_64
