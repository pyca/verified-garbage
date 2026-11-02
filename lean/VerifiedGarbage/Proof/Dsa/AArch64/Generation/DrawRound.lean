module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PrimeLoop
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SampleRound
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFrame
public import VerifiedGarbage.Proof.Dsa.AArch64.Run

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawBuffer
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Generation.WitnessSlice
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RoundHeader
/-! # One consumed draw, the shared round, and DSA's next loop state -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/SampleRoundHeader.lean`, which only this module imported.
section

/-! A complete witness iteration retains its immutable generation arguments. -/
section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64

theorem sampleRound_header_ranges {w j : Nat} (hj : j ∈ [16, 17, 18, 19, 24, 25, 27]) :
    ∀ r ∈ sampleRoundRanges w, 8 * j + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * j := by
  intro r hr
  rcases List.mem_append.mp hr with hm | ht
  · rcases List.mem_append.mp hm with htest | hrnd
    · simp only [testRanges, List.mem_cons, List.not_mem_nil, or_false] at htest
      have hj32 : j < 32 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega
      have hj1 : 1 ≤ j := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega
      rcases htest with rfl | rfl
      · left; simp only [slot, hdrBytes, aX]; omega_arith
      · right; simp only [kU]; omega
    · apply round_header_ranges w j ?_ r hrnd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ht
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases ht with rfl | rfl | rfl <;> decide

theorem sampleRoundRanges_le (w : Nat) : ∀ r ∈ sampleRoundRanges w, r.1 + r.2 ≤ slot w 28 := by
  intro r hr
  rcases List.mem_append.mp hr with hm | ht
  · rcases List.mem_append.mp hm with htest | hrnd
    · simp only [testRanges, List.mem_cons, List.not_mem_nil, or_false] at htest
      rcases htest with rfl | rfl <;> simp only [slot, hdrBytes, aX, kU] <;> omega_arith
    · have hh := witnessRoundRanges_lt w r hrnd
      simp only [slot, hdrBytes, aE] at hh ⊢
      omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
      simp only [slot, hdrBytes, kI, kElen, kUni, kP, kStat, sFn] <;> omega_arith

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaKeyGen.AArch64 VG.Proof.MillerRabin.AArch64
open VG.Proof.Dsa.Generation

def drawRoundRanges (w : Nat) : List (Nat × Nat) := [(8 * kUsed, 8)] ++ sampleRoundRanges w

theorem drawRound_ok (M : Mont) (K : Kernel) {P : PrimeParams} {used i uni : Nat} {s : State}
    (h : PrimeState P used s) (hroom : used + P.drawBytes ≤ P.rand.length)
    (hI : word s.mem P.B (8 * kI) = BitVec.ofNat 64 i)
    (hUni : word s.mem P.B (8 * kUni) = BitVec.ofNat 64 uni)
    (hi : i < 2 ^ 62) (huni : uni < 2 ^ 62) :
    WP isa (Impl.Dsa.AArch64.Generation.drawRound M.mm K.run P.len P.drawBytes) s fun t =>
      let wt := Spec.RsaKeyGen.witness (P.N - 1) (Spec.Rsa.os2ip ((P.rand.drop used).take P.drawBytes))
      let f := Proof.MillerRabin.Round.round P.N wt.1
      PrimeState P (used + P.drawBytes) t ∧
      word t.mem P.B (8 * kStat) = BitVec.ofNat 64 (if f then (if i + 1 < 17 ∨ uni + wt.2.toNat < P.checks then 4 else 1) else 3) ∧
      (f = true → word t.mem P.B (8 * kI) = BitVec.ofNat 64 (i + 1) ∧
        word t.mem P.B (8 * kUni) = BitVec.ofNat 64 (uni + wt.2.toNat)) ∧
      WorkFrame P.B (drawRoundRanges P.w) (primeExtras P) s.mem t.mem ∧ Keep mmRegs s t := by
  dsimp only
  unfold Impl.Dsa.AArch64.Generation.drawRound
  refine WP.seq (WP.mono (drawBuffer_ok h hroom) fun u ⟨hu, hsample, hfu, ku⟩ => ?_)
  have hIu : word u.mem P.B (8 * kI) = BitVec.ofNat 64 i :=
    (prime_frame_word h.ready.ws.scr.nowrap hfu (by decide : kI < 32) (by intro r hr; rw [List.mem_singleton.mp hr]; decide)).trans hI
  have hUniu : word u.mem P.B (8 * kUni) = BitVec.ofNat 64 uni :=
    (prime_frame_word h.ready.ws.scr.nowrap hfu (by decide : kUni < 32) (by intro r hr; rw [List.mem_singleton.mp hr]; decide)).trans hUni
  have hlen := P.slice_length hroom
  have hsamp := sampleRound_ok M K hsample P.w4 P.w128 P.exponentRoom
    (by rw [hlen]; exact P.bufferSeparate) P.odd P.n3 (by rw [hlen]; exact P.len2)
    (by rw [hlen]; have := P.lenDraw; have := P.drawMax; omega) (by rw [hlen]; exact P.lenWords)
    (by rw [hlen]; exact P.predBits) hIu hUniu hu.checks hi huni P.checksMax
  rw [hlen] at hsamp
  refine WP.mono hsamp fun t ⟨ht, hstat, hcount, hft, kt⟩ => ?_
  change WorkFrame P.B (sampleRoundRanges P.w) (primeExtras P) u.mem t.mem at hft
  have hused : word t.mem P.B (8 * kUsed) = BitVec.ofNat 64 (used + P.drawBytes) :=
    (prime_frame_word hu.ready.ws.scr.nowrap hft (by decide : kUsed < 32)
      (sampleRound_header_ranges (by decide : kUsed ∈ [16, 17, 18, 19, 24, 25, 27]))).trans hu.used
  have hpt := hu.advance ht hused hft kt
    (fun r hr => Nat.le_trans (sampleRoundRanges_le P.w r hr) P.room) (by
      intro k hk
      apply sampleRound_header_ranges
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hwt := witness_slice (r := P.rand) (used := used) P.lenDraw hroom P.predBits
  change Spec.RsaKeyGen.witness (P.N - 1) (Spec.Rsa.os2ip ((P.rand.drop used).take P.drawBytes)) =
    Spec.RsaKeyGen.witness (P.N - 1) (Spec.Rsa.os2ip (P.drawSlice used)) at hwt
  rw [← hwt] at hstat hcount
  exact ⟨hpt, hstat, hcount, (hfu.mono (fun r hr => List.mem_append_left _ hr)).trans
    (hft.mono (fun r hr => List.mem_append_right _ hr)), (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64.Generation
