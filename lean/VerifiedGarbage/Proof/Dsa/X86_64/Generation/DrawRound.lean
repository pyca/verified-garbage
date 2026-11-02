module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeLoop
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SampleRound
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawBuffer
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SampleRoundHeader
import VerifiedGarbage.Proof.Dsa.Generation.WitnessSlice

/-! # One consumed draw, the shared round, and DSA's next loop state -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate VG.Proof.MillerRabin.X86_64
open VG.Proof.Dsa.Generation

def drawRoundRanges (w : Nat) : List (Nat × Nat) := [(8 * kUsed, 8)] ++ sampleRoundRanges w

theorem drawRound_ok (M : Mont) (K : Kernel) {P : PrimeParams} {mi : BitVec 64} {used i uni : Nat} {s : State}
    (h : PrimeState P mi used s) (hroom : used + P.drawBytes ≤ P.rand.length)
    (hI : word s.mem P.B (8 * kI) = BitVec.ofNat 64 i)
    (hUni : word s.mem P.B (8 * kUni) = BitVec.ofNat 64 uni)
    (hi : i < 2 ^ 62) (huni : uni < 2 ^ 62) :
    WP isa (Impl.Dsa.X86_64.Generation.drawRound M.mm K.run) s fun t =>
      let wt := Spec.RsaKeyGen.witness (P.N - 1) (Spec.Rsa.os2ip ((P.rand.drop used).take P.drawBytes))
      let f := Proof.MillerRabin.Round.round P.N wt.1
      PrimeState P mi (used + P.drawBytes) t ∧
      word t.mem P.B (8 * kStat) = BitVec.ofNat 64 (if f then (if i + 1 < 17 ∨ uni + wt.2.toNat < P.checks then 4 else 1) else 3) ∧
      (f = true → word t.mem P.B (8 * kI) = BitVec.ofNat 64 (i + 1) ∧
        word t.mem P.B (8 * kUni) = BitVec.ofNat 64 (uni + wt.2.toNat)) ∧
      WorkFrame P.B (drawRoundRanges P.w) (primeExtras P) s.mem t.mem ∧ Keep mmRegs s t := by
  dsimp only
  unfold Impl.Dsa.X86_64.Generation.drawRound
  refine WP.seq (WP.mono (drawBuffer_ok h hroom) fun u ⟨hu, hsample, hfu, ku⟩ => ?_)
  have hIu : word u.mem P.B (8 * kI) = BitVec.ofNat 64 i :=
    (prime_frame_word h.ready.good.scr.nowrap hfu (by decide : kI < 32) (by rng_disj)).trans hI
  have hUniu : word u.mem P.B (8 * kUni) = BitVec.ofNat 64 uni :=
    (prime_frame_word h.ready.good.scr.nowrap hfu (by decide : kUni < 32) (by rng_disj)).trans hUni
  have hlen := P.slice_length hroom
  have hsamp := sampleRound_ok M K hsample P.dims P.room hu.callRoom
    (by rw [hlen]; exact P.bufferSeparate) P.odd P.n3 (by rw [hlen]; exact P.len2)
    (by rw [hlen]; have := P.lenDraw; have := P.drawMax; omega) (by rw [hlen]; exact P.lenWords)
    (by rw [hlen]; exact P.predBits) hIu hUniu hu.checks hi huni P.checksMax
  rw [hlen] at hsamp
  refine WP.mono hsamp fun t ⟨ht, hstat, hcount, hft, kt⟩ => ?_
  rw [hu.stack] at hft
  change WorkFrame P.B (sampleRoundRanges P.w) (primeExtras P) u.mem t.mem at hft
  have hused : word t.mem P.B (8 * kUsed) = BitVec.ofNat 64 (used + P.drawBytes) :=
    (prime_frame_word hu.ready.good.scr.nowrap hft (by decide : kUsed < 32)
      (sampleRound_header_ranges (by decide : kUsed = 16 ∨ kUsed = 17 ∨ kUsed = 18 ∨ kUsed = 19 ∨ kUsed = 23 ∨ kUsed = 24 ∨ kUsed = 25))).trans hu.used
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

end VG.Proof.Dsa.X86_64.Generation
