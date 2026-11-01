module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SampleRound
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRound
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TestWitness

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Sample
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundHeader
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundTail
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Round
import VerifiedGarbage.Proof.Bignum.WorkFrame
/-! # A complete DSA primality iteration through the callable RSA round -/

-- Formerly `VerifiedGarbage/Proof/Dsa/Generation/WorkFrame.lean`, which only this module imported.
section

/-! # Compose workspace changes and separate buffer or call-stack changes -/

section
namespace VG.Proof.Dsa.Generation
open VG VG.Proof.Bignum

theorem workFrame_append {B : Addr} {rs₁ rs₂ : List (Nat × Nat)} {ex₁ ex₂ : List Region}
    {m₁ m₂ m₃ : Mem} (h₁ : WorkFrame B rs₁ ex₁ m₁ m₂) (h₂ : WorkFrame B rs₂ ex₂ m₂ m₃) :
    WorkFrame B (rs₁ ++ rs₂) (ex₁ ++ ex₂) m₁ m₃ := by
  intro x hx hr
  exact (h₂ x (fun r h => hx r (List.mem_append_right _ h))
    (fun r h => hr r (List.mem_append_right _ h))).trans
      (h₁ x (fun r h => hx r (List.mem_append_left _ h))
        (fun r h => hr r (List.mem_append_left _ h)))

end VG.Proof.Dsa.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate
open VG.Proof.MillerRabin.X86_64 VG.Proof.Dsa.Generation

def sampleRoundRanges (w : Nat) : List (Nat × Nat) :=
  testRanges w ++ witnessRoundRanges w ++ [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)]

theorem sampleRound_ok (M : Mont) (K : Kernel) {B p : Addr} {Z w N i uni ch : Nat} {mi : BitVec 64}
    {bs : List Byte} {s : State}
    (h : SampleState B p Z w N mi bs s) (hd : MrDims B Z w) (hZ : slot w 28 ≤ Z)
    (hr : Caller.Room s B Z) (hout : Region.Disjoint ⟨B, Z⟩ ⟨p, bs.length⟩)
    (hodd : N % 2 = 1) (hN : 3 ≤ N)
    (hlen : 2 ≤ bs.length) (hmax : bs.length < 2 ^ 31) (hkw : (bs.length + 7) / 8 ≤ w)
    (hbits : Spec.RsaKeyGen.bitLength (N - 1) = 8 * bs.length)
    (hI : word s.mem B (8 * kI) = BitVec.ofNat 64 i)
    (hUni : word s.mem B (8 * kUni) = BitVec.ofNat 64 uni)
    (hC : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch)
    (hi : i < 2 ^ 62) (huni : uni < 2 ^ 62) (hch : ch < 2 ^ 62) :
    WP isa (Impl.Dsa.X86_64.Generation.sampleRound M.mm K.run) s fun t =>
      let wt := Spec.RsaKeyGen.witness (N - 1) (Spec.Rsa.os2ip bs)
      let f := Proof.MillerRabin.Round.round N wt.1
      ModulusReady t B Z w mi N ∧
      word t.mem B (8 * kStat) = BitVec.ofNat 64 (if f then (if i + 1 < 17 ∨ uni + wt.2.toNat < ch then 4 else 1) else 3) ∧
      (f = true → word t.mem B (8 * kI) = BitVec.ofNat 64 (i + 1) ∧
        word t.mem B (8 * kUni) = BitVec.ofNat 64 (uni + wt.2.toNat)) ∧
      WorkFrame B (sampleRoundRanges w) [⟨p, bs.length⟩, below (s.gpr .rsp) 128] s.mem t.mem ∧ Keep mmRegs s t := by
  dsimp only
  have hz : 256 ≤ Z := by have := hd.z; simp only [slot, hdrBytes] at this; omega
  unfold Impl.Dsa.X86_64.Generation.sampleRound
  refine WP.seq (WP.mono (sampleWitness_ok h hd hodd hlen hmax hkw hbits)
    fun u ⟨hu, hxu, huu, hfu, ku⟩ => ?_)
  have hhdr : ∀ k, k = kI ∨ k = kUni ∨ k = kChecks → word u.mem B (8 * k) = word s.mem B (8 * k) := by
    intro k hk
    apply hfu.word_eq (Z := Z)
    · rcases hk with rfl | rfl | rfl <;> simp only [testRanges] <;> rng_disj
    · rcases hk with rfl | rfl | rfl <;> dsimp only [kI, kUni, kChecks, kU, kElen, kP, kE, sFn] <;> omega
    · exact h.ready.good.scr.nowrap
    · simpa using hout
  have hsp : u.gpr .rsp = s.gpr .rsp := ku.gpr (by decide)
  have hru : Caller.Room u B Z := ⟨by rw [hsp]; exact hr.size, by rw [hsp]; exact hr.disjoint⟩
  refine WP.seq (WP.mono (round_ok M K hu hd hZ hru hodd hN hxu) fun v ⟨hv, hflag, hfv, kv⟩ => ?_)
  have hvhdr : ∀ k, k = kI ∨ k = kUni ∨ k = kChecks ∨ k = kU →
      word v.mem B (8 * k) = word u.mem B (8 * k) := by
    intro k hk
    apply hfv.word_eq (Z := Z)
    · apply round_header_ranges
      · rcases hk with rfl | rfl | rfl | rfl <;> decide
      · rcases hk with rfl | rfl | rfl | rfl <;> decide
    · rcases hk with rfl | rfl | rfl | rfl <;> dsimp only [kI, kUni, kChecks, kU, kElen, kP, kE, sFn] <;> omega
    · exact hu.good.scr.nowrap
    · simpa using hru.disjoint
  refine WP.mono (roundTail_ok hv hd hflag
    ((hvhdr kI (by simp)).trans ((hhdr kI (by simp)).trans hI))
    ((hvhdr kU (by simp)).trans huu)
    ((hvhdr kUni (by simp)).trans ((hhdr kUni (by simp)).trans hUni))
    ((hvhdr kChecks (by simp)).trans ((hhdr kChecks (by simp)).trans hC)) hi huni hch)
    fun t ⟨ht, hstat, hcount, hft, kt⟩ => ?_
  rw [hsp] at hfv
  have hfuv := workFrame_append hfu hfv
  refine ⟨ht, hstat, hcount, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  exact (hfuv.mono (fun r hr => List.mem_append_left _ hr)).trans
    (hft.work.mono (fun r hr => List.mem_append_right _ hr))

end VG.Proof.Dsa.X86_64.Generation
