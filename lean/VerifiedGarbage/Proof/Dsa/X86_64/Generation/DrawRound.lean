module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeLoop
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawBuffer
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Generation.WitnessSlice
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SampleRound
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRound
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TestWitness
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Sample
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.RoundTail
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrRoundAll
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Round
import VerifiedGarbage.Proof.Bignum.WorkFrame

/-! ### `Dsa.X86_64.Generation.SampleRound`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.RoundHeader`, which this module and modules that import it used -/

section

/-! # The shared round preserves DSA's tape pointers and witness counters -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin VG.Proof.MillerRabin.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem round_header_ranges {w k : Nat} (hk : k < 32)
    (hne : k ≠ 22 ∧ k ≠ 26 ∧ k ≠ 27 ∧ k ≠ 28 ∧ k ≠ 31) :
    ∀ r ∈ witnessRoundRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  simp only [witnessRoundRanges, Caller.callRanges, mutRanges, Proof.MillerRabin.Round.extended,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Caller.pad, slot, hdrBytes, aAcc, aTmp, aXm, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
  and_intros <;> omega_arith

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.RoundTail`, which only this module used -/

section

/-! # Reuse RSA's verified completion rule with DSA's uniform-round count -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem roundTail_ok {s : State} {B : Addr} {Z w N : Nat} {mi : BitVec 64}
    (h : ModulusReady s B Z w mi N) (hd : MrDims B Z w)
    {f u : Bool} {i uni ch : Nat}
    (hF : word s.mem B (8 * kFlag) = mask f) (hI : word s.mem B (8 * kI) = BitVec.ofNat 64 i)
    (hU : word s.mem B (8 * kU) = mask u) (hUni : word s.mem B (8 * kUni) = BitVec.ofNat 64 uni)
    (hC : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch)
    (hi : i < 2 ^ 62) (huni : uni < 2 ^ 62) (hch : ch < 2 ^ 62) :
    WP isa Impl.Dsa.X86_64.Generation.roundTail s fun t =>
      ModulusReady t B Z w mi N ∧
      word t.mem B (8 * kStat) = BitVec.ofNat 64 (if f then (if i + 1 < 17 ∨ uni + u.toNat < ch then 4 else 1) else 3) ∧
      (f = true → word t.mem B (8 * kI) = BitVec.ofNat 64 (i + 1) ∧
        word t.mem B (8 * kUni) = BitVec.ofNat 64 (uni + u.toNat)) ∧
      Frm B [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)] s.mem t.mem ∧ Keep [.rax, .rcx, .rdx] s t := by
  unfold Impl.Dsa.X86_64.Generation.roundTail
  refine WP.mono (VG.Proof.RsaKeyGen.X86_64.roundTail_ok h.good hd.z hF hI hU hUni hC hi huni hch)
    fun t ⟨hm, hk⟩ => ?_
  have hf : Frm B [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)] s.mem t.mem := by
    rw [hm]
    have wI := Frm.of_outside (rs := [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)])
      (writeW_outside s.mem B (BitVec.ofNat 64 (i + 1)) (d := 8 * kI) (by decide)) (by simp)
    cases f
    · exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by decide)) (by simp)
    · exact (wI.trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kUni) (by decide)) (by simp))).trans
        (Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by decide)) (by simp))
  refine ⟨h.of_frm hd hf hk ((hk.gpr (by decide)).trans h.good.rdi)
    (by rng_disj) (by rng_disj) (by rng_disj), ?_, ?_, hf, hk⟩
  · rw [hm]; cases f <;> simp only [↓reduceIte, Bool.false_eq_true, word_writeW_self]
  · intro htrue
    rw [hm, htrue]
    simp only [↓reduceIte]
    constructor
    · rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
    · rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]

end VG.Proof.Dsa.X86_64.Generation

end

end

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
  have hz : 256 ≤ Z := by have := hd.z; simp only [slot, hdrBytes] at this; omega_using [this]
  unfold Impl.Dsa.X86_64.Generation.sampleRound
  refine WP.seq (WP.mono (sampleWitness_ok h hd hodd hlen hmax hkw hbits)
    fun u ⟨hu, hxu, huu, hfu, ku⟩ => ?_)
  have hhdr : ∀ k, k = kI ∨ k = kUni ∨ k = kChecks → word u.mem B (8 * k) = word s.mem B (8 * k) := by
    intro k hk
    apply hfu.word_eq (Z := Z)
    · rcases hk with rfl | rfl | rfl <;> simp only [testRanges] <;> rng_disj
    · rcases hk with rfl | rfl | rfl <;> dsimp only [kI, kUni, kChecks, kU, kElen, kP, kE, sFn] <;> omega_using [hz]
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
    · rcases hk with rfl | rfl | rfl | rfl <;> dsimp only [kI, kUni, kChecks, kU, kElen, kP, kE, sFn] <;> omega_using [hz]
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

end

end

/-! ### `Dsa.X86_64.Generation.SampleRoundHeader`, which only this module used -/

section

/-! # Header slots retained by a complete DSA witness iteration -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum

/-- These slots carry the draw buffer, tape, and check count through an
entire iteration. Counters and the result status are intentionally omitted. -/
theorem sampleRound_header_ranges {w k : Nat}
    (hk : k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 23 ∨ k = 24 ∨ k = 25) :
    ∀ r ∈ sampleRoundRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  have hsmall : k < 32 := by omega_using [hk]
  have hne : k ≠ 22 ∧ k ≠ 26 ∧ k ≠ 27 ∧ k ≠ 28 ∧ k ≠ 31 := by omega_using [hk]
  intro r hr
  simp only [sampleRoundRanges, List.mem_append] at hr
  rcases hr with (hr | hr) | hr
  · simp only [testRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · left; simp only [slot, hdrBytes]; omega_using [hk]
    · left; simp only [slot, hdrBytes]; omega_using [hk]
    · left; change 8 * k + 8 ≤ 240; omega_using [hk]
  · exact round_header_ranges hsmall hne r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      dsimp only [VG.Impl.RsaKeyGen.X86_64.Candidate.kI, VG.Impl.RsaKeyGen.X86_64.Candidate.kElen,
        VG.Impl.RsaKeyGen.X86_64.Candidate.kUni, VG.Impl.RsaKeyGen.X86_64.Candidate.kP,
        VG.Impl.RsaKeyGen.X86_64.Candidate.kStat, sFn] <;> omega_using [hk]

open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem sampleRoundRanges_le (w : Nat) : ∀ r ∈ sampleRoundRanges w, r.1 + r.2 ≤ slot w 28 := by
  simp only [sampleRoundRanges, testRanges, witnessRoundRanges, Caller.callRanges,
    mutRanges, Proof.MillerRabin.Round.extended, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Caller.pad, slot, hdrBytes, aR1, aAcc, aTmp, aXm, kU, kI, kUni, kStat,
    kElen, kP, sFn, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
  and_intros <;> omega_using []

end VG.Proof.Dsa.X86_64.Generation

end

end


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
    (by rw [hlen]; have := P.lenDraw; have := P.drawMax; omega_arith) (by rw [hlen]; exact P.lenWords)
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
