module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedCall
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
import VerifiedGarbage.Proof.Framework.Omega
public import Mathlib.Algebra.Group.Nat.Defs

/-! # RSA's prepared witness and a generic shared round -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.MillerRabin VG.Proof.MillerRabin.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

def sharedMidRanges (w : Nat) : List (Nat × Nat) := witnessRanges w ++ Caller.callRanges w

theorem sharedKernel_hdr (w j : Nat) (hj : j ∈ [0, 16, 17, 18, 19, 20, 21, 23, 24, 25, 29, 30]) :
    ∀ r ∈ Caller.callRanges w, 8 * j + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * j := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Caller.callRanges, mutRanges, Proof.MillerRabin.Round.extended, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Caller.pad, slot, hdrBytes, aR1,
      Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
    and_intros <;> omega_arith

private theorem kernel_r2 (w : Nat) :
    ∀ r ∈ Caller.callRanges w, slot w aR2 + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aR2 := by
  simp only [Caller.callRanges, mutRanges, Proof.MillerRabin.Round.extended, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Caller.pad, slot, hdrBytes, aR1, aR2,
    Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
  and_intros <;> omega_arith

private theorem witness_exp (w : Nat) : ∀ r ∈ witnessRanges w, r.1 + r.2 ≤ slot w aE := by
  intro r hr
  simp only [witnessRanges, witRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl) | (rfl | rfl | rfl)
  all_goals simp only [slot, hdrBytes, aX, aAcc, aTmp, aXm, aE, kUsed, kU, sFn]; omega_arith

theorem sharedMid_ok (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) {s : State} {B : Addr} {Z w c bm : Nat} {mi : BitVec 64} {sp : Addr}
    (hd : MrDims B Z w) (hZ : slot w 28 ≤ Z) (henv : SharedEnv B Z sp s)
    (hc : MrCtx s B Z w mi c bm) (he : ECtx s.mem B w c)
    (hR2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c) (hc1 : 1 < c)
    (hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c)
    {rp : Addr} {used : Nat} {r : List Byte}
    (hR : word s.mem B (8 * kRand) = rp) (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w)) (hsrc : Src s B Z rp r)
    (hlen : used + 8 * w ≤ r.length)
    {i uni ch : Nat} (hI : word s.mem B (8 * kI) = BitVec.ofNat 64 i)
    (hN : word s.mem B (8 * kUni) = BitVec.ofNat 64 uni) (hC : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch) :
    WP isa (seqs ((mrWitness ++ [mm aXm aX aR2]) ++ [R.run])) s fun t =>
      (∃ bm', MrCtx t B Z w mi c bm') ∧ ECtx t.mem B w c ∧
      word t.mem B (8 * kFlag) = mask (passOf c w used r) ∧
      word t.mem B (8 * kI) = BitVec.ofNat 64 i ∧ word t.mem B (8 * kUni) = BitVec.ofNat 64 uni ∧
      word t.mem B (8 * kChecks) = BitVec.ofNat 64 ch ∧
      word t.mem B (8 * kU) = mask (wtOf c w used r).2 ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 (used + 8 * w) ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c ∧
      SharedFrame B sp (sharedMidRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have ho : c % 2 = 1 := hsh.1
  have hc3 : 3 ≤ c := by omega_arith
  obtain ⟨_, hb, _⟩ := VG.Proof.RsaKeyGen.cand_bits (by have := hd.w4; omega_arith) hsh
  have hn := hc.good.scr.nowrap
  have hz := hd.z
  refine wp_seqs_append (by simp [mrWitness]) (by simp) ?_
  refine WP.mono (sharedWitness_call_ok M hmc henv hd hc hR2 ho hc1 hb hR hU hK hsrc hlen) ?_
  rintro u ⟨hcu, hx, hr2, hu, hus, hfrm, hk⟩
  have heu : ECtx u.mem B w c :=
    ⟨by rw [SharedFrame.array hfrm henv (fun r hr => Or.inr (witness_exp w r hr)) (by have := aE_fits hd; omega_arith) hn]; exact he.e,
      by rw [SharedFrame.word hfrm henv (fun r hr => Or.inr (by have := witness_exp w r hr; omega_arith))
        (by have := aE_fits hd; omega_arith) hn]; exact he.l⟩
  have hx' : wv u.mem B (slot w aXm) w = (wtOf c w used r).1 % c * 2 ^ (64 * w) % c := by
    simpa only [wtOf, Nat.mod_mul_mod] using hx
  have henu := henv.kept hk (by decide)
  simp only [seqs]
  refine WP.mono (R.ok hcu heu hd hZ henu.room ho hc3 hx') ?_
  rintro t ⟨hct, het, hf, hfr, kt⟩
  have hfr : SharedFrame B sp (Caller.callRanges w) u.mem t.mem := by
    rw [henu.rsp] at hfr
    exact hfr
  have hfm : SharedFrame B sp (sharedMidRanges w) s.mem t.mem :=
    (hfrm.mono (fun r hr => List.mem_append_left _ hr)).trans
      (hfr.mono (fun r hr => List.mem_append_right _ hr))
  refine ⟨hct, het, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfm, (hk.trans kt).mono (by decide)⟩
  · simpa only [Proof.MillerRabin.Round.round, passOf] using hf
  · rw [SharedFrame.word hfm henv (d := 8 * kI) ?_ (by have := hdr_lt_slot w 28 (show kI < 32 by decide); omega_arith) hn]
    · exact hI
    · intro r hr
      rcases List.mem_append.mp hr with hw | hk
      · simp only [witnessRanges, witRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with (rfl | rfl | rfl) | (rfl | rfl | rfl) <;> rng_disj
      · exact sharedKernel_hdr w kI (by simp [kI, kElen, sFn]) r hk
  · rw [SharedFrame.word hfm henv (d := 8 * kUni) ?_ (by have := hdr_lt_slot w 28 (show kUni < 32 by decide); omega_arith) hn]
    · exact hN
    · intro r hr
      rcases List.mem_append.mp hr with hw | hk
      · simp only [witnessRanges, witRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with (rfl | rfl | rfl) | (rfl | rfl | rfl) <;> rng_disj
      · exact sharedKernel_hdr w kUni (by simp [kUni, kP, sFn]) r hk
  · rw [SharedFrame.word hfm henv (d := 8 * kChecks) ?_ (by have := hdr_lt_slot w 28 (show kChecks < 32 by decide); omega_arith) hn]
    · exact hC
    · intro r hr
      rcases List.mem_append.mp hr with hw | hk
      · simp only [witnessRanges, witRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with (rfl | rfl | rfl) | (rfl | rfl | rfl) <;> rng_disj
      · exact sharedKernel_hdr w kChecks (by simp [kChecks, kE, sFn]) r hk
  · rw [SharedFrame.word hfr henv (sharedKernel_hdr w kU (by simp [kU, sFn])) (by have := hdr_lt_slot w 28 (show kU < 32 by decide); omega_arith) hn]
    exact hu
  · rw [SharedFrame.word hfr henv (sharedKernel_hdr w kUsed (by simp [kUsed, sFn])) (by have := hdr_lt_slot w 28 (show kUsed < 32 by decide); omega_arith) hn]
    exact hus
  · have hslot := slot_le (w := w) (show aR2 < 8 by decide)
    rw [SharedFrame.array hfr henv (kernel_r2 w) (by omega_arith) hn]
    exact hr2

end VG.Proof.RsaKeyGen.X86_64
