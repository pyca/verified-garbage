module

public import VerifiedGarbage.Spec.Ffdh
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.WitnessRange
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessMont
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
import VerifiedGarbage.Proof.Ffdh.MillerRabin
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH parameter candidates on x86-64: reuse the callable windowed Miller–Rabin round -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin VG.Proof.MillerRabin.X86_64

private theorem round_constant (w j : Nat) (hj : j = aOne ∨ j = aR2) :
    ∀ r ∈ Caller.callRanges w, slot w j + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
  rcases hj with rfl | rfl
  all_goals
    simp only [Caller.callRanges, mutRanges, Proof.MillerRabin.Round.extended, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Caller.pad, slot, hdrBytes, aR1, aOne, aR2,
      Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
    and_intros <;> omega

theorem sharedRound_ok (K : Kernel) {s : State} {B : Addr} {Z w N a : Nat} {mi : BitVec 64}
    (h : ModulusReady s B Z w mi N) (hd : MrDims B Z w) (hZ : slot w 28 ≤ Z) (hr : Caller.Room s B Z)
    (ho : N % 2 = 1) (hN : 3 ≤ N)
    (ha : wv s.mem B (slot w aXm) w = a % N * 2 ^ (64 * w) % N) :
    WP isa K.run s fun t => ModulusReady t B Z w mi N ∧
      word t.mem B (8 * kFlag) = mask (Proof.MillerRabin.Round.round N a) ∧
      WorkFrame B (Caller.callRanges w) [below (s.gpr .rsp) 128] s.mem t.mem ∧ Keep mmRegs s t := by
  have hc : MrCtx s B Z w mi N (wv s.mem B (slot w aB) w) := ⟨h.good, h.inv, h.n, rfl, h.r1, h.rm1⟩
  refine WP.mono (K.ok hc h.exponent hd hZ hr ho hN ha) fun t ⟨⟨bm, hc'⟩, he, hf, hfrm, k⟩ => ?_
  have hread : ∀ j < 8, slot w j + 8 * w ≤ Z := by
    intro j hj
    have hb := slot_le (w := w) hj
    omega_using [hb, hd.z]
  have hconst : ∀ j, j = aOne ∨ j = aR2 → wv t.mem B (slot w j) w = wv s.mem B (slot w j) w := by
    intro j hj
    apply hfrm.wv_eq (round_constant w j hj) (hread j (by rcases hj with rfl | rfl <;> decide)) h.good.scr.nowrap
    intro r hr'
    simp only [List.mem_singleton] at hr'
    subst hr'
    exact hr.disjoint
  exact ⟨⟨hc'.good, hc'.inv, hc'.n, by rw [hconst aOne (Or.inl rfl)]; exact h.one,
    by rw [hconst aR2 (Or.inr rfl)]; exact h.r2, hc'.r1, hc'.rm1, he⟩, hf, hfrm, k⟩

def witnessRoundRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))] ++ Caller.callRanges w

/-- A masked draw uses the same callable windowed round as RSA, with FFDH's mathematical test. -/
theorem witnessRound_ok (M : Mont) (K : Kernel) {s : State} {B : Addr} {Z w N a : Nat} {mi : BitVec 64}
    (h : ModulusReady s B Z w mi N) (hd : MrDims B Z w) (hZ : slot w 28 ≤ Z) (hr : Caller.Room s B Z)
    (ho : N % 2 = 1) (hN : 3 ≤ N) (ha : wv s.mem B (slot w aXm) w = a) :
    WP isa (witnessRound M.mm K.run) s fun t => ModulusReady t B Z w mi N ∧
      word t.mem B (8 * kFlag) = mask (Spec.Ffdh.mrRound N a) ∧
      WorkFrame B (witnessRoundRanges w) [below (s.gpr .rsp) 128] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold witnessRound
  refine WP.seq (WP.mono (witnessMont_ok M h hd ho (by omega) ha) fun u ⟨hu, hxm, hf, k⟩ => ?_)
  have hsp : u.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  have hru : Caller.Room u B Z := ⟨by rw [hsp]; exact hr.size, by rw [hsp]; exact hr.disjoint⟩
  refine WP.mono (sharedRound_ok K hu hd hZ hru ho hN hxm) fun t ⟨ht, hflag, hf', k'⟩ => ?_
  rw [hsp] at hf'
  refine ⟨ht, ?_, (hf.work.mono (fun r hr => List.mem_append_left _ hr)).trans
    (hf'.mono (fun r hr => List.mem_append_right _ hr)), (k.trans k').mono (by decide)⟩
  simpa only [Proof.MillerRabin.Round.round, VG.Proof.Ffdh.rsa_round_eq a hN ho] using hflag

end VG.Proof.Ffdh.X86_64.ParameterCandidate
