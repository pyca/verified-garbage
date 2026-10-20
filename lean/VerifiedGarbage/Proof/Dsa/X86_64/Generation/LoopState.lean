module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawRound
import VerifiedGarbage.Proof.Framework.Omega

/-! # The invariant and result of DSA's finite blinded witness loop -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure PrimeLoopState (P : PrimeParams) (mi : BitVec 64) (s₀ : State)
    (res : Option (Bool × List Byte)) (i uni used : Nat) (s : State) : Prop where
  state : PrimeState P mi used s
  ki : word s.mem P.B (8 * kI) = BitVec.ofNat 64 i
  kuni : word s.mem P.B (8 * kUni) = BitVec.ofNat 64 uni
  usedBound : used ≤ P.rand.length
  i1 : 1 ≤ i
  countBound : P.drawBytes * (i - 1) ≤ used
  uniformBound : uni ≤ i
  go : i ≤ Spec.RsaKeyGen.blindedChecks ∨ uni < P.checks
  rest : primeRest P i uni used = res
  frame : WorkFrame P.B (drawRoundRanges P.w) (primeExtras P) s₀.mem s.mem
  keep : Keep mmRegs s₀ s

def PrimeLoopEnd (P : PrimeParams) (mi : BitVec 64) (s₀ : State)
    (res : Option (Bool × List Byte)) (s : State) : Prop :=
  ∃ used, PrimeState P mi used s ∧ used ≤ P.rand.length ∧
    (res = none → word s.mem P.B (8 * kStat) = BitVec.ofNat 64 0) ∧
    (∀ b rest, res = some (b, rest) →
      word s.mem P.B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 3) ∧ used = P.rand.length - rest.length) ∧
    WorkFrame P.B (drawRoundRanges P.w) (primeExtras P) s₀.mem s.mem ∧ Keep mmRegs s₀ s

theorem PrimeLoopState.counter_bound {P : PrimeParams} {mi : BitVec 64} {s₀ s : State}
    {res : Option (Bool × List Byte)} {i uni used : Nat} (h : PrimeLoopState P mi s₀ res i uni used s) :
    i < 2 ^ 62 ∧ uni < 2 ^ 62 := by
  have hb := Nat.le_trans (Nat.mul_le_mul_right (i - 1) P.drawMin) h.countBound
  have hr := P.randMax
  have hu := h.usedBound
  have hi := h.i1
  have hn := h.uniformBound
  omega

theorem PrimeLoopState.of_mem {P : PrimeParams} {mi : BitVec 64} {s₀ s t : State}
    {res : Option (Bool × List Byte)} {i uni used : Nat} (h : PrimeLoopState P mi s₀ res i uni used s)
    (hm : t.mem = s.mem) (hk : Keep mmRegs s t) : PrimeLoopState P mi s₀ res i uni used t := by
  exact ⟨h.state.of_mem hm hk, by rw [hm]; exact h.ki, by rw [hm]; exact h.kuni,
    h.usedBound, h.i1, h.countBound, h.uniformBound, h.go, h.rest,
    by rw [hm]; exact h.frame, (h.keep.trans hk).mono (by decide)⟩

theorem PrimeLoopEnd.of_mem {P : PrimeParams} {mi : BitVec 64} {s₀ s t : State}
    {res : Option (Bool × List Byte)} (h : PrimeLoopEnd P mi s₀ res s)
    (hm : t.mem = s.mem) (hk : Keep mmRegs s t) : PrimeLoopEnd P mi s₀ res t := by
  obtain ⟨used, hs, hu, he, hr, hf, hkeep⟩ := h
  refine ⟨used, hs.of_mem hm hk, hu, ?_, ?_, ?_, (hkeep.trans hk).mono (by decide)⟩
  · intro hn; rw [hm]; exact he hn
  · intro b rest hr'; rw [hm]; exact hr b rest hr'
  · rw [hm]; exact hf

theorem primeLoopEnd_some {P : PrimeParams} {mi : BitVec 64} {s₀ s : State}
    {res : Option (Bool × List Byte)} {used : Nat} {b : Bool}
    (h : PrimeState P mi used s) (hu : used ≤ P.rand.length)
    (hres : res = some (b, P.rand.drop used))
    (hstat : word s.mem P.B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 3))
    (hf : WorkFrame P.B (drawRoundRanges P.w) (primeExtras P) s₀.mem s.mem)
    (hk : Keep mmRegs s₀ s) : PrimeLoopEnd P mi s₀ res s := by
  refine ⟨used, h, hu, ?_, ?_, hf, hk⟩
  · intro hn; rw [hres] at hn; cases hn
  · intro b' rest he
    have hpair := Option.some.inj (hres.symm.trans he)
    obtain ⟨hb, hr⟩ := Prod.mk.inj hpair
    subst b' rest
    exact ⟨hstat, by rw [List.length_drop]; omega⟩

end VG.Proof.Dsa.X86_64.Generation
