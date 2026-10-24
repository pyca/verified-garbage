module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseWitness
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Rounds

/-! # FFDH parameter generation on x86-64: run and account for a modulus policy -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)

def PhaseOutcome (p : CandidateP) (used consumed : Nat) (q : Bool) (m : Mem) : Prop :=
  match checkWitnesses (p.phaseValue q) (Spec.Ffdh.primeChecks (p.phaseBits q)) (p.rand.drop used) with
  | none => word m p.B (8 * oStatus) = 0
  | some (pass, rest) => word m p.B (8 * oStatus) = BitVec.ofNat 64 (if pass then 1 else 2) ∧
      rest = p.rand.drop (used + consumed)

theorem PhaseOutcome.congr {p : CandidateP} {used consumed : Nat} {q : Bool} {m m' : Mem}
    (h : PhaseOutcome p used consumed q m)
    (hs : word m' p.B (8 * oStatus) = word m p.B (8 * oStatus)) :
    PhaseOutcome p used consumed q m' := by
  unfold PhaseOutcome at *
  simpa only [hs] using h

def PhaseRoundsPost (p : CandidateP) (used : Nat) (q : Bool) (s t : State) : Prop :=
  ∃ consumed, consumed ≤ (p.rand.drop used).length ∧ CandidateTape p (used + consumed) t ∧
    t.gpr .rdi = off p.B 256 ∧ word t.mem (off p.B 256) (8 * VG.Impl.Rsa.X86_64.Crt.sLink) = p.B ∧
    PhaseOutcome p used consumed q t.mem ∧
    CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧ Keep mmRegs s t

theorem rounds_state_ok (M : Mont) (K : Kernel)
    {p : CandidateP} {used : Nat} {q : Bool} {s : State} {mi : BitVec 64}
    (h : CandidateTape p used s) (hp : PhaseHeader p q s) (ho : p.phaseValue q % 2 = 1)
    (hr : ModulusReady s (off p.B 256) (p.Z - 256) (p.phaseWords q) mi (p.phaseValue q)) :
    WP isa (rounds M.mm K.run) s (PhaseRoundsPost p used q s) := by
  let wp := h.base.witnessParams q mi ho
  have hdraw : DrawState wp (off p.rp used) used (p.rand.drop used) s := h.drawState hp ho hr
  have hchecks : 0 < Spec.Ffdh.primeChecks (p.phaseBits q) ∧
      Spec.Ffdh.primeChecks (p.phaseBits q) < 2 ^ 31 := by
    unfold Spec.Ffdh.primeChecks
    split <;> decide
  refine WP.mono (rounds_ok M K hdraw (h.roundRoom ho) hp.checks hchecks.1 hchecks.2)
    fun t ⟨n, hn, ht, hresult, hs, hf, kt⟩ => ?_
  have hfr : CandidateFrame p s.mem t.mem := by
    intro a ha hout hstack
    apply hf a ha
    · intro i hi
      exact hout i (Nat.lt_of_lt_of_le hi (h.base.phase_load_widths q).2.2)
    · rw [h.base.sp]; exact hstack
  have hsave : CandidateSaved p s.mem t.mem := by
    intro j hj
    exact hs j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hb := h.base.keep hfr hsave kt ((kt.gpr (by decide)).trans h.base.sp)
  have htape : CandidateTape p (used + n) t := by
    refine ⟨hb, ?_, ?_, ?_, ht.usedWord⟩
    · rw [List.length_drop] at hn
      omega_using [hn, h.bound]
    · change word t.mem p.B (8 * oRandPtr) = off p.rp (used + n)
      have hx : word t.mem p.B (8 * oRandPtr) = off (off p.rp used) n := ht.ptr
      simpa only [off_off] using hx
    · change word t.mem p.B (8 * oRandLeft) = BitVec.ofNat 64 (p.rand.length - (used + n))
      have hx : word t.mem p.B (8 * oRandLeft) = BitVec.ofNat 64 ((p.rand.drop used).drop n).length := ht.left
      simpa only [List.length_drop, Nat.sub_sub] using hx
  refine ⟨n, hn, htape, ht.ready.good.rdi, ht.link, ?_, hsave, hfr, kt⟩
  change (match checkWitnesses (p.phaseValue q) (Spec.Ffdh.primeChecks (p.phaseBits q)) (p.rand.drop used) with
      | none => word t.mem p.B (8 * oStatus) = 0
      | some (pass, rest) => word t.mem p.B (8 * oStatus) = BitVec.ofNat 64 (if pass then 1 else 2) ∧
          rest = p.rand.drop (used + n))
  cases he : checkWitnesses (p.phaseValue q) (Spec.Ffdh.primeChecks (p.phaseBits q)) (p.rand.drop used) with
  | none => simpa only [wp, CandidateBase.witnessParams, he] using hresult
  | some ar =>
    obtain ⟨pass, rest⟩ := ar
    simpa only [wp, CandidateBase.witnessParams, he, List.drop_drop] using hresult

end VG.Proof.Ffdh.X86_64.ParameterCandidate
