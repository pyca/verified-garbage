module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Data
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrBit
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.WordShape
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Context
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessState
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages

/-! # FFDH parameter generation on x86-64: p and q phase widths and values -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.RsaKeyGen.X86_64

def CandidateP.phaseBits (p : CandidateP) (q : Bool) : Nat := if q then p.bits - 1 else p.bits
def CandidateP.phaseLen (p : CandidateP) (q : Bool) : Nat := (p.phaseBits q + 7) / 8
def CandidateP.phaseWords (p : CandidateP) (q : Bool) : Nat := (p.phaseLen q + 7) / 8
def CandidateP.phaseValue (p : CandidateP) (q : Bool) : Nat := if q then p.Q else p.P

theorem CandidateBase.phase_room {p : CandidateP} {s : State} (h : CandidateBase p s) (q : Bool) :
    4 ≤ p.phaseWords q ∧ p.phaseWords q ≤ 128 ∧ 256 + slot (p.phaseWords q) 28 ≤ p.Z := by
  exact candidate_room h.bits1 h.bits2 h.len h.room q

theorem CandidateBase.phase_dims {p : CandidateP} {s : State} (h : CandidateBase p s) (q : Bool) :
    MrDims (off p.B 256) (p.Z - 256) (p.phaseWords q) := by
  have hr : 256 + (256 + 28 * (8 * (p.phaseWords q + 2))) ≤ p.Z := (h.phase_room q).2.2
  refine ⟨?_, ?_, (h.phase_room q).1, (h.phase_room q).2.1⟩
  · change 256 + 8 * (8 * (p.phaseWords q + 2)) ≤ p.Z - 256
    omega_using [hr]
  · change 256 + 26 * (8 * (p.phaseWords q + 2)) + 8 * (p.phaseWords q + 2) ≤ p.Z - 256
    omega_using [hr]

theorem phase_width64 (p : CandidateP) (q : Bool) : p.phaseWords q = (p.phaseBits q + 63) / 64 := by
  unfold CandidateP.phaseWords CandidateP.phaseLen
  omega

theorem CandidateBase.phase_wordshape {p : CandidateP} {s : State} (h : CandidateBase p s) (q : Bool) :
    2 ^ (64 * (p.phaseWords q - 1)) ≤ p.phaseValue q ∧ p.phaseValue q < 2 ^ (64 * p.phaseWords q) := by
  rw [phase_width64]
  cases q
  · change 2 ^ (64 * ((p.bits + 63) / 64 - 1)) ≤ p.P ∧ p.P < 2 ^ (64 * ((p.bits + 63) / 64))
    exact VG.Proof.Ffdh.ParameterCandidate.candidate_word_shape (by omega_using [h.bits1]) _
  · change 2 ^ (64 * ((p.bits - 1 + 63) / 64 - 1)) ≤ p.Q ∧ p.Q < 2 ^ (64 * ((p.bits - 1 + 63) / 64))
    exact VG.Proof.Ffdh.ParameterCandidate.half_word_shape (by omega_using [h.bits1]) _

theorem CandidateBase.phase_bitLength {p : CandidateP} {s : State} (h : CandidateBase p s) (q : Bool)
    (hodd : p.phaseValue q % 2 = 1) :
    Spec.RsaKeyGen.bitLength (p.phaseValue q) = p.phaseBits q ∧
      Spec.RsaKeyGen.bitLength (p.phaseValue q - 1) = p.phaseBits q := by
  cases q
  · change Spec.RsaKeyGen.bitLength p.P = p.bits ∧ Spec.RsaKeyGen.bitLength (p.P - 1) = p.bits
    exact VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength (by omega_using [h.bits1]) _
  · change Spec.RsaKeyGen.bitLength p.Q = p.bits - 1 ∧ Spec.RsaKeyGen.bitLength (p.Q - 1) = p.bits - 1
    exact ⟨VG.Proof.Ffdh.ParameterCandidate.half_bitLength (by omega_using [h.bits1]) _,
      VG.Proof.Ffdh.ParameterCandidate.half_pred_bitLength (by omega_using [h.bits1]) _ hodd⟩

theorem CandidateBase.phase_large {p : CandidateP} {s : State} (h : CandidateBase p s) (q : Bool) :
    8161 < p.phaseValue q := by
  have hlo := (h.phase_wordshape q).1
  have hp : 2 ^ 14 ≤ 2 ^ (64 * (p.phaseWords q - 1)) :=
    Nat.pow_le_pow_right (by decide) (by omega_using [(h.phase_room q).1])
  omega_using [hlo, hp]

theorem CandidateBase.phase_load_widths {p : CandidateP} {s : State} (h : CandidateBase p s) (q : Bool) :
    p.phaseWords q ≤ (p.k + 7) / 8 ∧ (p.k + 7) / 8 ≤ p.phaseWords q + 1 ∧ p.phaseLen q ≤ p.k := by
  cases q <;> simp only [CandidateP.phaseWords, CandidateP.phaseLen, CandidateP.phaseBits] <;> simp
  all_goals omega_using [h.len, h.bits1, h.bits2]

theorem CandidateBase.phase_table_room {p : CandidateP} {s : State} (h : CandidateBase p s) (q : Bool) :
    slot (p.phaseWords q) VG.Impl.RsaKeyGen.X86_64.Candidate.aTab + 2048 ≤ p.Z - 256 := by
  have hw := (h.phase_load_widths q).1
  have hk := h.widths.1
  have hz := h.room
  change 256 + 11 * (8 * (p.phaseWords q + 2)) + 2048 ≤ p.Z - 256
  omega_using [hw, hk, hz]

structure PhaseHeader (p : CandidateP) (q : Bool) (s : State) : Prop where
  bits : word s.mem p.B (8 * oWitnessBits) = BitVec.ofNat 64 (p.phaseBits q)
  len : word s.mem p.B (8 * oWitnessLen) = BitVec.ofNat 64 (p.phaseLen q)
  checks : word s.mem p.B (8 * oChecks) = BitVec.ofNat 64 (Spec.Ffdh.primeChecks (p.phaseBits q))
  link : word s.mem (off p.B 256) (8 * VG.Impl.Rsa.X86_64.Crt.sLink) = p.B

theorem PhaseHeader.of_inner {p : CandidateP} {q : Bool} {s t : State} {rs : List (Nat × Nat)}
    (h : PhaseHeader p q s) (hb : CandidateBase p s) (hf : Frm (off p.B 256) rs s.mem t.mem)
    (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z - 256)
    (hl : ∀ r ∈ rs, 136 ≤ r.1 ∨ r.1 + r.2 ≤ 128) : PhaseHeader p q t := by
  have hh := hb.inner_header hf hrs
  refine ⟨(hh _ (by decide)).trans h.bits, (hh _ (by decide)).trans h.len,
    (hh _ (by decide)).trans h.checks, ?_⟩
  rw [hf.word_eq (d := 8 * VG.Impl.Rsa.X86_64.Crt.sLink) hl (by decide)]
  exact h.link

end VG.Proof.Ffdh.X86_64.ParameterCandidate
