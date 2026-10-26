module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseData
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundState
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages
import Mathlib.Data.Nat.GCD.Basic

/-! # FFDH parameter generation on x86-64: instantiate the shared witness policy -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.Ffdh.X86_64

def CandidateBase.witnessParams {p : CandidateP} {s : State} (h : CandidateBase p s)
    (q : Bool) (mi : BitVec 64) (ho : p.phaseValue q % 2 = 1) : WitnessParams where
  O := p.B
  Z := p.Z
  op := p.op
  bits := p.phaseBits q
  w := p.phaseWords q
  N := p.phaseValue q
  mi := mi
  bits1 := by cases q <;> simp only [CandidateP.phaseBits] <;> simp <;> omega_using [h.bits1]
  bits2 := by cases q <;> simp only [CandidateP.phaseBits] <;> simp <;> omega_using [h.bits2]
  width := rfl
  room := (h.phase_room q).2.2
  predBits := (h.phase_bitLength q ho).2
  odd := ho
  n3 := by omega_using [h.phase_large q]

theorem CandidateTape.drawState {p : CandidateP} {used : Nat} {q : Bool} {s : State} {mi : BitVec 64}
    (h : CandidateTape p used s) (hp : PhaseHeader p q s) (ho : p.phaseValue q % 2 = 1)
    (hr : ModulusReady s (off p.B 256) (p.Z - 256) (p.phaseWords q) mi (p.phaseValue q)) :
    DrawState (h.base.witnessParams q mi ho) (off p.rp used) used (p.rand.drop used) s := by
  refine ⟨h.base.scr, hr, hp.link,
    h.base.hdr (oOut, p.op) (by simp [CandidateP.headers]), hp.bits, hp.len,
    h.ptr, ?_, h.usedWord, ?_, source_drop h.base.rand used, ?_, ?_⟩
  · change word s.mem p.B (8 * oRandLeft) = BitVec.ofNat 64 (p.rand.drop used).length
    simpa only [List.length_drop] using h.left
  · simp only [List.length_drop]
    omega_using [h.bound, h.base.randLen]
  · exact ⟨fun i hi => h.base.out.wr i (Nat.lt_of_lt_of_le hi (h.base.phase_load_widths q).2.2),
      fun i hi => h.base.out.sep i (Nat.lt_of_lt_of_le hi (h.base.phase_load_widths q).2.2)⟩
  · intro i hi j hj he
    have hij : i < p.k := Nat.lt_of_lt_of_le hi (h.base.phase_load_widths q).2.2
    change off p.op i = off (off p.rp used) j at he
    rw [off_off] at he
    exact h.base.outRand i hij (used + j) (by rw [List.length_drop] at hj; omega) he

theorem CandidateTape.roundRoom {p : CandidateP} {used : Nat} {q : Bool} {s : State} {mi : BitVec 64}
    (h : CandidateTape p used s) (ho : p.phaseValue q % 2 = 1) :
    RoundRoom (h.base.witnessParams q mi ho) (off p.rp used) (p.rand.drop used) s := by
  refine ⟨by rw [h.base.sp]; exact h.base.stackSize, by rw [h.base.sp]; exact h.base.stackRoot, ?_⟩
  intro i hi
  rw [h.base.sp, off_off]
  exact h.base.stackRand (used + i) (by rw [List.length_drop] at hi; omega)

end VG.Proof.Ffdh.X86_64.ParameterCandidate
