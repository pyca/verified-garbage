module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Start
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CandidateTest
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.Contract

import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Basic.IsEmpty.Defs
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
/-! # FFDH parameter generation on x86-64: the complete callable body -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/ParameterCandidate/ResultBridge.lean`, which only this module imported.
section

/-! # FFDH parameter generation on x86-64: relate the native policy to the specification -/

section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum
open VG.Proof.Ffdh.ParameterCandidate

theorem CandidateBase.candidate_result {p : CandidateP} {s : State} (h : CandidateBase p s)
    (havail : p.k ≤ p.rand.length) :
    Spec.Ffdh.parameterCandidate p.bits p.gen p.rand =
      (candidateTail p (p.rand.drop p.k)).map (fun x => (if x.1 then some p.P else none, x.2)) := by
  rw [← checkedCandidate_eq]
  unfold checkedCandidate
  rw [← h.len, draw_of_le havail]
  simp only [bind, Option.bind_some]
  change (do
    if !(Spec.Ffdh.generationShape p.bits p.gen p.P && Spec.Ffdh.primeShape p.P && Spec.Ffdh.primeShape p.Q) then
      return (none, p.rand.drop p.k)
    let (pass, rest) ← checkWitnesses p.Q (Spec.Ffdh.primeChecks (Spec.RsaKeyGen.bitLength p.Q)) (p.rand.drop p.k)
    if !pass then return (none, rest)
    let (pass, rest) ← checkWitnesses p.P (Spec.Ffdh.primeChecks (Spec.RsaKeyGen.bitLength p.P)) rest
    return (if pass then some p.P else none, rest)) = _
  have hpodd : p.P % 2 = 1 :=
    (candidate_shape (bits := p.bits) (by omega_using [h.bits1]) _).1
  have hpbits : Spec.RsaKeyGen.bitLength p.P = p.phaseBits false := (h.phase_bitLength false hpodd).1
  by_cases hgp : (Spec.Ffdh.generationShape p.bits p.gen p.P && Spec.Ffdh.primeShape p.P) = true
  · by_cases hq : Spec.Ffdh.primeShape p.Q = true
    · have hqodd : p.Q % 2 = 1 := by
        have hh := hq
        unfold Spec.Ffdh.primeShape at hh
        exact beq_iff_eq.mp ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hh).1).2
      have hqbits : Spec.RsaKeyGen.bitLength p.Q = p.phaseBits true := (h.phase_bitLength true hqodd).1
      simp only [hgp, hq, Bool.and_self, Bool.not_true, Bool.false_eq_true, ite_false,
        candidateTail, ite_true, qPolicy, hqbits, hpbits]
      cases he : checkWitnesses p.Q (Spec.Ffdh.primeChecks (p.phaseBits true)) (p.rand.drop p.k) with
      | none => rfl
      | some ar =>
        obtain ⟨pass, rest⟩ := ar
        cases pass
        · rfl
        · simp only [bind, Option.bind_some, Bool.not_true, Bool.false_eq_true, ite_false]
          cases checkWitnesses p.P (Spec.Ffdh.primeChecks (p.phaseBits false)) rest with
          | none => rfl
          | some ar => obtain ⟨pass, rest'⟩ := ar; cases pass <;> rfl
    · have hqf : Spec.Ffdh.primeShape p.Q = false := Bool.eq_false_iff.mpr hq
      simp [candidateTail, qPolicy, hgp, hqf]
  · have hgpf : (Spec.Ffdh.generationShape p.bits p.gen p.P && Spec.Ffdh.primeShape p.P) = false :=
      Bool.eq_false_iff.mpr hgp
    simp [candidateTail, hgpf]

end VG.Proof.Ffdh.X86_64.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/ParameterCandidate/NativeResult.lean`, which only this module imported.
section

/-! # FFDH parameter generation on x86-64: the public status and consumed prefix -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.Proof.Bignum VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Ffdh.ParameterCandidate

def NativeResult (p : CandidateP) (used : Nat) (m : Mem) : Prop :=
  let r := Spec.Ffdh.parameterCandidate p.bits p.gen p.rand
  word m p.B (8 * oStatus) = BitVec.ofNat 64 (Proof.Ffdh.candidateStatus r) ∧
    (match r with | none => True | some (_, rest) => rest = p.rand.drop used) ∧
    (∀ n rest, r = some (some n, rest) → n = p.P)

theorem CandidateBase.nativeResult {p : CandidateP} {s : VG.X86_64.State} {n : Nat} {m : Mem}
    (h : CandidateBase p s) (havail : p.k ≤ p.rand.length)
    (hr : TapeOutcome p p.k n (candidateTail p (p.rand.drop p.k)) m) :
    NativeResult p (p.k + n) m := by
  unfold NativeResult
  rw [h.candidate_result havail]
  cases he : candidateTail p (p.rand.drop p.k) with
  | none => simpa [he, TapeOutcome, Proof.Ffdh.candidateStatus] using hr
  | some ar =>
    obtain ⟨pass, rest⟩ := ar
    cases pass
    · simp only [he, TapeOutcome] at hr
      simp [Proof.Ffdh.candidateStatus, hr]
    · simp only [he, TapeOutcome] at hr
      simp [Proof.Ffdh.candidateStatus, hr]

theorem CandidateBase.short_result {p : CandidateP} {s : VG.X86_64.State}
    (h : CandidateBase p s) (hshort : p.rand.length < p.k) :
    Spec.Ffdh.parameterCandidate p.bits p.gen p.rand = none := by
  rw [← checkedCandidate_eq]
  unfold checkedCandidate
  rw [← h.len, draw_of_short hshort]
  rfl

end VG.Proof.Ffdh.X86_64.ParameterCandidate
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64

def BodyPost (s t : State) : Prop :=
  let p := candidateOfState s
  ∃ used, CandidateTape p used t ∧ t.gpr .rdi = p.B ∧ NativeResult p used t.mem ∧
    (word t.mem p.B (8 * oStatus) = 1 → Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem p.op p.k) = p.P) ∧
    (∀ i < 6, word t.mem p.B (8 * i) = s.gpr (saved.getD i .rax)) ∧ Keep (.rdi :: mmRegs) s t

theorem body_ok (M : Mont) (R : R2Impl M) (K : Kernel) {s : State} (c : PcCtx s) :
    WP isa (body M.mm R.code K.run) s (BodyPost s) := by
  let p := candidateOfState s
  change WP isa (body M.mm R.code K.run) s (fun t => ∃ used,
    CandidateTape p used t ∧ t.gpr .rdi = p.B ∧ NativeResult p used t.mem ∧
      (word t.mem p.B (8 * oStatus) = 1 → Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem p.op p.k) = p.P) ∧
      (∀ i < 6, word t.mem p.B (8 * i) = s.gpr (saved.getD i .rax)) ∧ Keep (.rdi :: mmRegs) s t)
  unfold body
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (candidateEntry_base c) fun u ⟨hu, hdu, hstatus, _, hsaved, ku⟩ => ?_
  change CandidateTape p 0 u at hu
  change u.gpr .rdi = p.B at hdu
  change word u.mem p.B (8 * oStatus) = 0 at hstatus
  have hlen := hu.base.hdr (oLen, BitVec.ofNat 64 p.k) (by simp [CandidateP.headers])
  have hleft : word u.mem p.B (8 * oRandLeft) = BitVec.ofNat 64 p.rand.length := by simpa using hu.left
  have hrd : ∀ j < 32, InRegions (u.rd ++ u.wr) (off p.B (8 * j)) 8 :=
    fun j hj => hu.base.scr.ld (by omega_using [hj, hu.base.header_room])
  refine WP.mono (WP.keep [.rax] (Q := fun v => v.cf = some (decide (p.rand.length < p.k)) ∧ v.mem = u.mem)
    (by
      xrun [State.ea, hdr, hdrOff, hdu, hleft, hlen, hrd oRandLeft (by decide), hrd oLen (by decide)]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu.base.randLen,
        Nat.mod_eq_of_lt (show p.k < 2 ^ 64 by omega_using [hu.base.widths.2])]) rfl)
    fun v ⟨⟨hcf, hm⟩, kv⟩ => ?_
  obtain ⟨hv, _, _⟩ := hu.same_mem hm kv (by decide)
  have hdv : v.gpr .rdi = p.B := (kv.gpr (by decide)).trans hdu
  have hsavedv : ∀ i < 6, word v.mem p.B (8 * i) = s.gpr (saved.getD i .rax) := by
    intro i hi; rw [hm]; exact hsaved i hi
  have kk : Keep (.rdi :: mmRegs) s v := (ku.trans kv).mono (by decide)
  refine WP.ite (decide (p.rand.length < p.k)) (by simp [eval, hcf]) ?_ ?_
  · intro hshort
    have hr := hv.base.short_result (of_decide_eq_true hshort)
    have hstat : word v.mem p.B (8 * oStatus) = 0 := by rw [hm]; exact hstatus
    refine WP.block_nil ⟨0, hv, hdv, ?_, ?_, hsavedv, kk⟩
    · simp [NativeResult, hr, Proof.Ffdh.candidateStatus, hstat]
    · intro he; rw [hstat] at he; contradiction
  · intro havail
    refine WP.mono (testCandidate_ok M R K hv hdv (by omega_using [of_decide_eq_false havail]))
      fun t ⟨n, _, ht, hdt, hresult, hout, hs, _, kt⟩ => ?_
    exact ⟨p.k + n, ht, hdt, hv.base.nativeResult (by omega_using [of_decide_eq_false havail]) hresult,
      hout, fun i hi => (hs i (by omega)).trans (hsavedv i hi), (kk.trans kt).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
