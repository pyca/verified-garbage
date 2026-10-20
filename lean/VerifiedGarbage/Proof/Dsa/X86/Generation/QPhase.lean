module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.ParameterSearch
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SeedPlan
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeRunSpec
import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidatePreserve
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchPrime
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchQBuild
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchSlots
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchWrites

/-! # Hash and test one seed's subgroup candidate with exact witness consumption -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

theorem qPhase_ok {H : Hash} (K : HashOK H) {P : SearchContextPlan} {T : GenerationTape P.geometry}
    {W : Nat → BitVec 32} {s : State} {used : Nat} (R : SearchContext P W s) (seed : TapeMemory T s)
    (len : T.bytes.length = P.geometry.qLen) (source : W 1 = T.pointer)
    (cursor : W 16 = BitVec.ofNat 32 used) (usedBound : used ≤ P.witnesses.bytes.length)
    (digest : H.D = P.geometry.qLen) (final : H.F = P.geometry.qLen)
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * P.geometry.qLen) bs)
    (hashSize : ∀ bs, (Spec.Dsa.seedHash (8 * P.geometry.qLen) bs).length = P.geometry.qLen) :
    WP isa (qPhase H P.geometry.qLen) s fun t => ∃ W', ∃ result : PrimeStepResult,
      PSearchMemory (seedPlan P T len (W 10)) W' t ∧ W' 16 = BitVec.ofNat 32 result.used ∧ W' 19 = BitVec.ofNat 32 result.status ∧
      used ≤ result.used ∧ result.used ≤ P.witnesses.bytes.length ∧
      (result.status = 0 ∨ result.status = 1 ∨ result.status = 3) ∧
      primeRunResult P.witnesses.bytes result = Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * P.geometry.qLen) T.bytes)
        (P.witnesses.bytes.drop used) ∧
      Frame (parameterWrites P.geometry) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t := by
  have qw := P.geometry.qWidth
  have qr : q + P.geometry.qLen ≤ usedBytes P.geometry.pLen := by unfold q usedBytes domainCheck; omega
  have lo : 4 ≤ P.geometry.qLen := by omega
  have hi : P.geometry.qLen ≤ 384 := by omega
  have words : P.geometry.qLen % 4 = 0 := by rcases qw with h | h <;> rw [h] <;> decide
  have bits := VG.Proof.Dsa.Generation.qCandidate_bitLength (by omega : 2 ≤ 8 * P.geometry.qLen) T.bytes
  have shape := VG.Proof.Dsa.Generation.qCandidate_shape (by omega : 2 ≤ 8 * P.geometry.qLen) T.bytes
  let C := P.geometry.prime P.witnesses P.geometry.qLen (Spec.Dsa.qCandidate (8 * P.geometry.qLen) T.bytes) lo hi words bits shape.1
  have large : 3 < Spec.Dsa.qCandidate (8 * P.geometry.qLen) T.bytes := by
    have power := Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 2 ≤ 8 * P.geometry.qLen - 1)
    have four : (2 : Nat) ^ 2 = 4 := by decide
    rw [four] at power
    omega
  unfold qPhase
  refine WP.seq (WP.mono (searchQBuild_ok K R seed len source digest final hash hashSize)
    fun a ⟨Ra, seeda, qa, Oa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (searchCandidatePointer_ok Ra q) fun b ⟨Rb, Ob, Kb⟩ => ?_)
  have Fb : Frame (parameterWrites P.geometry) a.mem b.mem := Ob.mono (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr; simp [parameterWrites])
  have seedb := seeda.keep Fb T.parameterApart Kb
  have qb : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt b.mem (off P.geometry.base q) P.geometry.qLen) =
      Spec.Dsa.qCandidate (8 * P.geometry.qLen) T.bytes := by
    rw [drawFrame_bytes Ob (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact (P.geometry.frame_part qr).symm) (by omega), qa]
  refine WP.mono (searchPrime_ok Rb rfl lo hi words bits shape.1 qr (by unfold q arithmetic; omega) qb
    (show frameUpdate W 22 _ 16 = BitVec.ofNat 32 used from cursor) usedBound)
    fun t ⟨Rt, _, Ot, Kt⟩ => ?_
  have Ft := Ot.sub (checkPrime_parameterWrites _ _ _ _ _ _ _ _ _)
  have Ftest := Ot.sub (candidateTest_prime _ _ _ _ _ _ _ _ _)
  have qt : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem (off P.geometry.base q) P.geometry.qLen) =
      Spec.Dsa.qCandidate (8 * P.geometry.qLen) T.bytes := by
    rw [drawFrame_bytes Ftest (candidateTest_bufferApart _ qr (by unfold q witness; omega)) (by omega), qb]
  have bounds := primeDecision_bounds (G := C) (mem := b.mem) usedBound
  have spec := primeDecision_spec (G := C) b.mem used large shape.1
  rw [show Spec.Rsa.bytesAt b.mem (C.tape.setWidth 64) C.tapeLen = P.witnesses.bytes from Rb.witnesses.value] at spec
  exact ⟨_, primeDecision C b.mem used, ⟨Rt, seedb.keep Ft T.parameterApart Kt, source, qt, rfl⟩,
    rfl, rfl, bounds.1, bounds.2.1, bounds.2.2, spec, (Oa.trans Fb).trans Ft,
    Ka.trans ((Kb.mono (by decide)).trans Kt)⟩
end VG.Proof.Dsa.X86.Generation
