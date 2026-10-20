module
public meta import VerifiedGarbage.Impl.Dsa.X86.Generation.BufferArgs
public meta import VerifiedGarbage.Impl.Dsa.Generation.Layout
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchQBuildCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchPrimeCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchSlots
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
public import VerifiedGarbage.Impl.Dsa.X86.Generation.ParameterSearch
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchQBuild

/-! # Hash and primality-test a subgroup candidate using only public seed and tape data -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

def QBuiltAt (P : SearchContextPlan) (T : GenerationTape P.geometry) (used : Nat) (s : State) : Prop :=
  SeedCandidateAt P T used s ∧ Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off P.geometry.base q) P.geometry.qLen) =
    Spec.Dsa.qCandidate (8 * P.geometry.qLen) T.bytes

theorem qPhasePointer_ct (P : SearchContextPlan) (T : GenerationTape P.geometry) (used : Nat) :
    RelCT isa (Two fun (_ : Unit) => QBuiltAt P T used) (.block (candidatePointer q))
      (Two fun (_ : Unit) => SearchPrimeAt P P.geometry.qLen (Spec.Dsa.qCandidate (8 * P.geometry.qLen) T.bytes) used q) := by
  refine two_piece [.esp] ?_ (by taint_decide) ?_
  · rintro _ s t ⟨⟨Ws, Rs, _, _, _⟩, _⟩ ⟨⟨Wt, Rt, _, _, _⟩, _⟩ r hr
    obtain rfl := List.mem_singleton.mp hr
    exact BitVec.eq_of_toNat_eq (Rs.arena.frame.esp_toNat.trans Rt.arena.frame.esp_toNat.symm)
  · rintro _ s ⟨⟨W, R, _, _, cursor⟩, value⟩
    refine WP.mono (searchCandidatePointer_ok R q) fun t ⟨Rt, O, _⟩ => ?_
    refine ⟨_, Rt, rfl, cursor, ?_⟩
    have qw := P.geometry.qWidth
    have room : q + P.geometry.qLen ≤ usedBytes P.geometry.pLen := by unfold q usedBytes domainCheck; omega
    rw [drawFrame_bytes O (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact (P.geometry.frame_part room).symm)
      (by omega), value]

theorem qPhase_ct {H : Hash} (K : HashOK H) (P : SearchContextPlan) (T : GenerationTape P.geometry)
    (used : Nat) (len : T.bytes.length = P.geometry.qLen) (bound : used ≤ P.witnesses.bytes.length)
    (digest : H.D = P.geometry.qLen) (final : H.F = P.geometry.qLen)
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * P.geometry.qLen) bs)
    (hashSize : ∀ bs, (Spec.Dsa.seedHash (8 * P.geometry.qLen) bs).length = P.geometry.qLen) :
    RelCT isa (Two fun (_ : Unit) => SeedCandidateAt P T used) (qPhase H P.geometry.qLen) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun (_ : Unit) => QBuiltAt P T used)
    (searchQBuild_ct K P T used len final) ?_) (RelCT.seq (qPhasePointer_ct P T used) ?_)
  · rintro _ s ⟨W, R, seed, source, cursor⟩
    refine WP.mono (searchQBuild_ok K R seed len source digest final hash hashSize)
      fun t ⟨Rt, seedT, value, _, _⟩ => ?_
    exact ⟨⟨W, Rt, seedT, source, cursor⟩, value⟩
  · have qw := P.geometry.qWidth
    have words : P.geometry.qLen % 4 = 0 := by rcases qw with h | h <;> rw [h] <;> decide
    have bits := VG.Proof.Dsa.Generation.qCandidate_bitLength (by omega : 2 ≤ 8 * P.geometry.qLen) T.bytes
    have shape := VG.Proof.Dsa.Generation.qCandidate_shape (by omega : 2 ≤ 8 * P.geometry.qLen) T.bytes
    exact searchPrime_ct P P.geometry.qLen _ used q (by omega) (by omega) words bits shape.1
      (by unfold q usedBytes domainCheck; omega) (by unfold q arithmetic; omega) bound
end VG.Proof.Dsa.X86.Generation
