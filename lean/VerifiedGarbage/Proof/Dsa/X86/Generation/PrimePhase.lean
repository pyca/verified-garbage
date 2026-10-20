module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorPhase
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PAttempt
import VerifiedGarbage.Proof.Dsa.X86.Generation.NativePSearch
import VerifiedGarbage.Proof.Dsa.X86.Generation.OnSuccess
import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchStable

/-! # Compose p search and generator validation into the exact remainder of one seed attempt -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

def PSearchPlan.result (P : PSearchPlan) (used : Nat) :=
  VG.Proof.Dsa.Generation.primeResult (8 * P.context.geometry.pLen) (8 * P.context.geometry.qLen)
    P.qvalue P.seed.bytes P.hs (P.context.witnesses.bytes.drop used)

theorem primePhase_ok {H : Hash} (K : HashOK H) (F : KeyRandom.CheckCall.CheckFn) {P : PSearchPlan}
    {W : Nat → BitVec 32} {used : Nat} {s : State} (R : PSearchMemory P W s)
    (cursor : W 16 = BitVec.ofNat 32 used) (bound : used ≤ P.context.witnesses.bytes.length)
    (digest : H.D = P.context.geometry.qLen) (final : H.F = P.context.geometry.qLen)
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * P.seed.bytes.length) bs)
    (hashSize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * P.seed.bytes.length) bs).length = 8 * P.seed.bytes.length) :
    WP isa (.seq (nativePSearch H P.context.geometry.pLen P.context.geometry.qLen)
      (onSuccess (.seq (nativeGenerator P.context.geometry.pLen)
        (onSuccess (finishDomain F.name F.code P.context.geometry.pLen P.context.geometry.qLen))))) s
      (PhaseResult P.context P.seedUsed (P.result used) s) := by
  have start : P.remaining 0 used = Spec.Dsa.primeFromSeed (8 * P.context.geometry.pLen) (8 * P.context.geometry.qLen)
      P.qvalue P.seed.bytes (P.context.witnesses.bytes.drop used) := VG.Proof.Dsa.Generation.primeSearch_start _ _ _ _ _
  refine WP.seq (WP.mono (nativePSearch_ok K R cursor bound digest final hash hashSize)
    fun b ⟨Wb, nextUsed, Rb, cursorB, boundB, outcome, Ob, rd, wr⟩ => ?_)
  rcases outcome with ⟨status, answer⟩ | ⟨status, answer⟩ | ⟨value, status, answer, accepted⟩
  · have expected : P.result used = none := by
      unfold PSearchPlan.result VG.Proof.Dsa.Generation.primeResult
      rw [← start, answer]
    have done : PhaseResult P.context P.seedUsed (P.result used) s b :=
      ⟨Wb, nextUsed, Rb.context, Rb.seedUsed, cursorB, boundB, .inl ⟨status, expected⟩, Ob, rd, wr⟩
    exact onSuccess_ok Rb.context.arena.frame Rb.context.representation
      (by intro t _ _ yes; rw [status] at yes; contradiction)
      (fun t mem K _ => phaseResult_stable _ _ _ _ done mem (K.mono (by decide)))
  · have expected : P.result used = some (none, P.context.witnesses.bytes.drop nextUsed) := by
      unfold PSearchPlan.result VG.Proof.Dsa.Generation.primeResult
      rw [← start, answer]
    have done : PhaseResult P.context P.seedUsed (P.result used) s b :=
      ⟨Wb, nextUsed, Rb.context, Rb.seedUsed, cursorB, boundB, .inr (.inl ⟨status, expected⟩), Ob, rd, wr⟩
    exact onSuccess_ok Rb.context.arena.frame Rb.context.representation
      (by intro t _ _ yes; rw [status] at yes; contradiction)
      (fun t mem K _ => phaseResult_stable _ _ _ _ done mem (K.mono (by decide)))
  · have expected : P.result used = VG.Proof.Dsa.Generation.generatorResult value P.qvalue P.hs
        (P.context.witnesses.bytes.drop nextUsed) := by
      unfold PSearchPlan.result VG.Proof.Dsa.Generation.primeResult
      rw [← start, answer]
    refine onSuccess_ok Rb.context.arena.frame Rb.context.representation (fun t mem K _ => ?_)
      (by intro t _ _ no; exact False.elim (no status))
    have same : Outside (off P.context.geometry.base VG.Impl.Dsa.Generation.Layout.control) 0 12 b.mem t.mem := by
      rw [mem]; exact Outside.refl _ _ _ _
    have Rt := Rb.control same (K.mono (by decide))
    have At := accepted.control same (K.mono (by decide))
    have next := generatorPhase_ok F Rt At cursorB boundB
    rw [← expected] at next
    exact WP.mono next fun u done => done.prepend (by rw [mem]; exact Ob) (K.2.1.trans rd) (K.2.2.trans wr)
end VG.Proof.Dsa.X86.Generation
