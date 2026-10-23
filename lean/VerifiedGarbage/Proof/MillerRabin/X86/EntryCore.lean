module

public import VerifiedGarbage.Proof.MillerRabin.X86.EntryStage
import VerifiedGarbage.Proof.MillerRabin.X86.ResultMath
public import VerifiedGarbage.Proof.MillerRabin.X86.Baseline
import VerifiedGarbage.Proof.MillerRabin.X86.EntryMarker
import VerifiedGarbage.Proof.MillerRabin.X86.MontInstance
import VerifiedGarbage.Proof.Mont.X86.Sse2.PreparedVerified
import VerifiedGarbage.Proof.Mont.X86.Compact.Arithmetic
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame

/-! # The complete round body satisfies the reviewed mathematical result -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.RsaKeyGen
open VG.Impl.MillerRabin.X86

def Result (s : State) (t : State) : Prop :=
  (∀ b, initialValues s aX = b % initialValues s 0 * 2 ^ (64 * (geometry s).w) % initialValues s 0 →
    (t.gpr .eax).toNat = if Spec.MillerRabin.round (initialValues s 0) b then 1 else 0) ∧
  WorkspaceFrame (geometry s) (roundWrites (geometry s)) (entered s).mem t.mem

theorem Entry.narrowed_body {s : State} (E : Entry s) :
    WP isa (body montName montCode) (narrowed s) fun t =>
      Result s t ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] (narrowed s) t := by
  unfold body
  refine WP.seq (WP.mono E.narrowed_base fun t ⟨S, mem, K⟩ => ?_)
  obtain ⟨minimum, odd, _, Xlt, one, minus, exponent, _⟩ := E.prepared
  change 3 ≤ initialValues s 0 at minimum
  change initialValues s 0 % 2 = 1 at odd
  change initialValues s aX < initialValues s 0 at Xlt
  change initialValues s aOne = 2 ^ (64 * (geometry s).w) % initialValues s 0 at one
  change initialValues s aMinusOne = initialValues s 0 - 2 ^ (64 * (geometry s).w) % initialValues s 0 at minus
  change initialValues s aExponent = mrE (initialValues s 0) at exponent
  have marker := E.marker
  rw [← mem] at marker
  have Olt : initialValues s aOne < initialValues s 0 := by
    rw [one]
    exact Nat.mod_lt _ (by omega)
  refine WP.mono (core_ok VG.Proof.Mont.X86.Sse2.prepared_verified compact_noSp compact_stack E.valid S
    (by change (arg s 1).toNat * 8 = 8 * (arg s 1).toNat; omega) odd Xlt Olt (Nat.mod_lt _ (by decide)) marker.1 marker.2)
    fun u ⟨value, frame, keep⟩ => ?_
  refine ⟨⟨?_, ?_⟩, (K.mono (by decide)).widen keep⟩
  · intro b witness
    have fits : initialValues s 0 < 2 ^ (64 * (geometry s).w) := by
      rw [initialValues, Compact.numAt_val32]
      have := val32_lt s.mem (wsOf s) (Spec.Rsa.Mont.arrAt (geometry s).w 0) (2 * (geometry s).w)
      simpa only [show 32 * (2 * (geometry s).w) = 64 * (geometry s).w by omega] using this
    have final := finishedState_eq odd minimum fits witness one minus exponent
    change u.gpr .eax = BitVec.ofNat 32
      (finishedState (initialValues s) (initialValues s 0) (geometry s).w (2 * (geometry s).w)
        (mrA (initialValues s 0) % 64)).2.toNat at value
    rw [value, final]
    cases Spec.MillerRabin.round (initialValues s 0) b <;> rfl
  · rw [mem] at frame
    exact frame

end VG.Proof.MillerRabin.X86
