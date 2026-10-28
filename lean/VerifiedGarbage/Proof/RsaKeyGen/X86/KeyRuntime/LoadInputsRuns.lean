module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArgContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEnvironment
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ClearInputs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.LoadPrime
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.LoadExponent
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ContextArgument
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyScratchFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLoadFrames
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.Framework.Offset

/-! # The inputs load from any state that can read them: the read-only view of the arithmetic -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa kEv)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (Environment)
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context)

/-- `loadInputs` runs from a state that reads the primes and the exponent, wherever it may write. -/
theorem loadInputs_runs {E : Environment} {p : BitVec 32} {s : State} (valid : E.Valid)
    (H : Ws s E.base E.size E.n 32) (C : Context E.base E.size p E.argument s)
    (primes : ∀ i, i = 2 ∨ i = 3 → InRegions (s.rd ++ s.wr) (E.outputRegion i).base (E.outputRegion i).len)
    (exponent : InRegions (s.rd ++ s.wr) E.exponentRegion.base E.exponentRegion.len) :
    WP isa loadInputs s fun _ => True := by
  have widths := valid.widths
  have small : E.k ≤ E.n := by omega
  have head := H.hdr_le
  unfold loadInputs VG.Impl.Rsa.X86.Keys.seqs
  refine WP.seq (WP.mono (clearInputs_ok H) fun u ⟨Hu, Ou, _, _, Ku⟩ => ?_)
  have Fu : Frame [E.workspaceRegion] s.mem u.mem :=
    VG.Proof.RsaKeyGen.X86.Key.outs_scratch_frame (by have := H.old.workspace.nowrap; omega) Ou
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact H.old.fits)
  have Cu := C.keep Ku Fu
  have prime {a : State} (Ha : Ws a E.base E.size E.n 32) (Ca : Context E.base E.size p E.argument a)
      (ra : a.rd ++ a.wr = s.rd ++ s.wr) {i out : Nat} (index : i = 2 ∨ i = 3) (ho : out < 32)
      (persistent : 15 ≤ out) :
      WP isa (loadPrime (2 * i) out) a fun t => Ws t E.base E.size E.n 32 ∧
        Frame [E.workspaceRegion] a.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] a t := by
    have hi : i < 7 := by omega
    have len : E.outputLength i = 4 * E.k := by
      unfold Environment.outputLength
      split <;> omega
    have A : VG.Proof.Bignum.X86.CallArgument a E.base E.size (2 * i + 4) (E.out i) := by
      have H := context_argument Ca (i := 2 * i) (by omega)
      rcases index with rfl | rfl <;> exact H
    have readable : InRegions (a.rd ++ a.wr) ((E.out i).setWidth 64) (4 * E.k) := by
      rw [ra]
      have R := primes i index
      change InRegions _ ((E.out i).setWidth 64) (E.outputLength i) at R
      rwa [len] at R
    refine WP.mono (loadPrime_ok Ha widths.2.2.1 widths.2.2.2.1 ho persistent A
      (by rw [← len]; exact valid.outFit i hi) readable
      (by simpa only [Environment.outputRegion, Environment.workspaceRegion, len] using valid.outputScratch i hi))
      fun t ⟨ht, O, _, _, K⟩ => ?_
    exact ⟨ht, VG.Proof.RsaKeyGen.X86.Key.stage_scratch_frame Ha.old
      (by simp only [List.mem_singleton]; rintro j rfl; exact ho)
      (VG.Proof.RsaKeyGen.X86.Key.loadPrime_stage_frame small O), K⟩
  have ru : u.rd ++ u.wr = s.rd ++ s.wr := by rw [Ku.2.1, Ku.2.2]
  refine WP.seq (WP.mono (prime Hu Cu ru (i := 2) (out := aPa) (Or.inl rfl) (by decide) (by decide))
    fun v ⟨Hv, Fv, Kv⟩ => ?_)
  have rv : v.rd ++ v.wr = s.rd ++ s.wr := by rw [Kv.2.1, Kv.2.2, ru]
  have Cv := Cu.keep Kv Fv
  refine WP.seq (WP.mono (prime Hv Cv rv (i := 3) (out := aQa) (Or.inr rfl) (by decide) (by decide))
    fun w ⟨Hw, Fw, Kw⟩ => ?_)
  have rw' : w.rd ++ w.wr = s.rd ++ s.wr := by rw [Kw.2.1, Kw.2.2, rv]
  have Cw := Cv.keep Kw Fw
  refine WP.mono (loadExponent_ok Hw valid.exponentLength.1 valid.exponentLength.2
    (context_argument Cw (i := 14) (by decide)) (context_argument Cw (i := 15) (by decide)) valid.exponentFit
    (by rw [rw']; exact exponent)
    (valid.exponentScratch.sub_right (Offset.sub_base _ (by unfold kEv VG.Impl.Rsa.X86.Keys.hdr at *; omega))))
    fun _ _ => trivial

end VG.Proof.RsaKeyGen.X86.KeyRuntime
