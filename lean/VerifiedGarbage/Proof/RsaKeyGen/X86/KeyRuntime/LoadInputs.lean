module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArgContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ClearInputs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.LoadPrime
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.LoadExponent
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ContextArgument
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLoadFrames
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyScratchFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.Framework.Offset

/-! # The inputs at the run-time width establish the shared arithmetic's inputs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aOne aE kEv)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (Environment Input)

structure Loaded (E : Environment) (m : Mem) (s : State) : Prop where
  input : Input E s
  pValue : num s.mem E.base E.n aPa = Spec.Rsa.os2ip
    (Spec.Rsa.bytesAt m (E.outputRegion 2).base (E.outputRegion 2).len)
  qValue : num s.mem E.base E.n aQa = Spec.Rsa.os2ip
    (Spec.Rsa.bytesAt m (E.outputRegion 3).base (E.outputRegion 3).len)
  eValue : val32 s.mem E.base kEv 2 = Spec.Rsa.os2ip
    (Spec.Rsa.bytesAt m E.exponentRegion.base E.exponentRegion.len)
  pBound : num s.mem E.base E.n aPa < 2 ^ (32 * E.k)
  qBound : num s.mem E.base E.n aQa < 2 ^ (32 * E.k)
  one : num s.mem E.base E.n aOne = 1
  zero : num s.mem E.base E.n aZero = 0
  loaded : num s.mem E.base E.n aE = val32 s.mem E.base kEv 2

theorem loadInputs_ok {E : Environment} {p : BitVec 32} {s : State} (h : Input E s)
    (H : Ws s E.base E.size E.n 32) (C : VG.Proof.RsaKeyGen.X86.KeyArgs.Context E.base E.size p E.argument s) :
    WP isa loadInputs s fun t => Loaded E s.mem t ∧ Ws t E.base E.size E.n 32 ∧
      Frame [E.workspaceRegion] s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have widths := h.valid.widths
  have small : E.k ≤ E.n := by omega
  have head := h.ws.hdr_le
  unfold loadInputs VG.Impl.Rsa.X86.Keys.seqs
  -- The arrays cleared, and one.
  refine WP.seq (WP.mono (clearInputs_ok H) fun u ⟨Hu, Ou, one, zero, Ku⟩ => ?_)
  have hu : Input E u := h.afterOuts Hu.old Ku (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact (by decide : 72 ≤ hdr)) Ou
  have Fu : Frame [E.workspaceRegion] s.mem u.mem :=
    VG.Proof.RsaKeyGen.X86.Key.outs_scratch_frame (by have := h.ws.workspace.nowrap; omega) Ou
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact h.ws.fits)
  have Cu := C.keep Ku Fu
  -- A prime at argument `2 i`.
  have prime {a : State} (ha : Input E a) (Ha : Ws a E.base E.size E.n 32)
      (Ca : VG.Proof.RsaKeyGen.X86.KeyArgs.Context E.base E.size p E.argument a) {i out : Nat}
      (index : i = 2 ∨ i = 3) (ho : out < 32) (persistent : 15 ≤ out) :
      WP isa (loadPrime (2 * i) out) a fun t =>
        Input E t ∧ Ws t E.base E.size E.n 32 ∧ Frame [E.workspaceRegion] a.mem t.mem ∧
        num t.mem E.base E.n out = Spec.Rsa.os2ip
          (Spec.Rsa.bytesAt a.mem (E.outputRegion i).base (E.outputRegion i).len) ∧
        num t.mem E.base E.n out < 2 ^ (32 * E.k) ∧
        (∀ j, 1 ≤ j → j < 32 → j ≠ out → num t.mem E.base E.n j = num a.mem E.base E.n j) ∧
        Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] a t := by
    have hi : i < 7 := by omega
    have len : E.outputLength i = 4 * E.k := by
      unfold Environment.outputLength
      split <;> omega
    have A : VG.Proof.Bignum.X86.CallArgument a E.base E.size (2 * i + 4) (E.out i) := by
      have H := context_argument Ca (i := 2 * i) (by omega)
      rcases index with rfl | rfl <;> exact H
    have readable : InRegions (a.rd ++ a.wr) ((E.out i).setWidth 64) (4 * E.k) := by
      obtain ⟨r, hr, contains⟩ := ha.outWrite i hi
      refine ⟨r, List.mem_append_right _ hr, ?_⟩
      change r.Contains ((E.out i).setWidth 64) (E.outputLength i) at contains
      rwa [len] at contains
    refine WP.mono (loadPrime_ok Ha widths.2.2.1 widths.2.2.2.1 ho persistent A
      (by rw [← len]; exact ha.valid.outFit i hi) readable
      (by simpa only [Environment.outputRegion, Environment.workspaceRegion, len] using ha.valid.outputScratch i hi))
      fun t ⟨ht, O, value, bound, K⟩ => ?_
    have frame := VG.Proof.RsaKeyGen.X86.Key.loadPrime_stage_frame small O
    refine ⟨ha.afterStage ht.old K frame, ht, VG.Proof.RsaKeyGen.X86.Key.stage_scratch_frame ha.ws
      (by simp only [List.mem_singleton]; rintro j rfl; exact ho) frame, ?_, bound, ?_, K⟩
    · simpa only [Environment.outputRegion, len] using value
    · intro j positive hj different
      exact VG.Proof.RsaKeyGen.X86.Key.loadPrime_preserves_num small positive different (ha.ws.fit64 hj) O
  refine WP.seq (WP.mono (prime hu Hu Cu (i := 2) (out := aPa) (Or.inl rfl) (by decide) (by decide))
    fun v ⟨hv, Hv, Fv, pValue, pBound, pv, Kv⟩ => ?_)
  rw [h.output_preserved (by decide : 2 < 7) Fu] at pValue
  have oneV : num v.mem E.base E.n aOne = 1 := (pv _ (by decide) (by decide) (by decide)).trans one
  have zeroV : num v.mem E.base E.n aZero = 0 :=
    (pv _ (by decide) (by decide) (by decide)).trans (zero _ (by decide) (by decide))
  have Fsv := Fu.trans Fv
  have Cv := Cu.keep Kv Fv
  refine WP.seq (WP.mono (prime hv Hv Cv (i := 3) (out := aQa) (Or.inr rfl) (by decide) (by decide))
    fun w ⟨hw, Hw, Fw, qValue, qBound, qw, Kw⟩ => ?_)
  rw [h.output_preserved (by decide : 3 < 7) Fsv] at qValue
  have pValueW := (qw aPa (by decide) (by decide) (by decide)).trans pValue
  have pBoundW : num w.mem E.base E.n aPa < 2 ^ (32 * E.k) := by
    rw [qw aPa (by decide) (by decide) (by decide)]
    exact pBound
  have oneW := (qw aOne (by decide) (by decide) (by decide)).trans oneV
  have zeroW := (qw aZero (by decide) (by decide) (by decide)).trans zeroV
  have Fsw := Fsv.trans Fw
  have Cw := Cv.keep Kw Fw
  -- The exponent.
  refine WP.mono (loadExponent_ok Hw h.valid.exponentLength.1 h.valid.exponentLength.2
    (context_argument Cw (i := 14) (by decide)) (context_argument Cw (i := 15) (by decide)) hw.valid.exponentFit
    hw.exponentRead (hw.valid.exponentScratch.sub_right (Offset.sub_base _ (by unfold kEv hdr at *; omega))))
    fun x ⟨Hx, O, eValue, loaded, Kx⟩ => ?_
  have hx : Input E x := hw.afterExponent Hx.old Kx O
  have Fx := VG.Proof.RsaKeyGen.X86.Key.loadExponent_scratch_frame hw.ws O
  have ex (j : Nat) (hj : j < 32) (different : j ≠ aE) : num x.mem E.base E.n j = num w.mem E.base E.n j :=
    VG.Proof.RsaKeyGen.X86.Key.loadExponent_preserves_num different (hw.ws.fit64 hj) O
  change val32 x.mem E.base kEv 2 = Spec.Rsa.os2ip
    (Spec.Rsa.bytesAt w.mem E.exponentRegion.base E.exponentRegion.len) at eValue
  rw [h.exponent_preserved Fsw] at eValue
  have pValueX := (ex aPa (by decide) (by decide)).trans pValueW
  have qValueX := (ex aQa (by decide) (by decide)).trans qValue
  have pBoundX : num x.mem E.base E.n aPa < 2 ^ (32 * E.k) := by
    rw [ex aPa (by decide) (by decide)]
    exact pBoundW
  have qBoundX : num x.mem E.base E.n aQa < 2 ^ (32 * E.k) := by
    rw [ex aQa (by decide) (by decide)]
    exact qBound
  have oneX := (ex aOne (by decide) (by decide)).trans oneW
  have zeroX := (ex aZero (by decide) (by decide)).trans zeroW
  exact ⟨⟨hx, pValueX, qValueX, eValue, pBoundX, qBoundX, oneX, zeroX, loaded⟩, Hx, Fsw.trans Fx,
    (Ku.mono (by decide)).trans (Kv.trans (Kw.trans (Kx.mono (by decide))))⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
