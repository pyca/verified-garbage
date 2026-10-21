module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExport
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInputInitialize
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyImportPrime
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyImportExponent
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDerive
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyScratchFrame

/-! # Complete native import, derivation and masked export at every supported width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def BodyOutcome (E : Environment) (m : Mem) (t : State) : Prop :=
  WrittenCore E.outputs
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m E.exponentRegion.base E.exponentRegion.len))
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (E.outputRegion 2).base (E.outputRegion 2).len))
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (E.outputRegion 3).base (E.outputRegion 3).len)) t

theorem sized_ok {E : Environment} {s : State} (h : Input E s) :
    WP isa (sized E.n) s fun t =>
      Ws t E.base E.size E.n 32 ∧ BodyOutcome E s.mem t ∧
      Frame E.outputs.writes s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have widths := h.valid.widths
  unfold sized seqs
  refine WP.seq (WP.mono h.initialize_ok fun u ⟨hu, Fu, one, zero, Ku⟩ => ?_)
  refine WP.seq (WP.mono (hu.importPrime (out := aPa) (Or.inl rfl) (by decide) (by decide))
    fun v ⟨hv, Fv, pValue, pBound, pv, Kv⟩ => ?_)
  rw [h.output_preserved (by decide : 2 < 7) Fu] at pValue
  have oneV : num v.mem E.base E.n aOne = 1 := (pv _ (by decide) (by decide) (by decide)).trans one
  have zeroV : num v.mem E.base E.n aZero = 0 :=
    (pv _ (by decide) (by decide) (by decide)).trans (zero _ (by decide) (by decide))
  have Fsv := Fu.trans Fv
  refine WP.seq (WP.mono (hv.importPrime (out := aQa) (Or.inr rfl) (by decide) (by decide))
    fun w ⟨hw, Fw, qValue, qBound, qw, Kw⟩ => ?_)
  rw [h.output_preserved (by decide : 3 < 7) Fsv] at qValue
  have pValueW := (qw aPa (by decide) (by decide) (by decide)).trans pValue
  have pBoundW : num w.mem E.base E.n aPa < 2 ^ (32 * E.k) := by
    rw [qw aPa (by decide) (by decide) (by decide)]
    exact pBound
  have oneW := (qw aOne (by decide) (by decide) (by decide)).trans oneV
  have zeroW := (qw aZero (by decide) (by decide) (by decide)).trans zeroV
  have Fsw := Fsv.trans Fw
  refine WP.seq (WP.mono hw.importExponent fun x ⟨hx, Fx, eValue, loaded, ex, Kx⟩ => ?_)
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
  have Fsx := Fsw.trans Fx
  refine WP.seq (WP.mono (deriveLoaded_ok hx.ws widths.2.2.1 widths.2.2.2.1 widths.2.2.2.2.1
    widths.1 widths.2.1 pBoundX qBoundX zeroX oneX loaded)
    fun y ⟨hy, Oy, result, Ky⟩ => ?_)
  rw [eValue, pValueX, qValueX] at result
  have hyInput := hx.afterStage hy Ky Oy
  have Fy := stage_scratch_frame hx.ws (by simp [deriveArrays, prepareArrays, keyPartArrays]; decide) Oy
  refine WP.mono (writeCore_ok hyInput.outputs result) fun t ⟨ht, written, Ft, Kt⟩ => ?_
  refine ⟨ht, written, ?_, Ku.trans (Kv.trans (Kw.trans (Kx.trans (Ky.trans Kt))))⟩
  have prefixFrame : Frame E.outputs.writes s.mem y.mem := (Fsx.trans Fy).mono (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact List.mem_cons_self ..)
  exact prefixFrame.trans Ft

end VG.Proof.RsaKeyGen.X86.Key
