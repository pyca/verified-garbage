module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCorePair
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInputInitialize
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyImportPrime
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyImportExponent
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyScratchFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO

/-! # The complete native input prefix initializes the arithmetic and imports its original inputs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def inputCode (n : Nat) : Prog isa :=
  .seq (.seq (.seq (clearArrays n) (loadPrime n 16 aPa)) (loadPrime n 24 aQa)) (loadExponent n)

def inputExponent (E : Environment) (m : Mem) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt m E.exponentRegion.base E.exponentRegion.len)
def inputPrime (E : Environment) (m : Mem) (i : Nat) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (E.outputRegion i).base (E.outputRegion i).len)

theorem loadInputs_ok {E : Environment} {s : State} (h : Input E s) :
    WP isa (inputCode E.n) s fun t =>
      Input E t ∧ CoreStart E.base E.size E.n E.k (inputExponent E s.mem)
        (inputPrime E s.mem 2) (inputPrime E s.mem 3) t ∧
      Frame [E.workspaceRegion] s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have widths := h.valid.widths
  unfold inputCode
  apply WP.assoc'
  apply WP.assoc'
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
  refine WP.mono hw.importExponent fun x ⟨hx, Fx, eValue, loaded, ex, Kx⟩ => ?_
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
  exact ⟨hx, ⟨⟨hx.ws, pBoundX, qBoundX, zeroX, oneX, eValue, loaded.trans eValue⟩,
    pValueX, qValueX⟩, Fsx, Ku.trans (Kv.trans (Kw.trans Kx))⟩

end VG.Proof.RsaKeyGen.X86.Key
