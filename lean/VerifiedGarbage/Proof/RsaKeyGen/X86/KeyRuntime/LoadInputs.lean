module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInputInitialize
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyImportPrime
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyImportExponent
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyScratchFrame

/-! # The existing input adapters establish the shared arithmetic's inputs -/

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

theorem loadInputs_ok {E : Environment} {s : State} (h : Input E s) :
    WP isa (loadInputs E.n) s fun t => Loaded E s.mem t ∧
      Frame [E.workspaceRegion] s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  unfold loadInputs seqs
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
  exact ⟨⟨hx, pValueX, qValueX, eValue, pBoundX, qBoundX, oneX, zeroX, loaded⟩,
    Fsx, Ku.trans (Kv.trans (Kw.trans Kx))⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
