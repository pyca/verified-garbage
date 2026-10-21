module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutcome
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPrepare
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPartResult
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySmall
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRetry
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPartCorrect
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPartOutcome

/-! # Complete native numeric RSA derivation, including all failure cases -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def deriveArrays : List Nat := prepareArrays ++ keyPartArrays

theorem deriveLoaded_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0)
    (lower : 16 ≤ n) (upper : n ≤ 256)
    (boundP : num s.mem B n aPa < 2 ^ (32 * k)) (boundQ : num s.mem B n aQa < 2 ^ (32 * k))
    (zero : num s.mem B n aZero = 0) (one : num s.mem B n aOne = 1)
    (loaded : num s.mem B n aE = val32 s.mem B kEv 2) :
    WP isa (deriveLoaded n) s fun t =>
      Ws t B Z n 32 ∧ Outs B (stageRanges n deriveArrays) s.mem t.mem ∧
      CoreOutcome B n (val32 s.mem B kEv 2) (num s.mem B n aPa) (num s.mem B n aQa) t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have boundP' : num s.mem B n aPa < 2 ^ (16 * n) := by rw [show 16 * n = 32 * k by omega]; exact boundP
  have boundQ' : num s.mem B n aQa < 2 ^ (16 * n) := by rw [show 16 * n = 32 * k by omega]; exact boundQ
  unfold deriveLoaded
  refine WP.seq (WP.mono (prepareLoaded_ok h width positive even boundP boundQ zero one loaded)
    fun u ⟨hu, Ou, R, Ku⟩ => ?_)
  have frameU : Outs B (stageRanges n deriveArrays) s.mem u.mem := stage_mono (by decide) Ou
  refine WP.seq (WP.mono (smallMask_ok hu R.bit) fun v ⟨hv, Ov, flag, Kv⟩ => ?_)
  have ready := KeyReady.small hu R Ov
  have maskV : slot v.mem B kOk = slot u.mem B kOk := Ov.slot (by decide) (by simp)
  have DV : num v.mem B n aD = num u.mem B n aD := Ov.num (by decide) (by simp) (h.fit64 (by decide))
  have frameV : Outs B (stageRanges n deriveArrays) u.mem v.mem :=
    stage_keep (Nat.le_refl n) (by simp only [eq_self, true_and]; decide) (by simp) Ov
  have branch : isa.eval .ne v = some (decide (slot u.mem B kOk = 1 ∧ num u.mem B n aD ≤ 2 ^ (16 * n))) := by
    change v.zf.map Bool.not = _
    change v.zf = some (decide (¬(slot u.mem B kOk = 1 ∧ num u.mem B n aD ≤ 2 ^ (16 * n)))) at flag
    rw [flag]
    by_cases small : slot u.mem B kOk = 1 ∧ num u.mem B n aD ≤ 2 ^ (16 * n) <;> simp [small]
  refine WP.ite _ branch (fun retryBit => ?_) (fun normalBit => ?_)
  · have small := of_decide_eq_true retryBit
    refine WP.mono (retry_ok hv) fun t ⟨ht, Ot, mask, status, Kt⟩ => ?_
    have frameT : Outs B (stageRanges n deriveArrays) v.mem t.mem :=
      stage_keep (Nat.le_refl n) (by simp) (by decide) Ot
    exact ⟨ht, (frameU.trans frameV).trans frameT, R.retry small.1 small.2 mask status,
      Ku.trans ((Kv.mono (by decide)).trans (Kt.mono (by decide)))⟩
  · have notSmall : ¬(slot v.mem B kOk = 1 ∧ num v.mem B n aD ≤ 2 ^ (16 * n)) := by
      rw [maskV, DV]
      exact of_decide_eq_false normalBit
    have pBound : num v.mem B n aPa < 2 ^ (32 * k) := by
      rw [ready.pValue]
      exact Nat.max_lt.mpr ⟨boundP, boundQ⟩
    have qBound : num v.mem B n aQa < 2 ^ (32 * k) := by
      rw [ready.qValue]
      exact Nat.lt_of_le_of_lt (Nat.min_le_left ..) boundP
    refine WP.mono (keyPart_ok hv width positive even pBound qBound ready.bit
      (ready.loaded.trans ready.exponent.symm) ready.one) fun t ⟨ht, Ot, result, Kt⟩ => ?_
    have frameT : Outs B (stageRanges n deriveArrays) v.mem t.mem := stage_mono (by decide) Ot
    exact ⟨ht, (frameU.trans frameV).trans frameT,
      KeyReady.part hv lower upper boundP' boundQ' ready notSmall Ot result,
      Ku.trans ((Kv.mono (by decide)).trans Kt)⟩

end VG.Proof.RsaKeyGen.X86.Key
