module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPartResult
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyFinalMask
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Qinv
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Crt
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.FinalMask
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.PrimeProduct
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ScalarKey

/-! # Complete native arithmetic after the small-private-exponent check -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aD aPm aQm aOne aQi aN aE kEv kOk kFlag kStatus)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (KeyPartResult keyPartArrays stageRanges stage_preserves_num
  stage_preserves_e stage_mono stage_keep safePrime mask_bit mask_ite_one)

theorem keyPart_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0)
    (boundP : num s.mem B n aPa < 2 ^ (32 * k)) (boundQ : num s.mem B n aQa < 2 ^ (32 * k))
    (bit : slot s.mem B kOk ≤ 1) (loaded : num s.mem B n aE = val32 s.mem B kEv 2)
    (one : num s.mem B n aOne = 1) :
    WP isa keyPart s fun t =>
      Ws t B Z n 32 ∧ Outs B (stageRanges n keyPartArrays) s.mem t.mem ∧
      KeyPartResult B n s.mem t ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  unfold keyPart seqs
  refine WP.seq (WP.mono (qinvPart_ok h width positive boundP boundQ bit)
    fun u ⟨hu, Ou, Mu, boundQi, congruence, Ku⟩ => ?_)
  have oneU : num u.mem B n aOne = 1 :=
    (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)) Ou).trans one
  have Du : num u.mem B n aD = num s.mem B n aD :=
    stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)) Ou
  have Pmu : num u.mem B n aPm = num s.mem B n aPm :=
    stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)) Ou
  have Qmu : num u.mem B n aQm = num s.mem B n aQm :=
    stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)) Ou
  have frameU : Outs B (stageRanges n keyPartArrays) s.mem u.mem := stage_mono (by decide) Ou
  refine WP.seq (WP.mono (crtPart_ok hu oneU) fun v ⟨hv, Ov, Dp, Dq, Mv, Kv⟩ => ?_)
  rw [Du, Pmu] at Dp
  rw [Du, Qmu] at Dq
  rw [Mu] at Mv
  have qiV : num v.mem B n aQi = num u.mem B n aQi :=
    stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)) Ov
  have frameV : Outs B (stageRanges n keyPartArrays) u.mem v.mem := stage_mono (by decide) Ov
  have prefixFrame := frameU.trans frameV
  have Pv : num v.mem B n aPa = num s.mem B n aPa :=
    stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)) prefixFrame
  have Qv : num v.mem B n aQa = num s.mem B n aQa :=
    stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)) prefixFrame
  refine WP.seq (WP.mono (primeProduct_ok hv width positive even (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [Pv]; exact boundP) (by rw [Qv]; exact boundQ))
    fun w ⟨hw, Ow, N, Kw⟩ => ?_)
  rw [Pv, Qv] at N
  have frameW : Outs B (stageRanges n keyPartArrays) v.mem w.mem :=
    stage_keep (Nat.le_refl n) (by simp only [eq_self, true_and]; decide) (by decide) Ow
  have fullPrefix := prefixFrame.trans frameW
  have Pw : num w.mem B n aPa = num s.mem B n aPa :=
    stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)) fullPrefix
  have Qw : num w.mem B n aQa = num s.mem B n aQa :=
    stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)) fullPrefix
  have Ew : val32 w.mem B kEv 2 = val32 s.mem B kEv 2 := stage_preserves_e fullPrefix
  have loadedW : num w.mem B n aE = val32 w.mem B kEv 2 :=
    (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)) fullPrefix).trans (loaded.trans Ew.symm)
  have Mw : slot w.mem B kOk = (if slot s.mem B kOk = 1 ∧
      Nat.gcd (num s.mem B n aQa) (safePrime (num s.mem B n aPa)) = 1 then 1 else 0) :=
    (Ow.slot (by decide) (by decide)).trans Mv
  refine WP.seq (WP.mono (finalMask_ok hw (by rw [Mw]; exact mask_bit _) loadedW)
    fun a ⟨ha, Oa, Ma, Ka⟩ => ?_)
  rw [Mw, N, Pw, Qw, Ew] at Ma
  simp only [mask_ite_one, and_assoc] at Ma
  refine WP.mono (saveSlot_ok ha (by decide) (by decide)) fun t ⟨ht, Ot, status, Kt⟩ => ?_
  have last : Keep B n [aT1, aT2] [kFlag, kOk, kStatus] w.mem t.mem :=
    Oa.join Ot (js := [aT1, aT2]) (ds := [kFlag, kOk, kStatus])
  have tail : Keep B n [aN, aT1, aT2] (productScalars ++ [kFlag, kOk, kStatus]) v.mem t.mem :=
    Ow.join last (js := [aN, aT1, aT2]) (ds := (productScalars ++ [kFlag, kOk, kStatus]))
      (by decide) (by decide) (by decide) (by decide)
  have qiT : num t.mem B n aQi = num u.mem B n aQi :=
    (tail.num (by decide) (by decide) (h.fit64 (by decide))).trans qiV
  have frameA : Outs B (stageRanges n keyPartArrays) w.mem a.mem :=
    stage_keep (Nat.le_refl n) (by
      intro j hj
      left
      have H : ∀ j ∈ [aT1, aT2], j < 15 := by decide
      exact H j hj) (by decide) Oa
  have frameT : Outs B (stageRanges n keyPartArrays) a.mem t.mem :=
    stage_keep (Nat.le_refl n) (by simp) (by decide) Ot
  have maskT : slot t.mem B kOk = slot a.mem B kOk := Ot.slot (by decide) (by decide)
  refine ⟨ht, (fullPrefix.trans frameA).trans frameT, ⟨?_, ?_, ?_, ?_, ?_, maskT.trans Ma, ?_⟩,
    Ku.trans (Kv.trans ((Kw.mono (by decide)).trans ((Ka.mono (by decide)).trans (Kt.mono (by decide)))))⟩
  · exact (last.num (by decide) (by decide) (h.fit64 (by decide))).trans N
  · exact (tail.num (by decide) (by decide) (h.fit64 (by decide))).trans Dp
  · exact (tail.num (by decide) (by decide) (h.fit64 (by decide))).trans Dq
  · rw [qiT]
    exact boundQi
  · rw [qiT]
    exact congruence
  · exact status.trans maskT.symm

end VG.Proof.RsaKeyGen.X86.KeyRuntime
