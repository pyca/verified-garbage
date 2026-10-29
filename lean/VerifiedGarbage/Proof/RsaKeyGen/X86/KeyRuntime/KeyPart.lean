module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPartResult
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.StackRange
public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InverseKeeps
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyFinalMask
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Qinv
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.FinalMask
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.PrimeProduct
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ScalarKey
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Ops
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Constant
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCrtCorrect
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DivisionFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionLoad
/-! # Complete native arithmetic after the small-private-exponent check -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/Divisor.lean`, which only this module imported.
section

/-! # A safe CRT divisor, including zero factor predecessors -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aDen aOne kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem divisorOf_ok {s : State} {B : Addr} {Z n input : Nat} (h : Ws s B Z n 32)
    (hi : input < 32) (ip : 16 ≤ input) (one : num s.mem B n aOne = 1) :
    WP isa (divisorOf input) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aT2, aDen] [sT, kFlag] s.mem t.mem ∧
      num t.mem B n aDen = (if num s.mem B n input = 0 then 1 else num s.mem B n input) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have fi := h.fit64 hi
  have fo := h.fit64 (j := aOne) (by decide)
  unfold divisorOf seqs
  refine WP.seq (WP.mono (constant_ok h (by decide) (0 : BitVec 32))
    fun u ⟨hu, Ou, zero, Ku⟩ => ?_)
  change num u.mem B n aT1 = 0 at zero
  have Iu : num u.mem B n input = num s.mem B n input :=
    Ou.num (by simp only [List.mem_singleton]; unfold aT1; omega) (by simp) fi
  have oneU : num u.mem B n aOne = 1 :=
    (Ou.num (by decide) (by simp) fo).trans one
  refine WP.seq (WP.mono (eq_ok hu (by decide) hi (by decide)
    (by unfold aT2; omega) (by decide) (by decide)) fun v ⟨hv, Ov, flag, Kv⟩ => ?_)
  rw [Iu, zero] at flag
  have Iv : num v.mem B n input = num s.mem B n input :=
    (Ov.num (by simp only [List.mem_singleton]; unfold aT2; omega) (by decide) fi).trans Iu
  have oneV : num v.mem B n aOne = 1 :=
    (Ov.num (by decide) (by decide) fo).trans oneU
  have bit : slot v.mem B kFlag ≤ 1 := by rw [flag]; split <;> omega
  refine WP.mono (sel_ok hv (by decide) hi (by decide) (by decide) bit (by right; decide))
    fun t ⟨ht, Ot, selected, Kt⟩ => ?_
  refine ⟨ht, (Ou.join Ov (js := [aT1, aT2, aDen]) (ds := [sT, kFlag])).join Ot
    (js := [aT1, aT2, aDen]) (ds := [sT, kFlag]), ?_,
    (Ku.mono (by decide)).trans (Kv.trans (Kt.mono (by decide)))⟩
  rw [selected, flag, Iv, oneV]
  by_cases I : num s.mem B n input = 0 <;> simp [I]

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/Crt.lean`, which only this module imported.
section

/-! # Compute both CRT exponents with safe fixed-schedule division -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key (aD aQm aPm aOne aDp aDq aDen kOk)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (stageRanges stage_keep stage_preserves_num crtArrays crtDivisor)

theorem crtPart_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (one : num s.mem B n aOne = 1) :
    WP isa crtPart s fun t =>
      Ws t B Z n 32 ∧ Outs B (stageRanges n crtArrays) s.mem t.mem ∧
      num t.mem B n aDp = num s.mem B n aD % crtDivisor (num s.mem B n aPm) ∧
      num t.mem B n aDq = num s.mem B n aD % crtDivisor (num s.mem B n aQm) ∧
      slot t.mem B kOk = slot s.mem B kOk ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have fd := h.fit64 (j := aD) (by decide)
  have fq := h.fit64 (j := aQm) (by decide)
  have fo := h.fit64 (j := aOne) (by decide)
  have fp := h.fit64 (j := aDp) (by decide)
  unfold crtPart VG.Impl.Rsa.X86.Keys.seqs
  refine WP.seq (WP.mono (divisorOf_ok h (by decide) (by decide) one)
    fun u ⟨hu, Ou, divisorP, Ku⟩ => ?_)
  have frameU : Outs B (stageRanges n crtArrays) s.mem u.mem :=
    stage_keep (Nat.le_refl n) (by simp only [eq_self, true_and]; decide) (by decide) Ou
  have Du : num u.mem B n aD = num s.mem B n aD :=
    Ou.num (by decide) (by decide) fd
  have divP : 0 < num u.mem B n aDen := by rw [divisorP]; split <;> omega
  refine WP.seq (WP.mono (arrayDivision_ok hu (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) divP)
    fun v ⟨hv, Ov, _, P, Kv⟩ => ?_)
  rw [Du, divisorP] at P
  have frameV : Outs B (stageRanges n crtArrays) u.mem v.mem := stage_division (by decide) (by decide) Ov
  have prefixFrame := frameU.trans frameV
  have Qv : num v.mem B n aQm = num s.mem B n aQm :=
    stage_preserves_num (by decide) (by decide) fq prefixFrame
  have Dv : num v.mem B n aD = num s.mem B n aD :=
    stage_preserves_num (by decide) (by decide) fd prefixFrame
  have oneV : num v.mem B n aOne = 1 :=
    (stage_preserves_num (by decide) (by decide) fo prefixFrame).trans one
  refine WP.seq (WP.mono (divisorOf_ok hv (by decide) (by decide) oneV)
    fun w ⟨hw, Ow, divisorQ, Kw⟩ => ?_)
  rw [Qv] at divisorQ
  have frameW : Outs B (stageRanges n crtArrays) v.mem w.mem :=
    stage_keep (Nat.le_refl n) (by simp only [eq_self, true_and]; decide) (by decide) Ow
  have Dw : num w.mem B n aD = num s.mem B n aD :=
    (Ow.num (by decide) (by decide) fd).trans Dv
  have Pw : num w.mem B n aDp = num v.mem B n aDp := Ow.num (by decide) (by decide) fp
  have divQ : 0 < num w.mem B n aDen := by rw [divisorQ]; split <;> omega
  refine WP.mono (arrayDivision_ok hw (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) divQ)
    fun t ⟨ht, Ot, _, Q, Kt⟩ => ?_
  rw [Dw, divisorQ] at Q
  have frameT : Outs B (stageRanges n crtArrays) w.mem t.mem := stage_division (by decide) (by decide) Ot
  exact ⟨ht, (prefixFrame.trans frameW).trans frameT,
    ((arrayDivision_preserves_num (by decide) (by decide) (by decide) fp Ot).trans Pw).trans P,
    Q, (arrayDivision_preserves_slot (by decide) Ot).trans ((Ow.slot (by decide) (by decide)).trans
      ((arrayDivision_preserves_slot (by decide) Ov).trans (Ou.slot (by decide) (by decide)))),
    (Ku.mono (by decide)).trans (Kv.trans ((Kw.mono (by decide)).trans Kt))⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

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
      Ws t B Z n 32 ∧ OutsS B (s.gpr .esp) (stageRanges n keyPartArrays) s.mem t.mem ∧
      KeyPartResult B n s.mem t ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  unfold keyPart seqs
  refine WP.seq (WP.mono (qinvPart_ok h width positive boundP boundQ bit)
    fun u ⟨hu, Ou, Mu, boundQi, congruence, Ku⟩ => ?_)
  have oneU : num u.mem B n aOne = 1 :=
    (h.read_num (by decide) Ou (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans one
  have Du : num u.mem B n aD = num s.mem B n aD :=
    h.read_num (by decide) Ou (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))
  have Pmu : num u.mem B n aPm = num s.mem B n aPm :=
    h.read_num (by decide) Ou (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))
  have Qmu : num u.mem B n aQm = num s.mem B n aQm :=
    h.read_num (by decide) Ou (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))
  have frameU : OutsS B (s.gpr .esp) (stageRanges n keyPartArrays) s.mem u.mem :=
    OutsS.lift (fun _ _ => stage_mono (by decide)) Ou
  refine WP.seq (WP.mono (crtPart_ok hu oneU) fun v ⟨hv, Ov, Dp, Dq, Mv, Kv⟩ => ?_)
  rw [Du, Pmu] at Dp
  rw [Du, Qmu] at Dq
  rw [Mu] at Mv
  have qiV : num v.mem B n aQi = num u.mem B n aQi :=
    stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)) Ov
  have frameV : Outs B (stageRanges n keyPartArrays) u.mem v.mem := stage_mono (by decide) Ov
  have prefixFrame := frameU.trans (OutsS.of_outs frameV)
  have Pv : num v.mem B n aPa = num s.mem B n aPa :=
    h.read_num (by decide) prefixFrame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))
  have Qv : num v.mem B n aQa = num s.mem B n aQa :=
    h.read_num (by decide) prefixFrame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))
  refine WP.seq (WP.mono (primeProduct_ok hv width positive even (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [Pv]; exact boundP) (by rw [Qv]; exact boundQ))
    fun w ⟨hw, Ow, N, Kw⟩ => ?_)
  rw [Pv, Qv] at N
  have frameW : Outs B (stageRanges n keyPartArrays) v.mem w.mem :=
    stage_keep (Nat.le_refl n) (by simp only [eq_self, true_and]; decide) (by decide) Ow
  have fullPrefix := prefixFrame.trans (OutsS.of_outs frameW)
  have Pw : num w.mem B n aPa = num s.mem B n aPa :=
    h.read_num (by decide) fullPrefix (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))
  have Qw : num w.mem B n aQa = num s.mem B n aQa :=
    h.read_num (by decide) fullPrefix (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))
  have Ew : val32 w.mem B kEv 2 = val32 s.mem B kEv 2 := h.read_val32 (by decide) fullPrefix stage_preserves_e
  have loadedW : num w.mem B n aE = val32 w.mem B kEv 2 :=
    (h.read_num (by decide) fullPrefix (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans (loaded.trans Ew.symm)
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
  refine ⟨ht, (fullPrefix.trans (OutsS.of_outs frameA)).trans (OutsS.of_outs frameT), ⟨?_, ?_, ?_, ?_, ?_, maskT.trans Ma, ?_⟩,
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
