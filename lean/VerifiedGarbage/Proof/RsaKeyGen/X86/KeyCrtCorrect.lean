module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyCrt
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageFrame
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisor
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEvenFrame

/-! # Compute both CRT exponents with safe fixed-schedule division -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

def crtArrays : List Nat := [aDen, aU, aDp, aDq]
def crtDivisor (x : Nat) : Nat := if x = 0 then 1 else x

theorem crtPart_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (one : num s.mem B n aOne = 1) :
    WP isa (crtPart n) s fun t =>
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

end VG.Proof.RsaKeyGen.X86.Key
