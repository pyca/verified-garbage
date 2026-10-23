module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.MaskFlag
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.TopBit
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.FinalExponent
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ScalarKey
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Scalar
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyMaskFlag
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyFinalMask

/-! # The final native mask is exactly the RSA key shape check -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aN aE kOk kFlag kEv)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (mask_bit mask_ite_one maskFlag_preserves_e)

theorem finalMask_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (bit : slot s.mem B kOk ≤ 1) (loaded : num s.mem B n aE = val32 s.mem B kEv 2) :
    WP isa finalMask s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aT2] [kFlag, kOk] s.mem t.mem ∧
      slot t.mem B kOk = (if slot s.mem B kOk = 1 ∧
        2 ^ (32 * n - 1) ≤ num s.mem B n aN ∧
        num s.mem B n aPa % 2 = 1 ∧ num s.mem B n aQa % 2 = 1 ∧
        Spec.Rsa.exponentValid (val32 s.mem B kEv 2) = true then 1 else 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  unfold finalMask seqs
  refine WP.seq (WP.mono (withFlag_ok bit (by split <;> omega_arith) (topBit_ok h))
    fun u ⟨hu, Ou, Mu, Ku⟩ => ?_)
  have Pu : num u.mem B n aPa = num s.mem B n aPa := Ou.num (by simp) (by decide) (h.fit64 (by decide))
  refine WP.seq (WP.mono (withFlag_ok (by rw [Mu]; exact mask_bit _)
    (show num u.mem B n aPa % 2 ≤ 1 by omega_arith) (bitOf_ok hu (by decide) (by decide)))
    fun v ⟨hv, Ov, Mv, Kv⟩ => ?_)
  rw [Pu, Mu] at Mv
  have Fv := Ou.trans Ov
  have Qv : num v.mem B n aQa = num s.mem B n aQa := Fv.num (by simp) (by decide) (h.fit64 (by decide))
  refine WP.seq (WP.mono (withFlag_ok (by rw [Mv]; exact mask_bit _)
    (show num v.mem B n aQa % 2 ≤ 1 by omega_arith) (bitOf_ok hv (by decide) (by decide)))
    fun w ⟨hw, Ow, Mw, Kw⟩ => ?_)
  rw [Qv, Mv] at Mw
  have Fw := Fv.trans Ow
  have Ew : num w.mem B n aE = val32 s.mem B kEv 2 :=
    (Fw.num (by simp) (by decide) (h.fit64 (by decide))).trans loaded
  refine WP.seq (WP.mono (withFlag_ok (by rw [Mw]; exact mask_bit _)
    (show num w.mem B n aE % 2 ≤ 1 by omega_arith) (bitOf_ok hw (by decide) (by decide)))
    fun a ⟨ha, Oa, Ma, Ka⟩ => ?_)
  rw [Ew, Mw] at Ma
  have Fa := Fw.trans Oa
  have Ea : val32 a.mem B kEv 2 = val32 s.mem B kEv 2 := maskFlag_preserves_e Fa
  refine WP.seq (WP.mono (withFlag_ok (by rw [Ma]; exact mask_bit _)
    (by split <;> omega_arith) (exponentUpper_ok ha)) fun b ⟨hb, Ob, Mb, Kb⟩ => ?_)
  rw [Ea, Ma] at Mb
  have Fb := Fa.trans Ob
  have Eb : num b.mem B n aE = val32 s.mem B kEv 2 :=
    (Fb.num (by simp) (by decide) (h.fit64 (by decide))).trans loaded
  refine WP.mono (exponentAtLeastThree_ok hb (by rw [Mb]; exact mask_bit _))
    fun t ⟨ht, Ot, Mt, Kt⟩ => ?_
  rw [Eb, Mb] at Mt
  refine ⟨ht, Fb.join Ot (js := [aT1, aT2]) (ds := [kFlag, kOk]), ?_,
    (Ku.mono (by decide)).trans ((Kv.mono (by decide)).trans ((Kw.mono (by decide)).trans
      ((Ka.mono (by decide)).trans ((Kb.mono (by decide)).trans Kt))))⟩
  generalize slot s.mem B kOk = initialMask at Mt ⊢
  generalize num s.mem B n aN = modulus at Mt ⊢
  generalize num s.mem B n aPa = primeP at Mt ⊢
  generalize num s.mem B n aQa = primeQ at Mt ⊢
  generalize val32 s.mem B kEv 2 = exponent at Mt ⊢
  generalize slot t.mem B kOk = finalMaskValue at Mt ⊢
  simpa only [mask_ite_one, Spec.Rsa.exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    and_assoc, and_comm, and_left_comm] using Mt

end VG.Proof.RsaKeyGen.X86.KeyRuntime
