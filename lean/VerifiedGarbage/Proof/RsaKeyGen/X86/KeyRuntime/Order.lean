module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Ops
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Scalar
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace

/-! # The native factor sort preserves both values and hides their ordering -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (kFlag aPa aQa aPm aQm aPhi aHalf)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem order_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa (order) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aT2, aPa, aQa] [kFlag] s.mem t.mem ∧
      num t.mem B n aPa = max (num s.mem B n aPa) (num s.mem B n aQa) ∧
      num t.mem B n aQa = min (num s.mem B n aPa) (num s.mem B n aQa) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have hf : kFlag + 4 ≤ hdr := by decide
  have fp := h.fit64 (j := aPa) (by decide)
  have fq := h.fit64 (j := aQa) (by decide)
  have ft := h.fit64 (j := aT2) (by decide)
  unfold order seqs
  refine WP.seq (WP.mono (sub_ok h (by decide) (by decide) (by decide))
    fun u ⟨hu, Ou, subtract, bit, Ku⟩ => ?_)
  have borrow := VG.Proof.Rsa.borrow_iff subtract (val32_lt _ _ _ _) bit
  have pu : num u.mem B n aPa = num s.mem B n aPa := Ou.num (by decide) (by simp) fp
  have qu : num u.mem B n aQa = num s.mem B n aQa := Ou.num (by decide) (by simp) fq
  refine WP.seq (WP.mono (store_slot hu hf .ebx) fun v ⟨hv, Ov, flag, Kv⟩ => ?_)
  have pv : num v.mem B n aPa = num s.mem B n aPa := by
    rw [Ov.num (by simp) (by simp only [List.mem_singleton]; intro d e; subst d; exact hf) fp, pu]
  have qv : num v.mem B n aQa = num s.mem B n aQa := by
    rw [Ov.num (by simp) (by simp only [List.mem_singleton]; intro d e; subst d; exact hf) fq, qu]
  refine WP.seq (WP.mono (copy_ok hv (by decide) (by decide) (by decide)) fun w ⟨hw, Ow, copied, Kw, _⟩ => ?_)
  have pw : num w.mem B n aPa = num s.mem B n aPa := by rw [Ow.num (by decide) (by simp) fp, pv]
  have qw : num w.mem B n aQa = num s.mem B n aQa := by rw [Ow.num (by decide) (by simp) fq, qv]
  have tw : num w.mem B n aT2 = num s.mem B n aPa := copied.trans pv
  have fw : slot w.mem B kFlag = (u.gpr .ebx).toNat := by rw [Ow.slot hf (by simp), flag]
  have bw : slot w.mem B kFlag ≤ 1 := by rw [fw]; exact bit
  refine WP.seq (WP.mono (sel_ok hw (by decide) (by decide) (by decide) hf bw (by decide))
    fun x ⟨hx, Ox, selectedP, Kx⟩ => ?_)
  have qx : num x.mem B n aQa = num s.mem B n aQa := by rw [Ox.num (by decide) (by simp) fq, qw]
  have tx : num x.mem B n aT2 = num s.mem B n aPa := by rw [Ox.num (by decide) (by simp) ft, tw]
  have fx : slot x.mem B kFlag = (u.gpr .ebx).toNat := by rw [Ox.slot hf (by simp), fw]
  have bx : slot x.mem B kFlag ≤ 1 := by rw [fx]; exact bit
  refine WP.mono (sel_ok hx (by decide) (by decide) (by decide) hf bx (by decide))
    fun t ⟨ht, Ot, selectedQ, Kt⟩ => ?_
  have finalP : num t.mem B n aPa =
      if (u.gpr .ebx).toNat = 0 then num s.mem B n aPa else num s.mem B n aQa := by
    rw [Ot.num (by decide) (by simp) fp, selectedP, fw, pw, qw]
  have finalQ : num t.mem B n aQa =
      if (u.gpr .ebx).toNat = 0 then num s.mem B n aQa else num s.mem B n aPa := by
    rw [selectedQ, fx, qx, tx]
  refine ⟨ht, (((Ou.join Ov (js := [aT1, aT2, aPa, aQa]) (ds := [kFlag])).join Ow
    (js := [aT1, aT2, aPa, aQa]) (ds := [kFlag])).join Ox
    (js := [aT1, aT2, aPa, aQa]) (ds := [kFlag])).join Ot
    (js := [aT1, aT2, aPa, aQa]) (ds := [kFlag]), ?_, ?_,
    Ku.trans ((Kv.mono (by decide)).trans ((Kw.mono (by decide)).trans
      ((Kx.mono (by decide)).trans (Kt.mono (by decide)))))⟩
  · rw [finalP]
    by_cases p : (u.gpr .ebx).toNat = 0
    · rw [ite_eq_left p, Nat.max_eq_left (borrow.mp p)]
    · have lt : num s.mem B n aPa < num s.mem B n aQa := by
        have neg : ¬num s.mem B n aQa ≤ num s.mem B n aPa := fun le => p (borrow.mpr le)
        omega
      simp only [p, ite_false, Nat.max_eq_right (Nat.le_of_lt lt)]
  · rw [finalQ]
    by_cases p : (u.gpr .ebx).toNat = 0
    · rw [ite_eq_left p, Nat.min_eq_right (borrow.mp p)]
    · have lt : num s.mem B n aPa < num s.mem B n aQa := by
        have neg : ¬num s.mem B n aQa ≤ num s.mem B n aPa := fun le => p (borrow.mpr le)
        omega
      simp only [p, ite_false, Nat.min_eq_left (Nat.le_of_lt lt)]

end VG.Proof.RsaKeyGen.X86.KeyRuntime
