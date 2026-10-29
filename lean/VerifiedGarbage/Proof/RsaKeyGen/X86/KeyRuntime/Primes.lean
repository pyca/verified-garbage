module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.PrimeProduct

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Decrement
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Ops
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Scalar
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
/-! # Sorted factors, saturated predecessors, and their exact full product -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/Order.lean`, which only this module imported.
section

/-! # The native factor sort preserves both values and hides their ordering -/

section
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
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aPm aQm aPhi aOne kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

def primesArrays : List Nat := [aT1, aT2, aPa, aQa, aPm, aQm, aPhi]
def primesScalars : List Nat := [kFlag, sT] ++ productScalars

theorem primes_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0)
    (boundP : num s.mem B n aPa < 2 ^ (32 * k)) (boundQ : num s.mem B n aQa < 2 ^ (32 * k))
    (zero : num s.mem B n aZero = 0) (one : num s.mem B n aOne = 1) :
    WP isa primes s fun t =>
      Ws t B Z n 32 ∧ Keep B n primesArrays primesScalars s.mem t.mem ∧
      num t.mem B n aPa = max (num s.mem B n aPa) (num s.mem B n aQa) ∧
      num t.mem B n aQa = min (num s.mem B n aPa) (num s.mem B n aQa) ∧
      num t.mem B n aPm = max (num s.mem B n aPa) (num s.mem B n aQa) - 1 ∧
      num t.mem B n aQm = min (num s.mem B n aPa) (num s.mem B n aQa) - 1 ∧
      num t.mem B n aPhi = num t.mem B n aPm * num t.mem B n aQm ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  let P := max (num s.mem B n aPa) (num s.mem B n aQa)
  let Q := min (num s.mem B n aPa) (num s.mem B n aQa)
  have pBound : P < 2 ^ (32 * k) := Nat.max_lt.mpr ⟨boundP, boundQ⟩
  have qBound : Q < 2 ^ (32 * k) := Nat.lt_of_le_of_lt (Nat.min_le_left ..) boundP
  unfold primes seqs
  refine WP.seq (WP.mono (order_ok h) fun u ⟨hu, Ou, Pu, Qu, Ku⟩ => ?_)
  have Zu : num u.mem B n aZero = 0 :=
    (Ou.num (by decide) (by decide) (h.fit64 (by decide))).trans zero
  have oneU : num u.mem B n aOne = 1 :=
    (Ou.num (by decide) (by decide) (h.fit64 (by decide))).trans one
  refine WP.seq (WP.mono (decTo_ok hu (by decide) (by decide) (by decide) (by decide) (by decide) Zu oneU)
    fun v ⟨hv, Ov, Pm, Kv⟩ => ?_)
  rw [Pu] at Pm
  have Pv : num v.mem B n aPa = P :=
    (Ov.num (by decide) (by decide) (h.fit64 (by decide))).trans Pu
  have Qv : num v.mem B n aQa = Q :=
    (Ov.num (by decide) (by decide) (h.fit64 (by decide))).trans Qu
  have Zv : num v.mem B n aZero = 0 :=
    (Ov.num (by decide) (by decide) (h.fit64 (by decide))).trans Zu
  have oneV : num v.mem B n aOne = 1 :=
    (Ov.num (by decide) (by decide) (h.fit64 (by decide))).trans oneU
  refine WP.seq (WP.mono (decTo_ok hv (by decide) (by decide) (by decide) (by decide) (by decide) Zv oneV)
    fun w ⟨hw, Ow, Qm, Kw⟩ => ?_)
  rw [Qv] at Qm
  have Pw : num w.mem B n aPa = P :=
    (Ow.num (by decide) (by decide) (h.fit64 (by decide))).trans Pv
  have Qw : num w.mem B n aQa = Q :=
    (Ow.num (by decide) (by decide) (h.fit64 (by decide))).trans Qv
  have Pmw : num w.mem B n aPm = P - 1 :=
    (Ow.num (by decide) (by decide) (h.fit64 (by decide))).trans Pm
  refine WP.mono (primeProduct_ok hw width positive even (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [Pmw]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) pBound)
    (by rw [Qm]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) qBound))
    fun t ⟨ht, Ot, product, Kt⟩ => ?_
  have Pt : num t.mem B n aPa = P :=
    (Ot.num (by decide) (by decide) (h.fit64 (by decide))).trans Pw
  have Qt : num t.mem B n aQa = Q :=
    (Ot.num (by decide) (by decide) (h.fit64 (by decide))).trans Qw
  have Pmt : num t.mem B n aPm = num w.mem B n aPm := Ot.num (by decide) (by decide) (h.fit64 (by decide))
  have Qmt : num t.mem B n aQm = num w.mem B n aQm := Ot.num (by decide) (by decide) (h.fit64 (by decide))
  refine ⟨ht, ?_, Pt, Qt, Pmt.trans Pmw, Qmt.trans Qm, ?_, (Ku.mono (by decide)).trans ((Kv.mono (by decide)).trans ((Kw.mono (by decide)).trans (Kt.mono (by decide))))⟩
  · have first : Keep B n primesArrays primesScalars s.mem u.mem := Ou.mono (by decide) (by decide)
    have second : Keep B n primesArrays primesScalars u.mem v.mem := Ov.mono (by decide) (by decide)
    have third : Keep B n primesArrays primesScalars v.mem w.mem := Ow.mono (by decide) (by decide)
    have last : Keep B n primesArrays primesScalars w.mem t.mem := Ot.mono (by decide) (by decide)
    exact ((first.trans second).trans third).trans last
  · rw [Pmt, Qmt]
    exact product

end VG.Proof.RsaKeyGen.X86.KeyRuntime
