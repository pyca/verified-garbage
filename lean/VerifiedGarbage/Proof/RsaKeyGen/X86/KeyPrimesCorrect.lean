module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyPrimes
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOrder
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDecrement
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyProductValue

/-! # Sorted factors, saturated predecessors, and their exact full product -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def primesArrays : List Nat := [aT1, aT2, aPa, aQa, aPm, aQm, aPhi]
def primesScalars : List Nat := [kFlag, sT, kProduct]

theorem primes_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0)
    (boundP : num s.mem B n aPa < 2 ^ (32 * k)) (boundQ : num s.mem B n aQa < 2 ^ (32 * k))
    (zero : num s.mem B n aZero = 0) (one : num s.mem B n aOne = 1) :
    WP isa (primes n) s fun t =>
      Ws t B Z n 32 ∧ Keep B n primesArrays primesScalars s.mem t.mem ∧
      num t.mem B n aPa = max (num s.mem B n aPa) (num s.mem B n aQa) ∧
      num t.mem B n aQa = min (num s.mem B n aPa) (num s.mem B n aQa) ∧
      num t.mem B n aPm = max (num s.mem B n aPa) (num s.mem B n aQa) - 1 ∧
      num t.mem B n aQm = min (num s.mem B n aPa) (num s.mem B n aQa) - 1 ∧
      num t.mem B n aPhi = num t.mem B n aPm * num t.mem B n aQm ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
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
  refine ⟨ht, ?_, Pt, Qt, Pmt.trans Pmw, Qmt.trans Qm, ?_, Ku.trans (Kv.trans (Kw.trans (Kt.mono (by decide))))⟩
  · have first : Keep B n primesArrays primesScalars s.mem u.mem := Ou.mono (by decide) (by decide)
    have second : Keep B n primesArrays primesScalars u.mem v.mem := Ov.mono (by decide) (by decide)
    have third : Keep B n primesArrays primesScalars v.mem w.mem := Ow.mono (by decide) (by decide)
    have last : Keep B n primesArrays primesScalars w.mem t.mem := Ot.mono (by decide) (by decide)
    exact ((first.trans second).trans third).trans last
  · rw [Pmt, Qmt]
    exact product

end VG.Proof.RsaKeyGen.X86.Key
