module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGcdPart
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyHalveStep
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyTwos
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionCorrect
import VerifiedGarbage.Proof.RsaKeyGen.HalveBounds
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGcdFrame

/-! # The native RSA LCM agrees with the shared integer algorithm

The proof includes arbitrary predecessors, including zero. The inverse
runs at prime width, while products and division retain modulus width.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def lcmDivisionRanges (n : Nat) : List (Nat × Nat) :=
  [(hdr, 4 * (4 * (n + 2))), (arr n aL, 4 * n), (arr n aT1, 4 * n)]

def lcmRanges (n k : Nat) : List (Nat × Nat) :=
  ranges n halveArrays [kFlag] ++ (gcdPartRanges n k ++ lcmDivisionRanges n)

theorem lcmPart_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k)
    (boundP : num s.mem B n aPm < 2 ^ (32 * k)) (boundQ : num s.mem B n aQm < 2 ^ (32 * k))
    (product : num s.mem B n aPhi = num s.mem B n aPm * num s.mem B n aQm)
    (one : num s.mem B n aOne = 1) :
    WP isa (lcmPart n) s fun t =>
      Ws t B Z n 32 ∧ Outs B (lcmRanges n k) s.mem t.mem ∧
      num t.mem B n aL = Nat.lcm (num s.mem B n aPm) (num s.mem B n aQm) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  let P := num s.mem B n aPm
  let Q := num s.mem B n aQm
  let T := VG.Proof.RsaKeyGen.halveIter (32 * n) (P, Q, P * Q)
  have small : k ≤ n := by omega
  have powBound : 2 ^ (32 * k) ≤ 2 ^ (32 * n) := Nat.pow_le_pow_right (by decide) (by omega)
  have productLocal : num s.mem B n aPhi = P * Q := product
  have phiBound : P * Q < 2 ^ (32 * n) := by
    rw [← productLocal]
    exact val32_lt _ _ _ _
  have bounds : T.1 < 2 ^ (32 * k) ∧ T.2.1 < 2 ^ (32 * k) ∧ T.2.2 < 2 ^ (32 * n) :=
    VG.Proof.RsaKeyGen.halveIter_bounds (32 * n) ⟨boundP, boundQ, phiBound⟩
  have arithmetic : (2 ≤ canonV T.1 T.2.1 → canonV T.1 T.2.1 % 2 = 1) ∧
      Nat.lcm P Q = T.2.2 / (if canonV T.1 T.2.1 ≤ 1 then 1 else Nat.gcd (canonU T.1 T.2.1) (canonV T.1 T.2.1)) :=
    VG.Proof.RsaKeyGen.lcm_eq (Nat.lt_of_lt_of_le boundP powBound) (Nat.lt_of_lt_of_le boundQ powBound)
  unfold lcmPart seqs
  refine WP.seq (WP.mono (twos_ok h) fun u ⟨hu, Ou, tripleValue, Ku⟩ => ?_)
  rw [productLocal] at tripleValue
  have U : num u.mem B n aU = T.1 := congrArg Prod.fst tripleValue
  have V : num u.mem B n aV = T.2.1 := congrArg (fun p => p.2.1) tripleValue
  have F : num u.mem B n aPhi = T.2.2 := congrArg (fun p => p.2.2) tripleValue
  have oneU : num u.mem B n aOne = 1 := by
    rw [Ou.num (by decide) (by decide) (h.fit64 (by decide)), one]
  refine WP.seq (WP.mono (gcdPart_ok hu width positive
    (by rw [U]; exact bounds.1) (by rw [V]; exact bounds.2.1)
    (by rw [U, V]; exact arithmetic.1) oneU) fun v ⟨hv, Ov, denominator, Kv⟩ => ?_)
  rw [U, V] at denominator
  have phiV : num v.mem B n aPhi = T.2.2 := by
    rw [gcdPart_preserves_num small (by decide) (by decide) (by decide) (by decide)
      (h.fit64 (by decide)) Ov, F]
  have denPositive : 0 < num v.mem B n aDen := by
    rw [denominator]
    split
    · decide
    · next notSmall => exact Nat.gcd_pos_of_pos_right _ (by omega)
  have h4 : Ws v B Z n 4 :=
    ⟨hv.workspace, Nat.le_trans (arr_mono (by decide : 4 ≤ 32)) hv.fits, hv.wpos, hv.wle⟩
  have fi := hv.arr_fit (j := aPhi) (by decide)
  have fd := hv.arr_fit (j := aDen) (by decide)
  have fl := hv.arr_fit (j := aL) (by decide)
  have ft := hv.arr_fit (j := aT1) (by decide)
  have input : DivisionInputs Z n (arr n aPhi) (arr n aDen) := by
    refine ⟨?_, ?_, Or.inr (arr_mono (by decide)), Or.inr (arr_mono (by decide))⟩
    · unfold S at fi
      omega
    · unfold S at fd
      omega
  have output : DivisionOutputs Z n (arr n aL) (arr n aT1) := by
    refine ⟨?_, ?_, Or.inr (arr_mono (by decide)), Or.inr (arr_mono (by decide)), ?_⟩
    · unfold S at fl
      omega
    · unfold S at ft
      omega
    · have endT := arr_end (w := n) (show aT1 < aL by decide)
      unfold S at endT
      exact Or.inr (by omega)
  refine WP.mono (divisionFrom_ok h4 input output denPositive) fun t ⟨_, Ot, quotient, _, Kt⟩ => ?_
  change num t.mem B n aL = num v.mem B n aPhi / num v.mem B n aDen at quotient
  rw [phiV, denominator] at quotient
  refine ⟨hv.rest Kt, ?_, quotient.trans arithmetic.2.symm, Ku.trans (Kv.trans Kt)⟩
  have first : Outs B (lcmRanges n k) s.mem u.mem :=
    VG.Proof.Mont.Outs.mono Ou (fun r hr => List.mem_append_left _ hr)
  have middle : Outs B (lcmRanges n k) u.mem v.mem :=
    Ov.mono (fun r hr => List.mem_append_right _ (List.mem_append_left _ hr))
  have last : Outs B (lcmRanges n k) v.mem t.mem :=
    Ot.mono (fun r hr => List.mem_append_right _ (List.mem_append_right _ hr))
  exact (first.trans middle).trans last

end VG.Proof.RsaKeyGen.X86.Key
