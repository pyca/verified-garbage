module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.HalveStep
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ArrayDivision
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGcdFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.StackRange

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Twos
import VerifiedGarbage.Proof.RsaKeyGen.HalveBounds
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InverseKeeps
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionLoad
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGcdPart
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.OddSecond
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.GcdFrom
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.OddModulus
/-! # The native RSA LCM agrees with the shared integer algorithm

The proof includes arbitrary predecessors, including zero. The inverse
runs at prime width, while products and division retain modulus width.
-/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/GcdPart.lean`, which only this module imported.
section

/-! # Complete native GCD stage for the RSA LCM -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key (aU aV aDen aOne kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (gcdPartRanges gcdPartArrays canonU canonV)

theorem gcdPart_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k)
    (boundU : num s.mem B n aU < 2 ^ (32 * k)) (boundV : num s.mem B n aV < 2 ^ (32 * k))
    (odd : 2 ≤ canonV (num s.mem B n aU) (num s.mem B n aV) →
      canonV (num s.mem B n aU) (num s.mem B n aV) % 2 = 1)
    (one : num s.mem B n aOne = 1) :
    WP isa gcdPart s fun t =>
      Ws t B Z n 32 ∧ OutsS B (s.gpr .esp) (gcdPartRanges n k) s.mem t.mem ∧
      num t.mem B n aDen =
        (if canonV (num s.mem B n aU) (num s.mem B n aV) ≤ 1 then 1 else
          Nat.gcd (canonU (num s.mem B n aU) (num s.mem B n aV))
            (canonV (num s.mem B n aU) (num s.mem B n aV))) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  let A := num s.mem B n aU
  let C := num s.mem B n aV
  have cbU : canonU A C < 2 ^ (32 * k) := by
    unfold canonU
    split
    · exact boundV
    · exact boundU
  have cbV : canonV A C < 2 ^ (32 * k) := by
    unfold canonV
    split
    · exact boundU
    · exact boundV
  have bound3 : 3 < 2 ^ (32 * k) := by
    have P : 2 ^ 32 ≤ 2 ^ (32 * k) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have oddLocal : 2 ≤ canonV A C → canonV A C % 2 = 1 := odd
  have valid : canonV A C % 2 = 1 ∧ 3 ≤ canonV A C ↔ ¬canonV A C ≤ 1 := by
    constructor
    · intro H
      omega
    · intro H
      have O := oddLocal (by omega)
      exact ⟨O, by omega⟩
  unfold gcdPart VG.Impl.Rsa.X86.Keys.seqs
  refine WP.seq (WP.mono (oddSecond_ok h) fun u ⟨hu, Ou, U, V, Ku⟩ => ?_)
  change num u.mem B n aU = canonU A C at U
  change num u.mem B n aV = canonV A C at V
  have oneU : num u.mem B n aOne = 1 := by
    rw [Ou.num (by decide) (by decide) (h.fit64 (by decide)), one]
  refine WP.seq (WP.mono (oddModulus_ok hu (by decide) (by decide) (by decide))
    fun v ⟨hv, Ov, flag, modulus, Kv⟩ => ?_)
  rw [V] at flag modulus
  have Uv : num v.mem B n aU = canonU A C := by
    rw [Ov.num (by decide) (by decide) (h.fit64 (by decide)), U]
  have oneV : num v.mem B n aOne = 1 := by
    rw [Ov.num (by decide) (by decide) (h.fit64 (by decide)), oneU]
  have inputBound : num v.mem B n aU < 2 ^ (32 * k) := by rw [Uv]; exact cbU
  have modulusBound : num v.mem B n aDen < 2 ^ (32 * k) := by
    rw [modulus]
    split
    · exact cbV
    · exact bound3
  have modulusOdd : num v.mem B n aDen % 2 = 1 := by
    rw [modulus]
    split
    · next H => exact H.1
    · decide
  have modulusLarge : 1 < num v.mem B n aDen := by rw [modulus]; split <;> omega
  have bit : slot v.mem B kFlag ≤ 1 := by rw [flag]; split <;> omega
  refine WP.mono (gcdFrom_ok hv width positive inputBound modulusBound modulusOdd modulusLarge oneV bit)
    fun t ⟨ht, Ot, computed, Kt⟩ => ?_
  refine ⟨ht, ?_, ?_, (Ku.mono (by decide)).trans ((Kv.mono (by decide)).trans Kt)⟩
  · have first : Outs B (gcdPartRanges n k) s.mem u.mem :=
      VG.Proof.Mont.Outs.mono (Ou.mono (js' := gcdPartArrays) (by decide) (by simp))
        (fun r hr => List.mem_append_right _ hr)
    have middle : Outs B (gcdPartRanges n k) u.mem v.mem :=
      VG.Proof.Mont.Outs.mono (Ov.mono (js' := gcdPartArrays) (by decide) (by simp))
        (fun r hr => List.mem_append_right _ hr)
    have spV : v.gpr .esp = s.gpr .esp := by rw [Kv.1 .esp (by decide), Ku.1 .esp (by decide)]
    rw [spV] at Ot
    exact (OutsS.of_outs (first.trans middle)).trans (Ot.mono (fun r hr => List.mem_append_left _ hr))
  · change num t.mem B n aDen = if canonV A C ≤ 1 then 1 else Nat.gcd (canonU A C) (canonV A C)
    rw [computed, flag, Uv, modulus]
    by_cases H : canonV A C ≤ 1
    · have inactive : ¬(canonV A C % 2 = 1 ∧ 3 ≤ canonV A C) := fun P => valid.mp P H
      simp [H, inactive]
    · have active := valid.mpr H
      simp [H, active]

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPm aQm aPhi aU aV aDen aOne aL kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Proof.RsaKeyGen.X86.Key (canonU canonV gcdPartRanges gcdPart_preserves_num)

def lcmDivisionRanges (n : Nat) : List (Nat × Nat) :=
  arrayDivisionRanges n aL aT1

def lcmRanges (n k : Nat) : List (Nat × Nat) :=
  ranges n halveArrays [kFlag] ++ (gcdPartRanges n k ++ lcmDivisionRanges n)

theorem lcmPart_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k)
    (boundP : num s.mem B n aPm < 2 ^ (32 * k)) (boundQ : num s.mem B n aQm < 2 ^ (32 * k))
    (product : num s.mem B n aPhi = num s.mem B n aPm * num s.mem B n aQm)
    (one : num s.mem B n aOne = 1) :
    WP isa lcmPart s fun t =>
      Ws t B Z n 32 ∧ OutsS B (s.gpr .esp) (lcmRanges n k) s.mem t.mem ∧
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
    rw [hu.read_num (by decide) Ov (gcdPart_preserves_num small (by decide) (by decide) (by decide) (by decide)
      (h.fit64 (by decide))), F]
  have denPositive : 0 < num v.mem B n aDen := by
    rw [denominator]
    split
    · decide
    · next notSmall => exact Nat.gcd_pos_of_pos_right _ (by omega)
  refine WP.mono (arrayDivision_ok hv (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) denPositive)
    fun t ⟨ht, Ot, quotient, _, Kt⟩ => ?_
  change num t.mem B n aL = num v.mem B n aPhi / num v.mem B n aDen at quotient
  rw [phiV, denominator] at quotient
  refine ⟨ht, ?_, quotient.trans arithmetic.2.symm, Ku.trans (Kv.trans Kt)⟩
  have first : Outs B (lcmRanges n k) s.mem u.mem :=
    VG.Proof.Mont.Outs.mono Ou (fun r hr => List.mem_append_left _ hr)
  have spU : u.gpr .esp = s.gpr .esp := Ku.1 .esp (by decide)
  have middle : OutsS B (s.gpr .esp) (lcmRanges n k) u.mem v.mem := by
    rw [← spU]
    exact Ov.mono (fun r hr => List.mem_append_right _ (List.mem_append_left _ hr))
  have last : Outs B (lcmRanges n k) v.mem t.mem :=
    Ot.mono (fun r hr => List.mem_append_right _ (List.mem_append_right _ hr))
  exact ((OutsS.of_outs first).trans middle).trans (OutsS.of_outs last)

end VG.Proof.RsaKeyGen.X86.KeyRuntime
