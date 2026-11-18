module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageFrame
import VerifiedGarbage.Proof.Rsa.WordRanges
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
public import VerifiedGarbage.Impl.Rsa.X86.Inverse
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutcome
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageCover
public import VerifiedGarbage.Proof.RsaKeyGen.KeyMath
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseBridge
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
import VerifiedGarbage.Proof.Rsa.X86.InvParts
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseLoad

/-! ### `RsaKeyGen.X86.KeyPrepare`, which the modules that import this one used -/

section

/-! ### `RsaKeyGen.X86.KeyLcmFrame`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyGcdFrame`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyGcdFrom`, which this module and modules that import it used -/

section

/-! # Prime-width GCD computation preserves the full RSA workspace

A saved bit chooses the computed gcd or one. The bit is retained across
the smaller inverse, and widening clears every unused output word.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def gcdRanges (n k : Nat) : List (Nat × Nat) :=
  inverseRanges k invSlots ++ [(arr n aDen, S n)]

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # The native GCD stage keeps the primes and totient product intact -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def gcdPartArrays : List Nat := [aT1, aT2, aU, aV, aDen]
def gcdPartRanges (n k : Nat) : List (Nat × Nat) :=
  gcdRanges n k ++ ranges n gcdPartArrays [kFlag]

theorem gcdPart_preserves_num {m m' : Mem} {B : Addr} {n k j : Nat}
    (width : k ≤ n) (persistent : 15 ≤ j) (ju : j ≠ aU) (jv : j ≠ aV) (jd : j ≠ aDen)
    (fit : arr n j + S n ≤ 2 ^ 64) (changed : Outs B (gcdPartRanges n k) m m') :
    num m' B n j = num m B n j := by
  change val32 m' B (arr n j) n = val32 m B (arr n j) n
  apply changed.val32 _ (by unfold S at fit; omega_using [fit])
  intro r hr
  change r ∈ gcdRanges n k ++ ranges n gcdPartArrays [kFlag] at hr
  rcases List.mem_append.mp hr with inv | other
  · change r ∈ inverseRanges k invSlots ++ [(arr n aDen, S n)] at inv
    rcases List.mem_append.mp inv with small | den
    · simp only [inverseRanges, invSlots, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false] at small
      rcases small with rfl | rfl | rfl | rfl
      · have endBound := inverse_end_le width persistent
        have endEq : arr k 15 = hdr + 4 * (15 * (k + 2)) := by unfold arr S; omega_using []
        rw [endEq] at endBound
        exact Or.inr endBound
      all_goals have lower : hdr ≤ arr n j := Nat.le_add_right ..
      all_goals simp only [sOdd, sB, sC, hdr] at lower ⊢
      all_goals omega_using [lower]
    · simp only [List.mem_singleton] at den
      subst r
      have D := arr_disj (w := n) jd
      simp only at D ⊢
      unfold S at D ⊢
      omega_using [D]
  · simp only [ranges, List.mem_append, List.mem_map] at other
    rcases other with ⟨a, ha, rfl⟩ | ⟨d, hd, rfl⟩
    · have different : j ≠ a := by
        simp only [gcdPartArrays, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl
        · unfold aT1
          omega_using [persistent]
        · unfold aT2
          omega_using [persistent]
        · exact ju
        · exact jv
        · exact jd
      have D := arr_disj (w := n) different
      simp only at D ⊢
      unfold S at D ⊢
      omega_using [D]
    · simp only [List.mem_singleton] at hd
      subst d
      have lower : hdr ≤ arr n j := Nat.le_add_right ..
      exact Or.inr (Nat.le_trans (by decide : kFlag + 4 ≤ hdr) lower)

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # The complete native LCM leaves the factors and public exponent intact -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def lcmArrays : List Nat := [aHalf, aU, aV, aPhi, aDen, aL]

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyReady`, which this module and modules that import it used -/

section

/-! # Sorted factors and the specified inverse, ready for the retry branch -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

structure KeyReady (B : Addr) (n e p q : Nat) (m : Mem) : Prop where
  pValue : num m B n aPa = max p q
  qValue : num m B n aQa = min p q
  pm : num m B n aPm = max p q - 1
  qm : num m B n aQm = min p q - 1
  lcm : num m B n aL = Nat.lcm (max p q - 1) (min p q - 1)
  exponent : val32 m B kEv 2 = e
  loaded : num m B n aE = e
  one : num m B n aOne = 1
  inverse : Spec.Rsa.inverse e (Nat.lcm (max p q - 1) (min p q - 1)) =
    (if slot m B kOk = 0 then none else some (num m B n aD))
  bit : slot m B kOk ≤ 1

theorem KeyReady.small {s : State} {B : Addr} {Z n e p q : Nat} {m' : Mem}
    (h : Ws s B Z n 32) (R : KeyReady B n e p q s.mem)
    (O : Keep B n [aT1, aT2] [] s.mem m') : KeyReady B n e p q m' := by
  have same (j : Nat) (bound : j < 32) (persistent : 15 ≤ j) : num m' B n j = num s.mem B n j := by
    exact O.num (by
      intro a ha
      have H : ∀ a ∈ [aT1, aT2], a < 15 := by decide
      have Ha := H a ha
      omega_using [persistent, Ha]) (by simp) (h.fit64 bound)
  have E : val32 m' B kEv 2 = val32 s.mem B kEv 2 := by
    apply O.val32 _ (by decide)
    intro r hr
    change r ∈ [(arr n aT1, S n), (arr n aT2, S n)] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    all_goals exact Or.inl (Nat.le_trans (by decide : kEv + 8 ≤ hdr) (Nat.le_add_right ..))
  have mask : slot m' B kOk = slot s.mem B kOk := O.slot (by decide) (by simp)
  refine ⟨(same _ (by decide) (by decide)).trans R.pValue,
    (same _ (by decide) (by decide)).trans R.qValue,
    (same _ (by decide) (by decide)).trans R.pm,
    (same _ (by decide) (by decide)).trans R.qm,
    (same _ (by decide) (by decide)).trans R.lcm, E.trans R.exponent,
    (same _ (by decide) (by decide)).trans R.loaded,
    (same _ (by decide) (by decide)).trans R.one, ?_, ?_⟩
  · rw [mask, same _ (by decide) (by decide)]
    exact R.inverse
  · rw [mask]
    exact R.bit

theorem KeyReady.retry {B : Addr} {n e p q : Nat} {m m' : Mem} (R : KeyReady B n e p q m)
    (unit : slot m B kOk = 1) (small : num m B n aD ≤ 2 ^ (16 * n))
    (mask : slot m' B kOk = 0) (status : slot m' B kStatus = 2) : CoreOutcome B n e p q m' := by
  have inverse := R.inverse
  rw [unit, ite_eq_right (by decide : ¬(1 : Nat) = 0)] at inverse
  unfold CoreOutcome
  rw [keyFromPrimes_retry inverse small]
  exact ⟨status, mask⟩

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # The native factor, LCM, and private-inverse stages compose -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def prepareArrays : List Nat := [aPa, aQa, aPm, aQm, aPhi, aHalf, aU, aV, aDen, aL, aD]

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # Frames for the modulus-width inverse fallback -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem exponent_keep_frame {m m' : Mem} {B : Addr} {n : Nat} {js ds : List Nat}
    (arrays : ∀ j ∈ js, j < 15 ∨ j ∈ exponentArrays)
    (scalars : ∀ d ∈ ds, kOk ≤ d ∧ d + 4 ≤ kOk + 68) (O : Keep B n js ds m m') :
    Outs B (exponentRanges n) m m' := by
  apply VG.Proof.Rsa.outs_cover O
  intro r hr
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, hj, rfl⟩ | ⟨d, hd, rfl⟩
  · rcases arrays j hj with temp | result
    · refine ⟨(hdr, 15 * S n), by simp [exponentRanges, exponentTemps], ?_, ?_⟩
      · exact Nat.le_add_right ..
      · have endN := arr_end (w := n) temp
        change arr n j + S n ≤ arr n 15
        exact endN
    · exact ⟨(arr n j, S n), List.mem_append_right _
        (List.mem_append_left _ (List.mem_map.mpr ⟨j, result, rfl⟩)), Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨(kOk, 68), by simp [exponentRanges, exponentTemps], (scalars d hd).1, (scalars d hd).2⟩

end VG.Proof.RsaKeyGen.X86.Key
