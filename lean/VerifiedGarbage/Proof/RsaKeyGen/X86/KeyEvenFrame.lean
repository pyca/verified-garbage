module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageFrame
import VerifiedGarbage.Proof.Rsa.WordRanges
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
public import VerifiedGarbage.Impl.Rsa.X86.Inverse
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageCover
public import VerifiedGarbage.Proof.RsaKeyGen.KeyMath
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseBridge
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
import VerifiedGarbage.Proof.Rsa.X86.InvParts
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseLoad
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Proof.RsaKeyGen.KeyOp
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.X86.KeyScalar

/-! ### `RsaKeyGen.X86.KeyOutcome`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyQinv`, which this module and modules that import it used -/

section

/-! # The CRT coefficient uses a prime-width native inverse -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def safePrime (p : Nat) : Nat := if p % 2 = 1 ∧ 3 ≤ p then p else 3
def qinvArrays : List Nat := [aDen, aQi]

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # Relate native key components and statuses to the shared specification -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

def assembledKey (B : Addr) (n : Nat) (m : Mem) : Spec.RsaKeyGen.Key :=
  ⟨num m B n aN, val32 m B kEv 2, num m B n aD, num m B n aPa, num m B n aQa,
    num m B n aDp, num m B n aDq, num m B n aQi⟩

def CoreOutcome (B : Addr) (n e p q : Nat) (m : Mem) : Prop :=
  match Spec.RsaKeyGen.keyFromPrimes (32 * n) e p q with
  | .inl (.ok key) => slot m B kStatus = 1 ∧ slot m B kOk = 1 ∧ assembledKey B n m = key
  | .inr () => slot m B kStatus = 2 ∧ slot m B kOk = 0
  | .inl (.error _) => slot m B kStatus = 0 ∧ slot m B kOk = 0

abbrev nativeShape (n e p q : Nat) : Prop :=
  2 ^ (32 * n - 1) ≤ p * q ∧ Nat.gcd q (safePrime p) = 1 ∧
    p % 2 = 1 ∧ q % 2 = 1 ∧ Spec.Rsa.exponentValid e = true

theorem qModP_eq_safePrime (p : Nat) : VG.Proof.RsaKeyGen.qModP p = safePrime p := by
  unfold VG.Proof.RsaKeyGen.qModP safePrime
  by_cases H : p < 3
  · have G : ¬3 ≤ p := by omega_using [H]
    simp [H, G]
  · have G : 3 ≤ p := by omega_using [H]
    simp [H, G]

theorem sorted_left (p q : Nat) : (if p < q then q else p) = max p q := by
  by_cases H : p < q
  · simp only [H, ite_true, Nat.max_eq_right (Nat.le_of_lt H)]
  · simp only [H, ite_false, Nat.max_eq_left (show q ≤ p by omega_using [H])]

theorem sorted_right (p q : Nat) : (if p < q then p else q) = min p q := by
  by_cases H : p < q
  · simp only [H, ite_true, Nat.min_eq_left (Nat.le_of_lt H)]
  · simp only [H, ite_false, Nat.min_eq_right (show q ≤ p by omega_using [H])]

theorem keyFromPrimes_native {n e p q x : Nat} (lower : 16 ≤ n) (upper : n ≤ 256)
    (boundP : p < 2 ^ (16 * n)) (boundQ : q < 2 ^ (16 * n)) (boundE : e < 2 ^ 64)
    (congruence : (safePrime (max p q) : Int) ∣ (x : Int) * min p q - Nat.gcd (min p q) (safePrime (max p q)))
    (boundX : x < safePrime (max p q)) :
    Spec.RsaKeyGen.keyFromPrimes (32 * n) e p q =
      match Spec.Rsa.inverse e (Nat.lcm (max p q - 1) (min p q - 1)) with
      | none => .inl (.error .internal)
      | some d => if d ≤ 2 ^ (16 * n) then .inr ()
        else if nativeShape n e (max p q) (min p q) then
          .inl (.ok ⟨max p q * min p q, e, d, max p q, min p q,
            d % (max p q - 1), d % (min p q - 1), x⟩)
        else .inl (.error .internal) := by
  have exponent : 8 * (2 * n) = 16 * n := by omega_using []
  have modulus : 16 * (2 * n) = 32 * n := by omega_using []
  have raw := VG.Proof.RsaKeyGen.keyFromPrimes_code (pLen := 2 * n) (e := e) (P₀ := p) (Q₀ := q) (x := x)
    (by omega_using [lower]) (by omega_using [upper]) (by rw [exponent]; exact boundP) (by rw [exponent]; exact boundQ) boundE
    (by simpa only [sorted_left, sorted_right, qModP_eq_safePrime] using congruence)
    (by simpa only [sorted_left, qModP_eq_safePrime] using boundX)
  simp only [modulus, exponent, sorted_left, sorted_right, qModP_eq_safePrime,
    Bool.and_eq_true, decide_eq_true_eq, and_assoc] at raw
  rw [raw]
  cases inverse : Spec.Rsa.inverse e (Nat.lcm (max p q - 1) (min p q - 1)) with
  | none => rfl
  | some d =>
    by_cases small : d ≤ 2 ^ (16 * n)
    · simp [small]
    · by_cases shape : nativeShape n e (max p q) (min p q) <;> simp_all [nativeShape]

theorem keyFromPrimes_retry {n e p q d : Nat}
    (inverse : Spec.Rsa.inverse e (Nat.lcm (max p q - 1) (min p q - 1)) = some d)
    (small : d ≤ 2 ^ (16 * n)) : Spec.RsaKeyGen.keyFromPrimes (32 * n) e p q = .inr () := by
  have order : (if p < q then (q, p) else (p, q)) = (max p q, min p q) := by
    by_cases H : p < q
    · simp only [H, ite_true, Nat.max_eq_right (Nat.le_of_lt H), Nat.min_eq_left (Nat.le_of_lt H)]
    · simp only [H, ite_false, Nat.max_eq_left (show q ≤ p by omega_using [H]), Nat.min_eq_right (show q ≤ p by omega_using [H])]
  unfold Spec.RsaKeyGen.keyFromPrimes
  rw [order]
  dsimp only
  rw [inverse]
  dsimp only
  rw [show 32 * n / 2 = 16 * n by omega_using [], ite_eq_left small]

end VG.Proof.RsaKeyGen.X86.Key

end

end

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
