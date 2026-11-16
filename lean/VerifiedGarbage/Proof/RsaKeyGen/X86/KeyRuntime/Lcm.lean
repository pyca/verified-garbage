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
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEven
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Rsa.X86.KeySelect
import VerifiedGarbage.Impl.Rsa.X86.Inverse
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.OddSecond
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Inverse
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGcdFrom
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Widen
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Ops
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseBridge
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.OddModulus

/-! ### `RsaKeyGen.X86.KeyGcdPart`, which only this module used -/

section

/-! # Complete native GCD stage for the RSA LCM -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

def canonU (u v : Nat) : Nat := if v % 2 = 0 then v else u
def canonV (u v : Nat) : Nat := if v % 2 = 0 then u else v

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.GcdFrom`, which only this module used -/

section

/-! # Prime-width GCD computation preserves the full RSA workspace

A saved bit chooses the computed gcd or one. The bit is retained across
the smaller inverse, and widening clears every unused output word.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aU aDen aOne kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Proof.RsaKeyGen.X86.Key (gcdRanges inverse_workspace inverse_array_layout inverse_end_le
  InverseLayout)

theorem gcdFrom_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k)
    (boundU : num s.mem B n aU < 2 ^ (32 * k)) (boundM : num s.mem B n aDen < 2 ^ (32 * k))
    (odd : num s.mem B n aDen % 2 = 1) (large : 1 < num s.mem B n aDen)
    (one : num s.mem B n aOne = 1) (bit : slot s.mem B kFlag ≤ 1) :
    WP isa gcdFrom s fun t =>
      Ws t B Z n 32 ∧ OutsS B (s.gpr .esp) (gcdRanges n k) s.mem t.mem ∧
      num t.mem B n aDen = (if slot s.mem B kFlag = 0 then 1 else
        Nat.gcd (num s.mem B n aU) (num s.mem B n aDen)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  obtain small : k ≤ n := by omega_using [width]
  obtain hk := inverse_workspace h.old positive small
  obtain layout := inverse_array_layout h.old small (a := aU) (b := aDen)
    (by decide) (by decide) (by decide) (by decide)
  obtain U := VG.Proof.RsaKeyGen.WordBounds32.low_eq small boundU
  obtain M := VG.Proof.RsaKeyGen.WordBounds32.low_eq small boundM
  obtain divWidth : n / 2 = k := by omega_using [width]
  unfold gcdFrom seqs
  obtain layout' : InverseLayout Z (Width.prime.words n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aU).offset n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aDen).offset n) := by
    simpa only [VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, Width.words, divWidth] using layout
  refine WP.seq (WP.mono (inverseFrom_ok h (by decide) (by decide) layout' 
    (by change val32 s.mem B (arr n aDen) (n / 2) % 2 = 1; rw [divWidth, M]; exact odd)
    (by change 1 < val32 s.mem B (arr n aDen) (n / 2); rw [divWidth, M]; exact large)) fun u ⟨hu, Ou, gcd, _, _, Ku⟩ => ?_)
  simp only [VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, Width.words, divWidth] at Ou gcd
  change num u.mem B k 1 = Nat.gcd (val32 s.mem B (arr n aU) k) (val32 s.mem B (arr n aDen) k) at gcd
  rw [U, M] at gcd
  obtain oneU : num u.mem B n aOne = 1 := by
    rw [h.inverse_num small (by decide) (by decide) Ou, one]
  obtain flagU : slot u.mem B kFlag = slot s.mem B kFlag := h.inverse_slot (by decide) Ou
  obtain sourceBound : arr k 1 + 4 * k ≤ Z := by
    obtain F := hk.arr_fit (j := 1) (by decide)
    unfold S at F
    omega_using [F]
  obtain before : arr k 1 + 4 * k ≤ arr n aDen := by
    obtain F := arr_end (w := k) (show 1 < 15 by decide)
    obtain E := inverse_end_le small (j := aDen) (by decide)
    unfold S at F
    omega_using [F, E]
  obtain widenProof := widen_ok hu .prime (VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aDen)
    (.array .prime 1) (by change n / 2 ≤ n; omega_using [])
    (by exact h.arr_fit (by decide))
    (by simpa only [offset_array, Width.words, divWidth] using sourceBound)
    (Or.inl (by simpa only [VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, Width.words, divWidth] using before))
  simp only [VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, Width.words, divWidth] at widenProof
  refine WP.seq (WP.mono widenProof
    fun v ⟨hv, Ov, _, widened, Kv⟩ => ?_)
  obtain denV : num v.mem B n aDen = Nat.gcd (num s.mem B n aU) (num s.mem B n aDen) := widened.trans gcd
  obtain oneV : num v.mem B n aOne = 1 := by
    change val32 v.mem B (arr n aOne) n = 1
    rw [Ov.val32 (d := arr n aOne) (k := n) (by unfold arr S aOne aDen; omega_using []) (by have := h.fit64 (j := aOne) (by decide); unfold S at this; omega_using [this])]
    exact oneU
  obtain flagV : slot v.mem B kFlag = slot s.mem B kFlag := by
    change w32 v.mem B kFlag = w32 s.mem B kFlag
    rw [Ov.w32 (d := kFlag) (by unfold arr aDen kFlag hdr; omega_using []) (by decide)]
    exact flagU
  refine WP.mono (sel_ok hv (by decide) (by decide) (by decide) (by decide)
    (by rw [flagV]; exact bit) (by decide)) fun t ⟨ht, Ot, selected, Kt⟩ => ?_
  refine ⟨ht, ?_, by rw [selected, flagV, oneV, denV],
    Ku.trans ((Kv.mono (by decide)).trans (Kt.mono (by decide)))⟩
  obtain first : OutsS B (s.gpr .esp) (gcdRanges n k) s.mem u.mem :=
    Ou.mono (fun r hr => List.mem_append_left _ hr)
  obtain middle : OutsS B (s.gpr .esp) (gcdRanges n k) u.mem v.mem :=
    OutsS.of_outs (Outs.of_outside Ov (List.mem_append_right _ (List.mem_singleton_self _)))
  obtain last : OutsS B (s.gpr .esp) (gcdRanges n k) v.mem t.mem := by
    change Outs B [(arr n aDen, S n)] v.mem t.mem at Ot
    exact OutsS.of_outs (Ot.mono (fun r hr => List.mem_append_right _ hr))
  exact (first.trans middle).trans last

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

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
  obtain cbU : canonU A C < 2 ^ (32 * k) := by
    unfold canonU
    split
    · exact boundV
    · exact boundU
  obtain cbV : canonV A C < 2 ^ (32 * k) := by
    unfold canonV
    split
    · exact boundU
    · exact boundV
  obtain bound3 : 3 < 2 ^ (32 * k) := by
    obtain P : 2 ^ 32 ≤ 2 ^ (32 * k) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have oddLocal : 2 ≤ canonV A C → canonV A C % 2 = 1 := odd
  obtain valid : canonV A C % 2 = 1 ∧ 3 ≤ canonV A C ↔ ¬canonV A C ≤ 1 := by
    constructor
    · intro H
      omega
    · intro H
      obtain O := oddLocal (by omega)
      exact ⟨O, by omega⟩
  unfold gcdPart VG.Impl.Rsa.X86.Keys.seqs
  refine WP.seq (WP.mono (oddSecond_ok h) fun u ⟨hu, Ou, U, V, Ku⟩ => ?_)
  change num u.mem B n aU = canonU A C at U
  change num u.mem B n aV = canonV A C at V
  obtain oneU : num u.mem B n aOne = 1 := by
    rw [Ou.num (by decide) (by decide) (h.fit64 (by decide)), one]
  refine WP.seq (WP.mono (oddModulus_ok hu (by decide) (by decide) (by decide))
    fun v ⟨hv, Ov, flag, modulus, Kv⟩ => ?_)
  rw [V] at flag modulus
  obtain Uv : num v.mem B n aU = canonU A C := by
    rw [Ov.num (by decide) (by decide) (h.fit64 (by decide)), U]
  obtain oneV : num v.mem B n aOne = 1 := by
    rw [Ov.num (by decide) (by decide) (h.fit64 (by decide)), oneU]
  obtain inputBound : num v.mem B n aU < 2 ^ (32 * k) := by rw [Uv]; exact cbU
  obtain modulusBound : num v.mem B n aDen < 2 ^ (32 * k) := by
    rw [modulus]
    split
    · exact cbV
    · exact bound3
  obtain modulusOdd : num v.mem B n aDen % 2 = 1 := by
    rw [modulus]
    split
    · next H => exact H.1
    · decide
  obtain modulusLarge : 1 < num v.mem B n aDen := by rw [modulus]; split <;> omega
  obtain bit : slot v.mem B kFlag ≤ 1 := by rw [flag]; split <;> omega
  refine WP.mono (gcdFrom_ok hv width positive inputBound modulusBound modulusOdd modulusLarge oneV bit)
    fun t ⟨ht, Ot, computed, Kt⟩ => ?_
  refine ⟨ht, ?_, ?_, (Ku.mono (by decide)).trans ((Kv.mono (by decide)).trans Kt)⟩
  · have first : Outs B (gcdPartRanges n k) s.mem u.mem :=
      VG.Proof.Mont.Outs.mono (Ou.mono (js' := gcdPartArrays) (by decide) (by simp))
        (fun r hr => List.mem_append_right _ hr)
    obtain middle : Outs B (gcdPartRanges n k) u.mem v.mem :=
      VG.Proof.Mont.Outs.mono (Ov.mono (js' := gcdPartArrays) (by decide) (by simp))
        (fun r hr => List.mem_append_right _ hr)
    obtain spV : v.gpr .esp = s.gpr .esp := by rw [Kv.1 .esp (by decide), Ku.1 .esp (by decide)]
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
  obtain small : k ≤ n := by omega_using [width]
  obtain powBound : 2 ^ (32 * k) ≤ 2 ^ (32 * n) := Nat.pow_le_pow_right (by decide) (by omega_using [width])
  have productLocal : num s.mem B n aPhi = P * Q := product
  obtain phiBound : P * Q < 2 ^ (32 * n) := by
    rw [← productLocal]
    exact val32_lt _ _ _ _
  obtain bounds : T.1 < 2 ^ (32 * k) ∧ T.2.1 < 2 ^ (32 * k) ∧ T.2.2 < 2 ^ (32 * n) :=
    VG.Proof.RsaKeyGen.halveIter_bounds (32 * n) ⟨boundP, boundQ, phiBound⟩
  obtain arithmetic : (2 ≤ canonV T.1 T.2.1 → canonV T.1 T.2.1 % 2 = 1) ∧
      Nat.lcm P Q = T.2.2 / (if canonV T.1 T.2.1 ≤ 1 then 1 else Nat.gcd (canonU T.1 T.2.1) (canonV T.1 T.2.1)) :=
    VG.Proof.RsaKeyGen.lcm_eq (Nat.lt_of_lt_of_le boundP powBound) (Nat.lt_of_lt_of_le boundQ powBound)
  unfold lcmPart seqs
  refine WP.seq (WP.mono (twos_ok h) fun u ⟨hu, Ou, tripleValue, Ku⟩ => ?_)
  rw [productLocal] at tripleValue
  obtain U : num u.mem B n aU = T.1 := congrArg Prod.fst tripleValue
  obtain V : num u.mem B n aV = T.2.1 := congrArg (fun p => p.2.1) tripleValue
  obtain F : num u.mem B n aPhi = T.2.2 := congrArg (fun p => p.2.2) tripleValue
  obtain oneU : num u.mem B n aOne = 1 := by
    rw [Ou.num (by decide) (by decide) (h.fit64 (by decide)), one]
  refine WP.seq (WP.mono (gcdPart_ok hu width positive
    (by rw [U]; exact bounds.1) (by rw [V]; exact bounds.2.1)
    (by rw [U, V]; exact arithmetic.1) oneU) fun v ⟨hv, Ov, denominator, Kv⟩ => ?_)
  rw [U, V] at denominator
  obtain phiV : num v.mem B n aPhi = T.2.2 := by
    rw [hu.read_num (by decide) Ov (gcdPart_preserves_num small (by decide) (by decide) (by decide) (by decide)
      (h.fit64 (by decide))), F]
  obtain denPositive : 0 < num v.mem B n aDen := by
    rw [denominator]
    split
    · decide
    · next notSmall => exact Nat.gcd_pos_of_pos_right _ (by omega_using [notSmall])
  refine WP.mono (arrayDivision_ok hv (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) denPositive)
    fun t ⟨ht, Ot, quotient, _, Kt⟩ => ?_
  change num t.mem B n aL = num v.mem B n aPhi / num v.mem B n aDen at quotient
  rw [phiV, denominator] at quotient
  refine ⟨ht, ?_, quotient.trans arithmetic.2.symm, Ku.trans (Kv.trans Kt)⟩
  obtain first : Outs B (lcmRanges n k) s.mem u.mem :=
    VG.Proof.Mont.Outs.mono Ou (fun r hr => List.mem_append_left _ hr)
  obtain spU : u.gpr .esp = s.gpr .esp := Ku.1 .esp (by decide)
  obtain middle : OutsS B (s.gpr .esp) (lcmRanges n k) u.mem v.mem := by
    rw [← spU]
    exact Ov.mono (fun r hr => List.mem_append_right _ (List.mem_append_left _ hr))
  obtain last : Outs B (lcmRanges n k) v.mem t.mem :=
    Ot.mono (fun r hr => List.mem_append_right _ (List.mem_append_right _ hr))
  exact ((OutsS.of_outs first).trans middle).trans (OutsS.of_outs last)

end VG.Proof.RsaKeyGen.X86.KeyRuntime
