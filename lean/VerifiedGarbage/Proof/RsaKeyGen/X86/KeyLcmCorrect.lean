module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyHalveStep
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGcdFrame

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGcdPart
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionCorrect
import VerifiedGarbage.Proof.RsaKeyGen.HalveBounds
import VerifiedGarbage.Proof.Rsa.X86.DivCount
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Rsa.X86.KeyCopy
/-! # The native RSA LCM agrees with the shared integer algorithm

The proof includes arbitrary predecessors, including zero. The inverse
runs at prime width, while products and division retain modulus width.
-/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyTwosBody.lean`, which only this module imported.
section

/-! # One public iteration of the native RSA LCM halving schedule -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

structure HalveLoop (s₀ : State) (B : Addr) (Z n i : Nat) (s : State) : Prop where
  workspace : Ws s B Z n 32
  frame : Keep B n halveArrays [kFlag] s₀.mem s.mem
  rest : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s₀ s
  counter : s.gpr .esi = BitVec.ofNat 32 (32 * n - i)
  value : triple s.mem B n = VG.Proof.RsaKeyGen.halveIter i (triple s₀.mem B n)

theorem twoStep_ok {s₀ s : State} {B : Addr} {Z n i : Nat}
    (H : HalveLoop s₀ B Z n i s) (index : i < 32 * n) :
    WP isa (twoStep n) s fun t => HalveLoop s₀ B Z n (i + 1) t ∧
      t.zf = some (decide (i + 1 = 32 * n)) := by
  have bound : 32 * n < 2 ^ 32 := by have := H.workspace.wle; omega
  unfold twoStep
  refine WP.seq (WP.mono (halveStep_ok H.workspace) fun u ⟨hu, Ou, value, Ku⟩ => ?_)
  refine WP.mono (VG.Proof.Rsa.X86.Div.count_ok u) fun t ⟨counter, Zf, memory, Kt⟩ => ?_
  have before : u.gpr .esi = s.gpr .esi := Ku.1 _ (by decide)
  rw [H.value, ← VG.Proof.RsaKeyGen.halveIter_succ'] at value
  refine ⟨⟨hu.rest Kt, ?_, H.rest.trans ((Ku.mono (by decide)).widen Kt), ?_, ?_⟩, ?_⟩
  · rw [memory]
    exact H.frame.trans Ou
  · rw [counter, before, H.counter]
    change BitVec.ofNat 32 (32 * n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  · rw [memory]
    exact value
  · rw [Zf, before, H.counter]
    change some (BitVec.ofNat 32 (32 * n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [show 32 * n - i - 1 = 0 ↔ i + 1 = 32 * n by omega]

end VG.Proof.RsaKeyGen.X86.Key
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyTwosLoop.lean`, which only this module imported.
section

/-! # The complete fixed schedule matches the shared LCM arithmetic -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem twos_loop {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (counter : s.gpr .esi = BitVec.ofNat 32 (32 * n)) :
    WP isa (.loop (twoStep n) .ne) s fun t => HalveLoop s B Z n (32 * n) t := by
  have positive : 0 < 32 * n := by have := h.wpos; omega
  have initial : HalveLoop s B Z n 0 s :=
    ⟨h, VG.Proof.Rsa.X86.Keys.Keep.refl B n halveArrays [kFlag] s.mem, Keeps.refl .., by simpa only [Nat.sub_zero] using counter, rfl⟩
  refine WP.loop (M := isa)
    (fun remaining t => ∃ i, remaining = 32 * n - i ∧ i < 32 * n ∧ HalveLoop s B Z n i t)
    ?_ (32 * n) s ⟨0, by omega, positive, initial⟩
  rintro remaining t ⟨i, rfl, index, H⟩
  refine WP.mono (twoStep_ok H index) fun u ⟨next, Zf⟩ => ?_
  by_cases last : i + 1 = 32 * n
  · exact .inl ⟨by simp only [eval, Zf, last, decide_true, Option.map_some, Bool.not_true], last ▸ next⟩
  · exact .inr ⟨by simp only [eval, Zf, decide_eq_false last, Option.map_some, Bool.not_false],
      32 * n - (i + 1), by omega, i + 1, rfl, by omega, next⟩

end VG.Proof.RsaKeyGen.X86.Key
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyTwos.lean`, which only this module imported.
section

/-! # Preparing and running the complete native common-halving schedule -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem twos_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa (twos n) s fun t =>
      Ws t B Z n 32 ∧ Keep B n halveArrays [kFlag] s.mem t.mem ∧
      triple t.mem B n = VG.Proof.RsaKeyGen.halveIter (32 * n)
        (num s.mem B n aPm, num s.mem B n aQm, num s.mem B n aPhi) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have fu := h.fit64 (j := aU) (by decide)
  have fq := h.fit64 (j := aQm) (by decide)
  have ff := h.fit64 (j := aPhi) (by decide)
  unfold twos VG.Impl.Rsa.X86.Keys.seqs
  refine WP.seq (WP.mono (copy_ok h (by decide) (by decide)) fun u ⟨hu, Ou, copiedU, Ku, _⟩ => ?_)
  refine WP.seq (WP.mono (copy_ok hu (by decide) (by decide)) fun v ⟨hv, Ov, copiedV, Kv, _⟩ => ?_)
  refine WP.seq (wp_movS rfl fun w W _ => WP.block_nil ?_)
  have hw := hv.rest W.keeps (by decide) (by decide)
  refine WP.mono (twos_loop hw W.gpr) fun t H => ?_
  have valueW : triple w.mem B n =
      (num s.mem B n aPm, num s.mem B n aQm, num s.mem B n aPhi) := by
    unfold triple
    rw [W.mem, Ov.num (j := aU) (by decide) (by simp) fu, copiedU, copiedV,
      Ou.num (j := aQm) (by decide) (by simp) fq,
      Ov.num (j := aPhi) (by decide) (by simp) ff,
      Ou.num (j := aPhi) (by decide) (by simp) ff]
  have frame : Keep B n halveArrays [kFlag] v.mem t.mem := by
    have F := H.frame
    rw [W.mem] at F
    exact F
  refine ⟨H.workspace, ?_, ?_, ?_⟩
  · exact ((Ou.join Ov (js := halveArrays) (ds := [kFlag])
      (by simp [halveArrays]) (by simp) (by simp [halveArrays]) (by simp))).trans frame
  · rw [H.value, valueW]
  · exact (Ku.mono (by decide)).trans ((Kv.mono (by decide)).trans
      ((W.keeps.mono (by decide)).trans H.rest))

end VG.Proof.RsaKeyGen.X86.Key
end

end

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
