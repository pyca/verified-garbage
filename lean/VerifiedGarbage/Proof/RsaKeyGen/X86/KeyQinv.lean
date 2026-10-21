module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyCrt
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageFrame
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOddModulus
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseBridge
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseCorrect
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGcdIsOne
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWidenCopy
import VerifiedGarbage.Proof.Rsa.X86.KeyScalar
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32

/-! # The CRT coefficient uses a prime-width native inverse -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def safePrime (p : Nat) : Nat := if p % 2 = 1 ∧ 3 ≤ p then p else 3
def qinvArrays : List Nat := [aDen, aQi]

theorem qinvPart_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k)
    (boundP : num s.mem B n aPa < 2 ^ (32 * k)) (boundQ : num s.mem B n aQa < 2 ^ (32 * k))
    (bit : slot s.mem B kOk ≤ 1) :
    WP isa (qinvPart n) s fun t =>
      Ws t B Z n 32 ∧ Outs B (stageRanges n qinvArrays) s.mem t.mem ∧
      slot t.mem B kOk = (if slot s.mem B kOk = 1 ∧
        Nat.gcd (num s.mem B n aQa) (safePrime (num s.mem B n aPa)) = 1 then 1 else 0) ∧
      num t.mem B n aQi < safePrime (num s.mem B n aPa) ∧
      (safePrime (num s.mem B n aPa) : Int) ∣
        (num t.mem B n aQi : Int) * num s.mem B n aQa -
          Nat.gcd (num s.mem B n aQa) (safePrime (num s.mem B n aPa)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  let P := num s.mem B n aPa
  let Q := num s.mem B n aQa
  let M := safePrime P
  have small : k ≤ n := by omega
  have half : n / 2 = k := by omega
  have mo : M % 2 = 1 := by
    unfold M safePrime
    split
    · next H => exact H.1
    · decide
  have ml : 1 < M := by unfold M safePrime; split <;> omega
  have threeBound : 3 < 2 ^ (32 * k) := by
    have H := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 32 ≤ 32 * k by omega)
    omega
  have mb : M < 2 ^ (32 * k) := by
    unfold M safePrime
    split
    · exact boundP
    · exact threeBound
  unfold qinvPart seqs
  rw [half]
  refine WP.seq (WP.mono (oddModulus_ok h (by decide) (by decide) (by decide))
    fun u ⟨hu, Ou, _, modulus, Ku⟩ => ?_)
  change num u.mem B n aDen = M at modulus
  have Qu : num u.mem B n aQa = Q := Ou.num (by decide) (by decide) (h.fit64 (by decide))
  have maskU : slot u.mem B kOk = slot s.mem B kOk := Ou.slot (by decide) (by decide)
  have lowQ : val32 u.mem B (arr n aQa) k = Q :=
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq small (by change num u.mem B n aQa < _; rw [Qu]; exact boundQ)).trans Qu
  have lowM : val32 u.mem B (arr n aDen) k = M :=
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq small (by change num u.mem B n aDen < _; rw [modulus]; exact mb)).trans modulus
  have hk := inverse_workspace hu positive small
  have layout := inverse_array_layout hu small (a := aQa) (b := aDen)
    (by decide) (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (inverseFrom_ok hk layout
    (by change val32 u.mem B (arr n aDen) k % 2 = 1; rw [lowM]; exact mo)
    (by change 1 < val32 u.mem B (arr n aDen) k; rw [lowM]; exact ml))
    fun v ⟨hvSmall, Ov, gcd, congruence, boundX, Kv⟩ => ?_)
  change num v.mem B k 1 = Nat.gcd (val32 u.mem B (arr n aQa) k) (val32 u.mem B (arr n aDen) k) at gcd
  change (val32 u.mem B (arr n aDen) k : Int) ∣ (num v.mem B k 3 : Int) * val32 u.mem B (arr n aQa) k - num v.mem B k 1 at congruence
  change num v.mem B k 3 < val32 u.mem B (arr n aDen) k at boundX
  rw [lowQ, lowM] at gcd congruence
  rw [lowM] at boundX
  rw [gcd] at congruence
  have hv := hu.rest Kv
  have maskV : slot v.mem B kOk = slot s.mem B kOk :=
    (inverse_preserves_slot (by decide) Ov).trans maskU
  refine WP.seq (WP.mono (gcdIsOne_ok hvSmall (Nat.le_refl 15))
    fun w ⟨_, Ow, flag, Kw⟩ => ?_)
  rw [gcd] at flag
  have Xw : num w.mem B k 3 = num v.mem B k 3 :=
    Ow.num (by decide) (by decide) (hvSmall.fit64 (by decide))
  have maskW : slot w.mem B kOk = slot s.mem B kOk :=
    (Ow.slot (by decide) (by decide)).trans maskV
  have hw := hv.rest Kw
  refine WP.seq (WP.mono (andS_ok hw (by decide) (by decide) (by decide)
    (by rw [maskW]; exact bit) (by rw [flag]; split <;> omega))
    fun a ⟨ha, Oa, maskA, Ka⟩ => ?_)
  rw [maskW, flag] at maskA
  have Xa : num a.mem B k 3 = num v.mem B k 3 := by
    have F := hvSmall.fit64 (j := 3) (by decide)
    have same : val32 a.mem B (arr k 3) k = val32 w.mem B (arr k 3) k := by
      apply Oa.val32 _ (by unfold S at F; omega)
      intro r hr
      change r ∈ [] ++ [(kOk, 4)] at hr
      have E : r = (kOk, 4) := by simpa only [List.nil_append, List.mem_singleton] using hr
      subst r
      exact Or.inr (Nat.le_trans (by decide : kOk + 4 ≤ hdr) (Nat.le_add_right ..))
    exact same.trans Xw
  have sourceBound : arr k 3 + 4 * k ≤ Z := by
    have F := hk.arr_fit (j := 3) (by decide)
    unfold S at F
    omega
  have before : arr k 3 + 4 * k ≤ arr n aQi := by
    have F := arr_end (w := k) (show 3 < 15 by decide)
    have E := inverse_end_le small (j := aQi) (by decide)
    unfold S at F
    omega
  refine WP.mono (widenCopy_ok ha positive small (by decide) sourceBound (Or.inl before))
    fun t ⟨ht, Ot, _, coefficient, Kt⟩ => ?_
  have X : num t.mem B n aQi = num v.mem B k 3 := coefficient.trans Xa
  have maskT : slot t.mem B kOk = slot a.mem B kOk :=
    Ot.w32 (Nat.le_trans (by decide : kOk + 4 ≤ hdr) (Nat.le_add_right ..) |> Or.inl) (by decide)
  have frameU : Outs B (stageRanges n qinvArrays) s.mem u.mem :=
    stage_keep (Nat.le_refl n) (by simp only [eq_self, true_and]; decide) (by decide) Ou
  have frameV : Outs B (stageRanges n qinvArrays) u.mem v.mem := stage_inverse small Ov
  have frameW : Outs B (stageRanges n qinvArrays) v.mem w.mem :=
    stage_keep small (by
      intro j hj
      left
      have H : ∀ j ∈ [aT2, aT1], j < 15 := by decide
      exact H j hj) (by decide) Ow
  have frameA : Outs B (stageRanges n qinvArrays) w.mem a.mem :=
    stage_keep (Nat.le_refl n) (by simp) (by decide) Oa
  refine ⟨ht, (((frameU.trans frameV).trans frameW).trans frameA).trans (stage_outside (by decide) Ot),
    ?_, ?_, ?_, (Ku.mono (by decide)).trans (Kv.trans ((Kw.mono (by decide)).trans
      ((Ka.mono (by decide)).trans (Kt.mono (by decide)))))⟩
  · rw [maskT, maskA]
    change (if slot s.mem B kOk = 1 ∧ (if Nat.gcd Q M = 1 then 1 else 0) = 1 then 1 else 0) =
      (if slot s.mem B kOk = 1 ∧ Nat.gcd Q M = 1 then 1 else 0)
    by_cases G : Nat.gcd Q M = 1 <;> simp [G]
  · rw [X]
    exact boundX
  · rw [X]
    exact congruence

end VG.Proof.RsaKeyGen.X86.Key
