module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.ProductCorrect
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
import VerifiedGarbage.Proof.Mont.X86.WordOps

/-! # Assemble the private exponent from a quotient and a two-word scalar -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Mont.X86.Dynamic VG.Impl.RsaKeyGen.X86.Key

def dProductRanges (n : Nat) : List (Nat × Nat) :=
  [(kProduct, 4), (arr n 0, 4 * (n + 4)), (arr n aD, 4 * n)]

theorem dProduct_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) (width : 2 ≤ n)
    (fits : num s.mem B n aU * val32 s.mem B (arr n aDen) 2 + num s.mem B n aV < 2 ^ (32 * n)) :
    WP isa (dProduct n) s fun t =>
      Ws t B Z n 32 ∧ Outs B (dProductRanges n) s.mem t.mem ∧
      num t.mem B n aD = num s.mem B n aU * val32 s.mem B (arr n aDen) 2 + num s.mem B n aV ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have hn := h.workspace.nowrap
  have f0 := h.arr_fit (j := 0) (by decide)
  have f1 := h.arr_fit (j := 1) (by decide)
  have fu := h.arr_fit (j := aU) (by decide)
  have ft := h.arr_fit (j := aDen) (by decide)
  have fc := h.arr_fit (j := aV) (by decide)
  have fd := h.arr_fit (j := aD) (by decide)
  have L : Product.Layout Z n 2 (arr n 0) (arr n aU) (arr n aDen) kProduct := by
    refine ⟨h.wpos, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp only [arr, S, aU, aDen, kProduct, VG.Impl.Rsa.X86.Keys.hdr] at *
    all_goals omega
  unfold dProduct
  refine WP.seq (WP.mono (Product.correct h.workspace L) fun u ⟨Ou, V, Ku⟩ => ?_)
  change Outs B [(kProduct, 4), (arr n 0, 4 * (n + 4))] s.mem u.mem at Ou
  change val32 u.mem B (arr n 0) (n + 4) =
    val32 s.mem B (arr n aU) n * val32 s.mem B (arr n aDen) 2 at V
  change val32 s.mem B (arr n aU) n * val32 s.mem B (arr n aDen) 2 + val32 s.mem B (arr n aV) n < 2 ^ (32 * n) at fits
  have hu := h.rest Ku
  have low : val32 u.mem B (arr n 0) n = val32 s.mem B (arr n aU) n * val32 s.mem B (arr n aDen) 2 :=
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq (by omega : n ≤ n + 4) (by rw [V]; omega)).trans V
  have C : val32 u.mem B (arr n aV) n = val32 s.mem B (arr n aV) n := by
    apply Ou.val32 _ (by unfold S at fc; omega)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    all_goals simp only [arr, S, aV, kProduct, VG.Impl.Rsa.X86.Keys.hdr]
    all_goals omega
  refine WP.mono (chainAddW_ok hu.workspace h.wpos
    (by change arr n aD + 4 * n ≤ Z; unfold S at fd; omega)
    (by change arr n 0 + 4 * n ≤ Z; unfold S at f0; omega)
    (by change arr n aV + 4 * n ≤ Z; unfold S at fc; omega)
    (by change arr n aD + 4 * n ≤ arr n 0 ∨ arr n 0 + 4 * n ≤ arr n aD; unfold arr S aD; omega)
    (by change arr n aD + 4 * n ≤ arr n aV ∨ arr n aV + 4 * n ≤ arr n aD; unfold arr S aD aV; omega))
    fun t ⟨Ot, ⟨carry, _, sum⟩, Kt⟩ => ?_
  change Outside B (arr n aD) (4 * n) u.mem t.mem at Ot
  change val32 t.mem B (arr n aD) n + 2 ^ (32 * n) * carry.toNat =
    val32 u.mem B (arr n 0) n + val32 u.mem B (arr n aV) n at sum
  rw [low, C] at sum
  have result : num t.mem B n aD = num s.mem B n aU * val32 s.mem B (arr n aDen) 2 + num s.mem B n aV := by
    change val32 t.mem B (arr n aD) n = _
    cases carry <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at sum <;> omega
  refine ⟨hu.rest Kt, ?_, result, Ku.trans (Kt.mono (by decide))⟩
  have first : Outs B (dProductRanges n) s.mem u.mem := Ou.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [dProductRanges])
  exact first.trans (Outs.of_outside Ot (by simp [dProductRanges]))

end VG.Proof.RsaKeyGen.X86.Key
