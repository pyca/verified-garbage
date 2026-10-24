module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Ops
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace

/-! # Saturating predecessors of arbitrary RSA input factors -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aOne kFlag aPa aQa aPm aQm aPhi aHalf)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem decTo_ok {s : State} {B : Addr} {Z n out a : Nat}
    (h : Ws s B Z n 32) (ho : out < 32) (ha : a < 32)
    (_oPersistent : 16 ≤ out) (aPersistent : 16 ≤ a) (_oa : out ≠ a)
    (zero : num s.mem B n aZero = 0) (one : num s.mem B n aOne = 1) :
    WP isa (decTo out a) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aT2, out] [sT, kFlag] s.mem t.mem ∧
      num t.mem B n out = num s.mem B n a - 1 ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have hFlag : kFlag + 4 ≤ hdr := by decide
  have hT : sT + 4 ≤ hdr := by decide
  have fa := h.fit64 ha
  unfold decTo seqs
  refine WP.seq (WP.mono (eq_ok h (by decide) ha (by decide)
    (by unfold aT1; omega) (by decide) hFlag) fun u ⟨hu, Ou, flag, Ku⟩ => ?_)
  have A : num u.mem B n a = num s.mem B n a :=
    Ou.num (by simp only [List.mem_singleton]; intro k e; subst k; unfold aT1; omega)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro d hd; rcases hd with rfl | rfl <;> with_reducible assumption)
      fa
  have Zero : num u.mem B n aZero = 0 := by
    rw [Ou.num (by decide) (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro d hd; rcases hd with rfl | rfl <;> with_reducible assumption)
      (h.fit64 (by decide)), zero]
  have One : num u.mem B n aOne = 1 := by
    rw [Ou.num (by decide) (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro d hd; rcases hd with rfl | rfl <;> with_reducible assumption)
      (h.fit64 (by decide)), one]
  rw [zero] at flag
  have bit : slot u.mem B kFlag ≤ 1 := by rw [flag]; split <;> omega
  refine WP.seq (WP.mono (sel_ok hu (by decide) (by decide) (by decide) hFlag bit (by decide))
    fun v ⟨hv, Ov, selected, Kv⟩ => ?_)
  have Av : num v.mem B n a = num s.mem B n a := by
    rw [Ov.num (by simp only [List.mem_singleton]; intro k e; subst k; unfold aT2; omega) (by simp) fa, A]
  have amount : num v.mem B n aT2 = if num s.mem B n a = 0 then 0 else 1 := by
    rw [selected, flag, One, Zero]
    by_cases p : num s.mem B n a = 0 <;> simp only [p, ite_true, ite_false, Nat.one_ne_zero]
  refine WP.mono (sub_ok hv ho ha (by decide))
    fun t ⟨ht, Ot, value, borrow, Kt⟩ => ?_
  rw [Av, amount] at value
  have fits : (if num s.mem B n a = 0 then 0 else 1) ≤ num s.mem B n a := by
    split <;> omega
  have noBorrow := (VG.Proof.Rsa.borrow_iff value (val32_lt t.mem B (arr n out) n) borrow).mpr fits
  rw [noBorrow, Nat.mul_zero, Nat.add_zero] at value
  refine ⟨ht, (Ou.join Ov (js := [aT1, aT2, out]) (ds := [sT, kFlag])).join Ot
    (js := [aT1, aT2, out]) (ds := [sT, kFlag]), ?_, ?_⟩
  · by_cases p : num s.mem B n a = 0
    · simp only [p, ite_true] at value ⊢
      omega
    · simp only [p, ite_false] at value
      omega
  · exact Ku.trans ((Kv.mono (by decide)).trans Kt)

end VG.Proof.RsaKeyGen.X86.KeyRuntime
