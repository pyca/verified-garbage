module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyLcm
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyConstant
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOddFlag
import VerifiedGarbage.Proof.Rsa.X86.KeySub
import VerifiedGarbage.Proof.Rsa.X86.KeySelect
import VerifiedGarbage.Proof.Rsa.InverseArithmetic

/-! # Select a safe native inverse modulus without revealing validity -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem oddModulus_ok {s : State} {B : Addr} {Z n input out : Nat}
    (h : Ws s B Z n 32) (hi : input < 32) (ho : out < 32)
    (ip : 16 ≤ input) :
    WP isa (oddModulus n input out) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aT2, out] [kFlag] s.mem t.mem ∧
      slot t.mem B kFlag = (if num s.mem B n input % 2 = 1 ∧ 3 ≤ num s.mem B n input then 1 else 0) ∧
      num t.mem B n out = (if num s.mem B n input % 2 = 1 ∧ 3 ≤ num s.mem B n input then num s.mem B n input else 3) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have fi := h.fit64 hi
  have fc := h.fit64 (j := aT1) (by decide)
  have hf : kFlag + 4 ≤ hdr := by decide
  have bound : 3 < 2 ^ (32 * n) := by
    have P : 2 ^ 32 ≤ 2 ^ (32 * n) := Nat.pow_le_pow_right (by decide) (by have := h.wpos; omega)
    omega
  unfold oddModulus seqs
  refine WP.seq (WP.mono (constArray_ok h (by decide) bound) fun u ⟨hu, Ou, constant, Ku⟩ => ?_)
  have Iu : num u.mem B n input = num s.mem B n input :=
    Ou.num (by simp only [List.mem_singleton]; intro k e; subst k; unfold aT1; omega) (by simp) fi
  refine WP.seq (WP.mono (sub3_ok hu (by decide) hi (by decide)
    (by unfold aT2; omega) (by decide)) fun v ⟨hv, Ov, subtract, bit, Kv⟩ => ?_)
  rw [Iu, constant] at subtract
  have borrow := VG.Proof.Rsa.borrow_iff subtract (val32_lt _ _ _ _) bit
  have Iv : num v.mem B n input = num s.mem B n input := by
    rw [Ov.num (by simp only [List.mem_singleton]; intro k e; subst k; unfold aT2; omega) (by simp) fi, Iu]
  have Cv : num v.mem B n aT1 = 3 := by rw [Ov.num (by decide) (by simp) fc, constant]
  refine WP.seq (WP.mono (oddFlag_ok hv hi bit) fun w ⟨hw, Ow, flag, Kw⟩ => ?_)
  rw [Iv] at flag
  have valid : slot w.mem B kFlag =
      if num s.mem B n input % 2 = 1 ∧ 3 ≤ num s.mem B n input then 1 else 0 := by
    by_cases b : (v.gpr .ebx).toNat = 0
    · have ge := borrow.mp b
      by_cases p : num s.mem B n input % 2 = 1
      · simp only [b, ite_true, p] at flag
        simpa [p, ge] using flag
      · have parity : num s.mem B n input % 2 = 0 := by omega
        simp only [b, ite_true, parity] at flag
        simpa [p] using flag
    · have ng : ¬3 ≤ num s.mem B n input := fun ge => b (borrow.mpr ge)
      simp only [b, ite_false] at flag
      simpa [ng] using flag
  have bitW : slot w.mem B kFlag ≤ 1 := by rw [valid]; split <;> omega
  have Iw : num w.mem B n input = num s.mem B n input := by
    rw [Ow.num (by simp) (by simp only [List.mem_singleton]; intro d e; subst d; exact hf) fi, Iv]
  have Cw : num w.mem B n aT1 = 3 := by
    rw [Ow.num (by simp) (by simp only [List.mem_singleton]; intro d e; subst d; exact hf) fc, Cv]
  refine WP.mono (sel_ok hw ho (by decide) hi hf bitW) fun t ⟨ht, Ot, selected, Kt⟩ => ?_
  refine ⟨ht, (((Ou.join Ov (js := [aT1, aT2, out]) (ds := [])).join Ow
    (js := [aT1, aT2, out]) (ds := [kFlag])).join Ot
    (js := [aT1, aT2, out]) (ds := [kFlag])), ?_, ?_,
    (Ku.mono (by decide)).trans (Kv.trans ((Kw.mono (by decide)).trans (Kt.mono (by decide))))⟩
  · rw [Ot.slot hf (by simp), valid]
  · rw [selected, valid, Iw, Cw]
    by_cases p : num s.mem B n input % 2 = 1 ∧ 3 ≤ num s.mem B n input <;> simp [p]

end VG.Proof.RsaKeyGen.X86.Key
