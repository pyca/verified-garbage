module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyFinal
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Rsa

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyMaskFlag
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyFinalExponent
import VerifiedGarbage.Proof.Rsa.X86.KeyBits
import VerifiedGarbage.Proof.RsaKeyGen.TopWord32
import VerifiedGarbage.Proof.Mont.X86.Instr
/-! # The final native mask is exactly the RSA key shape check -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyTopBit.lean`, which only this module imported.
section

/-! # Check the high modulus bit with a single native-word load -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem topBit_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa (.block (topBit n)) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [] [kFlag] s.mem t.mem ∧
      slot t.mem B kFlag = (if 2 ^ (32 * n - 1) ≤ num s.mem B n aN then 1 else 0) ∧
      Keeps [.eax] s t := by
  have head := h.hdr_le
  have fits := h.arr_fit (j := aN) (by decide)
  have positive := h.wpos
  unfold topBit
  refine wp_movS (readSrc_sc h.workspace (by change arr n aN + 4 * (n - 1) + 4 ≤ Z; unfold S at fits; omega))
    fun u U _ => ?_
  refine wp_shr (by decide) fun v V _ => ?_
  have K := U.keeps.trans V.keeps
  have hv := h.rest K
  refine wp_storeS (hv.workspace.ea (by unfold kFlag hdr at *; omega))
    (hv.workspace.write (by unfold kFlag hdr at *; omega)) fun t T => WP.block_nil ?_
  have memory : v.mem = s.mem := V.mem.trans U.mem
  refine ⟨hv.rest (T.keeps []), ?_, ?_, K.trans (T.keeps _)⟩
  · rw [T.mem, memory]
    exact Keep.of_slot (writeW32_outside _ _ _ (by decide)) (by simp)
  · unfold slot
    rw [T.mem, memory, w32_write_self, V.gpr, U.gpr, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    change w32 s.mem B (arr n aN + 4 * (n - 1)) / 2 ^ 31 = _
    rw [← VG.Proof.RsaKeyGen.WordBounds32.top_div positive]
    change num s.mem B n aN / 2 ^ (32 * n - 1) = _
    have bound := val32_lt s.mem B (arr n aN) n
    change num s.mem B n aN < 2 ^ (32 * n) at bound
    have p := Nat.two_pow_pos (32 * n - 1)
    have factor : 2 ^ (32 * n) = 2 ^ (32 * n - 1) * 2 := by
      calc
        2 ^ (32 * n) = 2 ^ ((32 * n - 1) + 1) := congrArg (2 ^ ·) (by omega)
        _ = _ := Nat.pow_succ ..
    rw [factor] at bound
    split
    · next H => exact Nat.div_eq_of_lt_le (by simpa only [Nat.one_mul] using H) (by omega)
    · next H => exact Nat.div_eq_of_lt (by omega)

end VG.Proof.RsaKeyGen.X86.Key
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem mask_bit (P : Prop) [Decidable P] : (if P then 1 else 0 : Nat) ≤ 1 := by
  split <;> decide

theorem mask_ite_one (P : Prop) [Decidable P] : (if P then 1 else 0 : Nat) = 1 ↔ P := by
  by_cases H : P <;> simp [H]

/-- The flag the final checks leave, as the conjunction of the checks: a
lemma about numbers, so that `finalMask_ok` does not normalize the
condition among facts about memory. -/
theorem finalMask_cond (m k N P Q e : Nat) :
    (if 3 ≤ e ∧ (if (if (if (if (if m = 1 ∧ (if k ≤ N then 1 else 0) = 1 then 1 else 0) = 1 ∧
        P % 2 = 1 then 1 else 0) = 1 ∧ Q % 2 = 1 then 1 else 0) = 1 ∧ e % 2 = 1 then 1 else 0) = 1 ∧
        (if e < 2 ^ 33 then 1 else 0) = 1 then 1 else 0) = 1 then 1 else 0 : Nat) =
      if m = 1 ∧ k ≤ N ∧ P % 2 = 1 ∧ Q % 2 = 1 ∧ Spec.Rsa.exponentValid e = true then 1 else 0 := by
  simp only [mask_ite_one, Spec.Rsa.exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    and_assoc, and_comm, and_left_comm]

theorem finalMask_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (bit : slot s.mem B kOk ≤ 1) (loaded : num s.mem B n aE = val32 s.mem B kEv 2) :
    WP isa (finalMask n) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aT2] [kFlag, kOk] s.mem t.mem ∧
      slot t.mem B kOk = (if slot s.mem B kOk = 1 ∧
        2 ^ (32 * n - 1) ≤ num s.mem B n aN ∧
        num s.mem B n aPa % 2 = 1 ∧ num s.mem B n aQa % 2 = 1 ∧
        Spec.Rsa.exponentValid (val32 s.mem B kEv 2) = true then 1 else 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  unfold finalMask seqs
  refine WP.seq (WP.mono (withFlag_ok bit (by split <;> omega_arith) (topBit_ok h))
    fun u ⟨hu, Ou, Mu, Ku⟩ => ?_)
  have Pu : num u.mem B n aPa = num s.mem B n aPa := Ou.num (by simp) (by decide) (h.fit64 (by decide))
  refine WP.seq (WP.mono (withFlag_ok (by rw [Mu]; exact mask_bit _)
    (show num u.mem B n aPa % 2 ≤ 1 by omega_arith) (bitOf_ok hu (by decide) (by decide)))
    fun v ⟨hv, Ov, Mv, Kv⟩ => ?_)
  rw [Pu, Mu] at Mv
  have Fv := Ou.trans Ov
  have Qv : num v.mem B n aQa = num s.mem B n aQa := Fv.num (by simp) (by decide) (h.fit64 (by decide))
  refine WP.seq (WP.mono (withFlag_ok (by rw [Mv]; exact mask_bit _)
    (show num v.mem B n aQa % 2 ≤ 1 by omega_arith) (bitOf_ok hv (by decide) (by decide)))
    fun w ⟨hw, Ow, Mw, Kw⟩ => ?_)
  rw [Qv, Mv] at Mw
  have Fw := Fv.trans Ow
  have Ew : num w.mem B n aE = val32 s.mem B kEv 2 :=
    (Fw.num (by simp) (by decide) (h.fit64 (by decide))).trans loaded
  refine WP.seq (WP.mono (withFlag_ok (by rw [Mw]; exact mask_bit _)
    (show num w.mem B n aE % 2 ≤ 1 by omega_arith) (bitOf_ok hw (by decide) (by decide)))
    fun a ⟨ha, Oa, Ma, Ka⟩ => ?_)
  rw [Ew, Mw] at Ma
  have Fa := Fw.trans Oa
  have Ea : val32 a.mem B kEv 2 = val32 s.mem B kEv 2 := maskFlag_preserves_e Fa
  refine WP.seq (WP.mono (withFlag_ok (by rw [Ma]; exact mask_bit _)
    (by split <;> omega_arith) (exponentUpper_ok ha)) fun b ⟨hb, Ob, Mb, Kb⟩ => ?_)
  rw [Ea, Ma] at Mb
  have Fb := Fa.trans Ob
  have Eb : num b.mem B n aE = val32 s.mem B kEv 2 :=
    (Fb.num (by simp) (by decide) (h.fit64 (by decide))).trans loaded
  refine WP.mono (exponentAtLeastThree_ok hb (by rw [Mb]; exact mask_bit _))
    fun t ⟨ht, Ot, Mt, Kt⟩ => ?_
  rw [Eb, Mb] at Mt
  refine ⟨ht, Fb.join Ot (js := [aT1, aT2]) (ds := [kFlag, kOk]), ?_,
    (Ku.mono (by decide)).trans ((Kv.mono (by decide)).trans ((Kw.mono (by decide)).trans
      ((Ka.mono (by decide)).trans ((Kb.mono (by decide)).trans Kt))))⟩
  exact Mt.trans (finalMask_cond _ _ _ _ _ _)

end VG.Proof.RsaKeyGen.X86.Key
