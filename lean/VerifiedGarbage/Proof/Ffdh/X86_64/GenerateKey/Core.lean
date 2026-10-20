module

import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Tail
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Reject
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.ResultMath
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Start
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Scalar
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock

/-! # FFDH on x86-64: scalar rejection and generated public values -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

/-- The complete attempt result before restoring the caller's saved registers. -/
def AttemptPost (p : GkP) (rb : List Byte) (s t : State) : Prop :=
  t.gpr .rax = BitVec.ofNat 64 (resultStatus p rb) ∧ t.gpr .rdi = p.B ∧
    Spec.Rsa.bytesAt t.mem p.xp p.k = (if resultStatus p rb = 1 then p.cut rb else List.replicate p.k 0) ∧
    Spec.Rsa.bytesAt t.mem p.yp p.k = Spec.Rsa.i2osp (if resultStatus p rb = 1 then p.z rb else 0) p.k ∧
    (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ RunFrame p s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t

theorem core_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M)
    {p : GkP} {rb : List Byte} {s : State}
    (h : CheckPrivate.Base p.kp (p.xb rb) s) (hd : s.gpr .rdi = p.B)
    (hG : word s.mem p.B (8 * sG) = off p.dp p.k) (hQ : word s.mem p.B (8 * sQ) = off p.dp (2 * p.k))
    (hm : p.mv = true) (hx : Src s p.B p.Z p.xp (p.cut rb))
    (hoX : OutOk s p.B p.Z p.xp p.k) (hoY : OutOk s p.B p.Z p.yp p.k)
    (ha : Apart p.xp p.k p.yp p.k) (hlen : (p.cut rb).length = p.k) (hld : p.ld < p.k) :
    WP isa (seqs (core M.mm E.code (.seq (.block r2Head) R.code))) s (AttemptPost p rb s) := by
  have hk : 64 ≤ p.k := h.k1
  have hodd := (valid_facts hm hk).1
  unfold core
  simp only [List.append_assoc]
  refine wp_seqs_append
    (a := ([.block VG.Impl.Rsa.X86_64.head] ++ pSetup ++ VG.Impl.Rsa.X86_64.Crt.loadArr aXm sX sXl))
    (b := VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange ++ [.block [.alu .test .rax (.reg .rax)],
      .ite .e (seqs [.block [VG.Impl.Rsa.X86_64.Crt.leave], maskX, ret 2])
        (seqs (VG.Impl.Ffdh.X86_64.Domain.GenerateKey.tail M.mm E.code (.seq (.block r2Head) R.code)))])
    (by simp [pSetup]) (by simp)
    (WP.mono (CheckPrivate.setup_work h hd hG hQ hm) fun u₁ S₁ => ?_)
  obtain ⟨mi, hw₁, hd₁⟩ := S₁.1
  refine wp_seqs_append (a := VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange)
    (by simp [VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange, isNonzero, geArr, cmpArr]) (by simp)
    (WP.mono (CheckPrivate.scalar_ok hw₁ hd₁ hodd) fun u₂ S₂ => ?_)
  have hw₂ := S₂.1.1
  have hd₂ := S₂.1.2.1
  simp only [seqs]
  have hflag₂ : u₂.gpr .rax = bit (p.sv = true) := S₂.1.2.2
  refine WP.seq (WP.mono (test_bit_ok hflag₂) fun u₃ ⟨hz, hmem, k⟩ => ?_)
  have hw₃ := hw₂.keep hmem k
  have hd₃ := (k.gpr (by decide)).trans hd₂
  have S₃ : CheckPrivate.StepPost p.kp u₂ (fun _ => True) u₃ :=
    ⟨trivial, by rw [hmem]; exact InScr.refl _ _ _, fun _ _ => by rw [hmem], k.mono (by decide)⟩
  have H := (S₁.trans S₂).trans S₃
  have hx₃ := hx.congrK H.2.1 H.2.2.2
  have hox₃ : OutOk u₃ p.B p.Z p.xp p.k :=
    ⟨fun i hi => by rw [H.2.2.2.2.2]; exact hoX.wr i hi, hoX.sep⟩
  have hoy₃ : OutOk u₃ p.B p.Z p.yp p.k :=
    ⟨fun i hi => by rw [H.2.2.2.2.2]; exact hoY.wr i hi, hoY.sep⟩
  refine WP.ite (!decide (p.sv = true)) (by simp [eval, hz]) (fun he => ?_) (fun he => ?_)
  · have hsv : p.sv = false := by cases h : p.sv <;> simp_all
    have hax₃ : u₃.gpr .rax = 0 := by
      rw [k.gpr (by decide)]
      simpa only [bit, hsv, Bool.false_eq_true, ↓reduceIte] using hflag₂
    refine WP.mono (reject_ok hw₃ hd₃ hax₃ hx₃ hox₃ ha hlen hld)
      fun t ⟨hr, hd, hX, hY, hs, hf, kt⟩ => ?_
    refine ⟨?_, hd, ?_, ?_, ?_, (RunFrame.of_scr H.2.1).trans hf, keep_trans H.2.2.2 kt⟩
    · simpa [resultStatus, hsv] using hr
    · simpa [resultStatus, hsv] using hX
    · simpa [resultStatus, hsv, i2osp_zero'] using hY
    · intro i hi
      have hH : word u₃.mem p.B (8 * i) = word s.mem p.B (8 * i) := H.2.2.1 i hi
      exact (hs i hi).trans hH
  · have hsv : p.sv = true := by cases h : p.sv <;> simp_all
    refine WP.mono (tail_ok M E R hw₃ hd₃ hm hx₃ hox₃ hoy₃ ha hlen hld)
      fun t ⟨hr, hd, hX, hY, hs, hf, kt⟩ => ?_
    have hres : resultStatus p rb = if p.fl rb then 1 else 3 := by
      simp only [resultStatus, hsv, Bool.true_eq_false, ↓reduceIte]
    refine ⟨by rwa [hres], hd, ?_, ?_, ?_, (RunFrame.of_scr H.2.1).trans hf, keep_trans H.2.2.2 kt⟩
    · rw [hres]
      by_cases hf : p.fl rb
      · rw [ite_eq_left hf, ite_eq_left (by decide)]
        simpa only [ite_eq_left hf] using hX
      · rw [ite_eq_right hf, ite_eq_right (by decide)]
        simpa only [ite_eq_right hf] using hX
    · rw [hres]
      by_cases hf : p.fl rb
      · rw [ite_eq_left hf, ite_eq_left (by decide)]
        simpa only [ite_eq_left hf] using hY
      · rw [ite_eq_right hf, ite_eq_right (by decide)]
        simpa only [ite_eq_right hf] using hY
    · intro i hi
      have hH : word u₃.mem p.B (8 * i) = word s.mem p.B (8 * i) := H.2.2.1 i hi
      exact (hs i hi).trans hH

end VG.Proof.Ffdh.X86_64.GenerateKey
