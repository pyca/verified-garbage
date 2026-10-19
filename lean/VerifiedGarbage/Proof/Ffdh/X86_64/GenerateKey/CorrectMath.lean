module
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Core

import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Sample
import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH on x86-64: the attempt's outputs satisfy the shared key-generation specification -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Spec.Ffdh VG.Proof.Bignum

theorem resultStatus_lt (p : GkP) (rb : List Byte) : resultStatus p rb < 2 ^ 32 := by
  unfold resultStatus
  split
  · decide
  · split <;> decide

theorem attempt_spec {p : GkP} {rb : List Byte} {s u t : State} (hb : Base p rb u)
    (hm : p.mv = true) (ha : parametersValid p.params = true) (h : AttemptPost p rb s t) :
    ((t.gpr .rax).setWidth 32).toNat = keyStatus p.params (p.scalar rb) ∧
      if keyStatus p.params (p.scalar rb) = 1 then
        Spec.Rsa.bytesAt t.mem p.xp p.k = Spec.Rsa.i2osp (p.scalar rb) p.k ∧
          Spec.Rsa.bytesAt t.mem p.yp p.k = Spec.Rsa.i2osp (Spec.Rsa.powMod p.params.g (p.scalar rb) p.params.p) p.k
      else Spec.Rsa.bytesAt t.mem p.xp p.k = List.replicate p.k 0 ∧
        Spec.Rsa.bytesAt t.mem p.yp p.k = List.replicate p.k 0 := by
  obtain ⟨hr, _, hx, hy, _⟩ := h
  have hst := hb.resultStatus_eq hm ha
  have hlt := resultStatus_lt p rb
  refine ⟨?_, ?_⟩
  · rw [hr]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (hlt.trans (by decide)), Nat.mod_eq_of_lt hlt]
    exact hst
  · rw [← hst]
    by_cases hs : resultStatus p rb = 1
    · simp only [ite_eq_left hs] at hx hy ⊢
      refine ⟨hx.trans (hb.cut_i2osp hm), ?_⟩
      rw [hb.power_value hm] at hy
      rw [VG.Proof.Bignum.powMod_eq]
      exact hy
    · simp only [ite_eq_right hs] at hx hy ⊢
      exact ⟨hx, by rw [hy, i2osp_zero']⟩

end VG.Proof.Ffdh.X86_64.GenerateKey
