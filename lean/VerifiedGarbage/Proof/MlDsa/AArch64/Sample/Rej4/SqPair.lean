module
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqPhase

import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqFrame
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha3.AArch64.Sums

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3 (iterF iterF_succ)

theorem phasePair_ok (sha3 : Bool) {σ s : State} (hp : Pre σ) {n p : Nat} (hn : n < 6) (hpn : p < 2)
    (h : Phase σ n p s) :
    WP isa (Impl.MlDsa.AArch64.Sample.Rej4.pairStep sha3 (pReg p) (bReg (2*p)) (bReg (2*p+1))) s
      (Phase σ n (p+1)) := by
  have hpair := h.states p hpn
  simp only [Nat.lt_irrefl,ite_false,Nat.add_zero] at hpair
  refine WP.mono (pairBlock_ok sha3 hp h.env hpn hn (phase_state_ptr h hpn)
    (h.ptrs (2*p) (by omega_using [hpn])) (h.ptrs (2*p+1) (by omega_using [hpn])) hpair)
    fun t ⟨he,ht,hpt,hat,hbt,hft⟩ => ?_
  rw [← iterF_succ,← iterF_succ] at hpt
  rw [← iterF_succ] at hat hbt
  refine ⟨he,(ht.gpr .x22 (by decide)).trans h.x22,
    (ht.gpr .x23 (by decide)).trans h.x23,
    fun k hk => ?_,by rw [ht.gpr .x28 (by decide)]; exact h.count,
    fun i hi => ?_,fun k hk j hj => ?_⟩
  · exact (ht.gpr (bReg k) (b_regs k hk)).trans (h.ptrs k hk)
  · by_cases heq : i = p
    · subst i
      simpa only [Nat.lt_succ_self,ite_true] using hpt
    · apply pair_frame hpn hn hi heq hft
      have hs := h.states i hi
      by_cases hc : i < p <;> simpa (disch := omega) only [ite_eq_left,ite_eq_right] using hs
  · have hjnext : j < 168*(n+1) := by split at hj <;> omega_using [hj]
    have hj1008 : j < 1008 := by omega_using [hn, hjnext]
    by_cases hjold : j < 168*n
    · rw [old_byte hpn hn hk hj1008 (.inl hjold) hft]
      exact h.out k hk j (by split <;> omega_arith)
    · by_cases heq : k = 2*p
      · subst k
        rw [buf_byte_address σ (2*p) n j (by omega_using [hjold]),hat.byte (j := j-168*n) (by omega_using [hjnext]),
          ← F_block σ (2*p) (n := n) (j := j-168*n) hn (by omega_using [hjnext]),show 168*n+(j-168*n) = j by omega_using [hjold]]
      · by_cases heq' : k = 2*p+1
        · subst k
          rw [buf_byte_address σ (2*p+1) n j (by omega_using [hjold]),hbt.byte (j := j-168*n) (by omega_using [hjnext]),
            ← F_block σ (2*p+1) (n := n) (j := j-168*n) hn (by omega_using [hjnext]),show 168*n+(j-168*n) = j by omega_using [hjold]]
        · rw [old_byte hpn hn hk hj1008 (.inr ⟨heq,heq'⟩) hft]
          apply h.out k hk j
          by_cases hc : k < 2*p <;>
            simpa (disch := omega) only [ite_eq_left,ite_eq_right] using hj
end VG.Proof.MlDsa.AArch64.Sample.Rej4
