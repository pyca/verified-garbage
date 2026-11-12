module

public import VerifiedGarbage.Proof.Rsa.RISCV64.RdCorrect
public import VerifiedGarbage.Proof.Rsa.RISCV64.RdCT

/-!
# `vg_rsa_recover_primes_det` on RISC-V: verified

`rd_verified`: correct (`rd_correct`, `RdCorrect.lean`), constant time
(`code_ct`, `RdCT.lean`), and the contract on the registers and the stack
implied by the shared contract (`rd_implies`, `RdFront.lean`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.RecDet

open VG VG.RISCV64

open VG.Proof.Rsa.RISCV64.Keys (wp_seqs_cons wp_seqs_append)
open VG.Impl.Rsa.RISCV64.Keys (seqs)
open VG.Impl.Rsa.RISCV64.RecoverDet (setup loads prod det deMinus twos gcd divA divB minus4n sqrt factors)

/-- For the constant-time proof: a valid modulus's run up to the stores ends
with the body's registers and the working space as on entry (`S7`). -/
theorem pre_ok [InvLaw] : ∀ d s, S5 d s → s.gpr .s0 = 0 → WP isa (seqs [setup, loads, prod, det]) s (S7 d) := by
  rintro d s ⟨s0, c0, c, x0⟩ z
  have h := preC_of c0.1
  have three := (nv_facts (x0.mp z)).2
  have hmv := x0.mp z
  have w : WP isa (seqs [setup, loads, prod, det]) s fun t => ∃ q rem, Det s0 q rem t := by
    rw [wp_seqs_cons (List.cons_ne_nil _ _)]
    refine WP.mono (setup_ok h c) fun t1 ⟨c1, w1, z1⟩ => ?_
    rw [wp_seqs_cons (List.cons_ne_nil _ _)]
    refine WP.mono (loads_ok h c1 w1 z1) fun t2 l2 => ?_
    rw [wp_seqs_cons (List.cons_ne_nil _ _)]
    refine WP.mono (prod_ok h l2) fun t3 p3 => ?_
    show WP isa det t3 _
    unfold det
    rw [wp_seqs_cons (List.cons_ne_nil _ _)]
    refine WP.mono (deMinus_ok h p3) fun t4 d4 => ?_
    rw [show [twos, gcd, divA, divB, minus4n, sqrt, factors] =
      [twos, gcd, divA] ++ [divB, minus4n, sqrt, factors] from rfl, wp_seqs_append (by simp) (by simp)]
    exact WP.mono (stA_ok h three (nv_top hmv (Nat.le_trans (by decide : 1 ≤ 64) h.k1)) d4) fun t5 s5 =>
      stB_ok h three s5
  exact WP.mono w fun t ⟨_, _, dt⟩ => ⟨s0, c0, dt.cb, dt.ws⟩

/-- `vg_rsa_recover_primes_det`. -/
theorem rd_verified [InvLaw] :
    Verified RISCV64.target VG.Impl.Rsa.RISCV64.RecoverDet.code (Spec.Rsa.recoverPrimesDetContract RISCV64.abi) :=
  Verified.of_correct rd_correct (code_ct pre_ok) rd_implies

end VG.Proof.Rsa.RISCV64.RecDet
