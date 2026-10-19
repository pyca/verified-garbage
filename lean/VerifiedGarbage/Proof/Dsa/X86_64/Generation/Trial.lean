module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
public import VerifiedGarbage.Proof.Dsa.Generation.Trial

/-! # DSA uses RSA's complete native small-prime table and trial loop -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem trial_ok {s : State} {B : Addr} {Z w c bits : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hTZ : slot w aTab + 2048 ≤ Z)
    (hw : 1 ≤ w) (hw64 : w ≤ 64) (hc : wv s.mem B (slot w aN) w = c)
    (hcgt : 8161 < c) (hpolicy : 1024 < bits ↔ 16 < w) :
    WP isa (seqs trial) s fun t =>
      t.zf = some (!Spec.RsaKeyGen.obviouslyComposite bits c) ∧ Good t B Z w mi ∧
      Frm B [(slot w aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r12, .r13, .r14, .r15] s t := by
  refine WP.mono (VG.Proof.RsaKeyGen.X86_64.trial_ok hg hZ hTZ hw hw64) fun t ⟨hz, ht⟩ => ?_
  rw [hc, VG.Proof.Dsa.Generation.trialAny_dsa hcgt hpolicy] at hz
  exact ⟨hz, ht⟩

end VG.Proof.Dsa.X86_64.Generation
