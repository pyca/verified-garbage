module

public import VerifiedGarbage.Impl.Dsa.X86_64.RandomSign
import VerifiedGarbage.TCB.Axioms

/-! Structural checks for the unregistered randomized-signing programs.
These do not assert functional correctness or constant-time behavior. -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64
open Impl.Dsa.X86_64

theorem random_prepare_spSafe : Random.prepare.all (fun i => !isa.writesSp i) = true := by
  decide +kernel

theorem random_sample_spSafe : Random.sample.all (fun i => !isa.writesSp i) = true := by
  decide +kernel

theorem random_prepare_baseline : Random.prepare.requires isa.requires = [] := by
  decide +kernel

theorem random_sample_baseline : Random.sample.requires isa.requires = [] := by
  decide +kernel

/-- The wrapper inherits stack-pointer safety from whichever signer it calls. -/
theorem randomSign_spSafe (name : String) (signer : Prog isa)
    (h : signer.all (fun i => !isa.writesSp i) = true) :
    (RandomSign.code name signer).all (fun i => !isa.writesSp i) = true := by
  simp only [RandomSign.code, RandomSign.body, RandomSign.attempt, RandomSign.finish,
    RandomSign.zeroOut, Code.all, h]
  decide +kernel

end VG.Proof.Dsa.X86_64
