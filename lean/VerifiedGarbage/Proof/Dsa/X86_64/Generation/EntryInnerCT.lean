module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Entry
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hashes
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeTest

import VerifiedGarbage.Proof.Framework.X86_64.FrameAlloc
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryState
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntrySetupCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryTape
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.TCB.X86_64.Target
import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterCTState
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OutputPlan
/-! # The inner ABI frame preserves the proved generator trace and stack pointer -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MillerRabin.X86_64 VG.Impl.Dsa.X86_64.Generation

variable {checkName : String}

theorem generation_alloc {s : State} {bytes : Nat}
    (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 8 = 0) (hl : bytes ≤ (s.gpr .rsp).toNat) :
    isa.push (.alloc bytes) s = some (allocState bytes s) := by
  simp only [isa, push, allocState]
  exact ite_eq_left ⟨hb.1, hb.2.1, hb.2.2, hl⟩

theorem generation_free_rsp {s u v : State} {bytes : Nat}
    (h : isa.pop (.free bytes) (allocState bytes s) u = some v) : v.gpr .rsp = s.gpr .rsp := by
  simp only [isa, pop] at h
  split at h
  · rename_i hc
    obtain rfl := Option.some.inj h
    exact freeState_rsp hc.2.2.2.1
  · cases h

end VG.Proof.Dsa.X86_64.Generation
