module

import VerifiedGarbage.Proof.Dsa.X86.Comb.CheckInvokeTiming
import VerifiedGarbage.Proof.Dsa.X86.Comb.DeriveInvokeTiming
import VerifiedGarbage.Proof.Dsa.X86.Comb.GenerationStack
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Verified
public import Init.Prelude
public import VerifiedGarbage.Impl.Dsa.X86.CombKey
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.TCB.X86.Target

/-! Full correctness, constant time, and satisfiability for retained-table key generation. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb

theorem key_verified : Verified target generateKey (Spec.Dsa.generateKeyContract abi 232) :=
  KeyRandom.verifiedWith checkInvoke deriveInvoke keyInvariant_stable
    check_invoke_noSp derive_invoke_noSp checkInvoke_ct deriveInvoke_ct

end VG.Proof.Dsa.X86.Comb
