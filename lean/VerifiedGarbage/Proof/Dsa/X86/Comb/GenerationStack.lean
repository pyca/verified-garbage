module

public import VerifiedGarbage.Impl.Dsa.X86.CombKey
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-! Structural stack bounds for the two internal generation bodies. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb

theorem check_noSp : NoSp checkParameters := NoSp.of_all (by decide +kernel)
theorem derive_noSp : NoSp deriveKey := NoSp.of_all (by decide +kernel)
theorem check_invoke_noSp : NoSp (invoke checkParameters) := NoSp.of_all (by decide +kernel)
theorem derive_invoke_noSp : NoSp (invoke deriveKey) := NoSp.of_all (by decide +kernel)

theorem check_depth : stackUse checkParameters≤20 := by decide +kernel
theorem derive_depth : stackUse deriveKey≤20 := by decide +kernel

end VG.Proof.Dsa.X86.Comb
