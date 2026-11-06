module

public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Mont.X86.Rt.Step
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.ArgFar
public import VerifiedGarbage.Proof.Mont.X86.Row
public import VerifiedGarbage.Proof.Mont.X86.Loop
public import VerifiedGarbage.Proof.Mont.X86.OutsZ

/-! # The subtraction of the modulus, in the run-time width multiplication

`subM`'s loop: `[tmp] = [src] - [mo]`, `N` words, the borrow as a mask in
`ecx`, with `ebp`, `esi` and `ebx` at the three numbers and `edi` counting
`4 N` bytes down, as `chainSubW_ok` at fixed offsets.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Rt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt VG.Proof.Mont VG.Proof.Mont.X86

theorem restore_eq : Rt.restore = VG.Impl.Mont.X86.Dynamic.restore := rfl

/-- What the subtraction's loop changes. -/
abbrev clob7 : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi]

end VG.Proof.Mont.X86.Rt
