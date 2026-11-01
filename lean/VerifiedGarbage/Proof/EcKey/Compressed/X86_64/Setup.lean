module

public import VerifiedGarbage.Impl.EcKey.Compressed.X86_64
import VerifiedGarbage.Proof.Ecdh.X86_64.Check
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.X25519.X86_64.Step
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract
public import VerifiedGarbage.Proof.Weierstrass.MulContract

/-! # Compressed-point conversion: reuse the existing setup and checks -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

/-- The arguments after pointing signature setup at the public coordinate. -/
theorem args_ok (s : State) :
    WP isa (.block Impl.EcKey.Compressed.X86_64.args) s fun s' =>
      s'.gpr .r8 = s.gpr .rdx ∧ s'.gpr .r9 = s.gpr .rsi ∧
      s'.gpr .rcx = s.gpr .rsi + 1 ∧ s'.gpr .rsi = s.gpr .rsi + 1 ∧
      s'.gpr .rdx = s.gpr .rsi + 1 ∧ Keeps [.r8, .r9, .rcx, .rsi, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [Impl.EcKey.Compressed.X86_64.args, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, Option.map_some, Option.bind_some, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, rfl, rfl, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1,
    hr.2.2.2.1, hr.2.2.2.2, ite_false]

end VG.Proof.EcKey.Compressed.X86_64
