module

import VerifiedGarbage.Proof.Dsa.X86.Domain
import VerifiedGarbage.Proof.Dsa.X86.Subgroup
public import VerifiedGarbage.Proof.Dsa.Accepted
public import VerifiedGarbage.Impl.Dsa.X86.Validate
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.Moduli

/-! # Complete algebraic checks of public DSA components -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem publicKey_ok {base : Addr} {size pLen qLen p q g y : Nat} {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (Y : CallerBuffer s0 base size (.input .y) pLen)
    (hg : operandValue s0 base (.input .g) pLen = g)
    (hy : operandValue s0 base (.input .y) pLen = y) :
    WP isa (Validate.publicKey pLen qLen) s0 fun sf =>
      Moduli base size pLen qLen p q sf ∧
      flagW base (Layout.field .mask) sf = flagW base (Layout.field .mask) s0 &&& mask32 (publicChecks p q g y) ∧
      operandValue sf base (.local qMinusTwo) qLen = q - 2 ∧ Execution base s0 sf := by
  unfold Validate.publicKey
  refine WP.seq (WP.mono (domain_ok M G Y hg hy) fun s1 ⟨M1, F1, Q1, E1⟩ => ?_)
  refine WP.mono (subgroup_ok M1 (E1.buffer G (by decide)) (E1.buffer Y (by decide))
    ((E1.value G (by decide) M.extent).trans hg)
    ((E1.value Y (by decide) M.extent).trans hy)) fun sf ⟨Mf, Ff, Qf, Ef⟩ => ?_
  refine ⟨Mf, ?_, Qf.trans Q1, E1.trans Ef⟩
  rw [Ff, F1]
  simp only [BitVec.and_assoc, mask32_and, publicChecks, and_assoc]

end VG.Proof.Dsa.X86
