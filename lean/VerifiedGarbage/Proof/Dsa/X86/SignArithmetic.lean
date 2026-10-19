module
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.Moduli

import VerifiedGarbage.Proof.Dsa.X86.SignFinish
import VerifiedGarbage.Proof.Dsa.X86.SignStart

/-! # Complete arithmetic schedule of an x86 DSA signing attempt -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem signArithmetic_ok {base : Addr} {size pLen qLen p q g k x digestLen digest : Nat} {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (K : CallerBuffer s0 base size (.input .nonce) qLen)
    (X : CallerBuffer s0 base size (.input .x) qLen)
    (D : CallerBuffer s0 base size (.input .digest) digestLen)
    (hd : digestLen ≤ 32)
    (hP : pointerValue base s0 (.input .digestPrefixLen) = BitVec.ofNat 32 digestLen)
    (hg : operandValue s0 base (.input .g) pLen = g)
    (hk : operandValue s0 base (.input .nonce) qLen = k)
    (hx : operandValue s0 base (.input .x) qLen = x)
    (hD : operandValue s0 base (.input .digest) digestLen = digest)
    (hq2 : operandValue s0 base (.local qMinusTwo) qLen = q - 2) :
    WP isa (Core.sign pLen qLen) s0 fun sf =>
      Moduli base size pLen qLen p q sf ∧
      operandValue sf base (.local r) qLen = g ^ k % p % q ∧
      operandValue sf base (.local VG.Impl.Dsa.Layout.s) qLen =
        k ^ (q - 2) % q * ((digest % q + x * (g ^ k % p % q) % q) % q) % q ∧
      Execution base s0 sf ∧
      flagW base (Layout.field .mask) sf = flagW base (Layout.field .mask) s0 := by
  unfold Core.sign
  refine WP.seq (WP.mono (signStart_ok M G K hg hk hq2) fun s1 ⟨M1, R1, I1, E1, F1⟩ => ?_)
  refine WP.mono (signFinish_ok M1 (E1.buffer X (by decide)) (E1.buffer D (by decide)) hd (E1.prefixLen.trans hP)
    ((E1.value X (by decide) M.extent).trans hx)
    ((E1.value D (by decide) M.extent).trans hD) R1 I1) ?_
  intro sf H
  exact ⟨H.1, H.2.1, H.2.2.1, E1.trans H.2.2.2.1, H.2.2.2.2.trans F1⟩

end VG.Proof.Dsa.X86
