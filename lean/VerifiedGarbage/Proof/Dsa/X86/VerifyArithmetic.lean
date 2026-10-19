module
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.Moduli

import VerifiedGarbage.Proof.Dsa.X86.VerifyPowers
import VerifiedGarbage.Proof.Dsa.X86.VerifyScalars

/-! # Complete arithmetic schedule of x86 DSA verification -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem verifyArithmetic_ok {base : Addr} {size pLen qLen p q g y digestLen digest rv sv : Nat} {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (Y : CallerBuffer s0 base size (.input .y) pLen)
    (R : CallerBuffer s0 base size (.input .signature) qLen)
    (S : CallerBuffer s0 base size .signatureS qLen)
    (D : CallerBuffer s0 base size (.input .digest) digestLen)
    (hd : digestLen ≤ 32)
    (hP : pointerValue base s0 (.input .digestPrefixLen) = BitVec.ofNat 32 digestLen)
    (hg : operandValue s0 base (.input .g) pLen = g)
    (hy : operandValue s0 base (.input .y) pLen = y)
    (hr : operandValue s0 base (.input .signature) qLen = rv)
    (hs : operandValue s0 base .signatureS qLen = sv)
    (hD : operandValue s0 base (.input .digest) digestLen = digest)
    (hq2 : operandValue s0 base (.local qMinusTwo) qLen = q - 2) :
    WP isa (Core.verify pLen qLen) s0 fun sf =>
      Moduli base size pLen qLen p q sf ∧
      operandValue sf base (.local u) qLen =
        (g ^ (digest % q * (sv ^ (q - 2) % q) % q) % p *
          (y ^ (rv * (sv ^ (q - 2) % q) % q) % p) % p) % q ∧
      Execution base s0 sf ∧
      flagW base (Layout.field .mask) sf = flagW base (Layout.field .mask) s0 := by
  unfold Core.verify
  refine WP.seq (WP.mono (verifyScalars_ok M R S D hd hP hr hs hD hq2) fun s1 ⟨M1, U1, V1, E1, F1⟩ => ?_)
  refine WP.mono (verifyPowers_ok M1 (E1.buffer G (by decide)) (E1.buffer Y (by decide))
    ((E1.value G (by decide) M.extent).trans hg)
    ((E1.value Y (by decide) M.extent).trans hy) U1 V1) ?_
  intro sf H
  exact ⟨H.1, H.2.1, E1.trans H.2.2.1, H.2.2.2.trans F1⟩

end VG.Proof.Dsa.X86
