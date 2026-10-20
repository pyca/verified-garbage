module
public import VerifiedGarbage.Proof.Dsa.Accepted
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Impl.Dsa.X86.SignVerify
public import VerifiedGarbage.Proof.Dsa.X86.Checks

import VerifiedGarbage.Proof.Dsa.X86.VerifyCompute
import VerifiedGarbage.Proof.Dsa.X86.Result

/-! # Functional correctness of the post-shape verification body -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem verifyBody_ok {base : Addr} {size pLen qLen p q g y digestLen digest rv sv : Nat} {s0 : State}
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
    (hm : flagW base (Layout.field .mask) s0 = BitVec.allOnes 32) :
    let computed := (g ^ (digest % q * (sv ^ (q - 2) % q) % q) % p *
      (y ^ (rv * (sv ^ (q - 2) % q) % q) % p) % p) % q
    WP isa (SignVerify.verifyBody pLen qLen) s0 fun sf =>
      sf.gpr .eax = (if publicChecks p q g y ∧ (0 < rv ∧ rv < q) ∧ (0 < sv ∧ sv < q) ∧ computed = rv then 1 else 0) ∧
      Execution base s0 sf := by
  dsimp only
  let accepted := publicChecks p q g y ∧ (0 < rv ∧ rv < q) ∧ (0 < sv ∧ sv < q) ∧
    (g ^ (digest % q * (sv ^ (q - 2) % q) % q) % p *
      (y ^ (rv * (sv ^ (q - 2) % q) % q) % p) % p) % q = rv
  unfold SignVerify.verifyBody
  refine WP.seq (WP.mono (verifyCompute_ok M G Y R S D hd hP hg hy hr hs hD)
    fun s1 ⟨M1, F1, E1⟩ => ?_)
  have mask1 : flagW base (Layout.field .mask) s1 = mask32 accepted := by
    simpa only [hm, BitVec.allOnes_and] using F1
  refine WP.mono (result_ok M1.scr M1.saved accepted mask1) fun sf ⟨Vf, Kf, Of⟩ => ?_
  exact ⟨Vf, ⟨E1.keeps.trans (Kf.mono (by decide)), by rw [Of]; exact E1.mem⟩⟩

end VG.Proof.Dsa.X86
