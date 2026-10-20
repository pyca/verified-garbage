module

import VerifiedGarbage.Proof.Dsa.X86.VerifyBody
public import VerifiedGarbage.Proof.Dsa.Accepted
public import VerifiedGarbage.Impl.Dsa.X86.SignVerify
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.Moduli

/-! # The post-shape verifier returns the packed-byte specification result -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem verifyBody_spec {base : Addr} {size pLen qLen p q g y digestLen rv sv n : Nat} {s0 : State} {key signature digest : List Byte}
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
    (hD : operandValue s0 base (.input .digest) digestLen = Spec.Dsa.decodeBE (digest.take n))
    (hm : flagW base (Layout.field .mask) s0 = BitVec.allOnes 32)
    (shape : shapeValid p q)
    (keyLen : key.length = 3 * pLen + qLen) (sigLen : signature.length = 2 * qLen)
    (keyValue : Spec.Dsa.publicKeyBytes pLen qLen key = ⟨⟨p, q, g⟩, y, none⟩)
    (rValue : Spec.Dsa.decodeBE (signature.take qLen) = rv)
    (sValue : Spec.Dsa.decodeBE (signature.drop qLen) = sv)
    (qBits : Spec.Dsa.bitLength q = 8 * n) :
    WP isa (SignVerify.verifyBody pLen qLen) s0 fun sf =>
      (sf.gpr .eax).toNat = (if Spec.Dsa.verifyBytes pLen qLen key signature digest then 1 else 0) ∧
      Execution base s0 sf := by
  have spec := verifyBytes_compute M.widths shape keyLen sigLen keyValue rValue sValue qBits (digest := digest)
  refine WP.mono (verifyBody_ok M G Y R S D hd hP hg hy hr hs hD hm) fun sf ⟨V, E⟩ => ?_
  refine ⟨?_, E⟩
  rw [spec, V]
  simp only [decide_eq_true_eq]
  split <;> rfl

end VG.Proof.Dsa.X86
