module

import VerifiedGarbage.Proof.Dsa.X86.SignBody
public import VerifiedGarbage.Proof.Dsa.Accepted
public import VerifiedGarbage.Impl.Dsa.X86.Entry
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
public import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Dsa.OutputBytes

/-! # The post-shape signing body satisfies the packed-byte signing result -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem signBody_spec {base : Addr} {size pLen qLen p q g y x k digestLen n : Nat} {s0 : State} {out : BitVec 32} {key nonce digest : List Byte}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (Y : CallerBuffer s0 base size (.input .y) pLen)
    (X : CallerBuffer s0 base size (.input .x) qLen)
    (K : CallerBuffer s0 base size (.input .nonce) qLen)
    (D : CallerBuffer s0 base size (.input .digest) digestLen)
    (hd : digestLen ≤ 32)
    (hP : pointerValue base s0 (.input .digestPrefixLen) = BitVec.ofNat 32 digestLen)
    (hg : operandValue s0 base (.input .g) pLen = g)
    (hy : operandValue s0 base (.input .y) pLen = y)
    (hx : operandValue s0 base (.input .x) qLen = x)
    (hk : operandValue s0 base (.input .nonce) qLen = k)
    (hD : operandValue s0 base (.input .digest) digestLen = Spec.Dsa.decodeBE (digest.take n))
    (hm : flagW base (Layout.field .mask) s0 = BitVec.allOnes 32)
    (hp : pointerValue base s0 (.input .out) = out)
    (hf : out.toNat + 2 * qLen ≤ 2 ^ 32)
    (hw : ∀ e k, e + k ≤ 2 * qLen → InRegions s0.wr (out.setWidth 64 + BitVec.ofNat 64 e) k)
    (ha : Region.Disjoint ⟨base, size⟩ ⟨out.setWidth 64, 2 * qLen⟩)
    (shape : shapeValid p q)
    (keyLen : key.length = 3 * pLen + 2 * qLen) (nonceLen : nonce.length = qLen)
    (keyValue : Spec.Dsa.privateKeyBytes pLen qLen key = ⟨⟨p, q, g⟩, y, some x⟩)
    (nonceValue : Spec.Dsa.decodeBE nonce = k) (qBits : Spec.Dsa.bitLength q = 8 * n) :
    WP isa (SignVerify.signBody pLen qLen) s0 fun sf =>
      (sf.gpr .eax).toNat = Spec.Dsa.signStatus (Spec.Dsa.signBytes pLen qLen key nonce digest) ∧
      Spec.Rsa.bytesAt sf.mem (out.setWidth 64) (2 * qLen) =
        (Spec.Dsa.signBytes pLen qLen key nonce digest).getD (List.replicate (2 * qLen) 0) ∧
      Keeps powerClob s0 sf ∧ StackOutputFrame (s0.gpr .esp) base (out.setWidth 64) usedBytes (2 * qLen) s0.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved s0.mem (off base) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off base) regs Entry.savedRegisters := by
  have spec := signBytes_compute M.widths shape keyLen nonceLen keyValue nonceValue qBits (digest := digest)
  refine WP.mono (signBody_ok M G Y X K D hd hP hg hy hx hk hD hm hp hf hw ha)
    fun sf ⟨V, R, S, Keep, Frame, Saved⟩ => ?_
  have B := signatureBytes _ R S
  refine ⟨?_, ?_, Keep, Frame, Saved⟩
  · rw [spec]
    split
    · rename_i H
      rw [ite_eq_left H] at V
      rw [V]
      rfl
    · rename_i H
      rw [ite_eq_right H] at V
      rw [V]
      rfl
  · rw [spec]
    split
    · rename_i H
      rw [ite_eq_left H] at B
      exact B
    · rename_i H
      rw [ite_eq_right H] at B
      exact B

end VG.Proof.Dsa.X86
