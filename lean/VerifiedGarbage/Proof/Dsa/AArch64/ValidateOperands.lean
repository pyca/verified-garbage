module

public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingInput
public import VerifiedGarbage.Proof.Dsa.AArch64.InitializedLayout
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyBody
import VerifiedGarbage.Proof.Dsa.AArch64.SigningOperands
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Packed verification operands after workspace initialization -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem validatingOperands {p : VerifyingInput} {original s : State}
    {hp : original.gpr .x2 = BitVec.ofNat 64 p.pLen}
    {hq : original.gpr .x3 = BitVec.ofNat 64 p.qLen} {pi qi : BitVec 64}
    (h : Ready ((p.layout original hp hq).withInverses pi qi) s)
    (hkey : Src s p.base usedBytes (original.gpr .x0) p.key)
 :
    OperandBytes s p.base usedBytes Core.generator p.components.g ∧
    OperandBytes s p.base usedBytes Core.publicValue p.components.y ∧
    OperandBytes s p.base usedBytes ⟨.input .q, .qLen⟩ p.components.q := by
  let L := (p.layout original hp hq).withInverses pi qi
  have hqlen : p.components.q.length = p.qLen := p.components.qLength
  have hglen : p.components.g.length = p.pLen := p.components.gLength
  have hylen : p.components.y.length = p.pLen := p.components.yLength
  have qptr : L.fields .q = original.gpr .x0 + BitVec.ofNat 64 p.pLen := by
    change original.gpr .x0 + original.gpr .x2 = _
    rw [hp]
  have gptr : L.fields .g = original.gpr .x0 + BitVec.ofNat 64 (p.pLen + p.qLen) := by
    change original.gpr .x0 + original.gpr .x2 + original.gpr .x3 = _
    rw [hp, hq, Offset.add_add]
  have yptr : L.fields .y = original.gpr .x0 + BitVec.ofNat 64 (2 * p.pLen + p.qLen) := by
    change original.gpr .x0 + original.gpr .x2 + original.gpr .x3 + original.gpr .x2 = _
    rw [hp, hq, Offset.add_add, Offset.add_add, show p.pLen + (p.qLen + p.pLen) = 2 * p.pLen + p.qLen by omega]
  have hqsrc : Src s p.base usedBytes (L.fields .q) p.components.q := by
    rw [qptr]; exact source_slice hkey (by rw [p.keyLength]; omega)
  have hgsrc : Src s p.base usedBytes (L.fields .g) p.components.g := by
    rw [gptr]; exact source_slice hkey (by rw [p.keyLength]; omega)
  have hysrc : Src s p.base usedBytes (L.fields .y) p.components.y := by
    rw [yptr]; exact source_slice hkey (by rw [p.keyLength]; omega)
  have hpfield : L.fields .pLen = BitVec.ofNat 64 p.pLen := hp
  have hqfield : L.fields .qLen = BitVec.ofNat 64 p.qLen  := hq
  refine ⟨h.inputOperand .g .pLen (by decide) (by decide) hgsrc (by change L.fields .pLen = BitVec.ofNat 64 p.components.g.length; rw [hglen]; exact hpfield),
    h.inputOperand .y .pLen (by decide) (by decide) hysrc (by change L.fields .pLen = BitVec.ofNat 64 p.components.y.length; rw [hylen]; exact hpfield),
    h.inputOperand .q .qLen (by decide) (by decide) hqsrc (by rw [hqlen]; exact hqfield)⟩

end VG.Proof.Dsa.AArch64
