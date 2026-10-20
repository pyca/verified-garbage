module

public import VerifiedGarbage.Proof.Dsa.AArch64.SigningInput
public import VerifiedGarbage.Proof.Dsa.AArch64.InitializedLayout
public import VerifiedGarbage.Proof.Dsa.AArch64.SignBody
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Loading packed signing inputs into the verified arithmetic interface -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem Ready.inputOperand {L : ExecutionLayout} {s : State} (h : Ready L s)
    (f len : Field) (hf : f ≠ .mask) (hl : len ≠ .mask) {bs : List Byte}
    (hsrc : Src s L.base usedBytes (L.fields f) bs)
    (hlen : L.fields len = BitVec.ofNat 64 bs.length) :
    OperandBytes s L.base usedBytes ⟨.input f, len⟩ bs := by
  refine ⟨(h.fields len hl).trans hlen, ?_⟩
  simpa only [pointerValue, h.fields f hf] using hsrc

theorem signingOperands {p : SigningInput} {original s : State}
    {hp : original.gpr .x4 = BitVec.ofNat 64 p.pLen} {pi qi : BitVec 64}
    (h : Ready ((p.layout original hp).withInverses pi qi) s)
    (hkey : Src s p.base usedBytes (original.gpr .x2) p.key)
    (hnonce : Src s p.base usedBytes (original.gpr .x5) p.nonce)
    (hdigest : Src s p.base usedBytes p.digestPointer p.digest) :
    SigningOperands ((p.layout original hp).withInverses pi qi) p.values p.components.y p.components.q s := by
  let L := (p.layout original hp).withInverses pi qi
  have hqlen : p.components.q.length = p.qLen := p.components.qLength
  have hglen : p.components.g.length = p.pLen := p.components.gLength
  have hylen : p.components.y.length = p.pLen := p.components.yLength
  have hxlen : p.components.x.length = p.qLen := component_length (by rw [p.keyLength]; omega)
  have qptr : L.fields .q = original.gpr .x2 + BitVec.ofNat 64 p.pLen := by
    change original.gpr .x2 + original.gpr .x4 = _
    rw [hp]
  have gptr : L.fields .g = original.gpr .x2 + BitVec.ofNat 64 (p.pLen + p.qLen) := by
    change original.gpr .x2 + original.gpr .x4 + BitVec.ofNat 64 p.qLen = _
    rw [hp, Offset.add_add]
  have yptr : L.fields .y = original.gpr .x2 + BitVec.ofNat 64 (2 * p.pLen + p.qLen) := by
    change original.gpr .x2 + original.gpr .x4 + BitVec.ofNat 64 p.qLen + original.gpr .x4 = _
    rw [hp, Offset.add_add, Offset.add_add, show p.pLen + (p.qLen + p.pLen) = 2 * p.pLen + p.qLen by omega]
  have xptr : L.fields .x = original.gpr .x2 + BitVec.ofNat 64 (3 * p.pLen + p.qLen) := by
    change original.gpr .x2 + original.gpr .x4 + BitVec.ofNat 64 p.qLen + original.gpr .x4 + original.gpr .x4 = _
    rw [hp, Offset.add_add, Offset.add_add, Offset.add_add,
      show p.pLen + (p.qLen + (p.pLen + p.pLen)) = 3 * p.pLen + p.qLen by omega]
  have hqsrc : Src s p.base usedBytes (L.fields .q) p.components.q := by
    rw [qptr]; exact source_slice hkey (by rw [p.keyLength]; omega)
  have hgsrc : Src s p.base usedBytes (L.fields .g) p.components.g := by
    rw [gptr]; exact source_slice hkey (by rw [p.keyLength]; omega)
  have hysrc : Src s p.base usedBytes (L.fields .y) p.components.y := by
    rw [yptr]; exact source_slice hkey (by rw [p.keyLength]; omega)
  have hxsrc : Src s p.base usedBytes (L.fields .x) p.components.x := by
    rw [xptr]; exact source_slice hkey (by rw [p.keyLength]; omega)
  have hpfield : L.fields .pLen = BitVec.ofNat 64 p.pLen := hp
  have hqfield : L.fields .qLen = BitVec.ofNat 64 p.qLen := rfl
  refine ⟨h.inputOperand .g .pLen (by decide) (by decide) hgsrc (by change L.fields .pLen = BitVec.ofNat 64 p.components.g.length; rw [hglen]; exact hpfield),
    h.inputOperand .y .pLen (by decide) (by decide) hysrc (by rw [hylen]; exact hpfield),
    h.inputOperand .q .qLen (by decide) (by decide) hqsrc (by rw [hqlen]; exact hqfield),
    h.inputOperand .x .qLen (by decide) (by decide) hxsrc (by change L.fields .qLen = BitVec.ofNat 64 p.components.x.length; rw [hxlen]; exact hqfield),
    h.inputOperand .nonce .qLen (by decide) (by decide) hnonce (by change L.fields .qLen = BitVec.ofNat 64 p.nonce.length; rw [p.nonceLength]; exact hqfield),
    h.inputOperand .digest .digestPrefixLen (by decide) (by decide) (source_take hdigest) ?_,
    hglen, hylen, hqlen, hxlen, p.nonceLength, ?_, rfl⟩
  · change BitVec.ofNat 64 p.prefixLength = BitVec.ofNat 64 (p.digest.take _).length
    rw [List.length_take, Nat.min_comm]
  · change (p.digest.take _).length < 2 ^ 64
    simp only [List.length_take]
    exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) p.digestBound

end VG.Proof.Dsa.AArch64
