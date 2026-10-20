module

public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingInput
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyBody
public import VerifiedGarbage.Proof.Dsa.X86_64.WorkspaceBridge
import VerifiedGarbage.Proof.Dsa.X86_64.SigningOperands
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Packed verification operands after workspace initialization -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem verifyingOperands {p : VerifyingInput} {original s : State}
    {hp : original.gpr .rdx = BitVec.ofNat 64 p.pLen}
    {hq : original.gpr .rcx = BitVec.ofNat 64 p.qLen} {pi qi : BitVec 64}
    (h : Ready ((p.layout original hp hq).withInverses pi qi) s)
    (hkey : Src s p.base usedBytes (original.gpr .rdi) p.key)
    (hsig : Src s p.base usedBytes (original.gpr .r8) p.signature)
    (hdigest : Src s p.base usedBytes p.digestPointer p.digest) :
    VerificationOperands ((p.layout original hp hq).withInverses pi qi) p.values p.components.q s := by
  let L := (p.layout original hp hq).withInverses pi qi
  have hqlen : p.components.q.length = p.qLen := p.components.qLength
  have hglen : p.components.g.length = p.pLen := p.components.gLength
  have hylen : p.components.y.length = p.pLen := p.components.yLength
  have hrlen : (p.signature.take p.qLen).length = p.qLen := by
    simp only [List.length_take, p.signatureLength]; omega
  have hslen : (p.signature.drop p.qLen).length = p.qLen := by
    simp only [List.length_drop, p.signatureLength]; omega
  have qptr : L.fields .q = original.gpr .rdi + BitVec.ofNat 64 p.pLen := by
    change original.gpr .rdi + original.gpr .rdx = _
    rw [hp]
  have gptr : L.fields .g = original.gpr .rdi + BitVec.ofNat 64 (p.pLen + p.qLen) := by
    change original.gpr .rdi + original.gpr .rdx + original.gpr .rcx = _
    rw [hp, hq, Offset.add_add]
  have yptr : L.fields .y = original.gpr .rdi + BitVec.ofNat 64 (2 * p.pLen + p.qLen) := by
    change original.gpr .rdi + original.gpr .rdx + original.gpr .rcx + original.gpr .rdx = _
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
    h.inputOperand .q .qLen (by decide) (by decide) hqsrc (by rw [hqlen]; exact hqfield),
    h.inputOperand .signature .qLen (by decide) (by decide) (source_take hsig)
      (by change L.fields .qLen = BitVec.ofNat 64 (p.signature.take p.qLen).length; rw [hrlen]; exact hqfield),
    ?_,
    h.inputOperand .digest .digestPrefixLen (by decide) (by decide) (source_take hdigest) ?_,
    hglen, hylen, hqlen, hrlen, hslen, ?_, rfl⟩
  · refine ⟨(h.fields .qLen (by decide)).trans ?_, ?_⟩
    · change L.fields .qLen = BitVec.ofNat 64 (p.signature.drop p.qLen).length
      rw [hslen]; exact hqfield
    · simp only [Core.signatureS, pointerValue, h.fields .signature (by decide), h.fields .qLen (by decide)]
      change Src s p.base usedBytes (original.gpr .r8 + original.gpr .rcx) (p.signature.drop p.qLen)
      rw [hq]
      have hh := source_slice (offset := p.qLen) (len := p.qLen) hsig (by rw [p.signatureLength]; omega)
      rw [List.take_of_length_le (Nat.le_of_eq hslen)] at hh
      exact hh
  · change BitVec.ofNat 64 p.prefixLength = BitVec.ofNat 64 (p.digest.take _).length
    rw [List.length_take, Nat.min_comm]
  · change (p.digest.take _).length < 2 ^ 64
    simp only [List.length_take]
    exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) p.digestBound

end VG.Proof.Dsa.X86_64
