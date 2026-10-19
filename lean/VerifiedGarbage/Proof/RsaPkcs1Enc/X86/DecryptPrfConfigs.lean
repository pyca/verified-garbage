module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptPrfInvariant

/-! # Length-output and alternative-message IRPRF loop parameters -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

def clConfig : PrfConfig where
  label := lengthLabel
  lenCode := clLen
  length := 256
  dst := sCL
  blocks := 8
  extra := sDH
  extraLength := 32
  blockPositive := by decide
  blockBound := by decide
  labelBound := by decide
  dstLow := by decide
  dstHigh := by decide
  extraLow := by decide
  extraHigh := by decide
  separate := Or.inl (by decide)

def amConfig (g : Geometry) (h : g.Valid) : PrfConfig where
  label := messageLabel
  lenCode := amLen
  length := g.length
  dst := sAM
  blocks := (g.length + 31) / 32
  extra := sCL
  extraLength := 256
  blockPositive := by have := h.minLength; omega
  blockBound := by have := h.maxLength; omega
  labelBound := by decide
  dstLow := by decide
  dstHigh := by have := h.maxLength; unfold sAM sHash; omega
  extraLow := by decide
  extraHigh := by decide
  separate := Or.inl (by decide)

end VG.Proof.RsaPkcs1Enc.X86.Dec
