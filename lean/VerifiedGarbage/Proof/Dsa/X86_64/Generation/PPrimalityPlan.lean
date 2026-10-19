module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstructPlan
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeCall
public import VerifiedGarbage.Proof.Dsa.Generation.PDomain
import VerifiedGarbage.Proof.Framework.Omega

/-! # Instantiate native primality for each full-width p candidate -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

structure PPrimalityPlan where
  construct : PConstructPlan
  rand : List Byte
  rp : Addr
  size : construct.Z = arithmeticBytes
  tapePtr : construct.hash.W 13 = rp
  tapeLength : construct.hash.W 15 = BitVec.ofNat 64 rand.length
  randMax : rand.length < 2 ^ 64
  stackSize : 128 ≤ construct.hash.F.toNat
  stackSeparate : Region.Disjoint ⟨construct.B, construct.Z⟩ (below construct.hash.F 128)
  bufferSeparate : Region.Disjoint ⟨construct.B, construct.Z⟩ ⟨off (construct.hash.W 5) witness, construct.len⟩
  bufferOutside : ∀ i < construct.len, construct.Z ≤ ofs construct.B (off (off (construct.hash.W 5) witness) i)
  tapeBuffer : Region.Disjoint ⟨rp, rand.length⟩ ⟨off (construct.hash.W 5) witness, construct.len⟩
  tapeStack : Region.Disjoint ⟨rp, rand.length⟩ (below construct.hash.F 128)
  framePrime : ∀ r ∈ [⟨construct.B, arithmeticBytes⟩,
      ⟨off (construct.hash.W 5) witness, construct.len⟩, below construct.hash.F 128],
    (⟨construct.hash.F, frameBytes⟩ : Region).Disjoint r
  hashPrime : ∀ r ∈ [⟨construct.B, arithmeticBytes⟩,
      ⟨off (construct.hash.W 5) witness, construct.len⟩, below construct.hash.F 128],
    (⟨construct.hash.S, oRsa⟩ : Region).Disjoint r
  pPrime : ∀ r ∈ [⟨construct.B, arithmeticBytes⟩,
      ⟨off (construct.hash.W 5) witness, construct.len⟩, below construct.hash.F 128,
      ⟨construct.hash.F, frameBytes⟩],
    (⟨off (construct.hash.W 5) Impl.Dsa.Generation.Layout.p, construct.len⟩ : Region).Disjoint r
  exponentPrime : ∀ r ∈ [⟨construct.B, arithmeticBytes⟩,
      ⟨off (construct.hash.W 5) witness, construct.len⟩, below construct.hash.F 128,
      ⟨construct.hash.F, frameBytes⟩],
    (⟨off (construct.hash.W 5) exponent, construct.len⟩ : Region).Disjoint r
  tapeConstruct : ∀ r ∈ construct.changed, (⟨rp, rand.length⟩ : Region).Disjoint r

def PPrimalityPlan.prime (p : PPrimalityPlan) (h : VG.Proof.Dsa.Generation.PDomain p.construct.len p.construct.value) : PrimeParams where
  B := p.construct.B
  p := off (p.construct.hash.W 5) witness
  rp := p.rp
  sp := p.construct.hash.F
  Z := p.construct.Z
  w := p.construct.len / 8
  N := p.construct.value
  len := p.construct.len
  drawBytes := p.construct.len
  checks := if p.construct.len ≤ 256 then 64 else 128
  rand := p.rand
  dims := by
    rw [p.size]
    rcases p.construct.width with hh | hh | hh <;> rw [hh] <;> constructor <;> decide
  room := by rw [p.size]; rcases p.construct.width with hh | hh | hh <;> rw [hh] <;> decide
  len2 := by rcases p.construct.width with hh | hh | hh <;> omega
  lenDraw := Nat.le_refl _
  drawMax := by rcases p.construct.width with hh | hh | hh <;> omega
  drawMin := by rcases p.construct.width with hh | hh | hh <;> omega
  lenWords := by rcases p.construct.width with hh | hh | hh <;> rw [hh] <;> decide
  predBits := h.predBits
  drawWidth := h.draw
  odd := h.odd
  n3 := by have := h.large; omega
  checksMax := by split <;> decide
  randMax := p.randMax
  stackSize := p.stackSize
  stackSeparate := p.stackSeparate
  bufferSeparate := p.bufferSeparate
  bufferOutside := p.bufferOutside
  tapeBuffer := p.tapeBuffer
  tapeStack := p.tapeStack

def PPrimalityPlan.call (p : PPrimalityPlan) (h : VG.Proof.Dsa.Generation.PDomain p.construct.len p.construct.value) : PrimeCallPlan where
  prime := p.prime h
  hash := p.construct.hash.S
  candidate := Impl.Dsa.Generation.Layout.p
  W := p.construct.hash.W
  size := p.size
  candidateMax := by decide
  checksMax := by dsimp [PPrimalityPlan.prime]; split <;> decide
  wordsMax := by dsimp [PPrimalityPlan.prime]; rcases p.construct.width with hh | hh | hh <;> omega
  tableRoom := by
    dsimp [PPrimalityPlan.prime]
    rw [p.size]
    rcases p.construct.width with hh | hh | hh <;> rw [hh] <;> decide
  large := h.large
  policy := h.policy
  checks := h.checks.symm
  witnessPtr := rfl
  tapePtr := p.tapePtr
  tapeLength := p.tapeLength
  frameHeaders := p.construct.frameHeaders
  frameOutside := p.construct.frameOutside
  framePrime := p.framePrime
  hashPrime := p.hashPrime

def PPrimalityPlan.testWrites (p : PPrimalityPlan) : List Region :=
  [⟨p.construct.B, arithmeticBytes⟩,
    ⟨off (p.construct.hash.W 5) witness, p.construct.len⟩, below p.construct.hash.F 128,
    ⟨p.construct.hash.F, frameBytes⟩]

def PPrimalityPlan.changed (p : PPrimalityPlan) : List Region :=
  p.construct.changed ++ p.testWrites

def PPrimalityPlan.result (p : PPrimalityPlan) (used : Nat) : Option (Bool × List Byte) :=
  if p.construct.value < 2 ^ (8 * p.construct.len - 1) then some (false, p.rand.drop used)
  else Spec.Dsa.probablePrime p.construct.value (p.rand.drop used)

end VG.Proof.Dsa.X86_64.Generation
