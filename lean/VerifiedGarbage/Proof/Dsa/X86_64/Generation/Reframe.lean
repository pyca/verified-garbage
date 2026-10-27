module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PPrimalityPlan
import VerifiedGarbage.Proof.Framework.Omega

/-! # Reuse the fixed generation layout at the next offset and witness cursor -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def HashPlan.reframe (p : HashPlan) (W : Nat → BitVec 64) (offset : Nat)
    (h1 : W 1 = p.W 1) (h3 : W 3 = p.W 3) (h4 : W 4 = p.W 4)
    (h2 : W 2 = BitVec.ofNat 64 offset) (hcarry : offset + p.count < 2 ^ 32) : HashPlan :=
  { p with
    W := W
    offset := offset
    seed_slot := h1.trans p.seed_slot
    wrapped_slot := h3.trans p.wrapped_slot
    output_slot := h4.trans p.output_slot
    offset_slot := h2
    carry := hcarry }

def PConstructPlan.reframe (p : PConstructPlan) (W : Nat → BitVec 64) (offset : Nat)
    (h1 : W 1 = p.hash.W 1) (h3 : W 3 = p.hash.W 3) (h4 : W 4 = p.hash.W 4)
    (h5 : W 5 = p.hash.W 5) (h2 : W 2 = BitVec.ofNat 64 offset)
    (h0 : W 0 = off (W 5) shaped) (hcarry : offset + p.hash.count < 2 ^ 32) : PConstructPlan :=
  { p with
    hash := p.hash.reframe W offset h1 h3 h4 h2 hcarry
    base := by dsimp only [HashPlan.reframe]; simpa only [h5] using p.base
    shapedSlot := h0
    shapedOutside := by dsimp only [HashPlan.reframe]; simpa only [h5] using p.shapedOutside
    shapedHash := by dsimp only [HashPlan.reframe]; simpa only [h5] using p.shapedHash
    shapedInput := by dsimp only [HashPlan.reframe]; simpa only [h5] using p.shapedInput
    qHash := by dsimp only [HashPlan.reframe]; simpa only [HashPlan.changed, h5] using p.qHash
    pOutside := by dsimp only [HashPlan.reframe]; simpa only [h5] using p.pOutside
    exponentOutside := by dsimp only [HashPlan.reframe]; simpa only [h5] using p.exponentOutside
    pExponent := by dsimp only [HashPlan.reframe]; simpa only [h5] using p.pExponent
    frameArithmetic := by dsimp only [HashPlan.reframe]; simpa only [h5] using p.frameArithmetic
    hashArithmetic := by dsimp only [HashPlan.reframe]; simpa only [h5] using p.hashArithmetic }

def PPrimalityPlan.reframe (p : PPrimalityPlan) (W : Nat → BitVec 64) (offset : Nat)
    (h1 : W 1 = p.construct.hash.W 1) (h3 : W 3 = p.construct.hash.W 3)
    (h4 : W 4 = p.construct.hash.W 4) (h5 : W 5 = p.construct.hash.W 5)
    (h13 : W 13 = p.construct.hash.W 13) (h15 : W 15 = p.construct.hash.W 15)
    (h2 : W 2 = BitVec.ofNat 64 offset) (h0 : W 0 = off (W 5) shaped)
    (hcarry : offset + p.construct.hash.count < 2 ^ 32) : PPrimalityPlan :=
  { p with
    construct := p.construct.reframe W offset h1 h3 h4 h5 h2 h0 hcarry
    tapePtr := h13.trans p.tapePtr
    tapeLength := h15.trans p.tapeLength
    bufferSeparate := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.bufferSeparate
    bufferOutside := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.bufferOutside
    tapeBuffer := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.tapeBuffer
    framePrime := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.framePrime
    hashPrime := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.hashPrime
    pPrime := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.pPrime
    exponentPrime := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.exponentPrime
    arenaBound := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.arenaBound
    tapeArena := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.tapeArena
    arenaFrame := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.arenaFrame
    arenaStack := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.arenaStack
    tapeConstruct := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [PConstructPlan.changed, HashPlan.changed, h5] using p.tapeConstruct }

end VG.Proof.Dsa.X86_64.Generation
