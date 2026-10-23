module

public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The key generator's resources, from the shared cdecl contract

Its arguments: `out`, `out_len`, `used`, `key`, `key_len`, `p_len`, `q_len`,
`rand`, `rand_len`, `scratch`, `scratch_len`. The
232 bytes of stack below the return address hold its frame and the call of
the key derivation.
-/

@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86

/-- The region of buffer argument `i`, of `n` bytes. -/
abbrev argRegion (s : State) (i n : Nat) : Region := ⟨argumentPointer s i, n⟩

structure KeyABI (s : State) : Prop where
  stackLow : 232 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 44 ≤ 2 ^ 32
  rd : s.rd = [argRegion s 3 (arg s 4).toNat, argRegion s 7 (arg s 8).toNat]
  wr : s.wr = [argRegion s 0 (arg s 1).toNat, argRegion s 2 8, argRegion s 9 ((arg s 10).toNat * 8),
    ⟨argAddr s 0, 44⟩]
  outUsed : (argRegion s 0 (arg s 1).toNat).Disjoint (argRegion s 2 8)
  outKey : (argRegion s 0 (arg s 1).toNat).Disjoint (argRegion s 3 (arg s 4).toNat)
  outRand : (argRegion s 0 (arg s 1).toNat).Disjoint (argRegion s 7 (arg s 8).toNat)
  outScratch : (argRegion s 0 (arg s 1).toNat).Disjoint (argRegion s 9 ((arg s 10).toNat * 8))
  outArgs : (argRegion s 0 (arg s 1).toNat).Disjoint ⟨argAddr s 0, 44⟩
  usedKey : (argRegion s 2 8).Disjoint (argRegion s 3 (arg s 4).toNat)
  usedRand : (argRegion s 2 8).Disjoint (argRegion s 7 (arg s 8).toNat)
  usedScratch : (argRegion s 2 8).Disjoint (argRegion s 9 ((arg s 10).toNat * 8))
  usedArgs : (argRegion s 2 8).Disjoint ⟨argAddr s 0, 44⟩
  keyScratch : (argRegion s 3 (arg s 4).toNat).Disjoint (argRegion s 9 ((arg s 10).toNat * 8))
  keyArgs : (argRegion s 3 (arg s 4).toNat).Disjoint ⟨argAddr s 0, 44⟩
  randScratch : (argRegion s 7 (arg s 8).toNat).Disjoint (argRegion s 9 ((arg s 10).toNat * 8))
  randArgs : (argRegion s 7 (arg s 8).toNat).Disjoint ⟨argAddr s 0, 44⟩
  scratchArgs : (argRegion s 9 ((arg s 10).toNat * 8)).Disjoint ⟨argAddr s 0, 44⟩
  retOut : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (argRegion s 0 (arg s 1).toNat)
  retUsed : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (argRegion s 2 8)
  retKey : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (argRegion s 3 (arg s 4).toNat)
  retRand : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (argRegion s 7 (arg s 8).toNat)
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (argRegion s 9 ((arg s 10).toNat * 8))
  stackOutWide : (⟨(s.gpr .esp).setWidth 64 - 232#64, 232⟩ : Region).Disjoint (argRegion s 0 (arg s 1).toNat)
  stackUsedWide : (⟨(s.gpr .esp).setWidth 64 - 232#64, 232⟩ : Region).Disjoint (argRegion s 2 8)
  stackKeyWide : (⟨(s.gpr .esp).setWidth 64 - 232#64, 232⟩ : Region).Disjoint (argRegion s 3 (arg s 4).toNat)
  stackRandWide : (⟨(s.gpr .esp).setWidth 64 - 232#64, 232⟩ : Region).Disjoint (argRegion s 7 (arg s 8).toNat)
  stackScratchWide : (⟨(s.gpr .esp).setWidth 64 - 232#64, 232⟩ : Region).Disjoint
    (argRegion s 9 ((arg s 10).toNat * 8))
  outBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  usedBound : (arg s 2).toNat + 8 ≤ 2 ^ 32
  keyBound : (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32
  randBound : (arg s 7).toNat + (arg s 8).toNat ≤ 2 ^ 32
  scratchBound : (arg s 9).toNat + (arg s 10).toNat * 8 ≤ 2 ^ 32
  lengths : Spec.Dsa.lengthsValid (arg s 5).toNat (arg s 6).toNat
  outLength : (arg s 1).toNat = 3 * (arg s 5).toNat + 2 * (arg s 6).toNat
  keyLength : (arg s 4).toNat = 2 * (arg s 5).toNat + (arg s 6).toNat
  scratchLength : Spec.Dsa.generationScratchWords (arg s 5).toNat ≤ (arg s 10).toNat

theorem keyABI_of {s : State} (h : (Spec.Dsa.generateKeyContract abi 232).pre s) :
    KeyABI s := by
  sig_pre [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argSlots, argVal, argBytes,
    stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

theorem KeyABI.stackOut {s : State} (A : KeyABI s) :
    (⟨(s.gpr .esp).setWidth 64 - 144#64, 144⟩ : Region).Disjoint (argRegion s 0 (arg s 1).toNat) :=
  A.stackOutWide.sub_left (fun x hx => Offset.below_mono _ (a := 144) (b := 232) (by decide) (by decide) x hx)

theorem KeyABI.stackUsed {s : State} (A : KeyABI s) :
    (⟨(s.gpr .esp).setWidth 64 - 144#64, 144⟩ : Region).Disjoint (argRegion s 2 8) :=
  A.stackUsedWide.sub_left (fun x hx => Offset.below_mono _ (a := 144) (b := 232) (by decide) (by decide) x hx)

theorem KeyABI.stackKey {s : State} (A : KeyABI s) :
    (⟨(s.gpr .esp).setWidth 64 - 144#64, 144⟩ : Region).Disjoint (argRegion s 3 (arg s 4).toNat) :=
  A.stackKeyWide.sub_left (fun x hx => Offset.below_mono _ (a := 144) (b := 232) (by decide) (by decide) x hx)

theorem KeyABI.stackRand {s : State} (A : KeyABI s) :
    (⟨(s.gpr .esp).setWidth 64 - 144#64, 144⟩ : Region).Disjoint (argRegion s 7 (arg s 8).toNat) :=
  A.stackRandWide.sub_left (fun x hx => Offset.below_mono _ (a := 144) (b := 232) (by decide) (by decide) x hx)

theorem KeyABI.stackScratch {s : State} (A : KeyABI s) :
    (⟨(s.gpr .esp).setWidth 64 - 144#64, 144⟩ : Region).Disjoint (argRegion s 9 ((arg s 10).toNat * 8)) :=
  A.stackScratchWide.sub_left (fun x hx => Offset.below_mono _ (a := 144) (b := 232) (by decide) (by decide) x hx)

end VG.Proof.Dsa.X86.KeyRandom
