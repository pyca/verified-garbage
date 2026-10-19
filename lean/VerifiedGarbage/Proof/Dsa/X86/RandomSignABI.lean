module

public import VerifiedGarbage.Spec.Dsa.RandomSign
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.Call

/-!
# The randomized signer's resources, from the shared cdecl contract

Its arguments: `out`, `out_len`, `used`, `key`, `key_len`, `p_len`, `q_len`,
`digest`, `digest_len`, `rand`, `rand_len`, `scratch`, `scratch_len`. The
156 bytes of stack below the return address hold its frame and the call of
the supplied-nonce signer.
-/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86

/-- The region of buffer argument `i`, of `n` bytes. -/
abbrev argRegion (s : State) (i n : Nat) : Region := ⟨argumentPointer s i, n⟩

structure RandomSignABI (s : State) : Prop where
  stackLow : 156 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 52 ≤ 2 ^ 32
  rd : s.rd = [argRegion s 3 (arg s 4).toNat, argRegion s 7 (arg s 8).toNat,
    argRegion s 9 (arg s 10).toNat]
  wr : s.wr = [argRegion s 0 (arg s 1).toNat, argRegion s 2 8, argRegion s 11 ((arg s 12).toNat * 8),
    ⟨argAddr s 0, 52⟩]
  outUsed : (argRegion s 0 (arg s 1).toNat).Disjoint (argRegion s 2 8)
  outKey : (argRegion s 0 (arg s 1).toNat).Disjoint (argRegion s 3 (arg s 4).toNat)
  outDigest : (argRegion s 0 (arg s 1).toNat).Disjoint (argRegion s 7 (arg s 8).toNat)
  outRand : (argRegion s 0 (arg s 1).toNat).Disjoint (argRegion s 9 (arg s 10).toNat)
  outScratch : (argRegion s 0 (arg s 1).toNat).Disjoint (argRegion s 11 ((arg s 12).toNat * 8))
  outArgs : (argRegion s 0 (arg s 1).toNat).Disjoint ⟨argAddr s 0, 52⟩
  usedKey : (argRegion s 2 8).Disjoint (argRegion s 3 (arg s 4).toNat)
  usedDigest : (argRegion s 2 8).Disjoint (argRegion s 7 (arg s 8).toNat)
  usedRand : (argRegion s 2 8).Disjoint (argRegion s 9 (arg s 10).toNat)
  usedScratch : (argRegion s 2 8).Disjoint (argRegion s 11 ((arg s 12).toNat * 8))
  usedArgs : (argRegion s 2 8).Disjoint ⟨argAddr s 0, 52⟩
  keyScratch : (argRegion s 3 (arg s 4).toNat).Disjoint (argRegion s 11 ((arg s 12).toNat * 8))
  keyArgs : (argRegion s 3 (arg s 4).toNat).Disjoint ⟨argAddr s 0, 52⟩
  digestScratch : (argRegion s 7 (arg s 8).toNat).Disjoint (argRegion s 11 ((arg s 12).toNat * 8))
  digestArgs : (argRegion s 7 (arg s 8).toNat).Disjoint ⟨argAddr s 0, 52⟩
  randScratch : (argRegion s 9 (arg s 10).toNat).Disjoint (argRegion s 11 ((arg s 12).toNat * 8))
  randArgs : (argRegion s 9 (arg s 10).toNat).Disjoint ⟨argAddr s 0, 52⟩
  scratchArgs : (argRegion s 11 ((arg s 12).toNat * 8)).Disjoint ⟨argAddr s 0, 52⟩
  retOut : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (argRegion s 0 (arg s 1).toNat)
  retUsed : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (argRegion s 2 8)
  retKey : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (argRegion s 3 (arg s 4).toNat)
  retDigest : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (argRegion s 7 (arg s 8).toNat)
  retRand : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (argRegion s 9 (arg s 10).toNat)
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (argRegion s 11 ((arg s 12).toNat * 8))
  stackOutWide : (⟨(s.gpr .esp).setWidth 64 - 156#64, 156⟩ : Region).Disjoint (argRegion s 0 (arg s 1).toNat)
  stackUsedWide : (⟨(s.gpr .esp).setWidth 64 - 156#64, 156⟩ : Region).Disjoint (argRegion s 2 8)
  stackKeyWide : (⟨(s.gpr .esp).setWidth 64 - 156#64, 156⟩ : Region).Disjoint (argRegion s 3 (arg s 4).toNat)
  stackDigestWide : (⟨(s.gpr .esp).setWidth 64 - 156#64, 156⟩ : Region).Disjoint (argRegion s 7 (arg s 8).toNat)
  stackRandWide : (⟨(s.gpr .esp).setWidth 64 - 156#64, 156⟩ : Region).Disjoint (argRegion s 9 (arg s 10).toNat)
  stackScratchWide : (⟨(s.gpr .esp).setWidth 64 - 156#64, 156⟩ : Region).Disjoint
    (argRegion s 11 ((arg s 12).toNat * 8))
  outBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  usedBound : (arg s 2).toNat + 8 ≤ 2 ^ 32
  keyBound : (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32
  digestBound : (arg s 7).toNat + (arg s 8).toNat ≤ 2 ^ 32
  randBound : (arg s 9).toNat + (arg s 10).toNat ≤ 2 ^ 32
  scratchBound : (arg s 11).toNat + (arg s 12).toNat * 8 ≤ 2 ^ 32
  lengths : Spec.Dsa.lengthsValid (arg s 5).toNat (arg s 6).toNat
  outLength : (arg s 1).toNat = 2 * (arg s 6).toNat
  keyLength : (arg s 4).toNat = 3 * (arg s 5).toNat + 2 * (arg s 6).toNat
  scratchLength : Spec.Dsa.randomSignScratchWords (arg s 5).toNat ≤ (arg s 12).toNat

theorem randomSignABI_of {s : State} (h : (Spec.Dsa.randomSignContract abi 156).pre s) :
    RandomSignABI s := by
  sig_pre [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argSlots, argVal, argBytes,
    stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

theorem RandomSignABI.stackOut {s : State} (A : RandomSignABI s) :
    (⟨(s.gpr .esp).setWidth 64 - 144#64, 144⟩ : Region).Disjoint (argRegion s 0 (arg s 1).toNat) :=
  A.stackOutWide.sub_left (fun x hx => Offset.below_mono _ (a := 144) (b := 156) (by decide) (by decide) x hx)

theorem RandomSignABI.stackUsed {s : State} (A : RandomSignABI s) :
    (⟨(s.gpr .esp).setWidth 64 - 144#64, 144⟩ : Region).Disjoint (argRegion s 2 8) :=
  A.stackUsedWide.sub_left (fun x hx => Offset.below_mono _ (a := 144) (b := 156) (by decide) (by decide) x hx)

theorem RandomSignABI.stackKey {s : State} (A : RandomSignABI s) :
    (⟨(s.gpr .esp).setWidth 64 - 144#64, 144⟩ : Region).Disjoint (argRegion s 3 (arg s 4).toNat) :=
  A.stackKeyWide.sub_left (fun x hx => Offset.below_mono _ (a := 144) (b := 156) (by decide) (by decide) x hx)

theorem RandomSignABI.stackDigest {s : State} (A : RandomSignABI s) :
    (⟨(s.gpr .esp).setWidth 64 - 144#64, 144⟩ : Region).Disjoint (argRegion s 7 (arg s 8).toNat) :=
  A.stackDigestWide.sub_left (fun x hx => Offset.below_mono _ (a := 144) (b := 156) (by decide) (by decide) x hx)

theorem RandomSignABI.stackRand {s : State} (A : RandomSignABI s) :
    (⟨(s.gpr .esp).setWidth 64 - 144#64, 144⟩ : Region).Disjoint (argRegion s 9 (arg s 10).toNat) :=
  A.stackRandWide.sub_left (fun x hx => Offset.below_mono _ (a := 144) (b := 156) (by decide) (by decide) x hx)

theorem RandomSignABI.stackScratch {s : State} (A : RandomSignABI s) :
    (⟨(s.gpr .esp).setWidth 64 - 144#64, 144⟩ : Region).Disjoint (argRegion s 11 ((arg s 12).toNat * 8)) :=
  A.stackScratchWide.sub_left (fun x hx => Offset.below_mono _ (a := 144) (b := 156) (by decide) (by decide) x hx)

end VG.Proof.Dsa.X86
