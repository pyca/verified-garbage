module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryABI
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Geometry
import VerifiedGarbage.Proof.Framework.X86.Call

/-! # The internal frame and arena fit inside the public cdecl resources -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Impl.Dsa.Generation.Layout

theorem ordered_regions {a b : Region} (apart : a.Disjoint b) (apos : 0 < a.len) (bpos : 0 < b.len) :
    a.base.toNat + a.len ≤ b.base.toNat ∨ b.base.toNat + b.len ≤ a.base.toNat := by
  by_cases h : a.base.toNat ≤ b.base.toNat
  · left
    by_contra bad
    apply apart b.base
    · simp only [Region.Contains]; bv_omega
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; exact bpos
  · right
    by_contra bad
    apply apart a.base
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; exact apos
    · simp only [Region.Contains]; bv_omega

def entryFrame (s : State) : BitVec 32 := s.gpr .esp - 164#32

theorem ParameterABI.arenaRoom {s : State} (A : ParameterABI s) :
    usedBytes (arg s 2).toNat ≤ (arg s 11).toNat * 8 := by
  have h := A.scratchLength
  have w := A.lengths
  unfold Spec.Dsa.generationScratchWords at h
  unfold Spec.Dsa.generationLengthsValid at w
  unfold usedBytes domainCheck
  rcases w with h1 | h1 | h1 <;> omega

def ParameterABI.geometry {s : State} (A : ParameterABI s) : GenerationGeometry where
  parent := arg s 10
  frame := entryFrame s
  pLen := (arg s 2).toNat
  qLen := (arg s 3).toNat
  lengths := A.lengths
  arenaBound := by have := A.scratchBound; have := A.arenaRoom; omega
  frameBound := by
    have lo := A.stackLow
    have hi := A.stackBound
    unfold entryFrame VG.Impl.Dsa.X86.Generation.frameBytes
    rw [sub_toNat (by omega)]
    omega
  stackSize := by
    have lo := A.stackLow
    unfold entryFrame
    rw [sub_toNat (by omega)]
    omega
  separated := by
    have lo := A.stackLow
    have hi := A.stackBound
    have ar := A.arenaRoom
    have pw := A.lengths
    have positive : 0 < (arg s 11).toNat * 8 := by
      unfold usedBytes domainCheck at ar
      omega
    have sep := ordered_regions A.stackScratch (by decide : 0 < 292) positive
    change ((s.gpr .esp).setWidth 64 - 292#64).toNat + 292 ≤ (arg s 10).toNat ∨
      (arg s 10).toNat + (arg s 11).toNat * 8 ≤ ((s.gpr .esp).setWidth 64 - 292#64).toNat at sep
    have wide : ((s.gpr .esp).setWidth 64).toNat = (s.gpr .esp).toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (s.gpr .esp).isLt (by decide))]
    rw [BitVec.toNat_sub_of_le (by change 292 ≤ ((s.gpr .esp).setWidth 64).toNat; rw [wide]; omega), wide] at sep
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at sep
    unfold entryFrame VG.Impl.Dsa.X86.Generation.frameBytes
    rw [sub_toNat (by omega)]
    omega
end VG.Proof.Dsa.X86.Generation
