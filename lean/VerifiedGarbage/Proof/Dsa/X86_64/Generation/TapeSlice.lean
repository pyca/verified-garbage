module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeState
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Memory
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The next significant witness bytes are a disjoint slice of the random tape -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate

def PrimeParams.drawStart (P : PrimeParams) (used : Nat) : Nat := used + (P.drawBytes - P.len)
def PrimeParams.drawSlice (P : PrimeParams) (used : Nat) : List Byte := (P.rand.drop (P.drawStart used)).take P.len

theorem PrimeParams.slice_length (P : PrimeParams) {used : Nat} (h : used + P.drawBytes ≤ P.rand.length) :
    (P.drawSlice used).length = P.len := by
  simp only [PrimeParams.drawSlice, PrimeParams.drawStart, List.length_take, List.length_drop]
  have := P.lenDraw
  omega

theorem PrimeState.slice_source {P : PrimeParams} {mi : BitVec 64} {used : Nat} {s : State}
    (h : PrimeState P mi used s) : Src s P.B P.Z (off P.rp (P.drawStart used)) (P.drawSlice used) :=
  source_take (source_drop h.source (P.drawStart used)) P.len

theorem PrimeParams.slice_separate (P : PrimeParams) {used : Nat}
    (hroom : used + P.drawBytes ≤ P.rand.length) :
    ∀ i < (P.drawSlice used).length, ∀ j < (P.drawSlice used).length,
      off (off P.rp (P.drawStart used)) i ≠ off P.p j := by
  intro i hi j hj he
  rw [P.slice_length hroom] at hi hj
  have hs : P.drawStart used + i < P.rand.length := by
    dsimp only [PrimeParams.drawStart]; have := P.lenDraw; omega
  have ha : off (off P.rp (P.drawStart used)) i = off P.rp (P.drawStart used + i) := by
    simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
  apply P.tapeBuffer (off P.p j)
  · rw [← he, ha]
    apply (Region.contains_self P.rp P.rand.length).byte
    simp only [off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by have := P.randMax; omega)]
    exact hs
  · apply (Region.contains_self P.p P.len).byte
    simp only [off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by have := P.lenDraw; have := P.drawMax; omega)]
    exact hj

end VG.Proof.Dsa.X86_64.Generation
