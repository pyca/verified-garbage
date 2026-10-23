module

import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MillerRabin.X86.Caller

/-! # One private candidate frame supplies capacity to every prepared product -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateFrame
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Impl.Mont.X86

def privateSp (s : State) : BitVec 32 := s.gpr .esp - 28#32

theorem privateSp_nat {s : State} (fit : 28 ≤ (s.gpr .esp).toNat) :
    (privateSp s).toNat = (s.gpr .esp).toNat - 28 := sub_toNat fit

theorem allocated_scratch {g : Geometry} {s : State} (S : Scr s g.W g.L)
    (fit : 136 ≤ (s.gpr .esp).toNat)
    (separate : (s.gpr .esp).toNat ≤ g.W.toNat ∨ g.W.toNat + g.L + 136 ≤ (s.gpr .esp).toNat) :
    Scr (allocFrame 28 s) g.W g.L := by
  refine ⟨?_, List.mem_cons_of_mem _ S.wr, S.nowrap, ?_⟩
  · rw [allocFrame_gpr _ _ (by decide)]; exact S.edi
  · change 20 ≤ (privateSp s).toNat ∧ ((privateSp s).toNat ≤ g.W.toNat ∨ g.W.toNat + g.L + 20 ≤ (privateSp s).toNat)
    rw [privateSp_nat (by omega)]
    rcases separate with h | h <;> constructor <;> omega

theorem allocated_workspace {s : State} (fit : 28 ≤ (s.gpr .esp).toNat) :
    Ws (allocFrame 28 s) ((privateSp s).setWidth 64) 28 := by
  refine ⟨List.mem_cons_self, ?_⟩
  rw [BitVec.toNat_setWidth, privateSp_nat fit, Nat.mod_eq_of_lt (by have := (s.gpr .esp).isLt; omega)]
  have := (s.gpr .esp).isLt
  omega

theorem allocated_base {s : State} :
    PtrAt (allocFrame 28 s) ((privateSp s).setWidth 64) .esp 0 := by
  rw [PtrAt, allocFrame_esp]
  change (privateSp s).toNat = (((privateSp s).setWidth 64).toNat + 0) % 2 ^ 32
  simp only [BitVec.toNat_setWidth, Nat.add_zero,
    Nat.mod_eq_of_lt (Nat.lt_trans (privateSp s).isLt (by decide : 2 ^ 32 < 2 ^ 64)), Nat.mod_eq_of_lt (privateSp s).isLt]

theorem slot_ok {g : Geometry} {s : State} {capacity : Nat} (S : Scr s g.W g.L)
    (fit : 136 ≤ (s.gpr .esp).toNat)
    (separate : (s.gpr .esp).toNat ≤ g.W.toNat ∨ g.W.toNat + g.L + 136 ≤ (s.gpr .esp).toNat)
    (capacityReg : s.gpr .edx = BitVec.ofNat 32 capacity) :
    WP isa (.block [.store (at_ .esp 24) .edx]) (allocFrame 28 s) fun t =>
      Scr t g.W g.L ∧ Caller g capacity (privateSp s) t ∧
      (lengthRegion (privateSp s)).Disjoint (below (privateSp s) 108) ∧
      Frame [below (s.gpr .esp) 28] s.mem t.mem ∧ Keeps [] (allocFrame 28 s) t := by
  have low : 28 ≤ (s.gpr .esp).toNat := by omega
  have W := allocated_workspace low
  have P := allocated_base (s := s)
  have A := allocated_scratch S fit separate
  have address : (allocFrame 28 s).ea (at_ .esp 24) = off ((privateSp s).setWidth 64) 24 := by
    simpa only [Nat.zero_add] using ea_ptr W P (d := 24) (by decide)
  have writable : InRegions (allocFrame 28 s).wr (off ((privateSp s).setWidth 64) 24) 4 := ws_write W (by decide)
  refine wp_storeS address writable fun t T => WP.block_nil ?_
  have K := T.keeps []
  have spT : t.gpr .esp = privateSp s := (K.1 .esp (by decide)).trans (allocFrame_esp 28 s)
  have pnat := privateSp_nat low
  have pbound := (privateSp s).isLt
  have pn : ((privateSp s).setWidth 64).toNat = (privateSp s).toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans pbound (by decide))]
  have lenNat : (lengthRegion (privateSp s)).base.toNat = (privateSp s).toNat + 24 := by
    change ((privateSp s + 24#32).setWidth 64).toNat = _
    rw [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := (s.gpr .esp).isLt; omega), Nat.mod_eq_of_lt (by have := (s.gpr .esp).isLt; omega)]
  have belowNat : (below (privateSp s) 108).base.toNat = (privateSp s).toNat - 108 := by
    change ((privateSp s - 108#32).setWidth 64).toNat = _
    rw [BitVec.toNat_setWidth, sub_toNat (by omega), Nat.mod_eq_of_lt (by omega)]
  have lenStack : (lengthRegion (privateSp s)).Disjoint (below (privateSp s) 108) := by
    apply Region.Disjoint.symm
    apply Offset.disjoint_of_le
    · change (below (privateSp s) 108).base.toNat + 108 ≤ (lengthRegion (privateSp s)).base.toNat
      rw [belowNat, lenNat]; omega
    · change (lengthRegion (privateSp s)).base.toNat + 4 ≤ 2 ^ 64
      rw [lenNat]; omega
  have stackFar : (⟨g.W, g.L⟩ : Region).Disjoint (below (privateSp s) 108) := by
    rcases separate with h | h
    · apply Region.Disjoint.symm
      apply Offset.disjoint_of_le
      · change (below (privateSp s) 108).base.toNat + 108 ≤ g.W.toNat
        rw [belowNat]; omega
      · exact Nat.le_trans S.nowrap (by decide)
    · apply Offset.disjoint_of_le
      · change g.W.toNat + g.L ≤ (below (privateSp s) 108).base.toNat
        rw [belowNat]; omega
      · change (below (privateSp s) 108).base.toNat + 108 ≤ 2 ^ 64
        rw [belowNat]; omega
  have lenFar : (lengthRegion (privateSp s)).Disjoint ⟨g.W, g.L⟩ := by
    rcases separate with h | h
    · apply Offset.disjoint_of_le
      · change (lengthRegion (privateSp s)).base.toNat + 4 ≤ g.W.toNat
        rw [lenNat]; omega
      · exact Nat.le_trans S.nowrap (by decide)
    · apply Region.Disjoint.symm
      apply Offset.disjoint_of_le
      · change g.W.toNat + g.L ≤ (lengthRegion (privateSp s)).base.toNat
        rw [lenNat]; omega
      · change (lengthRegion (privateSp s)).base.toNat + 4 ≤ 2 ^ 64
        rw [lenNat]; omega
  have readLen : readSrc t (.mem (at_ .esp 24)) = some (BitVec.ofNat 32 capacity) := by
    have Pt : PtrAt t ((privateSp s).setWidth 64) .esp 0 := by
      rw [PtrAt, spT, pn, Nat.add_zero, Nat.mod_eq_of_lt pbound]
    have read := readSrc_ptr (W.of_keeps K) Pt (d := 24) (by decide)
    simp only [Nat.zero_add] at read
    rw [read, T.mem, Mem.readW_writeW_self32, allocFrame_gpr _ _ (by decide), capacityReg]
  have F : Frame [below (s.gpr .esp) 28] s.mem t.mem := by
    rw [T.mem]
    apply Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _)
    change (off ((privateSp s).setWidth 64) 24 - (below (s.gpr .esp) 28).base).toNat + 4 ≤ 28
    change (off ((privateSp s).setWidth 64) 24 - (privateSp s).setWidth 64).toNat + 4 ≤ 28
    rw [Mem.sub_ofNat_toNat _ (by decide : 24 < 2 ^ 64)]
  exact ⟨A.of_keeps K (by decide), ⟨spT, by omega,
    stackFar.sub_right (below_sub (by decide : 80 ≤ 108) (by omega)), lenFar,
    lenStack.sub_right (below_sub (by decide : 80 ≤ 108) (by omega)), readLen⟩, lenStack, F, K⟩

end VG.Proof.RsaKeyGen.X86.CandidateFrame
