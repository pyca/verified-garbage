module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.RoundEntry
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedSpec
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedGeometry

/-! # Prepared candidate data establishes the shared round's cdecl precondition -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.RoundCall
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.RoundCall

theorem entry_pre {g : Geometry} (v : g.Valid) {s : State} {c capacity b : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (S : Prepare.Data g c capacity p s)
    (A : Arguments g capacity s) (odd : c % 2 = 1) (large : 3 ≤ c)
    (witness : val32 s.mem g.W (g.array 5) g.words = b % c * 2 ^ (64 * g.w) % c)
    (fit : 68 ≤ (s.gpr .esp).toNat)
    (far : (⟨g.W, g.L⟩ : Region).Disjoint (below (s.gpr .esp) 68)) :
    (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 56).pre (entry g s) := by
  have sa := fun {i} (hi : i < 2) => entry_arg A (by omega) hi
  have capBound : capacity < 2 ^ 32 := by have := S.ready.scratch.nowrap; omega
  have ptrBound : g.W.toNat < 2 ^ 32 := by have := S.ready.scratch.nowrap; have := v.headerFit; omega
  have F := entry_frame (by omega : 12 ≤ (s.gpr .esp).toNat) S.ready.scratch.nowrap
    (far.sub_right (below_sub (by decide : 12 ≤ 68) fit))
  have Mu := S.ready.modulus.keep v F (by simp) (by simp)
  have lu : Spec.MillerRabin.Layout Spec.MillerRabin.compact (entry g s).mem g.W capacity := by
    unfold Spec.MillerRabin.Layout
    rw [Mu.width]
    refine ⟨Or.inr rfl, ?_, v.minWidth, v.maxWidth, ?_, ?_⟩
    · have M := Mu.layout v (by rw [length]; omega)
      simpa only [length, Nat.mul_div_cancel_left capacity (by decide : 0 < 8)] using M
    · change Spec.Rsa.Mont.arrAt g.w 28 ≤ 8 * capacity
      rw [← length]
      exact v.arraysFit
    · change (entry g s).mem.readW (off g.W 224) 64 = _
      rw [F.read64 (by have := v.headerFit; omega) (by simp)]
      exact S.stride
  have pu : Spec.MillerRabin.Prepared Spec.MillerRabin.compact (entry g s).mem g.W := by
    refine Prepare.prepared_of Mu odd large ?_ ?_ ?_ ?_ ?_
    · rw [F.val32 (v.arrayFit (by decide)) (by simp), witness]
      exact Nat.mod_lt _ (by omega)
    · rw [F.val32 (v.arrayFit (by decide)) (by simp)]; exact S.one
    · rw [F.val32 (v.arrayFit (by decide)) (by simp)]; exact S.minusOne
    · rw [F.val32 (v.arrayFit (by decide)) (by simp)]; exact S.exponent
    · change (entry g s).mem.readW (off g.W (g.array 27 + 8 * g.w)) 64 = _
      rw [F.read64 (by have := Prepared.paddedFit v (j := 27) (by decide); omega) (by simp)]
      exact S.marker
  have sp : (entry g s).gpr .esp = s.gpr .esp - 12#32 := by
    change (pushed args s).callEntry.gpr .esp = _
    exact callEntry_esp' args s
  have ar : argAddr (entry g s) 0 = (s.gpr .esp - 8#32).setWidth 64 := by
    rw [entry, argAddr_withRegions]
    exact callEntry_argAddr0 args s
  have rd : (entry g s).rd = [⟨argAddr (entry g s) 0, 8⟩] := by
    rw [entry, State.withRegions_rd, argAddr_withRegions]
  have wr : (entry g s).wr = [⟨g.W, g.L⟩] := rfl
  have sa0 : arg (entry g s) 0 = BitVec.ofNat 32 g.W.toNat := sa (by decide)
  have sa1 : arg (entry g s) 1 = BitVec.ofNat 32 capacity := sa (by decide)
  have ptr : (BitVec.ofNat 32 g.W.toNat).setWidth 64 = g.W := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ptrBound]
    exact Nat.mod_eq_of_lt g.W.isLt
  generalize eu : entry g s = u at *
  sig_pre [Spec.MillerRabin.roundContract, Spec.MillerRabin.roundSig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [sa0, sa1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt capBound, Nat.mod_eq_of_lt ptrBound,
    ptr, rd, wr, sp, ar, ← length, Nat.mul_comm capacity 8]
  have sp12 : (s.gpr .esp - 12#32).toNat = (s.gpr .esp).toNat - 12 := sub_toNat (by omega)
  have nat8 : ((s.gpr .esp - 8#32).setWidth 64).toNat = (s.gpr .esp).toNat - 8 := by
    rw [BitVec.toNat_setWidth, sub_toNat (by omega)]
    exact Nat.mod_eq_of_lt (by have := (s.gpr .esp).isLt; omega)
  have nat12 : ((s.gpr .esp - 12#32).setWidth 64).toNat = (s.gpr .esp).toNat - 12 := by
    rw [BitVec.toNat_setWidth, sp12]
    exact Nat.mod_eq_of_lt (by have := (s.gpr .esp).isLt; omega)
  have saved : (s.gpr .esp - 12#32).setWidth 64 - 56#64 = (s.gpr .esp - 68#32).setWidth 64 := by
    rw [← Taint.sub_setWidth (by rw [sp12]; omega : 56 ≤ (s.gpr .esp - 12#32).toNat)]
    congr 1
    rw [BitVec.sub_sub]
    rfl
  have nat68 : ((s.gpr .esp - 68#32).setWidth 64).toNat = (s.gpr .esp).toNat - 68 := by
    rw [BitVec.toNat_setWidth, sub_toNat fit]
    exact Nat.mod_eq_of_lt (by have := (s.gpr .esp).isLt; omega)
  have argSub : (⟨(s.gpr .esp - 8#32).setWidth 64, 8⟩ : Region).Sub (below (s.gpr .esp) 68) := below_sub (by decide) fit
  have retSub : (⟨(s.gpr .esp - 12#32).setWidth 64, 4⟩ : Region).Sub (below (s.gpr .esp) 68) :=
    fun x hx => below_sub (by decide : 12 ≤ 68) fit x ((Region.sub_prefix (by decide : 4 ≤ 12)) x hx)
  have saveSub : (⟨(s.gpr .esp - 12#32).setWidth 64 - 56#64, 56⟩ : Region).Sub (below (s.gpr .esp) 68) := by
    rw [saved]
    exact Region.sub_prefix (by decide : 56 ≤ 68)
  have retArgs : (⟨(s.gpr .esp - 12#32).setWidth 64, 4⟩ : Region).Disjoint ⟨(s.gpr .esp - 8#32).setWidth 64, 8⟩ :=
    Offset.disjoint_of_le (by simp only [nat12, nat8]; omega) (by simp only [nat8]; have := (s.gpr .esp).isLt; omega)
  have saveArgs : (⟨(s.gpr .esp - 12#32).setWidth 64 - 56#64, 56⟩ : Region).Disjoint ⟨(s.gpr .esp - 8#32).setWidth 64, 8⟩ := by
    rw [saved]
    exact Offset.disjoint_of_le (by simp only [nat68, nat8]; omega) (by simp only [nat8]; have := (s.gpr .esp).isLt; omega)
  exact ⟨by rw [sp12]; omega, by rw [sp12]; have := (s.gpr .esp).isLt; omega,
    trivial, trivial, far.sub_right argSub, (far.sub_right retSub).symm, retArgs,
    (far.sub_right saveSub).symm, saveArgs, S.ready.scratch.nowrap, lu, pu⟩

end VG.Proof.RsaKeyGen.X86.RoundCall
