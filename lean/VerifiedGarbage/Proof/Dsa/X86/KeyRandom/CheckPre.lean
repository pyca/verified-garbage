module
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Context
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Proof.Dsa.Contract

import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Copy
import VerifiedGarbage.Proof.Framework.Offset

/-! # The domain checker's precondition

Six outgoing arguments describe the public domain and scratch. The caller
reserves the checker call's stack and writable argument words.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.KeyRandom.CheckCall
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom

/-- The callee's arguments, from the caller's and the stack pointer `sp`. -/
def callVal (s₀ : State) (_sp : BitVec 32) : Nat → BitVec 32
  | 0 => X86.arg s₀ 3
  | 1 => X86.arg s₀ 4
  | 2 => X86.arg s₀ 5
  | 3 => X86.arg s₀ 6
  | 4 => X86.arg s₀ 9
  | _ => X86.arg s₀ 10

/-- The callee's arguments are at the frame's base. -/
def CallSlots (s₀ t : State) : Prop :=
  ∀ i < 6, slot t.mem (rBase s₀) (4 * i) = callVal s₀ (t.gpr .esp) i

/-- What the callee may read and write. -/
def callRd (s₀ : State) : List Region := [argRegion s₀ 3 (X86.arg s₀ 4).toNat]
def callWr (s₀ : State) : List Region :=
  [argRegion s₀ 9 ((X86.arg s₀ 10).toNat * 8), ⟨off (rLow s₀) 24, 24⟩]

theorem rBase_toNat {s₀ : State} (A : KeyABI s₀) : (rBase s₀).toNat = (rLow s₀).toNat + 24 := by
  rw [rBase]; exact off_rLow_toNat A (by decide)

theorem esp_toNat {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) :
    (t.gpr .esp).toNat = (rLow s₀).toNat + 24 := by
  rw [h.rf.esp_toNat, rBase_toNat A]

theorem esp_sub4 {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) :
    (t.gpr .esp - 4).setWidth 64 = off (rLow s₀) 20 := by
  have he := esp_toNat A h
  have := rLow_fit A (d := 192) (by decide)
  apply BitVec.eq_of_toNat_eq
  rw [off_rLow_toNat A (by decide), BitVec.toNat_setWidth, BitVec.toNat_sub, he]
  show (2 ^ 32 - 4 + ((rLow s₀).toNat + 24)) % 2 ^ 32 % 2 ^ 64 = _
  omega

theorem esp_ptr {s₀ t : State} (h : Ready s₀ t) {d : Nat} (hd : d < argOff 11) :
    (t.gpr .esp + BitVec.ofNat 32 d).setWidth 64 = off (rLow s₀) (24 + d) := by
  rw [h.rf.ptr hd, rBase_off]

/-- The callee's arguments, on its entry. -/
theorem ce_arg {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) (C : CallSlots s₀ t) (rd wr : List Region)
    {i : Nat} (hi : i < 6) : X86.arg (t.callEntry.withRegions rd wr) i = callVal s₀ (t.gpr .esp) i := by
  have he := esp_toNat A h
  have := rLow_fit A (d := 192) (by decide)
  rw [arg_withRegions, arg_callEntry (by omega) (by omega), h.rf.ptr (by unfold argOff KeyRandom.frameBytes; omega)]
  exact C i hi

theorem stk_sub (s₀ : State) {d n : Nat} (h : d + n ≤ 144) :
    Region.Sub ⟨off (rLow s₀) d, n⟩ (rStack s₀) := by
  rw [rLow_off]; exact Offset.sub_base _ (by omega)

theorem low_sub (s₀ : State) : Region.Sub ⟨rLow s₀, 20⟩ (rStack s₀) := by
  rw [rLow_eq]; exact Offset.sub_base _ (by decide)

theorem call_pre {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) (C : CallSlots s₀ t) :
    (Proof.Dsa.checkParametersContract abi 108).pre (t.callEntry.withRegions (callRd s₀) (callWr s₀)) := by
  have he := esp_toNat A h
  have hfit := rLow_fit A (d := 192) (by decide)
  have hql := rQBytes_le A
  have hqn := rQBytes_length A
  have hs4 := esp_sub4 A h
  have ha0 : argAddr (t.callEntry.withRegions (callRd s₀) (callWr s₀)) 0 = off (rLow s₀) 24 := by
    rw [argAddr_withRegions, argAddr_callEntry, esp_ptr h (by decide)]
  have hlow : off (rLow s₀) 20 - 108#64 = (s₀.gpr .esp).setWidth 64 - 232#64 := by
    unfold off rLow
    bv_omega_arith
  have relow : rLow s₀ = ((s₀.gpr .esp).setWidth 64 - 232#64) + 88#64 := by
    unfold rLow
    bv_omega_arith
  have d_key_arg : Region.Disjoint (argRegion s₀ 3 (X86.arg s₀ 4).toNat) ⟨off (rLow s₀) 24, 24⟩ :=
    A.stackKeyWide.symm.sub_right (stk_sub s₀ (by omega))
  have d_key_ret : Region.Disjoint (argRegion s₀ 3 (X86.arg s₀ 4).toNat) ⟨off (rLow s₀) 20, 4⟩ :=
    A.stackKeyWide.symm.sub_right (stk_sub s₀ (by omega))
  have d_key_low : Region.Disjoint (argRegion s₀ 3 (X86.arg s₀ 4).toNat) ⟨(s₀.gpr .esp).setWidth 64 - 232#64, 108⟩ :=
    A.stackKeyWide.symm.sub_right (Region.sub_prefix (by decide))
  have d_scr_arg : Region.Disjoint (argRegion s₀ 9 ((X86.arg s₀ 10).toNat * 8)) ⟨off (rLow s₀) 24, 24⟩ :=
    A.stackScratchWide.symm.sub_right (stk_sub s₀ (by omega))
  have d_scr_ret : Region.Disjoint (argRegion s₀ 9 ((X86.arg s₀ 10).toNat * 8)) ⟨off (rLow s₀) 20, 4⟩ :=
    A.stackScratchWide.symm.sub_right (stk_sub s₀ (by omega))
  have d_scr_low : Region.Disjoint (argRegion s₀ 9 ((X86.arg s₀ 10).toNat * 8)) ⟨(s₀.gpr .esp).setWidth 64 - 232#64, 108⟩ :=
    A.stackScratchWide.symm.sub_right (Region.sub_prefix (by decide))
  have d_ret_arg : Region.Disjoint ⟨off (rLow s₀) 20, 4⟩ ⟨off (rLow s₀) 24, 24⟩ :=
    Offset.disjoint _ (by omega) (by omega) (by omega)
  have d_low_arg : Region.Disjoint ⟨(s₀.gpr .esp).setWidth 64 - 232#64, 108⟩ ⟨off (rLow s₀) 24, 24⟩ := by
    rw [relow, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact Offset.base_disjoint _ (by omega) (by omega)
  have d_key_scr := A.keyScratch
  have b_key := A.keyBound
  have b_scr := A.scratchBound
  have p_len := A.lengths
  have p_key := A.keyLength
  have p_scr : Spec.Dsa.scratchWords (X86.arg s₀ 5).toNat ≤ (X86.arg s₀ 10).toNat := by
    have := A.scratchLength; unfold Spec.Dsa.generationScratchWords at this; unfold Spec.Dsa.scratchWords; omega
  have w_lo : 108 ≤ (t.gpr .esp - 4).toNat := by
    rw [BitVec.toNat_sub, he]; show 108 ≤ (2 ^ 32 - 4 + _) % 2 ^ 32
    have lo := A.stackLow
    rw [rLow_toNat A]
    omega
  have w_hi : (t.gpr .esp - 4).toNat + 4 + 24 ≤ 2 ^ 32 := by
    rw [BitVec.toNat_sub, he]; show (2 ^ 32 - 4 + _) % 2 ^ 32 + 4 + 24 ≤ 2 ^ 32; omega
  sig_pre [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [ce_arg A h C (callRd s₀) (callWr s₀) (show 0 < 6 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 1 < 6 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 2 < 6 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 3 < 6 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 4 < 6 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 5 < 6 by decide),
    callVal, ha0, hs4, hlow]
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›
    | exact rfl

end VG.Proof.Dsa.X86.KeyRandom.CheckCall
