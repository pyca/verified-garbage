module

public import VerifiedGarbage.Proof.Dsa.X86.RandomSample
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The supplied-nonce signer's precondition (x86)

`callArgs` stores the signer's eleven arguments at the frame's base
(`CallSlots`): the caller's buffers and lengths, and the nonce in the frame.
Its return address and the 20 bytes of stack below it lie in the 24 bytes
below the frame, so with the caller's buffers apart from all of the
signer's stack, `vg_dsa_sign`'s contract holds on its entry (`call_pre`).
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random

/-- The signer's arguments, from the caller's and the stack pointer `sp`. -/
def callVal (s₀ : State) (sp : BitVec 32) : Nat → BitVec 32
  | 0 => X86.arg s₀ 0
  | 1 => X86.arg s₀ 1
  | 2 => X86.arg s₀ 3
  | 3 => X86.arg s₀ 4
  | 4 => X86.arg s₀ 5
  | 5 => sp + BitVec.ofNat 32 oNonce
  | 6 => X86.arg s₀ 6
  | 7 => X86.arg s₀ 7
  | 8 => X86.arg s₀ 8
  | 9 => X86.arg s₀ 11
  | _ => X86.arg s₀ 12

/-- The signer's arguments are at the frame's base. -/
def CallSlots (s₀ t : State) : Prop :=
  ∀ i < 11, slot t.mem (rBase s₀) (4 * i) = callVal s₀ (t.gpr .esp) i

/-- What the signer may read and write. -/
def callRd (s₀ : State) : List Region :=
  [argRegion s₀ 3 (X86.arg s₀ 4).toNat, ⟨off (rLow s₀) 112, (X86.arg s₀ 6).toNat⟩,
    argRegion s₀ 7 (X86.arg s₀ 8).toNat]
def callWr (s₀ : State) : List Region :=
  [argRegion s₀ 0 (X86.arg s₀ 1).toNat, argRegion s₀ 11 ((X86.arg s₀ 12).toNat * 8), ⟨off (rLow s₀) 24, 44⟩]

theorem rBase_toNat {s₀ : State} (A : RandomSignABI s₀) : (rBase s₀).toNat = (rLow s₀).toNat + 24 := by
  rw [rBase]; exact off_rLow_toNat A (by decide)

theorem esp_toNat {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) :
    (t.gpr .esp).toNat = (rLow s₀).toNat + 24 := by
  rw [h.rf.esp_toNat, rBase_toNat A]

theorem esp_sub4 {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) :
    (t.gpr .esp - 4).setWidth 64 = off (rLow s₀) 20 := by
  have he := esp_toNat A h
  have := rLow_fit A (d := 200) (by decide)
  apply BitVec.eq_of_toNat_eq
  rw [off_rLow_toNat A (by decide), BitVec.toNat_setWidth, BitVec.toNat_sub, he]
  show (2 ^ 32 - 4 + ((rLow s₀).toNat + 24)) % 2 ^ 32 % 2 ^ 64 = _
  omega

theorem esp_ptr {s₀ t : State} (h : Ready s₀ t) {d : Nat} (hd : d < argOff 13) :
    (t.gpr .esp + BitVec.ofNat 32 d).setWidth 64 = off (rLow s₀) (24 + d) := by
  rw [h.rf.ptr hd, rBase_off]

/-- The signer's arguments, on its entry. -/
theorem ce_arg {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) (C : CallSlots s₀ t) (rd wr : List Region)
    {i : Nat} (hi : i < 11) : X86.arg (t.callEntry.withRegions rd wr) i = callVal s₀ (t.gpr .esp) i := by
  have he := esp_toNat A h
  have := rLow_fit A (d := 200) (by decide)
  rw [arg_withRegions, arg_callEntry (by omega) (by omega), h.rf.ptr (by unfold argOff Random.frameBytes; omega)]
  exact C i hi

theorem stk_sub (s₀ : State) {d n : Nat} (h : d + n ≤ 144) :
    Region.Sub ⟨off (rLow s₀) d, n⟩ (rStack s₀) := Offset.sub_base _ h

theorem low_sub (s₀ : State) : Region.Sub ⟨rLow s₀, 20⟩ (rStack s₀) := by
  have := Offset.sub_base (rLow s₀) (d := 0) (n := 20) (k := 144) (by decide)
  rwa [BitVec.add_zero] at this

theorem call_pre {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) (C : CallSlots s₀ t) :
    (Spec.Dsa.signContract abi 32).pre (t.callEntry.withRegions (callRd s₀) (callWr s₀)) := by
  have he := esp_toNat A h
  have hfit := rLow_fit A (d := 200) (by decide)
  have hql := rQBytes_le A
  have hqn := rQBytes_length A
  have hs4 := esp_sub4 A h
  have hn : (t.gpr .esp + BitVec.ofNat 32 oNonce).setWidth 64 = off (rLow s₀) 112 :=
    esp_ptr h (d := oNonce) (by decide)
  have hnn : (t.gpr .esp + BitVec.ofNat 32 oNonce).toNat = (rLow s₀).toNat + 112 := by
    rw [BitVec.toNat_add, he, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := oNonce) (by decide)]
    unfold oNonce; omega
  have ha0 : argAddr (t.callEntry.withRegions (callRd s₀) (callWr s₀)) 0 = off (rLow s₀) 24 := by
    rw [argAddr_withRegions, argAddr_callEntry, esp_ptr h (by decide)]
  have hlow : off (rLow s₀) 20 - 32#64 = (s₀.gpr .esp).setWidth 64 - 156#64 := by
    unfold off rLow
    bv_omega
  have relow : rLow s₀ = ((s₀.gpr .esp).setWidth 64 - 156#64) + 12#64 := by
    unfold rLow
    bv_omega
  have d_out_non : Region.Disjoint (argRegion s₀ 0 (X86.arg s₀ 1).toNat) ⟨off (rLow s₀) 112, (X86.arg s₀ 6).toNat⟩ :=
    A.stackOut.symm.sub_right (stk_sub s₀ (by omega))
  have d_out_arg : Region.Disjoint (argRegion s₀ 0 (X86.arg s₀ 1).toNat) ⟨off (rLow s₀) 24, 44⟩ :=
    A.stackOut.symm.sub_right (stk_sub s₀ (by omega))
  have d_out_ret : Region.Disjoint (argRegion s₀ 0 (X86.arg s₀ 1).toNat) ⟨off (rLow s₀) 20, 4⟩ :=
    A.stackOut.symm.sub_right (stk_sub s₀ (by omega))
  have d_out_low : Region.Disjoint (argRegion s₀ 0 (X86.arg s₀ 1).toNat) ⟨(s₀.gpr .esp).setWidth 64 - 156#64, 32⟩ :=
    A.stackOutWide.symm.sub_right (Region.sub_prefix (by decide))
  have d_key_non : Region.Disjoint (argRegion s₀ 3 (X86.arg s₀ 4).toNat) ⟨off (rLow s₀) 112, (X86.arg s₀ 6).toNat⟩ :=
    A.stackKey.symm.sub_right (stk_sub s₀ (by omega))
  have d_key_arg : Region.Disjoint (argRegion s₀ 3 (X86.arg s₀ 4).toNat) ⟨off (rLow s₀) 24, 44⟩ :=
    A.stackKey.symm.sub_right (stk_sub s₀ (by omega))
  have d_key_ret : Region.Disjoint (argRegion s₀ 3 (X86.arg s₀ 4).toNat) ⟨off (rLow s₀) 20, 4⟩ :=
    A.stackKey.symm.sub_right (stk_sub s₀ (by omega))
  have d_key_low : Region.Disjoint (argRegion s₀ 3 (X86.arg s₀ 4).toNat) ⟨(s₀.gpr .esp).setWidth 64 - 156#64, 32⟩ :=
    A.stackKeyWide.symm.sub_right (Region.sub_prefix (by decide))
  have d_dig_non : Region.Disjoint (argRegion s₀ 7 (X86.arg s₀ 8).toNat) ⟨off (rLow s₀) 112, (X86.arg s₀ 6).toNat⟩ :=
    A.stackDigest.symm.sub_right (stk_sub s₀ (by omega))
  have d_dig_arg : Region.Disjoint (argRegion s₀ 7 (X86.arg s₀ 8).toNat) ⟨off (rLow s₀) 24, 44⟩ :=
    A.stackDigest.symm.sub_right (stk_sub s₀ (by omega))
  have d_dig_ret : Region.Disjoint (argRegion s₀ 7 (X86.arg s₀ 8).toNat) ⟨off (rLow s₀) 20, 4⟩ :=
    A.stackDigest.symm.sub_right (stk_sub s₀ (by omega))
  have d_dig_low : Region.Disjoint (argRegion s₀ 7 (X86.arg s₀ 8).toNat) ⟨(s₀.gpr .esp).setWidth 64 - 156#64, 32⟩ :=
    A.stackDigestWide.symm.sub_right (Region.sub_prefix (by decide))
  have d_scr_non : Region.Disjoint (argRegion s₀ 11 ((X86.arg s₀ 12).toNat * 8)) ⟨off (rLow s₀) 112, (X86.arg s₀ 6).toNat⟩ :=
    A.stackScratch.symm.sub_right (stk_sub s₀ (by omega))
  have d_scr_arg : Region.Disjoint (argRegion s₀ 11 ((X86.arg s₀ 12).toNat * 8)) ⟨off (rLow s₀) 24, 44⟩ :=
    A.stackScratch.symm.sub_right (stk_sub s₀ (by omega))
  have d_scr_ret : Region.Disjoint (argRegion s₀ 11 ((X86.arg s₀ 12).toNat * 8)) ⟨off (rLow s₀) 20, 4⟩ :=
    A.stackScratch.symm.sub_right (stk_sub s₀ (by omega))
  have d_scr_low : Region.Disjoint (argRegion s₀ 11 ((X86.arg s₀ 12).toNat * 8)) ⟨(s₀.gpr .esp).setWidth 64 - 156#64, 32⟩ :=
    A.stackScratchWide.symm.sub_right (Region.sub_prefix (by decide))
  have d_non_arg : Region.Disjoint ⟨off (rLow s₀) 112, (X86.arg s₀ 6).toNat⟩ ⟨off (rLow s₀) 24, 44⟩ :=
    Offset.disjoint _ (by omega) (by omega) (by omega)
  have d_ret_non : Region.Disjoint ⟨off (rLow s₀) 20, 4⟩ ⟨off (rLow s₀) 112, (X86.arg s₀ 6).toNat⟩ :=
    Offset.disjoint _ (by omega) (by omega) (by omega)
  have d_ret_arg : Region.Disjoint ⟨off (rLow s₀) 20, 4⟩ ⟨off (rLow s₀) 24, 44⟩ :=
    Offset.disjoint _ (by omega) (by omega) (by omega)
  have d_low_non : Region.Disjoint ⟨(s₀.gpr .esp).setWidth 64 - 156#64, 32⟩ ⟨off (rLow s₀) 112, (X86.arg s₀ 6).toNat⟩ := by
    rw [relow, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact Offset.base_disjoint _ (by omega) (by omega)
  have d_low_arg : Region.Disjoint ⟨(s₀.gpr .esp).setWidth 64 - 156#64, 32⟩ ⟨off (rLow s₀) 24, 44⟩ := by
    rw [relow, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact Offset.base_disjoint _ (by omega) (by omega)
  have d_out_key := A.outKey
  have d_out_dig := A.outDigest
  have d_out_scr := A.outScratch
  have d_key_scr := A.keyScratch
  have d_dig_scr := A.digestScratch
  have b_out := A.outBound
  have b_key := A.keyBound
  have b_dig := A.digestBound
  have b_scr := A.scratchBound
  have b_non : (t.gpr .esp + BitVec.ofNat 32 oNonce).toNat + (X86.arg s₀ 6).toNat ≤ 2 ^ 32 := by
    rw [hnn]; omega
  have p_len := A.lengths
  have p_out := A.outLength
  have p_key := A.keyLength
  have p_scr : Spec.Dsa.scratchWords (X86.arg s₀ 5).toNat ≤ (X86.arg s₀ 12).toNat := by
    have := A.scratchLength; unfold Spec.Dsa.randomSignScratchWords at this; omega
  have w_lo : 32 ≤ (t.gpr .esp - 4).toNat := by
    rw [BitVec.toNat_sub, he]; show 32 ≤ (2 ^ 32 - 4 + _) % 2 ^ 32
    have lo := A.stackLow
    rw [rLow_toNat A]
    omega
  have w_hi : (t.gpr .esp - 4).toNat + 4 + 44 ≤ 2 ^ 32 := by
    rw [BitVec.toNat_sub, he]; show (2 ^ 32 - 4 + _) % 2 ^ 32 + 4 + 44 ≤ 2 ^ 32; omega
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [ce_arg A h C (callRd s₀) (callWr s₀) (show 0 < 11 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 1 < 11 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 2 < 11 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 3 < 11 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 4 < 11 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 5 < 11 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 6 < 11 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 7 < 11 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 8 < 11 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 9 < 11 by decide),
    ce_arg A h C (callRd s₀) (callWr s₀) (show 10 < 11 by decide),
    callVal, ha0, hs4, hlow, hn]
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›
    | exact rfl

end VG.Proof.Dsa.X86
