module

public import VerifiedGarbage.Impl.Dsa.X86.RandomSign
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Dsa.X86.RandomContext
import VerifiedGarbage.Proof.Dsa.X86.RandomCopy
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Dsa.X86.RandomCallPre`, which this module and modules that import it used -/

section

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
  obtain he := esp_toNat A h
  have := rLow_fit A (d := 200) (by decide)
  apply BitVec.eq_of_toNat_eq
  rw [off_rLow_toNat A (by decide), BitVec.toNat_setWidth, BitVec.toNat_sub, he]
  show (2 ^ 32 - 4 + ((rLow s₀).toNat + 24)) % 2 ^ 32 % 2 ^ 64 = _
  omega_arith

theorem esp_ptr {s₀ t : State} (h : Ready s₀ t) {d : Nat} (hd : d < argOff 13) :
    (t.gpr .esp + BitVec.ofNat 32 d).setWidth 64 = off (rLow s₀) (24 + d) := by
  rw [h.rf.ptr hd, rBase_off]

/-- The signer's arguments, on its entry. -/
theorem ce_arg {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) (C : CallSlots s₀ t) (rd wr : List Region)
    {i : Nat} (hi : i < 11) : X86.arg (t.callEntry.withRegions rd wr) i = callVal s₀ (t.gpr .esp) i := by
  obtain he := esp_toNat A h
  have := rLow_fit A (d := 200) (by decide)
  rw [arg_withRegions, arg_callEntry (by omega_arith) (by omega_arith), h.rf.ptr (by unfold argOff Random.frameBytes; omega_arith)]
  exact C i hi

theorem stk_sub (s₀ : State) {d n : Nat} (h : d + n ≤ 144) :
    Region.Sub ⟨off (rLow s₀) d, n⟩ (rStack s₀) := by
  rw [rLow_off]; exact Offset.sub_base _ (by omega_arith)

theorem call_pre {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) (C : CallSlots s₀ t) :
    (Spec.Dsa.signContract abi 108).pre (t.callEntry.withRegions (callRd s₀) (callWr s₀)) := by
  obtain he := esp_toNat A h
  obtain hfit := rLow_fit A (d := 200) (by decide)
  obtain hql := rQBytes_le A
  obtain hqn := rQBytes_length A
  obtain hs4 := esp_sub4 A h
  obtain hn : (t.gpr .esp + BitVec.ofNat 32 oNonce).setWidth 64 = off (rLow s₀) 112 :=
    esp_ptr h (d := oNonce) (by decide)
  obtain hnn : (t.gpr .esp + BitVec.ofNat 32 oNonce).toNat = (rLow s₀).toNat + 112 := by
    rw [BitVec.toNat_add, he, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := oNonce) (by decide)]
    unfold oNonce; omega_arith
  obtain ha0 : argAddr (t.callEntry.withRegions (callRd s₀) (callWr s₀)) 0 = off (rLow s₀) 24 := by
    rw [argAddr_withRegions, argAddr_callEntry, esp_ptr h (by decide)]
  obtain hlow : off (rLow s₀) 20 - 108#64 = (s₀.gpr .esp).setWidth 64 - 232#64 := by
    unfold off rLow
    bv_omega_arith
  obtain relow : rLow s₀ = ((s₀.gpr .esp).setWidth 64 - 232#64) + 88#64 := by
    unfold rLow
    bv_omega_arith
  obtain d_out_non : Region.Disjoint (argRegion s₀ 0 (X86.arg s₀ 1).toNat) ⟨off (rLow s₀) 112, (X86.arg s₀ 6).toNat⟩ :=
    A.stackOutWide.symm.sub_right (stk_sub s₀ (by omega_arith))
  obtain d_out_arg : Region.Disjoint (argRegion s₀ 0 (X86.arg s₀ 1).toNat) ⟨off (rLow s₀) 24, 44⟩ :=
    A.stackOutWide.symm.sub_right (stk_sub s₀ (by omega_arith))
  obtain d_out_ret : Region.Disjoint (argRegion s₀ 0 (X86.arg s₀ 1).toNat) ⟨off (rLow s₀) 20, 4⟩ :=
    A.stackOutWide.symm.sub_right (stk_sub s₀ (by omega_arith))
  obtain d_out_low : Region.Disjoint (argRegion s₀ 0 (X86.arg s₀ 1).toNat) ⟨(s₀.gpr .esp).setWidth 64 - 232#64, 108⟩ :=
    A.stackOutWide.symm.sub_right (Region.sub_prefix (by decide))
  obtain d_key_non : Region.Disjoint (argRegion s₀ 3 (X86.arg s₀ 4).toNat) ⟨off (rLow s₀) 112, (X86.arg s₀ 6).toNat⟩ :=
    A.stackKeyWide.symm.sub_right (stk_sub s₀ (by omega_arith))
  obtain d_key_arg : Region.Disjoint (argRegion s₀ 3 (X86.arg s₀ 4).toNat) ⟨off (rLow s₀) 24, 44⟩ :=
    A.stackKeyWide.symm.sub_right (stk_sub s₀ (by omega_arith))
  obtain d_key_ret : Region.Disjoint (argRegion s₀ 3 (X86.arg s₀ 4).toNat) ⟨off (rLow s₀) 20, 4⟩ :=
    A.stackKeyWide.symm.sub_right (stk_sub s₀ (by omega_arith))
  obtain d_key_low : Region.Disjoint (argRegion s₀ 3 (X86.arg s₀ 4).toNat) ⟨(s₀.gpr .esp).setWidth 64 - 232#64, 108⟩ :=
    A.stackKeyWide.symm.sub_right (Region.sub_prefix (by decide))
  obtain d_dig_non : Region.Disjoint (argRegion s₀ 7 (X86.arg s₀ 8).toNat) ⟨off (rLow s₀) 112, (X86.arg s₀ 6).toNat⟩ :=
    A.stackDigestWide.symm.sub_right (stk_sub s₀ (by omega_arith))
  obtain d_dig_arg : Region.Disjoint (argRegion s₀ 7 (X86.arg s₀ 8).toNat) ⟨off (rLow s₀) 24, 44⟩ :=
    A.stackDigestWide.symm.sub_right (stk_sub s₀ (by omega_arith))
  obtain d_dig_ret : Region.Disjoint (argRegion s₀ 7 (X86.arg s₀ 8).toNat) ⟨off (rLow s₀) 20, 4⟩ :=
    A.stackDigestWide.symm.sub_right (stk_sub s₀ (by omega_arith))
  obtain d_dig_low : Region.Disjoint (argRegion s₀ 7 (X86.arg s₀ 8).toNat) ⟨(s₀.gpr .esp).setWidth 64 - 232#64, 108⟩ :=
    A.stackDigestWide.symm.sub_right (Region.sub_prefix (by decide))
  obtain d_scr_non : Region.Disjoint (argRegion s₀ 11 ((X86.arg s₀ 12).toNat * 8)) ⟨off (rLow s₀) 112, (X86.arg s₀ 6).toNat⟩ :=
    A.stackScratchWide.symm.sub_right (stk_sub s₀ (by omega_arith))
  obtain d_scr_arg : Region.Disjoint (argRegion s₀ 11 ((X86.arg s₀ 12).toNat * 8)) ⟨off (rLow s₀) 24, 44⟩ :=
    A.stackScratchWide.symm.sub_right (stk_sub s₀ (by omega_arith))
  obtain d_scr_ret : Region.Disjoint (argRegion s₀ 11 ((X86.arg s₀ 12).toNat * 8)) ⟨off (rLow s₀) 20, 4⟩ :=
    A.stackScratchWide.symm.sub_right (stk_sub s₀ (by omega_arith))
  obtain d_scr_low : Region.Disjoint (argRegion s₀ 11 ((X86.arg s₀ 12).toNat * 8)) ⟨(s₀.gpr .esp).setWidth 64 - 232#64, 108⟩ :=
    A.stackScratchWide.symm.sub_right (Region.sub_prefix (by decide))
  obtain d_non_arg : Region.Disjoint ⟨off (rLow s₀) 112, (X86.arg s₀ 6).toNat⟩ ⟨off (rLow s₀) 24, 44⟩ :=
    Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  obtain d_ret_non : Region.Disjoint ⟨off (rLow s₀) 20, 4⟩ ⟨off (rLow s₀) 112, (X86.arg s₀ 6).toNat⟩ :=
    Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  obtain d_ret_arg : Region.Disjoint ⟨off (rLow s₀) 20, 4⟩ ⟨off (rLow s₀) 24, 44⟩ :=
    Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  obtain d_low_non : Region.Disjoint ⟨(s₀.gpr .esp).setWidth 64 - 232#64, 108⟩ ⟨off (rLow s₀) 112, (X86.arg s₀ 6).toNat⟩ := by
    rw [relow, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact Offset.base_disjoint _ (by omega_arith) (by omega_arith)
  obtain d_low_arg : Region.Disjoint ⟨(s₀.gpr .esp).setWidth 64 - 232#64, 108⟩ ⟨off (rLow s₀) 24, 44⟩ := by
    rw [relow, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact Offset.base_disjoint _ (by omega_arith) (by omega_arith)
  have d_out_key := A.outKey
  have d_out_dig := A.outDigest
  have d_out_scr := A.outScratch
  have d_key_scr := A.keyScratch
  have d_dig_scr := A.digestScratch
  have b_out := A.outBound
  have b_key := A.keyBound
  have b_dig := A.digestBound
  have b_scr := A.scratchBound
  obtain b_non : (t.gpr .esp + BitVec.ofNat 32 oNonce).toNat + (X86.arg s₀ 6).toNat ≤ 2 ^ 32 := by
    rw [hnn]; omega_arith
  have p_len := A.lengths
  have p_out := A.outLength
  have p_key := A.keyLength
  obtain p_scr : Spec.Dsa.scratchWords (X86.arg s₀ 5).toNat ≤ (X86.arg s₀ 12).toNat := by
    have := A.scratchLength; unfold Spec.Dsa.randomSignScratchWords at this; omega_arith
  obtain w_lo : 108 ≤ (t.gpr .esp - 4).toNat := by
    rw [BitVec.toNat_sub, he]; show 108 ≤ (2 ^ 32 - 4 + _) % 2 ^ 32
    have lo := A.stackLow
    rw [rLow_toNat A]
    omega_arith
  obtain w_hi : (t.gpr .esp - 4).toNat + 4 + 44 ≤ 2 ^ 32 := by
    rw [BitVec.toNat_sub, he]; show (2 ^ 32 - 4 + _) % 2 ^ 32 + 4 + 44 ≤ 2 ^ 32; omega_arith
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

end

end

/-!
# The signer's arguments (x86)

`callArgs` copies the caller's arguments the signer takes, and the nonce's
address, to the frame's first eleven words (`CallSlots`).
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random VG.Impl.Dsa.X86.RandomSign

/-- One argument's copy. -/
theorem copyArg_ok {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) {j i : Nat} (hj : j < 13)
    (hi : 4 * i + 4 ≤ 44) {is : List Instr} {Q : State → Prop}
    (k : ∀ u, Ready s₀ u → u.mem = t.mem.writeW (off (rBase s₀) (4 * i)) (X86.arg s₀ j) →
      Keeps [.eax] t u → WP isa (.block is) u Q) :
    WP isa (.block (copyArg j i ++ is)) t Q := by
  unfold copyArg
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (h.argSrc A hj) fun u₁ v₁ _ => ?_
  have h₁ := h.upd v₁ (by decide)
  refine wp_slot h₁.rf (by unfold Random.frameBytes; omega_using [hi]) v₁.gpr fun u₂ f₂ m₂ g₂ r₂ w₂ _ _ => ?_
  refine k u₂ (h₁.congr (rs := []) ⟨fun r _ => by rw [g₂], r₂, w₂⟩
    (by rw [m₂]; exact frame_store s₀ _ (by unfold Random.frameBytes; omega_using [hi]) _)) (by rw [m₂, v₁.mem])
    (v₁.keeps.trans ⟨fun r _ => by rw [g₂], r₂, w₂⟩)

/-- The memory after `callArgs`, from `m`, with the stack pointer `sp`. -/
def argsMem (s₀ : State) (m : Mem) (sp : BitVec 32) : Mem :=
  (((((((((((m.writeW (off (rBase s₀) (4 * 0)) (X86.arg s₀ 0)).writeW (off (rBase s₀) (4 * 1)) (X86.arg s₀ 1)).writeW
    (off (rBase s₀) (4 * 2)) (X86.arg s₀ 3)).writeW (off (rBase s₀) (4 * 3)) (X86.arg s₀ 4)).writeW
    (off (rBase s₀) (4 * 4)) (X86.arg s₀ 5)).writeW (off (rBase s₀) 20) (sp + BitVec.ofNat 32 oNonce)).writeW
    (off (rBase s₀) (4 * 6)) (X86.arg s₀ 6)).writeW (off (rBase s₀) (4 * 7)) (X86.arg s₀ 7)).writeW
    (off (rBase s₀) (4 * 8)) (X86.arg s₀ 8)).writeW (off (rBase s₀) (4 * 9)) (X86.arg s₀ 11)).writeW
    (off (rBase s₀) (4 * 10)) (X86.arg s₀ 12))

theorem argsMem_slots (s₀ : State) (m : Mem) (sp : BitVec 32) :
    ∀ i < 11, slot (argsMem s₀ m sp) (rBase s₀) (4 * i) = callVal s₀ sp i := by
  intro i hi
  unfold argsMem
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ =>
    simp (disch := decide) only [slot_write_self, slot_write_ne, Nat.reduceMul, callVal]

/-- A store within the range `(o, n)`. -/
theorem store_in (B : Addr) (m : Mem) {d o n : Nat} (v : BitVec 32) {rs : List (Nat × Nat)}
    (hm : (o, n) ∈ rs) (h₁ : o ≤ d) (h₂ : d + 4 ≤ o + n) (hb : d + 4 ≤ 2 ^ 64) :
    Outs B rs m (m.writeW (off B d) v) :=
  Outs.of_outside ((writeW32_outside m B v hb).mono h₁ h₂) hm

theorem argsMem_outs (s₀ : State) (m : Mem) (sp : BitVec 32) : Outs (rBase s₀) [(0, 44)] m (argsMem s₀ m sp) := by
  unfold argsMem
  have e := fun {m : Mem} {d : Nat} (v : BitVec 32) (h : d + 4 ≤ 44) =>
    store_in (rBase s₀) m (rs := [(0, 44)]) (o := 0) (n := 44) (d := d) v (List.mem_singleton_self _)
      (Nat.zero_le _) h (by omega_using [h])
  exact ((((((((((e _ (by decide)).trans (e _ (by decide))).trans (e _ (by decide))).trans
    (e _ (by decide))).trans (e _ (by decide))).trans (e _ (by decide))).trans
    (e _ (by decide))).trans (e _ (by decide))).trans (e _ (by decide))).trans
    (e _ (by decide))).trans (e _ (by decide))

theorem callArgs_ok {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ u, Ready s₀ u → u.mem = argsMem s₀ t.mem (t.gpr .esp) → Keeps [.eax] t u → WP isa (.block is) u Q) :
    WP isa (.block (callArgs ++ is)) t Q := by
  unfold callArgs
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine copyArg_ok A h (by decide) (by decide) fun u₁ h₁ m₁ k₁ => ?_
  refine copyArg_ok A h₁ (by decide) (by decide) fun u₂ h₂ m₂ k₂ => ?_
  refine copyArg_ok A h₂ (by decide) (by decide) fun u₃ h₃ m₃ k₃ => ?_
  refine copyArg_ok A h₃ (by decide) (by decide) fun u₄ h₄ m₄ k₄ => ?_
  refine copyArg_ok A h₄ (by decide) (by decide) fun u₅ h₅ m₅ k₅ => ?_
  refine wp_movS rfl fun u₆ v₆ _ => wp_addi fun u₇ v₇ => ?_
  have h₇ := (h₅.upd v₆ (by decide)).upd v₇ (by decide)
  refine wp_slot h₇.rf (by decide) v₇.gpr fun u₈ f₈ m₈ g₈ r₈ w₈ _ _ => ?_
  have k₈ : Keeps [.eax] u₅ u₈ := ((v₆.keeps).trans v₇.keeps).trans ⟨fun r _ => by rw [g₈], r₈, w₈⟩
  have h₈ : Ready s₀ u₈ := h₅.congr k₈ (by
    rw [m₈, v₇.mem, v₆.mem]; exact frame_store s₀ _ (by decide) _)
  refine copyArg_ok A h₈ (by decide) (by decide) fun u₉ h₉ m₉ k₉ => ?_
  refine copyArg_ok A h₉ (by decide) (by decide) fun u₁₀ h₁₀ m₁₀ k₁₀ => ?_
  refine copyArg_ok A h₁₀ (by decide) (by decide) fun u₁₁ h₁₁ m₁₁ k₁₁ => ?_
  refine copyArg_ok A h₁₁ (by decide) (by decide) fun u₁₂ h₁₂ m₁₂ k₁₂ => ?_
  refine copyArg_ok A h₁₂ (by decide) (by decide) fun u₁₃ h₁₃ m₁₃ k₁₃ => ?_
  have kk : Keeps [.eax] t u₁₃ := (((((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₈).trans k₉).trans
    k₁₀).trans k₁₁).trans k₁₂).trans k₁₃
  refine k u₁₃ h₁₃ ?_ kk
  have esp : u₅.gpr .esp = t.gpr .esp := ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).1 _ (by decide)
  rw [m₁₃, m₁₂, m₁₁, m₁₀, m₉, m₈, v₇.mem, v₆.mem, m₅, m₄, m₃, m₂, m₁, v₆.gpr, esp]
  rfl

end VG.Proof.Dsa.X86
