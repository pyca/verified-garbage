module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPre
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# `vg_rsa_private_checked` on PPC64LE: the frame

The frame (`Impl/Rsa/PPC64LE/Priv.lean`) is all of the stack the function
uses, `kR`, from its base `fb`; the push makes its local variable space `fr`
writable. `saveRegs_ok`: the saves of `r24`–`r29` and of the return address.
`restore_ok`: the restores give back the caller's registers.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv
open VG.Proof.Bignum.PPC64LE (Keep)

/-! ## Addresses -/

/-- The frame's local variable space, which its push makes writable. -/
abbrev fr (s : State) : Region := ⟨fb s + BitVec.ofNat 64 32, frameBytes - 32⟩

theorem frameR_eq (s : State) : frameR frameBytes s = fr s := rfl

theorem fb_toNat {s : State} (h : frameBytes ≤ s.sp.toNat) : (fb s).toNat + frameBytes = s.sp.toNat := by
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes at *; omega

/-- A region of the frame is in the stack the function uses. -/
theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    Region.Sub ⟨fb s + BitVec.ofNat 64 d, n⟩ (kR s) := Offset.sub_base _ h

theorem frame_contains (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    (kR s).Contains (fb s + BitVec.ofNat 64 d) n :=
  Offset.contains_base _ h (by unfold frameBytes at h; omega)

/-- The local variable space is writable. -/
theorem in_fr (s : State) (rs : List Region) {d n : Nat} (h₁ : 32 ≤ d) (h : d + n ≤ frameBytes) :
    InRegions (fr s :: rs) (fb s + BitVec.ofNat 64 d) n :=
  ⟨_, List.mem_cons_self .., Offset.contains _ h₁ (by unfold frameBytes at *; omega)
    (by unfold frameBytes; omega)⟩

theorem in_fr' (s : State) (rd rs : List Region) {d n : Nat} (h₁ : 32 ≤ d) (h : d + n ≤ frameBytes) :
    InRegions (rd ++ fr s :: rs) (fb s + BitVec.ofNat 64 d) n := by
  obtain ⟨r, hr, hc⟩ := in_fr s rs h₁ h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- Our stack arguments, from the frame. -/
theorem stackArgAddr_fb (s : State) (j : Nat) :
    stackArgAddr s j = fb s + BitVec.ofNat 64 (arg j) := by
  have e : BitVec.ofNat 64 (arg j) = BitVec.ofNat 64 frameBytes + BitVec.ofNat 64 (32 + 8 * (8 + j)) := by
    rw [BitVec.ofNat_add_ofNat]; unfold arg; congr 1; omega
  rw [stackArgAddr, e, ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- A call's stack arguments, in the frame. -/
theorem stackArgAddr_in (t : State) (j : Nat) :
    stackArgAddr t j = t.sp + BitVec.ofNat 64 (96 + 8 * j) := by
  rw [stackArgAddr, show 32 + 8 * (8 + j) = 96 + 8 * j by omega]

theorem stackArgAddr_eq (s : State) (j : Nat) :
    stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, Nat.add_zero]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, show 32 + 8 * 8 + 8 * j = 32 + 8 * (8 + j) by omega]

theorem in_aR {s : State} {j : Nat} (hj : j < 12) : (aR s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)

/-! ## The saves -/

/-- The slots of our caller's `r24`–`r29`. -/
def saved : List (Reg × Nat) :=
  [(.r24, oSave), (.r25, oSave + 8), (.r26, oSave + 16), (.r27, oSave + 24), (.r28, oSave + 32),
    (.r29, oSave + 40)]

/-- The callee-saved registers other than `r24`–`r29`. -/
def hiRegs : List Reg := [.r2, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r30, .r31]

theorem save_eq : save = ([.addSp .r12 0] : List Instr) ++ Spill.saveCode .r12 saved ++
    ([.mflr .r0, .store .d .r0 .r12 oLr] : List Instr) ++
    ([.logic .or .r24 .r3 .r3, .logic .or .r25 .r5 .r5, .logic .or .r26 .r6 .r6, .logic .or .r27 .r7 .r7,
      .logic .or .r28 .r8 .r8, .logic .or .r29 .r9 .r9] : List Instr) :=
  rfl

theorem restore_eq :
    restore = ([.addSp .r12 0, .load .d .r0 .r12 oLr, .mtlr .r0] : List Instr) ++ Spill.restoreCode .r12 saved :=
  rfl

theorem saved_offs : ∀ p ∈ saved, oSave ≤ p.2 ∧ p.2 + 8 ≤ oSave + 48 := by decide

theorem saved_ho : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 32768 := by decide

theorem preserved_split {r : Reg} (h : r ∈ preserved) : r ∈ saved.map Prod.fst ∨ r ∈ hiRegs := by
  revert r; decide

end VG.Proof.Rsa.PPC64LE.Priv
