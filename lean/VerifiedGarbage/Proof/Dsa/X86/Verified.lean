module

public import VerifiedGarbage.Impl.Dsa.X86.Entry
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.TCB.X86.Target

import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Dsa.X86.SharedTiming
import VerifiedGarbage.Proof.Dsa.X86.Installed
import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.PackedKeyBuffers
import VerifiedGarbage.Proof.Dsa.X86.SignSized
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86.SigningABI
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Dsa.X86.VerifyingOperation
import VerifiedGarbage.Proof.Dsa.X86.ReturnFrame
import VerifiedGarbage.Proof.Dsa.X86.WidthDispatch
import VerifiedGarbage.Proof.Dsa.X86.EntrySave
import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
/-! # Complete x86 DSA certificates against the shared contracts -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/SigningInstalled.lean`, which only this module imported.
section

/-! # Signing original caller bytes after cdecl argument installation -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem signingInstalled_spec {s t : State} (A : SigningABI s)
    (I : Installed (argumentPointer s 9) ((arg s 10).toNat * 8) Entry.signArguments 2 4 6 s t) :
    let result := Spec.Dsa.signBytes (arg s 4).toNat (arg s 6).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 7) (arg s 8).toNat)
    WP isa (Entry.sized true (arg s 4).toNat (arg s 6).toNat) t fun sf =>
      (sf.gpr .eax).toNat = Spec.Dsa.signStatus result ∧
      Spec.Rsa.bytesAt sf.mem (argumentPointer s 0) (2 * (arg s 6).toNat) =
        result.getD (List.replicate (2 * (arg s 6).toNat) 0) ∧
      Keeps powerClob t sf ∧
      StackOutputFrame (t.gpr .esp) (argumentPointer s 9) (argumentPointer s 0) usedBytes (2 * (arg s 6).toNat) t.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved t.mem (off (argumentPointer s 9)) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off (argumentPointer s 9)) regs Entry.savedRegisters := by
  dsimp only
  have L : 0 < (arg s 4).toNat ∧ 0 < (arg s 6).toNat := by
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega
  obtain ⟨Key, KeyBytes⟩ := I.input (by decide : (2, .p) ∈ Entry.signArguments) A.keyBound
    (by rw [A.rd, A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨Nonce, NonceBytes⟩ := I.input (by decide : (5, .nonce) ∈ Entry.signArguments) A.nonceBound
    (by rw [A.rd, A.wr]; simp) A.nonceScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowNonce.symm)
  obtain ⟨D, DigestBytes⟩ := I.input (by decide : (7, .digest) ∈ Entry.signArguments) A.digestBound
    (by rw [A.rd, A.wr]; simp) A.digestScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowDigest.symm)
  obtain ⟨Qptr, Gptr, Yptr, Xptr⟩ := I.pointers (by decide)
  obtain ⟨P, Q, G, Y, X, KeyValue⟩ := privateKey_buffers Key L.1 L.2
    (by have := A.keyLength; omega) KeyBytes Qptr Gptr Yptr Xptr
  apply signSized_spec (out := arg s 0) I.scr A.used A.lengths P Q G Y X Nonce D rfl rfl rfl rfl rfl rfl
    (congrArg BitVec.toNat (I.arguments (8, .digestLen) (by decide))) DigestBytes
    (I.arguments (0, .out) (by decide))
    (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using I.arguments (6, .qLen) (by decide))
    (by have := A.outBound; have := A.outLength; omega)
    ?_ (by rw [← A.outLength]; exact A.outScratch.symm)
    (by simpa only [Spec.Rsa.bytesAt, List.length_map, List.length_range] using A.keyLength)
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]) KeyValue
    (congrArg Spec.Dsa.decodeBE NonceBytes.symm)
  intro e k he
  rw [I.keeps.2.2, A.wr]
  refine ⟨_, List.mem_cons_self, Offset.contains_base _ (by have := A.outLength; omega) ?_⟩
  have := A.outBound
  have := A.outLength
  omega

end VG.Proof.Dsa.X86
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/SigningOperation.lean`, which only this module imported.
section

/-! # Complete functional and cdecl verification of the x86 signer -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem signingOperation_spec {s : State} (A : SigningABI s) :
    let result := Spec.Dsa.signBytes (arg s 4).toNat (arg s 6).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 7) (arg s 8).toNat)
    WP isa (Entry.operation true) s fun sf =>
      (sf.gpr .eax).toNat = Spec.Dsa.signStatus result ∧
      Spec.Rsa.bytesAt sf.mem (argumentPointer s 0) (arg s 1).toNat =
        result.getD (List.replicate (arg s 1).toNat 0) ∧
      abiPreserved s sf ∧
      StackOutputFrame (s.gpr .esp) (argumentPointer s 9) (argumentPointer s 0) ((arg s 10).toNat * 8) (arg s 1).toNat s.mem sf.mem ∧
      sf.rd = s.rd ∧ sf.wr = s.wr := by
  dsimp only
  have sz : 8272 ≤ (arg s 10).toNat * 8 := by have H : 15712 ≤ (arg s 10).toNat * 8 := A.used; omega
  unfold Entry.operation Core.sequence
  dsimp only [List.foldr, ite_true]
  refine WP.seq (WP.mono (signingEntry_ok A) fun t I => ?_)
  refine WP.seq (widthDispatch_ok true _ I.scr (by change 8256 ≤ _; omega)
    (supportedWidths_member A.lengths) (by decide)
    (congrArg BitVec.toNat (I.arguments (4, .pLen) (by decide)))
    (congrArg BitVec.toNat (I.arguments (6, .qLen) (by decide))) ?_)
  intro u Ku Ou
  have J := I.compare Ku Ou
  refine WP.mono (signingInstalled_spec A J) fun v ⟨Value, Bytes, K, O, Saved⟩ => ?_
  have Ov : StackOutputFrame (s.gpr .esp) (argumentPointer s 9) (argumentPointer s 0)
      ((arg s 10).toNat * 8) (arg s 1).toNat s.mem v.mem := by
    intro a hb ho hstack
    have H := A.used
    exact (O a (by omega) (by rw [← A.outLength]; exact ho) (by rw [J.keeps.1 .esp (by decide)]; exact hstack)).trans (J.outside a (.inr (by omega)))
  have Esp : v.gpr .esp = s.gpr .esp := (K.1 _ (by decide)).trans (J.keeps.1 _ (by decide))
  refine WP.seq (WP.mono (entryRestore_ok (J.scr.of_keeps K (by decide)) sz (Saved s.gpr J.saved))
    fun sf R => WP.block_nil ?_)
  refine ⟨?_, ?_, restored_abi R Esp (outputFrame_return Ov A.retScratch A.retOut A.stackLow), ?_, ?_, ?_⟩
  · rw [R.other .eax (by decide)]; exact Value
  · rw [R.mem, A.outLength]; exact Bytes
  · rw [R.mem]; exact Ov
  · rw [R.rd, K.2.1, J.keeps.2.1]
  · rw [R.wr, K.2.2, J.keeps.2.2]

end VG.Proof.Dsa.X86
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/SharedCorrect.lean`, which only this module imported.
section

/-! # Whole-operation functional correctness against the shared DSA contracts -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.X86

theorem verifyingSharedPost {s t : State}
    (V : (t.gpr .eax).toNat = (if Spec.Dsa.verifyBytes (arg s 2).toNat (arg s 3).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 6) (arg s 7).toNat) then 1 else 0)) :
    (Spec.Dsa.verifyContract abi 108).post s t := by
  sig_post [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argSlots, argVal, argBytes]
  change ((t.gpr .edx ++ t.gpr .eax).setWidth 32).toNat = _
  rw [BitVec.setWidth_append_eq_right]
  exact V

theorem signingSharedPost {s t : State}
    (V : (t.gpr .eax).toNat = Spec.Dsa.signStatus (Spec.Dsa.signBytes (arg s 4).toNat (arg s 6).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 7) (arg s 8).toNat)))
    (B : Spec.Rsa.bytesAt t.mem (argumentPointer s 0) (arg s 1).toNat =
      (Spec.Dsa.signBytes (arg s 4).toNat (arg s 6).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat)
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 7) (arg s 8).toNat)).getD
          (List.replicate (arg s 1).toNat 0)) :
    (Spec.Dsa.signContract abi 108).post s t := by
  sig_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argSlots, argVal, argBytes]
  change ((t.gpr .edx ++ t.gpr .eax).setWidth 32).toNat = _ ∧ _
  rw [BitVec.setWidth_append_eq_right]
  exact ⟨V, B⟩

theorem verifyingCorrect (s : State) (h : (Spec.Dsa.verifyContract abi 108).pre s) :
    ∃ trace t, Exec isa (Entry.operation false) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.verifyContract abi 108).post s t := by
  obtain ⟨trace, t, E, V, ABI, _⟩ := verifyingOperation_spec (verifyingABI_of h)
  exact ⟨trace, t, E, ABI, verifyingSharedPost V⟩

theorem signingCorrect (s : State) (h : (Spec.Dsa.signContract abi 108).pre s) :
    ∃ trace t, Exec isa (Entry.operation true) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.signContract abi 108).post s t := by
  obtain ⟨trace, t, E, V, B, ABI, _⟩ := signingOperation_spec (signingABI_of h)
  exact ⟨trace, t, E, ABI, signingSharedPost V B⟩

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.X86

/-- A disjoint 1024/160 call; its zero-valued key is rejected at runtime. -/
def signingSatState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 16 else if a = 0x20008 then 40 else if a = 0x2000d then 32 else if a = 0x20010 then 168 else if a = 0x20011 then 1 else if a = 0x20014 then 128 else if a = 0x20019 then 64 else if a = 0x2001c then 20 else if a = 0x20021 then 80 else if a = 0x20029 then 128 else if a = 0x2002d then 8 else 0
  rd := [⟨0x2000, 424⟩, ⟨0x4000, 20⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x1000, 40⟩, ⟨0x8000, 16384⟩, ⟨0x20004, 44⟩]

theorem signingSatisfiable : ∃ s, (Spec.Dsa.signContract abi 108).pre s := by
  have a0 : arg signingSatState 0 = 4096 := by decide
  have a1 : arg signingSatState 1 = 40 := by decide
  have a2 : arg signingSatState 2 = 8192 := by decide
  have a3 : arg signingSatState 3 = 424 := by decide
  have a4 : arg signingSatState 4 = 128 := by decide
  have a5 : arg signingSatState 5 = 16384 := by decide
  have a6 : arg signingSatState 6 = 20 := by decide
  have a7 : arg signingSatState 7 = 20480 := by decide
  have a8 : arg signingSatState 8 = 0 := by decide
  have a9 : arg signingSatState 9 = 32768 := by decide
  have a10 : arg signingSatState 10 = 2048 := by decide
  have e : argAddr signingSatState 0 = 0x20004 := by decide
  have esp : signingSatState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e, esp, signingSatState] using signingSatState

theorem signing_verified : Verified target (Entry.operation true) (Spec.Dsa.signContract abi 108) :=
  ⟨signingCorrect, signingConstantTime, signingSatisfiable⟩

/-- A disjoint 1024/160 call; its zero-valued key is rejected at runtime. -/
def verifyingSatState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 32 else if a = 0x20008 then 148 else if a = 0x20009 then 1 else if a = 0x2000c then 128 else if a = 0x20010 then 20 else if a = 0x20015 then 64 else if a = 0x20018 then 40 else if a = 0x2001d then 80 else if a = 0x20025 then 128 else if a = 0x20029 then 8 else 0
  rd := [⟨0x2000, 404⟩, ⟨0x4000, 40⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x8000, 16384⟩, ⟨0x20004, 40⟩]

theorem verifyingSatisfiable : ∃ s, (Spec.Dsa.verifyContract abi 108).pre s := by
  have a0 : arg verifyingSatState 0 = 8192 := by decide
  have a1 : arg verifyingSatState 1 = 404 := by decide
  have a2 : arg verifyingSatState 2 = 128 := by decide
  have a3 : arg verifyingSatState 3 = 20 := by decide
  have a4 : arg verifyingSatState 4 = 16384 := by decide
  have a5 : arg verifyingSatState 5 = 40 := by decide
  have a6 : arg verifyingSatState 6 = 20480 := by decide
  have a7 : arg verifyingSatState 7 = 0 := by decide
  have a8 : arg verifyingSatState 8 = 32768 := by decide
  have a9 : arg verifyingSatState 9 = 2048 := by decide
  have e : argAddr verifyingSatState 0 = 0x20004 := by decide
  have esp : verifyingSatState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, e, esp, verifyingSatState] using verifyingSatState

theorem verifying_verified : Verified target (Entry.operation false) (Spec.Dsa.verifyContract abi 108) :=
  ⟨verifyingCorrect, verifyingConstantTime, verifyingSatisfiable⟩

end VG.Proof.Dsa.X86
