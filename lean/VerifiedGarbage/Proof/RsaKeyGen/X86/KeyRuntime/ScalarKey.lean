module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyBorrowMask
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySaveSlot
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyNotSlot
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDTrivial
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRetry
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExponentBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyFinalExponent
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! # Reuse the unchanged scalar key controls in the runtime workspace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (Keep slot)
open VG.Impl.RsaKeyGen.X86.Key

theorem borrowMask_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (borrow : (s.gpr .ebx).toNat ≤ 1) (flag : slot s.mem B kFlag ≤ 1) :
    WP isa (.block borrowMask) s fun t => Ws t B Z n 32 ∧ Keep B n [] [kOk] s.mem t.mem ∧
      slot t.mem B kOk = (if (s.gpr .ebx).toNat = 0 ∧ slot s.mem B kFlag = 1 then 1 else 0) ∧
      Keeps [.eax] s t :=
  h.lift (by decide) (by decide) (by simp) (by decide) (Key.borrowMask_ok h.old borrow flag)

theorem saveSlot_ok {s : State} {B : Addr} {Z n N a d : Nat} (h : Ws s B Z n N)
    (ha : a + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) (hd : d + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) :
    WP isa (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc a)),
      .store (VG.Impl.Mont.X86.sc d) .eax]) s fun t => Ws t B Z n N ∧
      Keep B n [] [d] s.mem t.mem ∧ slot t.mem B d = slot s.mem B a ∧ Keeps [.eax] s t :=
  h.lift (by decide) (by decide) (by simp) (by simpa using hd) (Key.saveSlot_ok h.old ha hd)

theorem notSlot_ok {s : State} {B : Addr} {Z n N d a : Nat} (h : Ws s B Z n N)
    (hd : d + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) (ha : a + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr)
    (bit : slot s.mem B a ≤ 1) :
    WP isa (.block (notSlot d a)) s fun t => Ws t B Z n N ∧ Keep B n [] [d] s.mem t.mem ∧
      slot t.mem B d = 1 - slot s.mem B a ∧ Keeps [.eax] s t :=
  h.lift (by decide) (by decide) (by simp) (by simpa using hd) (Key.notSlot_ok h.old hd ha bit)

theorem dZero_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa dZero s fun t => Ws t B Z n 32 ∧ Keep B n [] [kOk] s.mem t.mem ∧
      slot t.mem B kOk = 0 ∧ Keeps [.eax] s t :=
  h.lift (by decide) (by decide) (by simp) (by decide) (Key.dZero_ok h.old)

theorem equalExponent_ok {s : State} {B : Addr} {Z n N : Nat} (h : Ws s B Z n N) (value : BitVec 32) :
    WP isa (.block (equalExponent value)) s fun t => Ws t B Z n N ∧ t.mem = s.mem ∧
      isa.eval .e t = some (decide (val32 s.mem B kEv 2 = value.toNat)) ∧ Keeps [.eax] s t :=
  WP.mono (Key.equalExponent_ok h.old value) fun _ ⟨_, memory, flag, K⟩ =>
    ⟨h.keep K (by rw [memory]; exact Outside.refl _ _ _ _), memory, flag, K⟩

theorem parityExponent_ok {s : State} {B : Addr} {Z n N : Nat} (h : Ws s B Z n N) :
    WP isa (.block parityExponent) s fun t => Ws t B Z n N ∧ t.mem = s.mem ∧
      isa.eval .e t = some (decide (val32 s.mem B kEv 2 % 2 = 0)) ∧ Keeps [.eax] s t :=
  WP.mono (Key.parityExponent_ok h.old) fun _ ⟨_, memory, flag, K⟩ =>
    ⟨h.keep K (by rw [memory]; exact Outside.refl _ _ _ _), memory, flag, K⟩

theorem exponentUpper_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa (.block exponentUpper) s fun t => Ws t B Z n 32 ∧ Keep B n [] [kFlag] s.mem t.mem ∧
      slot t.mem B kFlag = (if val32 s.mem B kEv 2 < 2 ^ 33 then 1 else 0) ∧ Keeps [.eax] s t :=
  h.lift (by decide) (by decide) (by simp) (by decide) (Key.exponentUpper_ok h.old)

theorem retry_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa retry s fun t => Ws t B Z n 32 ∧ Keep B n [] [kOk, kStatus] s.mem t.mem ∧
      slot t.mem B kOk = 0 ∧ slot t.mem B kStatus = 2 ∧ Keeps [.eax] s t :=
  WP.mono (Key.retry_ok h.old) fun _ ⟨_, O, mask, status, K⟩ =>
    ⟨h.afterKeep K O (by simp) (by decide), O, mask, status, K⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
