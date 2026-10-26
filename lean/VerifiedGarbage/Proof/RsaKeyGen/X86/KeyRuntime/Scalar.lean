module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
import VerifiedGarbage.Proof.Rsa.X86.KeyScalar
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Word
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! # The runtime context lifts the existing header-word proofs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (slot num Keep)
open VG.Impl.Rsa.X86.Keys (hdr andS)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem store_slot {s : State} {B : Addr} {Z n N d : Nat} (h : Ws s B Z n N)
    (hd : d + 4 ≤ hdr) (r : Reg) :
    WP isa (.block [.store (VG.Impl.Mont.X86.sc d) r]) s fun t =>
      Ws t B Z n N ∧ Keep B n [] [d] s.mem t.mem ∧
      slot t.mem B d = (s.gpr r).toNat ∧ Keeps [] s t :=
  h.lift (by decide) (by decide) (by simp) (by simpa using hd)
    (VG.Proof.Rsa.X86.Keys.store_slot h.old hd r)

theorem andS_ok {s : State} {B : Addr} {Z n N d a b : Nat} (h : Ws s B Z n N)
    (hd : d + 4 ≤ hdr) (ha : a + 4 ≤ hdr) (hb : b + 4 ≤ hdr)
    (ba : slot s.mem B a ≤ 1) (bb : slot s.mem B b ≤ 1) :
    WP isa (.block (andS d a b)) s fun t =>
      Ws t B Z n N ∧ Keep B n [] [d] s.mem t.mem ∧
      slot t.mem B d = (if slot s.mem B a = 1 ∧ slot s.mem B b = 1 then 1 else 0) ∧
      Keeps [.eax] s t :=
  h.lift (by decide) (by decide) (by simp) (by simpa using hd)
    (VG.Proof.Rsa.X86.Keys.andS_ok h.old hd ha hb ba bb)

theorem bitOf_ok {s : State} {B : Addr} {Z n N j sl : Nat} (h : Ws s B Z n N)
    (hj : j < N) (hsl : sl + 4 ≤ hdr) :
    WP isa (.block (VG.Impl.Rsa.X86.KeyRt.bitOf full sl j)) s fun t =>
      Ws t B Z n N ∧ Keep B n [] [sl] s.mem t.mem ∧
      slot t.mem B sl = num s.mem B n j % 2 ∧ Keeps [.eax, .edx] s t := by
  have core := VG.Proof.Rsa.X86.KeyRt.bitOf_ok h.full hj hsl
  rw [kw_full h.width] at core
  exact WP.mono core fun _ ⟨_, O, V, K⟩ =>
    ⟨h.afterKeep K O (by simp) (by simpa using hsl), O, V, K⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
