module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Div
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Defs.Prop
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import Mathlib.Util.CompileInductive

/-! # The runtime division kernel is shared with RSA key checking -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num Keep arr)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Impl.Rsa.X86.KeyRt (sCy sQb)

theorem divide_ok {s : State} {B : Addr} {Z n N : Nat} {w : Width}
    (h : Ws s B Z n N) (bound : 4 ≤ N) (hw : w ≠ .correction)
    (top : w32 s.mem B (arr (w.words n) 2 + 4 * w.words n) = 0) :
    WP isa (divide w) s fun t => Ws t B Z n N ∧
      Keep B (w.words n) [0, 1, 3] [sCy, sQb] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧
      (0 < num s.mem B (w.words n) 2 →
        num t.mem B (w.words n) 0 = num s.mem B (w.words n) 0 / num s.mem B (w.words n) 2 ∧
        num t.mem B (w.words n) 1 = num s.mem B (w.words n) 0 % num s.mem B (w.words n) 2) := by
  have code : divide w = VG.Impl.Rsa.X86.KeyRt.div w.lay 0 1 2 3 := by
    cases w <;> simp_all [divide]
  rw [code]
  have H := shrinkRt (h.runtime hw) bound
  have core := VG.Proof.Rsa.X86.KeyRt.div_ok H
    (by decide : 0 < 4) (by decide : 1 < 4) (by decide : 2 < 4) (by decide : 3 < 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simpa only [kw_words h.width] using top)
  rw [kw_words h.width] at core
  refine WP.mono core fun t ⟨_, O, K, V⟩ => ⟨h.afterBank hw K O ?_ (by decide), O, K, V⟩
  intro j hj
  have small := (by decide : ∀ j ∈ ([0, 1, 3] : List Nat), j < 4) j hj
  omega

end VG.Proof.RsaKeyGen.X86.KeyRuntime
