module
public import VerifiedGarbage.Impl.Dsa.Layout
public import VerifiedGarbage.Impl.Rsa.X86_64.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Push
import Aesop.BuiltinRules
import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Impl.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Bignum.X86_64.Words

/-! # Loading caller scratch and preserving stack and saved registers -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem stackAddress (sp : Addr) (j : Nat) :
    sp + BitVec.ofInt 64 (8 * (j : Int)) = off sp (8 * j) := by
  rw [show 8 * (j : Int) = ((8 * j : Nat) : Int) by omega, BitVec.ofInt_natCast]

theorem entryScratch_ok {s : State} {sp B : Addr} (j : Nat) (hsp : s.gpr .rsp = sp)
    (hr : InRegions (s.rd ++ s.wr) (off sp (8 * j)) 8) (hb : word s.mem sp (8 * j) = B) :
    WP isa (.block [.mov .r11 (.mem (Crt.stk j))]) s fun t =>
      t.gpr .r11 = B ∧ t.mem = s.mem ∧ Keep [.r11] s t := by
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = B ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨hp, hm⟩, hk⟩ => ⟨hp, hm, hk⟩
  xrun [State.ea, Crt.stk, hsp, stackAddress, hr, hb]

theorem saved_ne_r11 {i : Nat} (hi : i < 6) : saved.getD i .rax ≠ .r11 := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem entry_stack_frame {mem mem' : Mem} {B sp : Addr} {Z o n d : Nat}
    (hf : Outside B o n mem mem') (hhi : o + n ≤ Z)
    (hsep : ∀ i < 8, Z ≤ ofs B (off sp d + BitVec.ofNat 64 i)) : word mem' sp d = word mem sp d := by
  apply Mem.readW_congr
  intro i hi
  exact hf _ (Or.inr (Nat.le_trans hhi (hsep i hi)))

theorem entry_saved_frame {mem mem' : Mem} {B : Addr} {i : Nat}
    (hf : Outside B 256 (pWorkspace - 256) mem mem') (hi : i < 6) :
    word mem' B (8 * i) = word mem B (8 * i) :=
  hf.word (Or.inl (by omega)) (by omega)

end VG.Proof.Dsa.X86_64
