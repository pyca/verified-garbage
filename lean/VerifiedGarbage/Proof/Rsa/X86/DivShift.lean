module
public import VerifiedGarbage.Impl.Rsa.X86.Div
public import VerifiedGarbage.Proof.Mont.X86.WordOps

import VerifiedGarbage.Proof.Rsa.X86.DivCopy
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The division shift returns the high bit without branching on it -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Div
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86.Dynamic VG.Impl.Rsa.X86.Div

theorem saveCarry_ok (s : State) (save : Bool) (c : Bool) (hc : s.gpr .ecx = cmask c) :
    WP isa (.block (if save then [.mov .ebx (.reg .ecx), .alu .and .ebx (.imm 1)] else [])) s fun t =>
      t.gpr .ebx = (if save then (BitVec.ofBool c).setWidth 32 else s.gpr .ebx) ∧
      t.mem = s.mem ∧ Keeps [.ebx] s t := by
  cases save with
  | false => exact WP.block_nil ⟨rfl, rfl, Keeps.refl _ _⟩
  | true =>
    refine wp_movS rfl fun u U _ => ?_
    refine wp_logicS (.inl rfl) rfl fun t T => WP.block_nil ?_
    refine ⟨?_, T.mem.trans U.mem, U.keeps.trans T.keeps⟩
    rw [T.gpr, U.gpr, hc, ite_eq_left rfl]
    cases c <;> rfl

theorem shift_ok {s : State} {base : Addr} {size n dst tmp : Nat} (hs : Scr s base size)
    (hn : 0 < n) (hdst : dst + 4 * n ≤ size) (htmp : tmp + 4 * n ≤ size)
    (sep : tmp + 4 * n ≤ dst ∨ dst + 4 * n ≤ tmp) (save : Bool) :
    WP isa (shift n dst tmp save) s fun t =>
      Outs base [(dst, 4 * n), (tmp, 4 * n)] s.mem t.mem ∧
      (∃ c : Bool, val32 t.mem base dst n + 2 ^ (32 * n) * c.toNat =
          2 * val32 s.mem base dst n ∧
        t.gpr .ebx = (if save then (BitVec.ofBool c).setWidth 32 else s.gpr .ebx)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  unfold shift
  refine WP.seq (WP.mono (chainAddW_ok hs hn htmp hdst hdst sep sep) ?_)
  rintro u ⟨frameU, ⟨c, carry, value⟩, restU⟩
  refine WP.seq (WP.mono (saveCarry_ok u save c carry) ?_)
  rintro w ⟨bit, memW, restW⟩
  have hw := (hs.of_keeps restU (by decide)).of_keeps restW (by decide)
  refine WP.mono (copyWords_ok hw hn htmp hdst (by omega)) ?_
  rintro t ⟨frameT, valueT, restT⟩
  refine ⟨(Outs.of_outside frameU (by simp)).trans ?_, ⟨c, ?_, ?_⟩,
    (restU.mono (by decide)).trans ((restW.mono (by decide)).trans (restT.mono (by decide)))⟩
  · rw [memW] at frameT
    exact Outs.of_outside frameT (by simp)
  · rw [valueT, memW]
    omega
  · rw [restT.1 .ebx (by decide), bit, restU.1 .ebx (by decide)]
end VG.Proof.Rsa.X86.Div
