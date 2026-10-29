module

public import VerifiedGarbage.Proof.Rsa.X86.DivContext
public import VerifiedGarbage.Impl.Rsa.X86.Div
public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.Rsa.X86.DivBit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Rsa.X86.DivCopy
import VerifiedGarbage.Proof.Mont.X86.Instr
/-! # The quotient's high bit is shifted into the extended remainder -/

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/DivShift.lean`, which only this module imported.
section

/-! # The division shift returns the high bit without branching on it -/

section
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
end

end

@[expose] public section
namespace VG.Proof.Rsa.X86.Div
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Rsa.X86.Div

theorem shiftArrays_ok {g : Geometry} {s : State} (h : Context g s) :
    WP isa (shiftArrays g.n (g.offsets 0) (g.offsets 1) (g.offsets 3)) s fun t =>
      g.value t.mem 0 = 2 * g.value s.mem 0 % 2 ^ (32 * g.n) ∧
      (g.value s.mem 1 < 2 ^ (32 * g.n) →
        g.value t.mem 1 = 2 * g.value s.mem 1 + g.value s.mem 0 / 2 ^ (32 * g.n - 1)) ∧
      Context g t ∧ Outs g.base g.ranges s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have f0 : g.offsets 0 + 4 * g.n ≤ g.size := h.fits 0
  have f1 : g.offsets 1 + 4 * (g.n + 1) ≤ g.size := h.fits 1
  have f3 : g.offsets 3 + 4 * (g.n + 1) ≤ g.size := h.fits 3
  have sep01 : g.offsets 0 + 4 * g.n ≤ g.offsets 1 ∨
      g.offsets 1 + 4 * (g.n + 1) ≤ g.offsets 0 := h.separate 0 1 (by decide)
  have sep03 : g.offsets 0 + 4 * g.n ≤ g.offsets 3 ∨
      g.offsets 3 + 4 * (g.n + 1) ≤ g.offsets 0 := h.separate 0 3 (by decide)
  have sep13 : g.offsets 1 + 4 * (g.n + 1) ≤ g.offsets 3 ∨
      g.offsets 3 + 4 * (g.n + 1) ≤ g.offsets 1 := h.separate 1 3 (by decide)
  have nowrap := h.workspace.nowrap
  unfold shiftArrays
  refine WP.seq (WP.mono (shift_ok h.workspace h.positive f0 (by omega) (by omega) true) ?_)
  rintro u ⟨frameU, ⟨c, qVal, bitU⟩, restU⟩
  change g.value u.mem 0 + 2 ^ (32 * g.n) * c.toNat = 2 * g.value s.mem 0 at qVal
  have hu := h.after restU
  have remU : g.value u.mem 1 = g.value s.mem 1 := by
    change val32 _ _ _ (g.n + 1) = val32 _ _ _ (g.n + 1)
    apply frameU.val32
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> omega
    · omega
  refine WP.seq (WP.mono (shift_ok hu.workspace (by omega) f1 f3 (by omega) false) ?_)
  rintro w ⟨frameW, ⟨cr, rVal, bitW⟩, restW⟩
  have hw := hu.after restW
  have bit : (w.gpr .ebx).toNat = c.toNat := by
    rw [bitW, bitU]
    cases c <;> rfl
  have boundedBit : (w.gpr .ebx).toNat ≤ 1 := by rw [bit]; cases c <;> decide
  refine WP.mono (insertBit_ok hw.workspace (by omega) f1 boundedBit) ?_
  rintro t ⟨frameT, restT, remT⟩
  change g.value w.mem 1 % 2 = 0 → g.value t.mem 1 = g.value w.mem 1 + (w.gpr .ebx).toNat at remT
  have quoW : g.value w.mem 0 = g.value u.mem 0 := by
    change val32 _ _ _ g.n = val32 _ _ _ g.n
    apply frameW.val32
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> omega
    · omega
  have quoT : g.value t.mem 0 = g.value w.mem 0 := by
    change val32 _ _ _ g.n = val32 _ _ _ g.n
    exact frameT.val32 (by omega) (by omega)
  have quoBound : g.value u.mem 0 < 2 ^ (32 * g.n) := val32_lt _ _ _ _
  have quoOriginal : g.value s.mem 0 < 2 ^ (32 * g.n) := val32_lt _ _ _ _
  have radix : 2 ^ (32 * g.n) = 2 * 2 ^ (32 * g.n - 1) := by
    rw [← Nat.pow_succ']; congr 1; have := h.positive; omega
  have quotient : g.value u.mem 0 = 2 * g.value s.mem 0 % 2 ^ (32 * g.n) := by
    have eq := congrArg (fun x => x % 2 ^ (32 * g.n)) qVal
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt quoBound] at eq
    exact eq
  have high : c.toNat = g.value s.mem 0 / 2 ^ (32 * g.n - 1) := by
    change g.value u.mem 0 + 2 ^ (32 * g.n) * c.toNat = 2 * g.value s.mem 0 at qVal
    rw [radix] at qVal quoOriginal quoBound
    cases c with
    | false =>
      simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at qVal ⊢
      exact (Nat.div_eq_of_lt (by omega)).symm
    | true =>
      simp only [Bool.toNat_true, Nat.mul_one] at qVal ⊢
      exact (Nat.div_eq_of_lt_le (by omega) (by omega)).symm
  refine ⟨quoT.trans (quoW.trans quotient), ?_, hw.after restT,
    (quotientShift_frame frameU).trans ((frameW.mono (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [Geometry.ranges])).trans
        (Outs.of_outside frameT (by simp [Geometry.ranges]))),
    restU.trans (restW.trans (restT.mono (by decide)))⟩
  intro remBound
  change g.value w.mem 1 + 2 ^ (32 * (g.n + 1)) * cr.toNat = 2 * g.value u.mem 1 at rVal
  have remWidth : g.value w.mem 1 < 2 ^ (32 * (g.n + 1)) := val32_lt _ _ _ _
  rw [remU, pow32_succ] at rVal
  have remDouble : g.value w.mem 1 = 2 * g.value s.mem 1 := by
    cases cr <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at rVal <;> omega
  have even : g.value w.mem 1 % 2 = 0 := by rw [remDouble]; omega
  rw [remT even, bit, remDouble, high]
end VG.Proof.Rsa.X86.Div
