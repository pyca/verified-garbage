module
public import VerifiedGarbage.Impl.Rsa.X86.Div
public import VerifiedGarbage.Proof.Mont.X86.WordOps

import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Conditional subtraction selects the next remainder and quotient bit -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Div
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86.Dynamic VG.Impl.Rsa.X86.Div

theorem selectMask_ok (s : State) (c : Bool) (hc : s.gpr .ecx = cmask c) :
    WP isa (.block selectMask) s fun t =>
      t.gpr .ecx = cmask (!c) ∧ t.gpr .ebx = (BitVec.ofBool (!c)).setWidth 32 ∧
      t.mem = s.mem ∧ Keeps [.ebx, .ecx] s t := by
  unfold selectMask
  refine wp_movS rfl fun u U _ => ?_
  refine wp_logicS (.inr rfl) rfl fun v V => ?_
  refine wp_logicS (.inl rfl) rfl fun w W => ?_
  refine wp_logicS (.inr rfl) rfl fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, T.mem.trans (W.mem.trans (V.mem.trans U.mem)),
    (U.keeps.mono (by decide)).trans ((V.keeps.mono (by decide)).trans
      ((W.keeps.mono (by decide)).trans (T.keeps.mono (by decide))))⟩
  · rw [T.gpr, W.other .ecx (by decide), V.other .ecx (by decide), U.other .ecx (by decide), hc,
      ite_eq_right (by decide)]
    cases c <;> rfl
  · rw [T.other .ebx (by decide), W.gpr, V.gpr, U.gpr, hc,
      ite_eq_left rfl, ite_eq_right (by decide)]
    cases c <;> rfl

theorem reduce_ok {s : State} {base : Addr} {size n rem divisor tmp : Nat} (hs : Scr s base size)
    (hrem : rem + 4 * (n + 1) ≤ size) (hdiv : divisor + 4 * (n + 1) ≤ size)
    (htmp : tmp + 4 * (n + 1) ≤ size)
    (sr : tmp + 4 * (n + 1) ≤ rem ∨ rem + 4 * (n + 1) ≤ tmp)
    (sd : tmp + 4 * (n + 1) ≤ divisor ∨ divisor + 4 * (n + 1) ≤ tmp) :
    WP isa (reduce n rem divisor tmp) s fun t =>
      Outs base [(rem, 4 * (n + 1)), (tmp, 4 * (n + 1))] s.mem t.mem ∧
      val32 t.mem base rem (n + 1) =
        (if val32 s.mem base rem (n + 1) < val32 s.mem base divisor (n + 1)
          then val32 s.mem base rem (n + 1)
          else val32 s.mem base rem (n + 1) - val32 s.mem base divisor (n + 1)) ∧
      t.gpr .ebx = (if val32 s.mem base rem (n + 1) < val32 s.mem base divisor (n + 1) then 0 else 1) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  unfold reduce
  refine WP.seq (WP.mono (chainSubW_ok hs (by omega) htmp hrem hdiv sr sd) ?_)
  rintro u ⟨frameU, ⟨c, carry, value⟩, restU⟩
  refine WP.seq (WP.mono (selectMask_ok u c carry) ?_)
  rintro w ⟨mask, bit, memW, restW⟩
  have hw := (hs.of_keeps restU (by decide)).of_keeps restW (by decide)
  refine WP.mono (selectsW_ok hw (!c) mask (by omega) hrem htmp hrem (.inl rfl) (by omega)) ?_
  rintro t ⟨frameT, valueT, restT⟩
  have nowrap := hs.nowrap
  have same : val32 w.mem base rem (n + 1) = val32 s.mem base rem (n + 1) := by
    rw [memW]
    exact frameU.val32 (by omega) (by omega)
  have ub := val32_lt u.mem base tmp (n + 1)
  have rb := val32_lt s.mem base rem (n + 1)
  have db := val32_lt s.mem base divisor (n + 1)
  refine ⟨(Outs.of_outside frameU (by simp)).trans ?_, ?_, ?_,
    (restU.mono (by decide)).trans ((restW.mono (by decide)).trans (restT.mono (by decide)))⟩
  · rw [memW] at frameT
    exact Outs.of_outside frameT (by simp)
  · rw [valueT]
    cases c with
    | false =>
      simp only [Bool.not_false, ite_true, memW, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at *
      rw [ite_eq_right (by omega)]
      omega
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ite_false, Bool.toNat_true, Nat.mul_one] at *
      rw [same, ite_eq_left (by omega)]
  · rw [restT.1 .ebx (by decide), bit]
    cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at value
    · rw [ite_eq_right (by omega)]; rfl
    · rw [ite_eq_left (by omega)]; rfl
end VG.Proof.Rsa.X86.Div
