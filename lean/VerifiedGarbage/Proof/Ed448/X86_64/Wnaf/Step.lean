module
public import VerifiedGarbage.Impl.Ed448.Wnaf
public import VerifiedGarbage.Impl.Ed448.X86_64.Wnaf.Recode
public import VerifiedGarbage.Proof.X448.X86_64.Reduce

import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Write
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Digit
import VerifiedGarbage.Proof.Ed448.Wnaf.Recoding
import VerifiedGarbage.Proof.Framework.Block
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Algebra.Group.Nat.Defs
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Spec.Ed448

/-! One recoded byte and the residual invariant. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Wnaf
open VG VG.X86_64 VG.Impl.Ed448.X86_64.Wnaf
open VG.Proof.X448.X86_64
open VG.Impl.Ed448.Wnaf (digitAt residual)

abbrev Enc (k n : Nat) : Byte := (BitVec.ofInt 64 (digitAt k n)).setWidth 8

structure StepOut (base : Addr) (dst k n : Nat) (s u : State) : Prop where
  rbx : u.gpr .rbx = BitVec.ofNat 64 (n + 1)
  carry : ∃ c ≤ 32, u.gpr .rcx = BitVec.ofNat 64 c ∧ residual k (n + 1) + 16 = k / 2 ^ (n + 1) + c
  gpr : ∀ r, r ∉ .rbx :: clob → u.gpr r = s.gpr r
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  mem : u.mem = s.mem.writeW (off base (dst + n)) (Enc k n)

theorem step_ok {s : State} {base : Addr} (hs : Scr s base) {dst k n c : Nat}
    (hdst : dst + n + 1 ≤ 8192) (hb : s.gpr .rbx = BitVec.ofNat 64 n)
    (hc : c ≤ 32) (hrc : s.gpr .rcx = BitVec.ofNat 64 c)
    (hrel : residual k n + 16 = k / 2 ^ n + c) {p : List Instr}
    (hp : WP isa (.block p) s fun u =>
      u.gpr .rax = BitVec.ofNat 64 (k / 2 ^ n % 32) ∧
      u.gpr .rdx = BitVec.ofNat 64 (k / 2 ^ n % 2) ∧ Keeps [.rax, .rdx] s u) :
    WP isa (.block (p ++ digitStep ++ writeDigit dst)) s (StepOut base dst k n s) := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono hp fun a ⟨ar, ad, ak⟩ => ?_
  rw [WP.block_append_iff]
  have ac : a.gpr .rcx = BitVec.ofNat 64 c := (ak.1 _ (by decide)).trans hrc
  have aD : a.gpr .rdx = BitVec.ofNat 64 (k / 2 ^ n % 32 % 2) := by
    rw [ad]; congr 1; omega
  refine WP.mono (digitStep_ok (Nat.mod_lt _ (by decide)) hc ar aD ac) fun b ⟨bd, bc, bk⟩ => ?_
  have hb' : b.gpr .rbx = BitVec.ofNat 64 n := ((bk.1 _ (by decide)).trans (ak.1 _ (by decide))).trans hb
  have bs : Scr b base := (hs.of_keeps ak (by decide)).of_keeps bk (by decide)
  refine WP.mono (writeDigit_ok bs hdst hb') fun u ⟨ub, ug, ur, uw, um⟩ => ?_
  refine ⟨ub, ?_, ?_, ur.trans (bk.2.2.1.trans ak.2.2.1),
    uw.trans (bk.2.2.2.trans ak.2.2.2), ?_⟩
  · refine ⟨Impl.Ed448.Wnaf.carryNext (k / 2 ^ n % 32) c,
      Proof.Ed448.Wnaf.carry_bounds _ (Nat.mod_lt _ (by decide)) c hc, (ug _ (by decide)).trans bc, ?_⟩
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    exact Proof.Ed448.Wnaf.carry_step hrel hc
  · intro r hr
    have rbx : r ≠ .rbx := fun h => hr (by simp only [h, List.mem_cons_self])
    have ra : r ∉ [Reg.rax, .rdx] := fun h => hr (List.mem_cons_of_mem _
      ((show ∀ r ∈ [Reg.rax, .rdx], r ∈ clob from by decide) r h))
    have rb : r ∉ [Reg.rax, .rcx, .r15] := fun h => hr (List.mem_cons_of_mem _
      ((show ∀ r ∈ [Reg.rax, .rcx, .r15], r ∈ clob from by decide) r h))
    exact ((ug r rbx).trans (bk.1 r rb)).trans (ak.1 r ra)
  · rw [um, bd, bk.2.1, ak.2.1, Proof.Ed448.Wnaf.local_digit hrel]
    rfl

end VG.Proof.Ed448.X86_64.Wnaf
