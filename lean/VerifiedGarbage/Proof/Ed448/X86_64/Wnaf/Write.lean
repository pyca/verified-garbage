module
public import VerifiedGarbage.Impl.Ed448.X86_64.Wnaf.Recode
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.X86_64.Basic

import VerifiedGarbage.Proof.X448.X86_64.Bits
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Nat.Totient
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual

/-! Bounded byte output for public signed digits. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Wnaf
open VG VG.X86_64 VG.Impl.Ed448.X86_64.Wnaf
open VG.Proof.X448.X86_64

theorem writeDigit_ok {s : State} {base : Addr} (hs : Scr s base) {o t : Nat}
    (ho : o + t + 1 ≤ 8192) (hb : s.gpr .rbx = BitVec.ofNat 64 t) :
    WP isa (.block (writeDigit o)) s fun u =>
      u.gpr .rbx = BitVec.ofNat 64 (t + 1) ∧
      (∀ r, r ≠ .rbx → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
      u.mem = s.mem.writeW (off base (o + t)) ((s.gpr .r15).setWidth 8) := by
  have hw := hs.write ho
  apply WP.of_runBlock
  simp only [writeDigit, runBlock_cons, runStep_some, runBlock_nil, exec, State.store8,
    ea_bitsAt hs.rdi hb, hw, ite_true, Option.bind_some, execAlu, readSrc,
    hb, inc_eq, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => by simp only [hr, ite_false], trivial, trivial, trivial⟩

theorem cmp456_ok {s : State} {t : Nat} (ht : t ≤ 456)
    (hb : s.gpr .rbx = BitVec.ofNat 64 t) :
    WP isa (.block [.alu .cmp .rbx (.imm 456)]) s fun u =>
      u.zf = some (decide (t = 456)) ∧ Keeps [] s u := by
  have h : ∀ t ≤ 456, (BitVec.ofNat 64 t - (456 : BitVec 32).signExtend 64 == 0) = decide (t = 456) := by
    decide +kernel
  xrun [hb]
  exact ⟨h t ht, fun _ _ => rfl, rfl, rfl, rfl⟩

end VG.Proof.Ed448.X86_64.Wnaf
