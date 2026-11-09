module

public import VerifiedGarbage.Impl.Ed448.X86_64.ScalarBase
public import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Fn
import VerifiedGarbage.Proof.X448.X86_64.Iter
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# Ed448 base-point multiplication on x86-64: the counter of a step

The start of a step: the counter `rbx` counts down to the bit `t`
(`dec_ok`), and its test (`testRbx_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr Index Env E Keep FieldOk off contains_sc mask cswapE opSwap ea_bits
  clob)
open VG.Impl.X448.X86_64 (BITS slot cswap)

theorem dec_ok (s : State) {t : Nat} (hb : s.gpr .rbx = BitVec.ofNat 64 (t + 1)) :
    WP isa (.block ([.alu .sub .rbx (.imm 1)] : List Instr)) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 t ∧ (∀ r, r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hb' : s.gpr .rbx - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 t := by
    have e1 : (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 := by decide
    rw [hb, e1, BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, hb',
    Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  exact ⟨trivial, fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags], rfl,
    rfl, rfl⟩

theorem testRbx_ok (s : State) (n : Nat) (hn : n < 456) (hb : s.gpr .rbx = BitVec.ofNat 64 n) :
    WP isa (.block ([.alu .test .rbx (.reg .rbx)] : List Instr)) s fun t =>
      t.zf = some (decide (n = 0)) ∧ (∀ r, t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
        t.wr = s.wr := by
  have e : (BitVec.ofNat 64 n &&& BitVec.ofNat 64 n == 0) = decide (n = 0) := by
    have : ∀ n < 456, (BitVec.ofNat 64 n &&& BitVec.ofNat 64 n == 0) = decide (n = 0) := by
      decide +kernel
    exact this n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.zf_arithFlags, hb, e]
  exact ⟨trivial, fun _ => rfl, rfl, rfl, rfl⟩

end VG.Proof.Ed448.X86_64
