module

public import VerifiedGarbage.Proof.Ed448.X86_64.VerifyRoot
public import VerifiedGarbage.Proof.Ed448.X86_64.ScalarWord
public import VerifiedGarbage.Proof.Ed448.X86_64.ScalarIO
public import VerifiedGarbage.Proof.X448.X86_64.Main
public import VerifiedGarbage.Impl.Ed448.Wnaf
public import VerifiedGarbage.Proof.Ed448.X86_64.FieldVariant
public import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
public import VerifiedGarbage.Proof.X448.X86_64.Adx.Sqr

/-! # The tactic of `VerifyChecks.lean`

In a module of its own: a macro costs much more to elaborate where it is
defined than where it is imported. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64
open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr word off Outside ofs writeW_outside word_writeW_self contains_sc)
open VG.Impl.X448.X86_64 (W w sc at_)

/-- Runs a block symbolically, keeping the register writes folded. -/
syntax "erun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| erun) => `(tactic| erun [])
  | `(tactic| erun [$ls,*]) => `(tactic| plain_simp_names (
                       apply WP.of_runBlock
                       set_option linter.unusedSimpArgs false in
                       simp (config := { decide := true }) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
                         readSrc32, execAlu, execShift, State.setReg32, State.load64, State.load8, State.store64,
                         State.store8, sc, VG.Proof.Ed448.X86_64.ea_at, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
                         RegUpd.cf_setReg, RegUpd.zf_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
                         RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.cf_arithFlags, RegUpd.zf_arithFlags,
                         RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags,
                         RegUpd.cf_setFlags, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left',
                         ite_true, ite_false, reduceCtorEq, true_and, and_true, $ls,*]))

end VG.Proof.Ed448.X86_64
