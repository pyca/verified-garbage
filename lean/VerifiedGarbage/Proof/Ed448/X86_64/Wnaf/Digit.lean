module

public import VerifiedGarbage.Impl.Ed448.X86_64.Wnaf.Recode
public import VerifiedGarbage.Proof.X448.X86_64.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.NormNum.Prime
public import VerifiedGarbage.Impl.Ed448.Wnaf
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Impl.Ed448.X86_64.Wnaf.Joint

/-! The bounded word arithmetic implementing one public recoding step. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Wnaf
open VG VG.X86_64 VG.Impl.Ed448.X86_64.Wnaf
open VG.Proof.X448.X86_64 (Keeps)

private def rawDigit (bits c : Nat) : BitVec 64 :=
  let r := (BitVec.ofNat 64 bits + BitVec.ofNat 64 c + 16) &&& 31
  if r &&& 1 == 0 then 0 else if r < 16 then r else r - 32

private theorem rawDigit_ok : ∀ bits < 32, ∀ c ≤ 32,
    rawDigit bits c = BitVec.ofInt 64 (Impl.Ed448.Wnaf.localDigit bits c) := by decide +kernel

private theorem rawCarry_ok : ∀ bits < 32, ∀ c ≤ 32,
    (BitVec.ofNat 64 c + BitVec.ofNat 64 (bits % 2) + 16 - rawDigit bits c) >>> 1 =
      BitVec.ofNat 64 (Impl.Ed448.Wnaf.carryNext bits c) := by decide +kernel

theorem digitStep_ok {s : State} {bits c : Nat} (hb : bits < 32) (hc : c ≤ 32)
    (ha : s.gpr .rax = BitVec.ofNat 64 bits) (hd : s.gpr .rdx = BitVec.ofNat 64 (bits % 2))
    (hs : s.gpr .rcx = BitVec.ofNat 64 c) :
    WP isa (.block digitStep) s fun u =>
      u.gpr .r15 = BitVec.ofInt 64 (Impl.Ed448.Wnaf.localDigit bits c) ∧
      u.gpr .rcx = BitVec.ofNat 64 (Impl.Ed448.Wnaf.carryNext bits c) ∧
      Keeps [.rax, .rcx, .r15] s u := by
  xrun [digitStep, ha, hd, hs, execCmov, eval]
  simp only [apply_ite State.gpr, ite_apply, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    reduceCtorEq, ite_true, ite_false, ite_self, ha, hd, hs, decide_eq_true_eq]
  refine ⟨rawDigit_ok bits hb c hc, rawCarry_ok bits hb c hc, ?_⟩
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [apply_ite State.gpr, ite_apply, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
      hr.1, hr.2.1, hr.2.2, ite_false, ite_self]
  · simp only [apply_ite State.mem, RegUpd.mem_setReg, RegUpd.mem_setFlags, ite_self]
  · simp only [apply_ite State.rd, RegUpd.rd_setReg, RegUpd.rd_setFlags, ite_self]
  · simp only [apply_ite State.wr, RegUpd.wr_setReg, RegUpd.wr_setFlags, ite_self]

end VG.Proof.Ed448.X86_64.Wnaf
