module
public import VerifiedGarbage.Impl.Ed448.X86_64.ScalarBase
public import VerifiedGarbage.Proof.Ed448.Formulas
public import VerifiedGarbage.Proof.X448.X86_64.Env

import VerifiedGarbage.Proof.X448.X86_64.Inv
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop
import VerifiedGarbage.Proof.Ed448.X86_64.BaseConst
import VerifiedGarbage.Proof.Framework.Block
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Nat.Totient
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig

/-! Reset the accumulator after building the projective table. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Wnaf
open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.Ed448 VG.Proof.X448.X86_64

structure InitPost (base : Addr) (s u : State) : Prop where
  scr : Scr u base
  rbx : u.gpr .rbx = BitVec.ofNat 64 461
  gpr : ∀ r, r ∉ .rbx :: clob → u.gpr r = s.gpr r
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  mem : Outside base 64 1584 s.mem u.mem
  d : E u.mem base 11 = E s.mem base 11
  p : pt (E u.mem base) 0 1 2 = Spec.Ed448.identity

theorem initPoint_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block (constSlot 0 0 ++ constSlot 1 1 ++ constSlot 2 1 ++
      ([.mov32 .rbx (.imm 461)] : List Instr))) s (InitPost base s) := by
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (constE_ok hs 0 0 c0) fun a ⟨ka, ea⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (constE_ok (ka.scr hs) 1 1 c1) fun b ⟨kb, eb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (constE_ok (kb.scr (ka.scr hs)) 2 1 c1) fun c ⟨kc, ec⟩ => ?_
  refine WP.mono (setRbx_ok c 461 (by decide)) fun u ⟨ub, ug, um, ur, uw⟩ => ?_
  have ks := (ka.trans kb).trans kc
  refine ⟨⟨(ug _ (by decide)).trans (ks.scr hs).rdi, uw ▸ (ks.scr hs).wr, hs.nowrap⟩,
    ub, ?_, ur.trans ks.rd, uw.trans ks.wr, ?_, ?_, ?_⟩
  · intro r hr
    have hrc : r ∉ clob := fun hh => hr (List.mem_cons_of_mem _ hh)
    have hrb : r ≠ .rbx := fun hh => hr (by simp [hh])
    exact (ug r hrb).trans (ks.gpr r hrc)
  · rw [um]; exact ks.mem
  · rw [um, ec, eb, ea]; rfl
  · rw [um, ec, eb, ea]; rfl

end VG.Proof.Ed448.X86_64.Wnaf
