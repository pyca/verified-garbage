module

import VerifiedGarbage.Proof.Ed25519.X86_64.PointAccumulateLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowersLoop
public import VerifiedGarbage.Impl.Ed25519.X86_64.PointMul
public import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowers
import VerifiedGarbage.Proof.Ed25519.X86_64.Points
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Lit

/-! Merged from `Proof.Ed25519.X86_64.PointBatch`. -/

@[expose] public section

section
/-! The local table preserves the accumulator, bits, and checkpoints. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Keeps clob)

variable {fld : Arith} [EdArith fld]

theorem PowersKeep.of_keep {base : Addr} {o n : Nat} {s t : State} (h : Keep base s t) :
    PowersKeep base o n s t := ⟨fun r _ _ hr => h.gpr r hr, h.rd, h.wr, TableFrame.workspace h.mem⟩

end VG.Proof.Ed25519.X86_64
end

/-! The public batch counter survives field and table operations. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Outside Keeps ea_sc)

theorem batchBegin_ok {s : State} {base : Addr} (hs : Scratch s base)
    (j : Nat) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1)) :
    WP isa (.block batchBegin) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 j ∧ t.mem.readW (off base 56) 64 = BitVec.ofNat 64 j ∧
      (∀ r, r ≠ .rbx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base 56 8 s.mem t.mem := by
  have hw : InRegions s.wr (off base 56) 8 :=
    ⟨_, hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  have hr : InRegions (s.rd ++ s.wr) (off base 56) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  have he : BitVec.ofNat 64 (j + 1) - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 j := by
    rw [show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [batchBegin, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.load64, State.store64, ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, hs.rdi, hr, hw, hc, he,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, fun r hr => ?_, trivial, trivial, ?_⟩
  · exact Mem.readW_writeW_self64 _ _ _
  · simp only [hr, ite_false]
  · intro p hp
    exact VG.Proof.X25519.X86_64.writeW_outside _ _ _ (by decide) p hp

end VG.Proof.Ed25519.X86_64
