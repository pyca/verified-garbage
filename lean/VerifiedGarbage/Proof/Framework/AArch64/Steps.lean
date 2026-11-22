module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce

/-!
# AArch64: weakest preconditions one instruction at a time

Untrusted: everything here is checked by Lean. For code whose blocks are
proven an instruction at a time, as x86-64's `Steps` does: each `wp_*` rule
runs the first instruction of a block and hands the rest a state described
by `Upd` (one register written, the flags aside) or `Mupd` (memory written),
so the caller reads registers through the writes without unfolding them.
-/

@[expose] public section

namespace VG.AArch64.Steps

/-- `s'` is `s` with register `d` set to `v` (the flags aside). -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  syms : s'.syms = s.syms

theorem Upd.write (s : State) (d : Reg) (v : BitVec 64) : Upd s (s.write .x d v) d v :=
  ⟨by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _, fun _ h => RegUpd.gpr_write_of_ne _ _ _ h,
    RegUpd.sp_write _ _ _ _, RegUpd.mem_write _ _ _ _, RegUpd.rd_write _ _ _ _, RegUpd.wr_write _ _ _ _, rfl⟩

/-- `s'` is `s` with memory `m` (the flags aside). -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  sp : s'.sp = s.sp
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  syms : s'.syms = s.syms

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `add d, n, #imm` (`mov d, n` for `imm = 0`). -/
theorem wp_addImm {d n : Reg} {imm : Nat} (hi : imm < 4096)
    (k : ∀ s', Upd s s' d (s.gpr n + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addImm .x d n imm :: is)) s Q :=
  WP.cons (exec_addImm_x hi) (by
    have := k _ (Upd.write s d (s.gpr n + BitVec.ofNat 64 imm))
    simpa only [State.read, Size.bits, BitVec.setWidth_eq] using this)

/-- `add d, n, m`. -/
theorem wp_add {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n + s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.add .x d n m :: is)) s Q :=
  WP.cons exec_add (by
    have := k _ (Upd.write s d (s.gpr n + s.gpr m))
    simpa only [State.read, Size.bits, BitVec.setWidth_eq] using this)

/-- `sub d, n, m`. -/
theorem wp_sub {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n - s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.sub .x d n m :: is)) s Q :=
  WP.cons rfl (by
    have := k _ (Upd.write s d (s.gpr n - s.gpr m))
    simpa only [State.read, Size.bits, BitVec.setWidth_eq] using this)

/-- `movz d, #imm`. -/
theorem wp_movz {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm.setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.movz .x d imm 0 :: is)) s Q :=
  WP.cons (by simp only [reduceExec]; rfl) (by
    have := k _ (Upd.write s d (imm.setWidth 64))
    simpa only [Size.bits, Nat.mul_zero, BitVec.shiftLeft_zero] using this)

/-- `ldr d, [n, #off]`, a load of eight bytes the regions allow. -/
theorem wp_ldr {d n : Reg} {off : Nat} {a : Addr} (ho : off % 8 = 0 ∧ off < 32768)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Upd s s' d (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr .x d n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_ldr_x ho hin) (k _ (Upd.write _ _ _))

/-- `add d, sp, #imm`. -/
theorem wp_addSp {d : Reg} {imm : Nat} (hi : imm < 4096)
    (k : ∀ s', Upd s s' d (s.sp + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addSp d imm :: is)) s Q :=
  WP.cons (by simp only [reduceExec, hi, ite_true]) (k _ (Upd.write _ _ _))

/-- `str t, [sp, #off]`. -/
theorem wp_strSp {t : Reg} {off : Nat} {a : Addr} (ho : off % 8 = 0 ∧ off < 32768)
    (ha : s.sp + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.strSp t off :: is)) s Q := by
  subst ha
  refine WP.cons (s' := { s with mem := s.mem.writeW (s.sp + BitVec.ofNat 64 off) (s.gpr t) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp only [reduceExec, ho, and_self, ite_true, State.store, hout, State.read, Size.bits,
    BitVec.setWidth_eq, Mem.writeW]

/-- `ldr t, [sp, #off]`. -/
theorem wp_ldrSp {t : Reg} {off : Nat} {a : Addr} (ho : off % 8 = 0 ∧ off < 32768)
    (ha : s.sp + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Upd s s' t (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrSp t off :: is)) s Q := by
  subst ha
  refine WP.cons ?_ (k _ (Upd.write _ _ _))
  simp only [reduceExec, ho, and_self, ite_true, State.load, hin, Option.map_some, Mem.readW,
    BitVec.setWidth_eq]

/-- `strb t, [n, #off]`: the low byte of `t`. -/
theorem wp_strb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.write a 1 ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.strb t n off :: is)) s Q := by
  subst ha
  refine WP.cons (s' := { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 1 ((s.gpr t).setWidth 8) })
    ?_ (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp only [reduceExec, addr, Nat.mod_one, Nat.mul_one, ho, and_self, ite_true, Option.bind_some, State.store,
    hout, State.read, Size.bits, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide), Nat.mul_one]

/-- `subs d, n, m`: C, no borrow, is `m ≤ n` (unsigned). -/
theorem wp_subs {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n - s.gpr m) → s'.c = decide ((s.gpr m).toNat ≤ (s.gpr n).toNat) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.subs .x d n m :: is)) s Q := by
  refine WP.cons rfl (k _ ⟨?_, fun r h => ?_, rfl, rfl, rfl, rfl, rfl⟩ ?_)
  · rw [RegUpd.gpr_addWithCarry]
    simp only [ite_true, State.read, Size.bits, BitVec.setWidth_eq, Bool.toNat_true]
    rw [BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add, BitVec.add_assoc]
  · rw [RegUpd.gpr_addWithCarry]; simp only [h, ite_false]
  · rw [RegUpd.c_addWithCarry]
    simp only [State.read, Size.bits, BitVec.setWidth_eq, Bool.toNat_true, BitVec.toNat_not]
    have := (s.gpr m).isLt
    have := (s.gpr n).isLt
    exact decide_eq_decide.mpr (by omega)

/-- `csel d, n, m, hs`: `n` if C is set, else `m`. -/
theorem wp_cselHs {d n m : Reg}
    (k : ∀ s', Upd s s' d (if s.c then s.gpr n else s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.cselc .x d n m .hs :: is)) s Q :=
  WP.cons rfl (by
    have := k _ (Upd.write s d (if s.c then s.gpr n else s.gpr m))
    simpa only [CondCode.holds, State.read, Size.bits, BitVec.setWidth_eq, apply_ite (BitVec.setWidth 64)] using this)

end

end VG.AArch64.Steps
