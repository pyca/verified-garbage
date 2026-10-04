import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Arith
import VerifiedGarbage.Proof.Gcm.AArch64.Ghash
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Gcm.Contract
import VerifiedGarbage.TCB.AArch64.Target
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF

-- Formerly the module `VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups`.
section

/-!
# GHASH with PMULL: the instruction groups

What each group of instructions of `Impl.Gcm.AArch64.Pmull` does to the state,
each proved by one symbolic execution for any registers it is used with, and
what a load and a store of a block are in `Q`.
-/

namespace VG.Proof.Gcm.AArch64.Pmull

open VG VG.AArch64 VG.Proof.Gcm.Poly
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI A T C Y tReg sReg poly)

/-! ## Loads and stores of blocks -/

theorem getLsbD_read (m : Mem) : ∀ (n : Nat) (a : Addr) (i : Nat), i < 8 * n →
    (m.read a n).getLsbD i = (m (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8)
  | 0, _, _, h => absurd h (by omega)
  | n + 1, a, i, h => by
    simp only [Mem.read, BitVec.getLsbD_append]
    by_cases hi : i < 8
    · simp [hi, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
    · simp only [hi, ite_false]
      rw [getLsbD_read m n (a + 1) (i - 8) (by omega)]
      have e1 : (i - 8) / 8 = i / 8 - 1 := by omega
      have e2 : (i - 8) % 8 = i % 8 := by omega
      rw [e1, e2]
      congr 2
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
      omega

theorem vdword_read16 (m : Mem) (p : Addr) {e : Nat} (he : e < 2) :
    vdword (m.read p 16) e = m.readW (p + BitVec.ofNat 64 (8 * e)) 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vdword, Mem.readW, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, hi,
    decide_true, Bool.true_and]
  rw [getLsbD_read m 16 p _ (by omega), getLsbD_read m 8 _ i (by omega), Offset.add_add,
    show 8 * e + i / 8 = (64 * e + i) / 8 by omega, show i % 8 = (64 * e + i) % 8 by omega]

/-- A block, loaded and `rev64`ed. -/
theorem ρ_load (m : Mem) (p : Addr) :
    ρ (VRevOp.eval .rev64b (m.read p 16)) = φ (Spec.Gcm.blockAt m p) := by
  rw [ρ, vdword_rev64b _ (by decide), vdword_rev64b _ (by decide), vdword_read16 m p (by decide),
    vdword_read16 m p (by decide), ← blockAt_rev, φ_append]

theorem read_write16 (m : Mem) (p : Addr) (v : BitVec (8 * 16)) : (m.write p 16 v).read p 16 = v :=
  Mem.read_eq_of_bytes fun i hi => by
    simp only [Mem.write, Mem.sub_ofNat_toNat p (show i < 2 ^ 64 by omega), hi, ite_true]

/-- A block as loaded, `rev64`ed and stored. -/
theorem φ_store (m : Mem) (p : Addr) (v : BitVec 128) :
    φ (Spec.Gcm.blockAt (m.write p 16 (VRevOp.eval .rev64b v)) p) = ρ v := by
  rw [← ρ_load, read_write16, rev64b_rev64b]

/-! ## Reading through writes -/

theorem v_setV (s : State) (d : VReg) (x : BitVec 128) (r : VReg) :
    (s.setV d x).v r = if r = d then x else s.v r := rfl

theorem gpr_setV (s : State) (d : VReg) (x : BitVec 128) : (s.setV d x).gpr = s.gpr := rfl
theorem mem_setV (s : State) (d : VReg) (x : BitVec 128) : (s.setV d x).mem = s.mem := rfl
theorem rd_setV (s : State) (d : VReg) (x : BitVec 128) : (s.setV d x).rd = s.rd := rfl
theorem wr_setV (s : State) (d : VReg) (x : BitVec 128) : (s.setV d x).wr = s.wr := rfl
theorem sp_setV (s : State) (d : VReg) (x : BitVec 128) : (s.setV d x).sp = s.sp := rfl

/-- `s'` differs from `s` at most in the vector registers `rs`. -/
structure VOnly (rs : List VReg) (s s' : State) : Prop where
  v : ∀ r, r ∉ rs → s'.v r = s.v r
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem VOnly.trans {rs rs' : List VReg} {s s' s'' : State} (h : VOnly rs s s')
    (h' : VOnly rs' s' s'') : VOnly (rs ++ rs') s s'' :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    exact (h'.v r hr.2).trans (h.v r hr.1),
   h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp⟩

theorem VOnly.weaken {rs rs' : List VReg} {s s' : State} (h : VOnly rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs' := by decide) : VOnly rs' s s' :=
  ⟨fun r hr => h.v r fun h' => hr (hs r h'), h.gpr, h.mem, h.rd, h.wr, h.sp⟩

theorem VOnly.refl (rs : List VReg) (s : State) : VOnly rs s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The groups -/

/-- The product registers. -/
def prod (s : State) : Prod := ⟨s.v LO, s.v MID, s.v HI⟩

theorem VOnly.prod {rs : List VReg} {s s' : State} (h : VOnly rs s s') (h3 : VReg.v3 ∉ rs)
    (h4 : VReg.v4 ∉ rs) (h5 : VReg.v5 ∉ rs) : Pmull.prod s' = Pmull.prod s := by
  simp only [Pmull.prod, h.v _ h3, h.v _ h4, h.v _ h5]

/-- A register `acc` only reads. -/
def Free (r : VReg) : Prop := r ≠ .v3 ∧ r ≠ .v4 ∧ r ≠ .v5 ∧ r ≠ .v7

theorem exec_pmull0 (d n m : VReg) (s : State) :
    exec (.vop (.pmull false d n m)) s =
      some (s.setV d (polyMul (vdword (s.v n) 0) (vdword (s.v m) 0))) := rfl

theorem exec_pmull1 (d n m : VReg) (s : State) :
    exec (.vop (.pmull true d n m)) s =
      some (s.setV d (polyMul (vdword (s.v n) 1) (vdword (s.v m) 1))) := rfl

theorem exec_eor (d n m : VReg) (s : State) :
    exec (.vop (.logic .eor d n m)) s = some (s.setV d (s.v n ^^^ s.v m)) := rfl

theorem exec_ext8 (d n m : VReg) (s : State) :
    exec (.vop (.ext d n m 8)) s = some (s.setV d (ext8 (s.v n) (s.v m))) := rfl

theorem exec_movi0 (d : VReg) (s : State) : exec (.vop (.movi0 d)) s = some (s.setV d 0) := rfl

theorem exec_rev64b (d n : VReg) (s : State) :
    exec (.vop (.rev .rev64b d n)) s = some (s.setV d (VRevOp.eval .rev64b (s.v n))) := rfl

theorem exec_ldrq {t : VReg} {n : Reg} {off : Nat} {s : State} (ho : off % 16 = 0)
    (ho' : off < 4096 * 16) (hin : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.ldrq t n off) s = some (s.setV t (s.mem.read (s.gpr n + BitVec.ofNat 64 off) 16)) := by
  simp only [exec, addr, ho, ho', and_self, ite_true, Option.bind_some, State.load, hin,
    Option.map_some]

theorem zero_ok (s : State) :
    WP isa (.block Impl.Gcm.AArch64.Pmull.zero) s fun s' =>
      prod s' = Prod.zero ∧ VOnly [LO, MID, HI] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.Pmull.zero, runBlock_cons, runStep_some, runBlock_nil, exec_movi0,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
    by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · simp only [prod, v_setV, ite_true, ite_false, reduceCtorEq]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [v_setV, hr.1, hr.2.1, hr.2.2, ite_false]

theorem acc_ok (a sk t : VReg) (s : State) (ha : Free a) (hs : Free sk) (ht : Free t) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.acc a sk t)) s fun s' =>
      prod s' = (prod s).acc (s.v a) (s.v sk) (s.v t) ∧ VOnly [LO, MID, HI, T] s s' := by
  obtain ⟨ha3, ha4, ha5, ha7⟩ := ha
  obtain ⟨-, -, hs5, hs7⟩ := hs
  obtain ⟨ht3, ht4, ht5, ht7⟩ := ht
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.Pmull.acc, runBlock_cons, runStep_some, runBlock_nil, exec_pmull0,
    exec_pmull1, exec_eor, Option.some.injEq, exists_eq_left', v_setV, ite_true, ite_false,
    reduceCtorEq, ha3, ha4, ha5, ha7, hs5, hs7, ht3, ht4, ht5, ht7]
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
    by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · simp only [prod, Prod.acc, v_setV, ite_true, ite_false, reduceCtorEq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [v_setV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem reduce_ok (d : VReg) (s : State) (hc : s.v C = ofVDwords poly poly) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.reduce d)) s fun s' =>
      s'.v d = reduce (prod s) ∧ VOnly [LO, MID, HI, T, d] s s' := by
  have hc0 : vdword (ofVDwords poly poly) 0 = poly := vdword_append_0 _ _
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.Pmull.reduce, runBlock_cons, runStep_some, runBlock_nil,
    exec_pmull0, exec_eor, exec_ext8, Option.some.injEq, exists_eq_left', v_setV, ite_true,
    ite_false, reduceCtorEq, hc]
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
    by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · simp only [hc0]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [v_setV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- `d ← mul(a, t)` with its halves swapped, a block of class `x · a · t` (`a` as loaded). -/
theorem mul_ok (d a sk t : VReg) (s : State) (ha : Free a) (hs : Free sk) (ht : Free t)
    (hst : s.v sk = ext8 (s.v t) (s.v t)) (hc : s.v C = ofVDwords poly poly) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.mul d a sk t)) s fun s' =>
      ρ (s'.v d) = x * ρ (s.v a) * φ (s.v t) ∧ VOnly [LO, MID, HI, T, d] s s' := by
  rw [Impl.Gcm.AArch64.Pmull.mul, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zero_ok s) fun s₁ ⟨p₁, o₁⟩ => ?_
  refine WP.mono (acc_ok a sk t s₁ ha hs ht) fun s₂ ⟨p₂, o₂⟩ => ?_
  have k : ∀ r, r ≠ .v3 → r ≠ .v4 → r ≠ .v5 → r ≠ .v7 → s₂.v r = s.v r := fun r h3 h4 h5 h7 => by
    rw [o₂.v r (by simp [h3, h4, h5, h7]), o₁.v r (by simp [h3, h4, h5])]
  refine WP.mono (reduce_ok d s₂ (by rw [k C (by decide) (by decide) (by decide) (by decide), hc]))
    fun s₃ ⟨p₃, o₃⟩ => ⟨?_, ?_⟩
  · rw [p₃, ρ_reduce, p₂, p₁, o₁.v a (by simp [ha.1, ha.2.1, ha.2.2.1]),
      o₁.v sk (by simp [hs.1, hs.2.1, hs.2.2.1]), o₁.v t (by simp [ht.1, ht.2.1, ht.2.2.1]), hst,
      Prod.val_acc, Prod.val_zero, zero_add]
  · exact (o₁.trans (o₂.trans o₃)).weaken fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with (h | h | h) | (h | h | h | h) | (h | h | h | h | h) <;> simp [h]

/-- `ext d, n, n, #8`: the halves of `n`, swapped. -/
theorem swap_ok (d n : VReg) (s : State) :
    WP isa (.block [.vop (.ext d n n 8)]) s fun s' =>
      s'.v d = ext8 (s.v n) (s.v n) ∧ VOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_ext8, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
    by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · simp only [v_setV, ite_true]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [v_setV, hr, ite_false]

/-- A 16-byte load at `[n, #off]`, and `rev64`. -/
theorem ldrev_ok (d : VReg) (n : Reg) (off : Nat) (s : State) (ho : off % 16 = 0)
    (ho' : off < 4096 * 16) (hin : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.loadRev d n off)) s fun s' =>
      ρ (s'.v d) = φ (Spec.Gcm.blockAt s.mem (s.gpr n + BitVec.ofNat 64 off)) ∧ VOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.Pmull.loadRev, runBlock_cons, runStep_some, runBlock_nil,
    exec_ldrq ho ho' hin, exec_rev64b,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
    by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · simp only [v_setV, ite_true, ρ_load]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [v_setV, hr, ite_false]

theorem exec_strq {t : VReg} {n : Reg} {off : Nat} {s : State} (ho : off % 16 = 0)
    (ho' : off < 4096 * 16) (hout : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.strq t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 16 (s.v t) } := by
  simp only [exec, addr, ho, ho', and_self, ite_true, Option.bind_some, State.store, hout]

/-- `eor d, n, m`. -/
theorem eor_ok (d n m : VReg) (s : State) :
    WP isa (.block [.vop (.logic .eor d n m)]) s fun s' =>
      s'.v d = s.v n ^^^ s.v m ∧ VOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_eor, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
    by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · simp only [v_setV, ite_true]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [v_setV, hr, ite_false]

/-! ## General-purpose registers and constants -/

theorem v_write (s : State) (sz : Size) (r : Reg) (w : BitVec sz.bits) : (s.write sz r w).v = s.v := rfl
theorem mem_write (s : State) (sz : Size) (r : Reg) (w : BitVec sz.bits) :
    (s.write sz r w).mem = s.mem := rfl
theorem rd_write (s : State) (sz : Size) (r : Reg) (w : BitVec sz.bits) :
    (s.write sz r w).rd = s.rd := rfl
theorem wr_write (s : State) (sz : Size) (r : Reg) (w : BitVec sz.bits) :
    (s.write sz r w).wr = s.wr := rfl

theorem exec_movz_x {d : Reg} {imm : BitVec 16} {hw : Nat} (h : 16 * hw < 64) (s : State) :
    exec (.movz .x d imm hw) s = some (s.write .x d (imm.setWidth 64 <<< (16 * hw))) := by
  simp only [exec, Size.bits, h, ite_true]

theorem exec_dup_d2 (d : VReg) (n : Reg) (s : State) :
    exec (.vop (.dup .d2 d n)) s = some (s.setV d (ofVDwords (s.gpr n) (s.gpr n))) := rfl

theorem exec_ins_d2 {d : VReg} {i : Nat} {n : Reg} (h : i < 2) (s : State) :
    exec (.vop (.ins .d2 d i n)) s = some (s.setV d (setLane (s.v d) 64 i (s.gpr n))) := by
  simp only [exec, VOp.eval, h, ite_true, Option.map_some]

theorem setLane_pair (v : BitVec 128) (a b : BitVec 64) :
    setLane (setLane v 64 0 a) 64 1 b = b ++ a := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [setLane, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, BitVec.getLsbD_append,
    hj, decide_true, Bool.true_and, Nat.mul_zero, Nat.mul_one, Nat.sub_zero]
  by_cases h : j < 64
  · simp only [h, decide_true, ite_true]
    simp
  · simp only [h, decide_false, ite_false, show j - 64 < 64 by omega, show j - 64 < 128 by omega]
    simp [show 64 ≤ j by omega]

theorem gpr_write_x (s : State) (d : Reg) (w : BitVec 64) (r : Reg) :
    (s.write .x d w).gpr r = if r = d then w else s.gpr r := by
  simp only [RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq]

/-- The reduction constant, zero, and `x⁻²` in both orders. -/
theorem consts_ok (s : State) :
    WP isa (.block Impl.Gcm.AArch64.Pmull.consts) s fun s' =>
      s'.v C = ofVDwords poly poly ∧ s'.v (tReg 2) = xInv2 ∧
      s'.v (sReg 2) = ext8 xInv2 xInv2 ∧
      (∀ r, r ≠ C → r ≠ tReg 2 → r ≠ sReg 2 → s'.v r = s.v r) ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.Pmull.consts, tReg, sReg, runBlock_cons, runStep_some, runBlock_nil,
    exec_movz_x (show 16 * 3 < 64 by decide), exec_movz_x (show 16 * 0 < 64 by decide),
    exec_dup_d2, exec_ins_d2 (show 0 < 2 by decide), exec_ins_d2 (show 1 < 2 by decide),
    v_setV, gpr_setV, v_write, gpr_write_x, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left', setLane_pair, mem_setV, rd_setV, wr_setV, mem_write,
    rd_write, wr_write, and_true]
  refine ⟨by decide, by decide, by rw [ext8_eq]; decide, fun r hc ht hs => ?_,
    fun r h5 h6 h7 => ?_⟩
  · simp only [hc, ht, hs, ite_false]
  · simp only [h5, h6, h7, ite_false]

theorem exec_addImm {d n : Reg} {imm : Nat} (h : imm < 4096) (s : State) :
    exec (.addImm .x d n imm) s = some (s.write .x d (s.gpr n + BitVec.ofNat 64 imm)) := by
  simp only [exec, h, ite_true, State.read, Size.bits, BitVec.setWidth_eq]

theorem exec_subImm {d n : Reg} {imm : Nat} (h : imm < 4096) (s : State) :
    exec (.subImm .x d n imm) s = some (s.write .x d (s.gpr n - BitVec.ofNat 64 imm)) := by
  simp only [exec, h, ite_true, State.read, Size.bits, BitVec.setWidth_eq]

theorem exec_lsr {d n : Reg} {sh : Nat} (h : sh < 64) (s : State) :
    exec (.lsr .x d n sh) s = some (s.write .x d (s.gpr n >>> sh)) := by
  simp only [exec, Size.bits, h, ite_true, State.read, BitVec.setWidth_eq]

/-- Past `k` blocks. -/
theorem advance_ok (k : Nat) (hk : 16 * k < 4096) (s : State) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.advance k)) s fun s' =>
      s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 (16 * k) ∧
      s'.gpr .x3 = s.gpr .x3 - BitVec.ofNat 64 k ∧ s'.gpr .x5 = s'.gpr .x3 >>> 3 ∧
      (∀ r, r ≠ .x2 → r ≠ .x3 → r ≠ .x5 → s'.gpr r = s.gpr r) ∧ s'.v = s.v ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.Pmull.advance, runBlock_cons, runStep_some, runBlock_nil,
    exec_addImm hk, exec_subImm (show k < 4096 by omega), exec_lsr (show 3 < 64 by decide),
    gpr_write_x, ite_true,
    ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, fun r h2 h3 h5 => by simp only [h2, h3, h5, ite_false], rfl, rfl, rfl, rfl⟩

/-- `lsr d, n, #sh`. -/
theorem lsr_ok (d n : Reg) (sh : Nat) (hsh : sh < 64) (s : State) :
    WP isa (.block [.lsr .x d n sh]) s fun s' =>
      s'.gpr d = s.gpr n >>> sh ∧ (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.v = s.v ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_lsr hsh, gpr_write_x, ite_true,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r h => by simp only [h, ite_false], rfl, rfl, rfl, rfl⟩

/-! ## The registers of the powers -/

theorem tReg_free (k : Nat) : Free (tReg k) := by
  unfold tReg Free; split <;> decide

theorem sReg_free (k : Nat) : Free (sReg k) := by
  unfold sReg Free; split <;> decide

/-- The registers of the powers are not those of a block's arithmetic or the constants. -/
theorem tReg_nmem (k : Nat) : tReg k ∉ [LO, MID, HI, A, T, Y, C] := by
  unfold tReg; split <;> decide

theorem sReg_nmem (k : Nat) : sReg k ∉ [LO, MID, HI, A, T, Y, C] := by
  unfold sReg; split <;> decide

theorem tReg_nmem' {rs : List VReg} (k : Nat)
    (hs : ∀ r ∈ rs, r ∈ [LO, MID, HI, A, T, Y, C] := by decide) : tReg k ∉ rs :=
  fun h => tReg_nmem k (hs _ h)

theorem sReg_nmem' {rs : List VReg} (k : Nat)
    (hs : ∀ r ∈ rs, r ∈ [LO, MID, HI, A, T, Y, C] := by decide) : sReg k ∉ rs :=
  fun h => sReg_nmem k (hs _ h)

theorem ne_tReg {r : VReg} (k : Nat) (h : r ∈ [LO, MID, HI, A, T, Y, C] := by decide) :
    r ≠ tReg k :=
  fun e => tReg_nmem k (e ▸ h)

theorem ne_sReg {r : VReg} (k : Nat) (h : r ∈ [LO, MID, HI, A, T, Y, C] := by decide) :
    r ≠ sReg k :=
  fun e => sReg_nmem k (e ▸ h)

theorem tReg_ne_sReg (i j : Nat) : tReg i ≠ sReg j := by
  unfold tReg sReg; split <;> split <;> decide

theorem tReg_inj : ∀ i < 9, ∀ j < 9, 1 ≤ i → 1 ≤ j → tReg i = tReg j → i = j := by decide

theorem sReg_inj : ∀ i < 9, ∀ j < 9, 1 ≤ i → 1 ≤ j → sReg i = sReg j → i = j := by decide

end VG.Proof.Gcm.AArch64.Pmull

end

/-!
# GHASH with PMULL: the whole function

`ghash_verified` proves `Impl.Gcm.AArch64.Pmull.ghash` against
`Proof.Gcm.ghashAArch64` (the contract of `vg_ghash`,
`Proof/Gcm/AArch64/Ghash.lean`).

The registers `tReg k` hold `Tₖ` with `x · Tₖ = Hᵏ` (`k = 1 …`, up to 8
once the powers are computed), so that `mul(a, Tₖ) = a · Hᵏ`, `sReg k` the
same with its halves swapped, and `v0` holds `Y` after `i` blocks, as
loaded; the memory is not written until the epilogue stores `Y`.
-/

namespace VG.Proof.Gcm.AArch64.Pmull

open VG VG.AArch64 VG.Proof.Gcm VG.Proof.Gcm.Poly
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI A T C Y tReg sReg poly)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul)

/-! ## `Y` and the blocks -/

/-- `Y` after `i` blocks. -/
abbrev Ys (s₀ : State) (i : Nat) : Block :=
  ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) i)

theorem φ_Ys_succ (s₀ : State) (i : Nat) :
    φ (Ys s₀ (i + 1)) = (φ (Ys s₀ i) + φ (blockAt s₀.mem (blkAddr s₀ i))) * φ (H₀ s₀) := by
  rw [Ys, ghashFrom_blocksAt_succ, φ_mul, φ_xor]

/-- Block `i + j` is in the data. -/
theorem in_blk16 {s₀ : State} (hp : Pre s₀) {i j : Nat} (h : i + j < nb s₀) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 (16 * j)) 16 := by
  have := hp.nb_lt
  refine ⟨dR s₀, by simp [hp.rd], ?_⟩
  rw [blkAddr, Offset.add_add, ← Nat.mul_add]
  exact contains_offset (by omega) (by omega)

theorem add_ofNat_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

theorem shr3_toNat {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n >>> 3).toNat = n / 8 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.shiftRight_eq_div_pow]

theorem shr3_beq {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n >>> 3 == 0) = decide (n < 8) := by
  by_cases h : n < 8
  · have e : BitVec.ofNat 64 n >>> 3 = 0 :=
      BitVec.eq_of_toNat_eq (by rw [shr3_toNat hn]; show n / 8 = 0; omega)
    rw [e, decide_eq_true h]; rfl
  · have e : BitVec.ofNat 64 n >>> 3 ≠ 0 := fun e => by
      have h' := congrArg BitVec.toNat e
      rw [shr3_toNat hn] at h'
      have : n / 8 = 0 := h'
      omega
    rw [beq_eq_false_iff_ne.mpr e, decide_eq_false h]

theorem shr_beq {n : Nat} (s : Nat) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n >>> s == 0) = decide (n < 2 ^ s) := by
  have h : (BitVec.ofNat 64 n >>> s).toNat = n / 2 ^ s := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.shiftRight_eq_div_pow]
  by_cases hlt : n < 2 ^ s
  · have e : BitVec.ofNat 64 n >>> s = 0 :=
      BitVec.eq_of_toNat_eq (by rw [h]; exact Nat.div_eq_of_lt hlt)
    rw [e, decide_eq_true hlt]; rfl
  · have e : BitVec.ofNat 64 n >>> s ≠ 0 := fun e => by
      have h' := congrArg BitVec.toNat e
      rw [h] at h'
      have h0 : n / 2 ^ s = 0 := h'
      have := Nat.div_pos (Nat.le_of_not_lt hlt) (Nat.two_pow_pos s)
      omega
    rw [beq_eq_false_iff_ne.mpr e, decide_eq_false hlt]

theorem shr3_bne {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n >>> 3 != 0) = decide (8 ≤ n) := by
  rw [bne, shr3_beq hn]
  by_cases h : n < 8
  · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false h, decide_eq_true (by omega)]; rfl

theorem ofNat_beq {k : Nat} (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases h : k = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 k ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e; rwa [toNat_ofNat_lt hk] at this)
    rw [beq_eq_false_iff_ne.mpr this]; simp only [h, decide_false]

theorem ofNat_bne {k : Nat} (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k != 0) = decide (k ≠ 0) := by
  rw [bne, ofNat_beq hk]
  by_cases h : k = 0
  · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false h, decide_eq_true h]; rfl

theorem free_A : Free A := by unfold Free; decide

/-! ## The invariant -/

/-- What holds after `i` blocks, with the powers up to `K`. -/
structure Inv (s₀ : State) (K i : Nat) (s : State) : Prop where
  le : i ≤ nb s₀
  c : s.v C = ofVDwords poly poly
  t : ∀ k, 1 ≤ k → k ≤ K → x * φ (s.v (tReg k)) = φ (H₀ s₀) ^ k
  sw : ∀ k, 1 ≤ k → k ≤ K → s.v (sReg k) = ext8 (s.v (tReg k)) (s.v (tReg k))
  y : ρ (s.v Y) = φ (Ys s₀ i)
  x0 : s.gpr .x0 = hA s₀
  x1 : s.gpr .x1 = yp s₀
  x2 : s.gpr .x2 = blkAddr s₀ i
  x3 : s.gpr .x3 = BitVec.ofNat 64 (nb s₀ - i)
  x5 : s.gpr .x5 = s.gpr .x3 >>> 3
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The invariant does not depend on `x6`. -/
theorem Inv.of_x6 {s₀ : State} {K i : Nat} {s s' : State} (hI : Inv s₀ K i s)
    (hg : ∀ r, r ≠ .x6 → s'.gpr r = s.gpr r) (hv : s'.v = s.v) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv s₀ K i s' where
  le := hI.le
  c := by rw [hv, hI.c]
  t k hk hkK := by rw [hv, hI.t k hk hkK]
  sw k hk hkK := by rw [hv, hI.sw k hk hkK]
  y := by rw [hv, hI.y]
  x0 := by rw [hg .x0 (by decide), hI.x0]
  x1 := by rw [hg .x1 (by decide), hI.x1]
  x2 := by rw [hg .x2 (by decide), hI.x2]
  x3 := by rw [hg .x3 (by decide), hI.x3]
  x5 := by rw [hg .x5 (by decide), hg .x3 (by decide), hI.x5]
  mem := by rw [hm, hI.mem]
  rd := by rw [hrd, hI.rd]
  wr := by rw [hwr, hI.wr]

/-! ## The powers -/

theorem nmem_pow {r a b : VReg} (h1 : r ∉ [LO, MID, HI, T]) (h2 : r ≠ a) (h3 : r ≠ b) :
    r ∉ [LO, MID, HI, T, a] ++ [b] := by
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or] at h1 ⊢
  exact ⟨⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2⟩, h3⟩

theorem tReg_ne {i j : Nat} (hi : 1 ≤ i) (hi' : i ≤ 8) (hj : 1 ≤ j) (hj' : j ≤ 8) (h : i ≠ j) :
    tReg i ≠ tReg j := fun e => h (tReg_inj i (by omega) j (by omega) hi hj e)

theorem sReg_ne {i j : Nat} (hi : 1 ≤ i) (hi' : i ≤ 8) (hj : 1 ≤ j) (hj' : j ≤ 8) (h : i ≠ j) :
    sReg i ≠ sReg j := fun e => h (sReg_inj i (by omega) j (by omega) hi hj e)

/-- `H'ᴷ⁺¹ = mul(H'ⁱ, H'ʲ)`. -/
theorem pow_ok {s₀ : State} {K i j n : Nat} (hi : 1 ≤ i) (hiK : i ≤ K) (hj : 1 ≤ j) (hjK : j ≤ K)
    (hij : i + j = K + 1) (hK : K + 1 ≤ 8) {s : State} (hI : Inv s₀ K n s) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.pow (K + 1) i j)) s (Inv s₀ (K + 1) n) := by
  rw [Impl.Gcm.AArch64.Pmull.pow, WP.block_append_iff]
  refine WP.mono (mul_ok (sReg (K + 1)) (sReg i) (sReg j) (tReg j) s (sReg_free _) (sReg_free _)
    (tReg_free _) (hI.sw j hj hjK) hI.c) fun s₁ ⟨m₁, o₁⟩ => ?_
  refine WP.mono (swap_ok (tReg (K + 1)) (sReg (K + 1)) s₁) fun s' ⟨w, o₂⟩ => ?_
  have O := o₁.trans o₂
  have kv : ∀ r, r ∉ [LO, MID, HI, T] → r ≠ tReg (K + 1) → r ≠ sReg (K + 1) → s'.v r = s.v r :=
    fun r h1 h2 h3 => O.v r (nmem_pow h1 h3 h2)
  have ks : s'.v (sReg (K + 1)) = s₁.v (sReg (K + 1)) := o₂.v _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun e => tReg_ne_sReg _ _ e.symm)
  have told : ∀ k, 1 ≤ k → k ≤ K → s'.v (tReg k) = s.v (tReg k) := fun k hk hkK =>
    kv _ (tReg_nmem' k) (tReg_ne hk (by omega) (by omega) hK (by omega)) (tReg_ne_sReg _ _)
  have sold : ∀ k, 1 ≤ k → k ≤ K → s'.v (sReg k) = s.v (sReg k) := fun k hk hkK =>
    kv _ (sReg_nmem' k) (fun e => tReg_ne_sReg _ _ e.symm) (sReg_ne hk (by omega) (by omega) hK (by omega))
  refine ⟨hI.le, by rw [kv C (by decide) (ne_tReg _) (ne_sReg _), hI.c],
    fun k hk hkK => ?_, fun k hk hkK => ?_,
    by rw [kv Y (by decide) (ne_tReg _) (ne_sReg _), hI.y], by rw [O.gpr, hI.x0],
    by rw [O.gpr, hI.x1], by rw [O.gpr, hI.x2], by rw [O.gpr, hI.x3], by rw [O.gpr, hI.x5],
    by rw [O.mem, hI.mem], by rw [O.rd, hI.rd], by rw [O.wr, hI.wr]⟩
  · rcases (by omega : k = K + 1 ∨ k ≤ K) with rfl | hkK'
    · rw [w, φ_ext8_self, m₁, hI.sw i hi hiK, ρ_ext8_self, ← hij, pow_add, ← hI.t i hi hiK,
        ← hI.t j hj hjK]
      ring
    · rw [told k hk hkK', hI.t k hk hkK']
  · rcases (by omega : k = K + 1 ∨ k ≤ K) with rfl | hkK'
    · rw [ks, w, ext8_ext8]
    · rw [told k hk hkK', sold k hk hkK', hI.sw k hk hkK']

theorem powers_ok {s₀ : State} {n : Nat} {s : State} (hI : Inv s₀ 1 n s) :
    WP isa (.block Impl.Gcm.AArch64.Pmull.powers) s (Inv s₀ 8 n) := by
  simp only [Impl.Gcm.AArch64.Pmull.powers, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (pow_ok (K := 1) (i := 1) (j := 1) le_rfl le_rfl le_rfl le_rfl rfl (by decide) hI)
    fun s₂ h₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pow_ok (K := 2) (i := 2) (j := 1) (by decide) le_rfl le_rfl (by decide) rfl
    (by decide) h₂) fun s₃ h₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pow_ok (K := 3) (i := 2) (j := 2) (by decide) (by decide) (by decide) (by decide)
    rfl (by decide) h₃) fun s₄ h₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pow_ok (K := 4) (i := 4) (j := 1) (by decide) le_rfl le_rfl (by decide) rfl
    (by decide) h₄) fun s₅ h₅ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pow_ok (K := 5) (i := 4) (j := 2) (by decide) (by decide) (by decide) (by decide)
    rfl (by decide) h₅) fun s₆ h₆ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pow_ok (K := 6) (i := 4) (j := 3) (by decide) (by decide) (by decide) (by decide)
    rfl (by decide) h₆) fun s₇ h₇ => ?_
  exact pow_ok (K := 7) (i := 4) (j := 4) (by decide) (by decide) (by decide) (by decide) rfl
    (by decide) h₇

/-! ## The blocks -/

/-- After `j` blocks of `k` from the second on, from `sB`: with the first
block's product, which is added last, the product is `Y` after `j + 1` blocks
times `Hᵏ⁻¹⁻ʲ`. -/
def BI (s₀ sB : State) (k i j : Nat) (s : State) : Prop :=
  (prod s).val + (φ (Ys s₀ i) + φ (blockAt s₀.mem (blkAddr s₀ i))) * φ (H₀ s₀) ^ k =
      φ (Ys s₀ (i + 1 + j)) * φ (H₀ s₀) ^ (k - 1 - j) ∧
    VOnly [LO, MID, HI, A, T] sB s

theorem blk_ok {s₀ : State} (hp : Pre s₀) {K k i j : Nat} (hkK : k ≤ K) (hK : K ≤ 8)
    (hj : j + 1 < k) (hi : i + k ≤ nb s₀) {sB s : State} (hI : Inv s₀ K i sB)
    (hB : BI s₀ sB k i j s) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.blk k j)) s (BI s₀ sB k i (j + 1)) := by
  obtain ⟨hv, o⟩ := hB
  rw [Impl.Gcm.AArch64.Pmull.blk, WP.block_append_iff]
  refine WP.mono (ldrev_ok A .x2 (16 * (j + 1)) s (Nat.mul_mod_right 16 _) (by omega)
    (by rw [o.rd, o.wr, o.gpr, hI.rd, hI.wr, hI.x2]; exact in_blk16 hp (by omega)))
    fun s₁ ⟨l₁, o₁⟩ => ?_
  refine WP.mono (acc_ok A (sReg (k - 1 - j)) (tReg (k - 1 - j)) s₁ free_A (sReg_free _)
    (tReg_free _)) fun s₂ ⟨p₂, o₂⟩ => ⟨?_, (o.trans (o₁.trans o₂)).weaken⟩
  have o₀₁ := o.trans o₁
  have hs : s₁.v (sReg (k - 1 - j)) = ext8 (s₁.v (tReg (k - 1 - j))) (s₁.v (tReg (k - 1 - j))) := by
    rw [o₀₁.v _ (sReg_nmem' _), o₀₁.v _ (tReg_nmem' _), hI.sw _ (by omega) (by omega)]
  have ht : x * φ (s₁.v (tReg (k - 1 - j))) = φ (H₀ s₀) ^ (k - 1 - j) := by
    rw [o₀₁.v _ (tReg_nmem' _), hI.t _ (by omega) (by omega)]
  have ha : blockAt s.mem (s.gpr .x2 + BitVec.ofNat 64 (16 * (j + 1))) =
      blockAt s₀.mem (blkAddr s₀ (i + 1 + j)) := by
    rw [o.mem, o.gpr, hI.mem, hI.x2, blkAddr, blkAddr, Offset.add_add, ← Nat.mul_add,
      show i + (j + 1) = i + 1 + j by omega]
  have e : φ (H₀ s₀) ^ (k - 1 - j) = φ (H₀ s₀) ^ (k - 1 - (j + 1)) * φ (H₀ s₀) := by
    rw [← pow_succ]; exact congrArg _ (by omega)
  rw [p₂, hs, Prod.val_acc, o₁.prod (by decide) (by decide) (by decide), l₁, ha,
    show i + 1 + (j + 1) = (i + 1 + j) + 1 by omega, φ_Ys_succ]
  linear_combination hv + (φ (Ys s₀ (i + 1 + j)) + φ (blockAt s₀.mem (blkAddr s₀ (i + 1 + j)))) * e +
    φ (blockAt s₀.mem (blkAddr s₀ (i + 1 + j))) * ht

theorem body_ok {s₀ : State} (hp : Pre s₀) {K k i : Nat} (hk : 1 ≤ k) (hkK : k ≤ K) (hK : K ≤ 8)
    (hi : i + k ≤ nb s₀) {s : State} (hI : Inv s₀ K i s) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.body k)) s (Inv s₀ K (i + k)) := by
  have hn := hp.nb_lt
  simp only [Impl.Gcm.AArch64.Pmull.body, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok s) fun s₁ ⟨p₁, o₁⟩ => ?_
  have b₀ : BI s₀ s k i 0 s₁ := by
    refine ⟨?_, o₁.weaken⟩
    have e : φ (H₀ s₀) ^ k = φ (H₀ s₀) ^ (k - 1 - 0) * φ (H₀ s₀) := by
      rw [← pow_succ]; exact congrArg _ (by omega)
    rw [p₁, Prod.val_zero, zero_add, Nat.add_zero, φ_Ys_succ]
    linear_combination (φ (Ys s₀ i) + φ (blockAt s₀.mem (blkAddr s₀ i))) * e
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (N := k - 1) (BI s₀ s k i)
    (fun j s' hj hB => blk_ok hp hkK hK (by omega) hi hI hB) (k - 1) (Nat.le_refl _) s₁ b₀)
    fun s₂ ⟨p₂, o₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok A .x2 (16 * 0) s₂ rfl (by decide)
    (by rw [o₂.rd, o₂.wr, o₂.gpr, hI.rd, hI.wr, hI.x2]; exact in_blk16 hp (by omega)))
    fun s₃ ⟨l₃, o₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (eor_ok A A Y s₃) fun s₄ ⟨e₄, o₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (acc_ok A (sReg k) (tReg k) s₄ free_A (sReg_free _) (tReg_free _))
    fun s₅ ⟨p₅, o₅⟩ => ?_
  have o₂₄ := o₂.trans (o₃.trans o₄)
  have hv : (prod s₅).val = φ (Ys s₀ (i + k)) := by
    have hs : s₄.v (sReg k) = ext8 (s₄.v (tReg k)) (s₄.v (tReg k)) := by
      rw [o₂₄.v _ (sReg_nmem' _), o₂₄.v _ (tReg_nmem' _), hI.sw _ hk hkK]
    have ht : x * φ (s₄.v (tReg k)) = φ (H₀ s₀) ^ k := by
      rw [o₂₄.v _ (tReg_nmem' _), hI.t _ hk hkK]
    have hy : ρ (s₃.v Y) = φ (Ys s₀ i) := by
      rw [(o₂.trans o₃).v Y (by decide), hI.y]
    have ha : blockAt s₂.mem (s₂.gpr .x2 + BitVec.ofNat 64 (16 * 0)) =
        blockAt s₀.mem (blkAddr s₀ i) := by
      rw [o₂.mem, o₂.gpr, hI.mem, hI.x2, Nat.mul_zero, add_ofNat_zero]
    rw [p₅, hs, Prod.val_acc, (o₃.trans o₄).prod (by decide) (by decide) (by decide), e₄, ρ_xor,
      l₃, hy, ha]
    have e := p₂
    rw [show i + 1 + (k - 1) = i + k by omega, show k - 1 - (k - 1) = 0 by omega, pow_zero,
      mul_one] at e
    linear_combination e + (φ (blockAt s₀.mem (blkAddr s₀ i)) + φ (Ys s₀ i)) * ht
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok Y s₅ (by rw [(o₂₄.trans o₅).v C (by decide), hI.c]))
    fun s₆ ⟨r₆, o₆⟩ => ?_
  refine WP.mono (advance_ok k (by omega) s₆)
    fun s' ⟨f2, f3, f5, fg, fv, fm, frd, fwr⟩ => ?_
  have O : VOnly [LO, MID, HI, A, T, Y] s s₆ :=
    (o₂.trans ((o₃.trans (o₄.trans o₅)).trans o₆)).weaken
  have kv : ∀ r, r ∉ [LO, MID, HI, A, T, Y] → s'.v r = s.v r := fun r h => by rw [fv, O.v r h]
  have kg : ∀ r, r ≠ .x2 → r ≠ .x3 → r ≠ .x5 → s'.gpr r = s.gpr r := fun r h2 h3 h5 => by
    rw [fg r h2 h3 h5, O.gpr]
  refine ⟨by omega, by rw [kv C (by decide), hI.c],
    fun m hm hmK => by rw [kv _ (tReg_nmem' _), hI.t m hm hmK],
    fun m hm hmK => by rw [kv _ (sReg_nmem' _), kv _ (tReg_nmem' _), hI.sw m hm hmK], ?_,
    by rw [kg .x0 (by decide) (by decide) (by decide), hI.x0],
    by rw [kg .x1 (by decide) (by decide) (by decide), hI.x1], ?_, ?_, f5,
    by rw [fm, O.mem, hI.mem], by rw [frd, O.rd, hI.rd], by rw [fwr, O.wr, hI.wr]⟩
  · rw [fv, r₆, ρ_reduce, hv]
  · rw [f2, O.gpr, hI.x2, blkAddr, blkAddr, Offset.add_add, ← Nat.mul_add]
  · rw [f3, O.gpr, hI.x3, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]

/-! ## The prologue and the epilogue -/

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block Impl.Gcm.AArch64.Pmull.prologue) s₀ (Inv s₀ 1 0) := by
  simp only [Impl.Gcm.AArch64.Pmull.prologue, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok A .x0 0 s₀ rfl (by decide)
    ⟨hR s₀, by simp [hp.rd], contains_offset (by decide) (by decide)⟩) fun s₁ ⟨l₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok s₁) fun s₂ ⟨c₂, t₂, w₂, kv₂, kg₂, m₂, rd₂, wr₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mul_ok (sReg 1) A (sReg 2) (tReg 2) s₂ free_A (sReg_free _) (tReg_free _)
    (by rw [w₂, t₂]) c₂) fun s₃ ⟨m₃, o₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (swap_ok (tReg 1) (sReg 1) s₃) fun s₄ ⟨w₄, o₄⟩ => ?_
  have g₄ : ∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → s₄.gpr r = s₀.gpr r := fun r h5 h6 h7 => by
    rw [o₄.gpr, o₃.gpr, kg₂ r h5 h6 h7, o₁.gpr]
  have mem₄ : s₄.mem = s₀.mem := by rw [o₄.mem, o₃.mem, m₂, o₁.mem]
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok Y .x1 0 s₄ rfl (by decide)
    (by rw [o₄.rd, o₄.wr, o₃.rd, o₃.wr, rd₂, wr₂, o₁.rd, o₁.wr,
      g₄ .x1 (by decide) (by decide) (by decide)]
        exact ⟨yR s₀, by simp [hp.wr], contains_offset (by decide) (by decide)⟩))
    fun s₅ ⟨l₅, o₅⟩ => ?_
  refine WP.mono (lsr_ok .x5 .x3 3 (by decide) s₅) fun s' ⟨f5, fg, fv, fm, frd, fwr⟩ => ?_
  have g : ∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → s'.gpr r = s₀.gpr r := fun r h5 h6 h7 => by
    rw [fg r h5, o₅.gpr, g₄ r h5 h6 h7]
  have O : VOnly ([tReg 1] ++ [Y]) s₃ s₅ := o₄.trans o₅
  have t₁ : s'.v (tReg 1) = ext8 (s₃.v (sReg 1)) (s₃.v (sReg 1)) := by
    rw [fv, o₅.v _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact (ne_tReg (r := Y) 1).symm), w₄]
  have s₁' : s'.v (sReg 1) = s₃.v (sReg 1) := by
    rw [fv, O.v _ (by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun e => tReg_ne_sReg _ _ e.symm, (ne_sReg (r := Y) 1).symm⟩)]
  have hA₂ : s₂.v A = s₁.v A := kv₂ A (by decide) (ne_tReg 2) (ne_sReg 2)
  refine ⟨Nat.zero_le _, ?_, fun k hk hk1 => ?_, fun k hk hk1 => ?_, ?_,
    by rw [g .x0 (by decide) (by decide) (by decide)],
    by rw [g .x1 (by decide) (by decide) (by decide)],
    by rw [g .x2 (by decide) (by decide) (by decide)]; simp [blkAddr],
    by rw [g .x3 (by decide) (by decide) (by decide)]; simp [nb],
    by rw [f5, fg .x3 (by decide)], by rw [fm, o₅.mem, mem₄],
    by rw [frd, o₅.rd, o₄.rd, o₃.rd, rd₂, o₁.rd], by rw [fwr, o₅.wr, o₄.wr, o₃.wr, wr₂, o₁.wr]⟩
  · have h : C ∉ [LO, MID, HI, T, sReg 1] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨by decide, by decide, by decide, by decide, ne_sReg 1⟩
    have h' : C ∉ [tReg 1] ++ [Y] := by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨ne_tReg 1, by decide⟩
    rw [fv, O.v C h', o₃.v C h, c₂]
  · obtain rfl : k = 1 := by omega
    rw [t₁, φ_ext8_self, m₃, hA₂, l₁, t₂, add_ofNat_zero]
    linear_combination φ (H₀ s₀) * x2_φ_xInv2
  · obtain rfl : k = 1 := by omega
    rw [t₁, s₁', ext8_ext8]
  · rw [fv, l₅, mem₄, g₄ .x1 (by decide) (by decide) (by decide), add_ofNat_zero]
    exact congrArg φ (ghashFrom_blocksAt_zero _ _ _ _).symm

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {K : Nat} {s : State} (hI : Inv s₀ K (nb s₀) s) :
    WP isa (.block Impl.Gcm.AArch64.Pmull.epilogue) s fun s' => Proof.Gcm.ghashAArch64.post s₀ s' := by
  have hout : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 0) 16 := by
    rw [hI.wr, hI.x1]
    exact ⟨yR s₀, by simp [hp.wr], contains_offset (by decide) (by decide)⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_rev64b Y Y s, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_strq (s := s.setV Y _) (by decide) (by decide) hout,
    WP.block_nil ?_⟩
  show blockAt ((s.setV Y _).mem.write ((s.setV Y _).gpr .x1 + BitVec.ofNat 64 0) 16
    ((s.setV Y _).v Y)) (yp s₀) = Ys s₀ (nb s₀)
  apply φ_inj
  simp only [mem_setV, gpr_setV, v_setV, ↓reduceIte, hI.x1, add_ofNat_zero, φ_store, hI.y]

/-! ## The whole function -/

theorem WP.seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq a b) s fun s' => WP isa c s' Q) : WP isa (.seq a (.seq b c)) s Q := by
  rw [WP.seq_iff] at h
  exact WP.seq (WP.mono h fun _ h' => WP.seq h')

/-- The remaining blocks, one at a time. -/
theorem ones_ok {s₀ : State} (hp : Pre s₀) {K i : Nat} (hK1 : 1 ≤ K) (hK8 : K ≤ 8) {s : State}
    (hI : Inv s₀ K i s) :
    WP isa (.ite (.zero .x .x3) (.block [])
      (.loop (.block (Impl.Gcm.AArch64.Pmull.body 1)) (.nonzero .x .x3))) s (Inv s₀ K (nb s₀)) := by
  have hn := hp.nb_lt
  have hev : eval (.zero .x .x3) s = some (decide (nb s₀ - i = 0)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI.x3,
      ofNat_beq (show nb s₀ - i < 2 ^ 64 by omega)]
  refine WP.ite _ hev (fun h => ?_) (fun h => ?_)
  · have : i = nb s₀ := by have := hI.le; simp only [decide_eq_true_eq] at h; omega
    exact WP.block_nil (this ▸ hI)
  · let Inv1 : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ Inv s₀ K i s
    have hstep : ∀ m s, Inv1 m s → WP isa (.block (Impl.Gcm.AArch64.Pmull.body 1)) s (fun s' =>
        (eval (.nonzero .x .x3) s' = some false ∧ Inv s₀ K (nb s₀) s') ∨
        (eval (.nonzero .x .x3) s' = some true ∧ ∃ m' < m, Inv1 m' s')) := by
      rintro m s ⟨i, rfl, hi, hI⟩
      refine WP.mono (body_ok hp le_rfl hK1 hK8 (by omega) hI) fun s' hI' => ?_
      have hev : eval (.nonzero .x .x3) s' = some (decide (nb s₀ - (i + 1) ≠ 0)) := by
        simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI'.x3,
          ofNat_bne (show nb s₀ - (i + 1) < 2 ^ 64 by omega)]
      by_cases hlast : nb s₀ - (i + 1) = 0
      · have : i + 1 = nb s₀ := by omega
        exact .inl ⟨by rw [hev, decide_eq_false (not_not.mpr hlast)], this ▸ hI'⟩
      · exact .inr ⟨by rw [hev, decide_eq_true hlast], nb s₀ - (i + 1), by omega, i + 1, rfl,
          by omega, hI'⟩
    have hlt : i < nb s₀ := by have := hI.le; simp only [decide_eq_false_iff_not] at h; omega
    exact WP.loop (M := isa) Inv1 hstep (nb s₀ - i) s ⟨i, rfl, hlt, hI⟩

/-- `k` blocks if bit `sh` of the remaining count (less than `2 ^ (sh + 1)`) is
set, with `k = 2 ^ sh`. -/
theorem bit_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (sh k : Nat) (hk : k = 2 ^ sh) (hk1 : 1 ≤ k)
    (hk8 : k ≤ 8) (hsh : sh < 64) (hi : nb s₀ - i < 2 * k) {s : State} (hI : Inv s₀ 8 i s) :
    WP isa (.seq (.block [.lsr .x .x6 .x3 sh])
      (.ite (.zero .x .x6) (.block []) (.block (Impl.Gcm.AArch64.Pmull.body k)))) s
      (fun s' => ∃ i', nb s₀ - i' < k ∧ Inv s₀ 8 i' s') := by
  have hn := hp.nb_lt
  refine WP.seq (WP.mono (lsr_ok .x6 .x3 sh hsh s) fun s₁ ⟨f6, fg, fv, fm, frd, fwr⟩ => ?_)
  have hI₁ := hI.of_x6 fg fv fm frd fwr
  have hev : eval (.zero .x .x6) s₁ = some (decide (nb s₀ - i < k)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, f6, hI.x3,
      shr_beq sh (show nb s₀ - i < 2 ^ 64 by omega), hk]
  refine WP.ite _ hev (fun h => WP.block_nil ⟨i, by simpa using h, hI₁⟩) (fun h => ?_)
  simp only [decide_eq_false_iff_not, Nat.not_lt] at h
  exact WP.mono (body_ok hp hk1 hk8 le_rfl (by omega) hI₁) fun s' h' => ⟨i + k, by omega, h'⟩

/-- The last `n mod 8` blocks, once the powers are computed. -/
theorem tail_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : nb s₀ - i < 8) {s : State}
    (hI : Inv s₀ 8 i s) :
    WP isa Impl.Gcm.AArch64.Pmull.tail s (Inv s₀ 8 (nb s₀)) := by
  have hn := hp.nb_lt
  unfold Impl.Gcm.AArch64.Pmull.tail
  refine WP.seq_assoc (WP.mono (bit_ok hp 2 4 rfl (by decide) (by decide) (by decide) (by omega) hI)
    fun s₁ ⟨i₁, hi₁, hI₁⟩ => ?_)
  refine WP.seq_assoc (WP.mono (bit_ok hp 1 2 rfl (by decide) (by decide) (by decide) (by omega)
    hI₁) fun s₂ ⟨i₂, hi₂, hI₂⟩ => ?_)
  have hev : eval (.zero .x .x3) s₂ = some (decide (nb s₀ - i₂ = 0)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI₂.x3,
      ofNat_beq (show nb s₀ - i₂ < 2 ^ 64 by omega)]
  refine WP.ite _ hev (fun h => ?_) (fun h => ?_)
  · have : i₂ = nb s₀ := by have := hI₂.le; simp only [decide_eq_true_eq] at h; omega
    exact WP.block_nil (this ▸ hI₂)
  · simp only [decide_eq_false_iff_not] at h
    have : i₂ + 1 = nb s₀ := by omega
    exact this ▸ body_ok hp le_rfl (by decide) le_rfl (by omega) hI₂

theorem loops_ok {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.Gcm.AArch64.Pmull.ghash s₀ fun s' => Proof.Gcm.ghashAArch64.post s₀ s' := by
  have hn := hp.nb_lt
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ hI₁ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ K, Inv s₀ K (nb s₀) s) ?_
    fun s₂ ⟨K, hI₂⟩ => epilogue_ok hp hI₂)
  have hev : eval (.zero .x .x5) s₁ = some (decide (nb s₀ < 8)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI₁.x5, hI₁.x3, Nat.sub_zero,
      shr3_beq (show nb s₀ < 2 ^ 64 by omega)]
  refine WP.ite _ hev (fun _ => WP.mono (ones_ok hp le_rfl (by decide) hI₁) fun s h => ⟨1, h⟩)
    (fun h => ?_)
  simp only [decide_eq_false_iff_not, Nat.not_lt] at h
  refine WP.seq (WP.mono (powers_ok hI₁) fun s₃ hI₃ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ i, nb s₀ - i < 8 ∧ Inv s₀ 8 i s) ?_
    fun s₄ ⟨i, hi, hI₄⟩ => WP.mono (tail_ok hp hi hI₄) fun s h => ⟨8, h⟩)
  let Inv8 : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i + 8 ≤ nb s₀ ∧ Inv s₀ 8 i s
  have hstep : ∀ m s, Inv8 m s → WP isa (.block (Impl.Gcm.AArch64.Pmull.body 8)) s (fun s' =>
      (eval (.nonzero .x .x5) s' = some false ∧ ∃ i, nb s₀ - i < 8 ∧ Inv s₀ 8 i s') ∨
      (eval (.nonzero .x .x5) s' = some true ∧ ∃ m' < m, Inv8 m' s')) := by
    rintro m s ⟨i, rfl, hi, hI⟩
    refine WP.mono (body_ok hp (by decide) le_rfl le_rfl hi hI) fun s' hI' => ?_
    have hev : eval (.nonzero .x .x5) s' = some (decide (8 ≤ nb s₀ - (i + 8))) := by
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI'.x5, hI'.x3,
        shr3_bne (show nb s₀ - (i + 8) < 2 ^ 64 by omega)]
    by_cases h8 : 8 ≤ nb s₀ - (i + 8)
    · exact .inr ⟨by rw [hev, decide_eq_true h8], nb s₀ - (i + 8), by omega, i + 8, rfl,
        by omega, hI'⟩
    · exact .inl ⟨by rw [hev, decide_eq_false h8], i + 8, by omega, hI'⟩
  exact WP.loop (M := isa) Inv8 hstep (nb s₀) s₃ ⟨0, rfl, by omega, hI₃⟩

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.Gcm.AArch64.Pmull.ghash s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Gcm.ghashAArch64.post s₀ s' :=
  WP.mono (WP.gprs (rs := preserved) (loops_ok hp) (by decide +kernel) (by decide +kernel))
    fun _ ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩

theorem ghash_correct (s : State) (hs : Proof.Gcm.ghashAArch64.pre s) :
    ∃ t s', Exec isa Impl.Gcm.AArch64.Pmull.ghash s t s' ∧ abiPreserved s s' ∧
      Proof.Gcm.ghashAArch64.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem ghash_ct : ConstantTime isa Proof.Gcm.ghashAArch64.pre Proof.Gcm.ghashAArch64.pub
    Impl.Gcm.AArch64.Pmull.ghash := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem ghash_verified :
    Verified AArch64.target Impl.Gcm.AArch64.Pmull.ghash (Spec.Gcm.ghashContract AArch64.abi) :=
  Verified.of_correct ghash_correct ghash_ct (by
    sig_implies [Spec.Gcm.ghashContract, Spec.Gcm.ghashSig, Proof.Gcm.ghashAArch64, AArch64.abi,
      AArch64.argRegs] [Proof.Gcm.AArch64.satState] using Proof.Gcm.AArch64.satState)

end VG.Proof.Gcm.AArch64.Pmull
