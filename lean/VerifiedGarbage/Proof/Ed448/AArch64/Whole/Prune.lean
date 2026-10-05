import VerifiedGarbage.Impl.Ed448.AArch64.Whole
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
import VerifiedGarbage.Proof.Ed448.PruneBytes
import VerifiedGarbage.Proof.Ed448.Signing
import VerifiedGarbage.Spec.Sha3

/-!
# Ed448's complete operations on AArch64: pruning a hash in the frame

`pruneAt h d` stores the first 57 bytes of the hash at `sp + h`, pruned
(`Spec.Ed448.prune`), as the scalar at `sp + d` (`prune_run`), writing only
the scalar's 64 bytes.
-/

namespace VG.Proof.Ed448.AArch64.Whole

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Whole

/-- Word `k` of the scalar, from word `k` of the hash. -/
def pruneValue (k : Nat) (x : BitVec 64) : BitVec 64 :=
  if k = 0 then x &&& BitVec.ofNat 64 (2 ^ 64 - 4)
  else if k = 6 then x ||| BitVec.ofNat 64 (2 ^ 63)
  else x

structure Step (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  v : t.v = s.v
  regs : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x14 → r ≠ .x15 → t.gpr r = s.gpr r

theorem Step.refl (s : State) : VG.Proof.Ed448.AArch64.Whole.Step s s := ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ _ => rfl⟩

theorem Step.trans {s t u : State} (h : VG.Proof.Ed448.AArch64.Whole.Step s t) (h' : VG.Proof.Ed448.AArch64.Whole.Step t u) : VG.Proof.Ed448.AArch64.Whole.Step s u :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp, h'.v.trans h.v,
    fun r h9 h10 h14 h15 => (h'.regs r h9 h10 h14 h15).trans (h.regs r h9 h10 h14 h15)⟩

theorem pruneWord_ok {s : State} {h d k : Nat} (hk : k < 7) (hh8 : h % 8 = 0) (hhl : h + 64 ≤ 256)
    (hdl : d + 64 ≤ 256)
    (hr : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (h + 8 * k)) 8)
    (hw : InRegions s.wr (s.sp + BitVec.ofNat 64 (d + 8 * k)) 8) :
    WP isa (.block (pruneWord h d k)) s fun t => VG.Proof.Ed448.AArch64.Whole.Step s t ∧
      t.mem = s.mem.writeW (s.sp + BitVec.ofNat 64 (d + 8 * k))
        (pruneValue k (s.mem.readW (s.sp + BitVec.ofNat 64 (h + 8 * k)) 64)) := by
  have ho : (h + 8 * k) % 8 = 0 ∧ h + 8 * k < 32768 := by omega
  have hs : d + 8 * k < 4096 := by omega
  apply WP.of_runBlock
  by_cases h0 : k = 0
  · subst k
    simp only [Nat.mul_zero, Nat.add_zero] at hr hw ho hs
    simp only [pruneWord, pruneLow, pruneValue, ite_true, List.cons_append, List.nil_append,
      Nat.mul_zero, Nat.add_zero, runBlock_cons, runStep_some, runBlock_nil, exec, State.load, Size.bits,
      Size.bytes, State.read, State.store, addr, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
      RegUpd.wr_write, RegUpd.sp_write, RegUpd.v_write, BitVec.setWidth_eq, ho, hs,
      Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
      ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, hr, hw,
      BitVec.shiftLeft_zero, BitVec.add_zero, Mem.readW, Mem.writeW, Option.some.injEq,
      exists_eq_left']
    refine ⟨⟨rfl, rfl, rfl, rfl, ?_⟩, ?_⟩
    · intro r h9 h10 _ h15
      simp only [RegUpd.gpr_write, h9, h10, h15, ite_false]
    · rfl
  · by_cases h6 : k = 6
    · subst k
      simp only [Nat.reduceMul] at hr hw ho hs
      simp only [pruneWord, pruneHigh, pruneValue, h0, ite_true, ite_false,
        List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
        exec, State.load, Size.bits, Size.bytes, State.read, State.store, addr,
        RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
        RegUpd.sp_write, RegUpd.v_write, BitVec.setWidth_eq, ho, hs,
        Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
        ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, hr, hw,
        BitVec.add_zero, Mem.readW, Mem.writeW, Option.some.injEq,
        exists_eq_left']
      refine ⟨⟨rfl, rfl, rfl, rfl, ?_⟩, ?_⟩
      · intro r h9 h10 _ h15
        simp only [RegUpd.gpr_write, h9, h10, h15, ite_false]
      · rfl
    · simp only [pruneWord, pruneValue, h0, h6, ite_false, List.cons_append, List.nil_append,
        runBlock_cons, runStep_some, runBlock_nil, exec, State.load, Size.bits, Size.bytes,
        State.read, State.store, addr, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
        RegUpd.wr_write, RegUpd.sp_write, RegUpd.v_write, BitVec.setWidth_eq,
        ho, hs, and_self, ite_true, ite_false, reduceCtorEq, Option.map_some,
        Option.bind_some, hr, hw, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, BitVec.add_zero,
        Mem.readW, Mem.writeW, Option.some.injEq, exists_eq_left']
      refine ⟨⟨rfl, rfl, rfl, rfl, ?_⟩, True.intro⟩
      intro r h9 _ _ h15
      simp only [RegUpd.gpr_write, h9, h15, ite_false]

structure PruneInv (h d : Nat) (s : State) (n : Nat) (t : State) : Prop where
  step : VG.Proof.Ed448.AArch64.Whole.Step s t
  frame : Frame [⟨s.sp + BitVec.ofNat 64 d, 64⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (s.sp + BitVec.ofNat 64 (d + 8 * j)) 64 =
    pruneValue j (s.mem.readW (s.sp + BitVec.ofNat 64 (h + 8 * j)) 64)

theorem prunePrefix_ok {s : State} {h d : Nat} (hw : (⟨s.sp, 256⟩ : Region) ∈ s.wr) (hh8 : h % 8 = 0)
    (hhl : h + 64 ≤ 256) (hdl : d + 64 ≤ 256) (hsep : d + 64 ≤ h ∨ h + 64 ≤ d) :
    ∀ n ≤ 7, WP isa (.block ((List.range n).flatMap (pruneWord h d))) s (PruneInv h d s n)
  | 0, _ => WP.block_nil ⟨.refl s, Frame.refl _ _, fun _ h => by omega⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (prunePrefix_ok hw hh8 hhl hdl hsep n (by omega)) fun u hu => ?_
    have ur : InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 (h + 8 * n)) 8 := by
      rw [hu.step.sp, hu.step.wr]
      exact ⟨_, List.mem_append_right _ hw, Offset.contains_base _ (by omega) (by omega)⟩
    have uw : InRegions u.wr (u.sp + BitVec.ofNat 64 (d + 8 * n)) 8 := by
      rw [hu.step.sp, hu.step.wr]
      exact ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩
    refine WP.mono (pruneWord_ok (by omega) hh8 hhl hdl ur uw) fun t ⟨kt, mt⟩ => ?_
    rw [hu.step.sp] at mt
    have same : u.mem.readW (s.sp + BitVec.ofNat 64 (h + 8 * n)) 64 =
        s.mem.readW (s.sp + BitVec.ofNat 64 (h + 8 * n)) 64 := by
      apply hu.frame.readW (Region.contains_self _ _) _ (by decide)
      simp only [List.mem_singleton]
      rintro r rfl
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    rw [same] at mt
    refine ⟨hu.step.trans kt, ?_, fun j hj => ?_⟩
    · rw [mt]
      exact hu.frame.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
    · rw [mt]
      by_cases hjn : j = n
      · subst j; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep ?_ (by decide)]
        · exact hu.words j (by omega)
        · exact Offset.sep _ (by omega) (by omega) (by omega)

theorem byte_of_zero (m : Mem) (p : Addr) (h : m.readW p 64 = 0) : m p = 0 := by
  have e := Mem.extractLsb'_read m p (n := 8) (j := 0) (by decide)
  rw [BitVec.add_zero] at e
  rw [← e]
  have h' : m.read p 8 = 0 := by
    have : m.readW p 64 = m.read p 8 := by simp only [Mem.readW]; rfl
    rw [← this, h]
  rw [h']
  rfl

theorem take57 (m : Mem) (p : Addr) :
    (Spec.Sha3.bytesAt m p 114).take 57 = Spec.Ed448.bytesAt m p 57 := by
  simp [Spec.Sha3.bytesAt, Spec.Ed448.bytesAt, ← List.map_take, List.take_range]

theorem pruneValue_toNat0 (x : BitVec 64) : (pruneValue 0 x).toNat = x.toNat &&& (2 ^ 64 - 4) := by
  have c : (2 ^ 64 - 4) % 2 ^ 64 = 2 ^ 64 - 4 := by decide
  simp only [pruneValue, ite_true, BitVec.toNat_and, BitVec.toNat_ofNat, c]

theorem pruneValue_toNat6 (x : BitVec 64) : (pruneValue 6 x).toNat = x.toNat ||| 2 ^ 63 := by
  have c : 2 ^ 63 % 2 ^ 64 = 2 ^ 63 := by decide
  simp only [pruneValue, Nat.reduceEqDiff, ite_true, ite_false, BitVec.toNat_or, BitVec.toNat_ofNat, c]

/-- The hash at `sp + h`, pruned, as the scalar at `sp + d`. -/
theorem prune_run {s : State} {h d : Nat} (hw : (⟨s.sp, 256⟩ : Region) ∈ s.wr) (hh8 : h % 8 = 0)
    (hd8 : d % 8 = 0) (hhl : h + 64 ≤ 256) (hdl : d + 64 ≤ 256) (hsep : d + 64 ≤ h ∨ h + 64 ≤ d)
    {hb : List Byte} (hh : Spec.Sha3.bytesAt s.mem (s.sp + BitVec.ofNat 64 h) 114 = hb) :
    WP isa (.block (pruneAt h d)) s fun t => VG.Proof.Ed448.AArch64.Whole.Step s t ∧
      Frame [⟨s.sp + BitVec.ofNat 64 d, 64⟩] s.mem t.mem ∧
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt t.mem (s.sp + BitVec.ofNat 64 d) 57) = Spec.Ed448.prune hb := by
  rw [pruneAt, WP.block_append_iff]
  refine WP.mono (prunePrefix_ok hw hh8 hhl hdl hsep 7 (by decide)) fun u hu => ?_
  have e7 : 8 * (d / 8 + 7) = d + 56 := by omega
  refine WP.mono (VG.Proof.Ed25519.AArch64.Whole.zeroWord_ok hu.step.sp (by rw [hu.step.wr]; exact hw)
    (k := d / 8 + 7) (by omega)) fun t ⟨kt, mt⟩ => ⟨?_, ?_, ?_⟩
  · exact hu.step.trans ⟨kt.rd, kt.wr, kt.sp, kt.vec, fun r _ _ h14 h15 => kt.regs r h14 h15⟩
  · rw [mt, e7]
    exact hu.frame.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
  · rw [e7] at mt
    have hw' : ∀ j < 7, t.mem.readW (s.sp + BitVec.ofNat 64 (d + 8 * j)) 64 =
        pruneValue j (s.mem.readW (s.sp + BitVec.ofNat 64 (h + 8 * j)) 64) := fun j hj => by
      rw [mt, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact hu.words j hj
    have hz : t.mem (s.sp + BitVec.ofNat 64 (d + 56)) = 0 :=
      byte_of_zero _ _ (by rw [mt]; exact Mem.readW_writeW_self64 _ _ _)
    have w0 := hw' 0 (by decide)
    have w1 := hw' 1 (by decide)
    have w2 := hw' 2 (by decide)
    have w3 := hw' 3 (by decide)
    have w4 := hw' 4 (by decide)
    have w5 := hw' 5 (by decide)
    have w6 := hw' 6 (by decide)
    simp only [Nat.reduceMul, Nat.mul_zero, Nat.add_zero] at w0 w1 w2 w3 w4 w5 w6
    rw [Spec.Ed448.prune, ← hh, take57, Proof.Ed448.decode57, Proof.Ed448.decode57]
    simp only [Offset.add_add, Nat.add_zero]
    rw [w0, w1, w2, w3, w4, w5, w6, hz, pruneValue_toNat0, pruneValue_toNat6]
    simp only [pruneValue, Nat.reduceEqDiff, ite_false]
    exact (Proof.Ed448.prune_nat _ _ _ _ _ _ _ _ (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
      (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)).symm

end VG.Proof.Ed448.AArch64.Whole
