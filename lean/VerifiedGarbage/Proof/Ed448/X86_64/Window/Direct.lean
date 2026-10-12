module

public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Memory
public import VerifiedGarbage.Impl.Ed448.X86_64.WindowSelect
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! Direct coordinate selection preserves the mask and every unrelated field slot. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Window

open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Window
open VG.Proof.Ed448.X86_64
open VG.Proof.X448.X86_64
open VG.Impl.X448.X86_64 (W sc slot loads stores)

private theorem retain_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : o + 56 ≤ 8192) {sw : Bool} (hc : s.gpr .rcx = mask sw) :
    WP isa (.block (retain o)) s fun u =>
      rv u W = (if sw then rv s W else fe s.mem base o) ∧ Keeps W s u := by
  have hr : ∀ i < 7, InRegions (s.rd ++ s.wr) (off base (o + 8 * i)) 8 :=
    fun i hi => hs.read (by omega)
  have he : (BitVec.allOnes 64 == (0 : BitVec 64)) = false := by decide
  apply WP.of_runBlock
  cases sw <;>
    simp only [retain, W, List.range_succ, List.range_zero, List.nil_append, List.zip_cons_cons,
      List.zip_nil_right, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, execCmov, eval, RegUpd.zf_setReg, RegUpd.zf_arithFlags, BitVec.and_self, BitVec.reduceBEq, Bool.false_eq_true, hc, mask,
      ea_sc, hs.rdi, State.load64, hr 0 (by decide), hr 1 (by decide), hr 2 (by decide), hr 3 (by decide), hr 4 (by decide), hr 5 (by decide), hr 6 (by decide), he, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
      RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags,
      RegUpd.wr_setReg, RegUpd.wr_arithFlags, Option.map_some, Option.bind_some,
      Option.some.injEq, exists_eq_left', reduceCtorEq, ite_true, ite_false]
  all_goals
    constructor
    · simp only [rv, fe, mv, VG.Proof.X448.X86_64.word, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
        reduceCtorEq, ite_true, ite_false, Nat.mul_zero, Nat.add_zero, Nat.reduceMul,
        Nat.add_assoc, Nat.reduceAdd]
    · refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1,
        hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]

theorem selectMem_ok {s : State} {base : Addr} (hs : Scr s base) (i : Index) {a : Nat}
    (ha : a + 56 ≤ 8192) {sw : Bool} (hc : s.gpr .rcx = mask sw) :
    WP isa (.block (selectMem (slot i.val) a)) s fun u => Keep base s u ∧
      u.gpr .rcx = s.gpr .rcx ∧
      E u.mem base = Function.update (E s.mem base) i (if sw then F s.mem base a else E s.mem base i) := by
  have hi := slot_lt i
  have gi := slot_ge i
  simp only [Impl.X448.X86_64.ACC] at hi
  rw [selectMem, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loads_ok hs a W (by decide) (by decide) (by simp only [W]; omega))
    fun s1 ⟨_, v1, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (retain_ok (hs.of_keeps k1 (by decide)) (by omega)
    ((k1.1 _ (by decide)).trans hc)) fun s2 ⟨v2, k2⟩ => ?_
  refine WP.mono (stores_E ((hs.of_keeps k1 (by decide)).of_keeps k2 (by decide)) i W rfl)
    fun u ⟨eu, ou, gu, ru, wu⟩ => ?_
  refine ⟨⟨?_, ru.trans (k2.2.2.1.trans k1.2.2.1), wu.trans (k2.2.2.2.trans k1.2.2.2), ?_⟩, ?_, ?_⟩
  · intro r hr
    have h : r ∉ W := fun h => hr ((show ∀ r ∈ W, r ∈ clob from by decide) r h)
    exact ((gu r).trans (k2.1 r h)).trans (k1.1 r h)
  · rw [k2.2.1, k1.2.1] at ou
    exact ou.mono (by omega) (by omega)
  · exact ((gu _).trans (k2.1 _ (by decide))).trans (k1.1 _ (by decide))
  · rw [eu, v2, v1, k2.2.1, k1.2.1]
    cases sw <;> rfl

theorem selectConst_ok {s : State} {base : Addr} (hs : Scr s base) (i : Index) (v : Spec.X448.Fe)
    (hv : VG.Proof.X448.toFe (wv (words7 v.val)) = v)
    {sw : Bool} (hc : s.gpr .rcx = mask sw) :
    WP isa (.block (selectConst (slot i.val) v)) s fun u => Keep base s u ∧
      u.gpr .rcx = s.gpr .rcx ∧
      E u.mem base = Function.update (E s.mem base) i (if sw then v else E s.mem base i) := by
  have hi := slot_lt i
  have gi := slot_ge i
  simp only [Impl.X448.X86_64.ACC] at hi
  rw [selectConst, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadWords_ok s v.val) fun s1 ⟨v1, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (retain_ok (hs.of_keeps k1 (by decide)) (by omega)
    ((k1.1 _ (by decide)).trans hc)) fun s2 ⟨v2, k2⟩ => ?_
  refine WP.mono (stores_E ((hs.of_keeps k1 (by decide)).of_keeps k2 (by decide)) i W rfl)
    fun u ⟨eu, ou, gu, ru, wu⟩ => ?_
  refine ⟨⟨?_, ru.trans (k2.2.2.1.trans k1.2.2.1), wu.trans (k2.2.2.2.trans k1.2.2.2), ?_⟩, ?_, ?_⟩
  · intro r hr
    have h : r ∉ W := fun h => hr ((show ∀ r ∈ W, r ∈ clob from by decide) r h)
    exact ((gu r).trans (k2.1 r h)).trans (k1.1 r h)
  · rw [k2.2.1, k1.2.1] at ou
    exact ou.mono (by omega) (by omega)
  · exact ((gu _).trans (k2.1 _ (by decide))).trans (k1.1 _ (by decide))
  · rw [eu, v2, v1, k2.2.1, k1.2.1]
    cases sw with
    | false => rfl
    | true => simp only [ite_true, hv]

end VG.Proof.Ed448.X86_64.Window
