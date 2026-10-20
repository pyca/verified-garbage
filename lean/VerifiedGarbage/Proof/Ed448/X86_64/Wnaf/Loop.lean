module
public import VerifiedGarbage.Impl.Ed448.X86_64.Wnaf.Joint
public import VerifiedGarbage.Proof.Ed448.Window
public import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Fn
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Memory
public import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Step

import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Math
import VerifiedGarbage.Proof.Ed448.Wnaf.Recoding
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Ed448.X86_64.BaseLoop
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Recode

/-! The common binary loop over two sparse signed digit streams. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Wnaf
open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Impl.Ed448.X86_64.Wnaf
open VG.Proof.Ed448 VG.Proof.X448.X86_64
open VG.Impl.Ed448.Wnaf (residual digitAt)
open VG.Proof.Ed448.X86_64.Window (tablePoint tablePoint_keep)

def Digits (base : Addr) (o k : Nat) (s : State) : Prop :=
  ∀ i < 461, s.mem (off base (o + i)) = Enc k i

theorem Digits.keep {base : Addr} {o k : Nat} {s u : State} (h : Digits base o k s)
    (ho : 2048 ≤ o) (hb : o + 461 ≤ 8192) (g : Keep base s u) : Digits base o k u := by
  intro i hi
  rw [g.mem _ (Or.inr (by rw [ofs_off' base (by omega)]; omega))]
  exact h i hi

structure Inv (base : Addr) (S K : Nat) (A : Spec.Ed448.Point) (s₀ : State) (n : Nat) (s : State) : Prop where
  scr : Scr s base
  rbx : s.gpr .rbx = BitVec.ofNat 64 n
  gpr : ∀ r, r ∉ .rbx :: clob → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base 64 1584 s₀.mem s.mem
  bs : Digits base SDIG S s
  bk : Digits base KDIG K s
  d : E s.mem base 11 = Spec.Ed448.d
  tab : ∀ i < 17, tablePoint s.mem base i = Proof.Ed448.Window.multiples A i
  rep : ∀ a, Rep A a → Rep (pt (E s.mem base) 0 1 2)
    ((residual S n : Int) • baseAff + (residual K n : Int) • a)

theorem dec1_ok (s : State) {n : Nat} (hr : s.gpr .rbx = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block [.alu .sub .rbx (.imm 1)]) s fun u =>
      u.gpr .rbx = BitVec.ofNat 64 n ∧ Keeps [.rbx] s u := by
  have he : s.gpr .rbx - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 n := by
    rw [hr, show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      BitVec.ofNat_add, BitVec.add_sub_cancel]
  xrun [he]
  refine ⟨he, fun r h => ?_, rfl, rfl, rfl⟩
  have hn : r ≠ .rbx := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using h
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hn, ite_false]

theorem testCounter_ok (s : State) (n : Nat) (hn : n < 461) (hb : s.gpr .rbx = BitVec.ofNat 64 n) :
    WP isa (.block ([.alu .test .rbx (.reg .rbx)] : List Instr)) s fun t =>
      t.zf = some (decide (n = 0)) ∧ (∀ r, t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
        t.wr = s.wr := by
  have e : (BitVec.ofNat 64 n &&& BitVec.ofNat 64 n == 0) = decide (n = 0) := by
    have : ∀ n < 461, (BitVec.ofNat 64 n &&& BitVec.ofNat 64 n == 0) = decide (n = 0) := by
      decide +kernel
    exact this n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.zf_arithFlags, hb, e]
  exact ⟨trivial, fun _ => rfl, rfl, rfl, rfl⟩


theorem pointStep_ok {F : Impl.X448.X86_64.Field} (hf : FieldOk F) {P : Point64.Ops} (hP : Point64.PointOk P)
    {base : Addr} {S K n : Nat} {A : Spec.Ed448.Point} {s₀ s : State}
    (h : Inv base S K A s₀ (n + 1) s) (hn : n < 461) :
    WP isa (step F P) s fun u => Inv base S K A s₀ n u ∧ u.zf = some (decide (n = 0)) := by
  refine WP.seq (WP.mono (dec1_ok s h.rbx) fun a ⟨ar, ak⟩ => ?_)
  have sa : Scr a base := h.scr.of_keeps ak (by decide)
  refine WP.seq (WP.mono (hP.dbl sa) fun b ⟨kb, eb⟩ => ?_)
  have bp : pt (E b.mem base) 0 1 2 = double (pt (E s.mem base) 0 1 2) := by
    rw [eb, doubleOps_eval, ak.2.1]
  have bd : E b.mem base 11 = Spec.Ed448.d := by
    rw [eb, doubleOps_keep _ _ (Or.inl ⟨by decide, by decide⟩), ak.2.1, h.d]
  have bS : Digits base SDIG S b := by
    apply Digits.keep (o := SDIG) _ (by decide) (by decide) kb
    rw [Digits, ak.2.1]; exact h.bs
  have bK : Digits base KDIG K b := by
    apply Digits.keep (o := KDIG) _ (by decide) (by decide) kb
    rw [Digits, ak.2.1]; exact h.bk
  refine WP.seq (WP.mono (addBase_ok hP (kb.scr sa) hn (Proof.Ed448.Wnaf.digit_bounds _)
    ((kb.gpr _ (by decide)).trans ar) (bS n hn) bd) fun c ⟨kc, dc, pc⟩ => ?_)
  have cK := bK.keep (by decide) (by decide) kc
  refine WP.seq (WP.mono (addKey_ok hf hP (kc.scr (kb.scr sa)) hn (Proof.Ed448.Wnaf.digit_bounds _)
    (((kc.gpr _ (by decide)).trans (kb.gpr _ (by decide))).trans ar) (cK n hn) dc)
    fun d ⟨kd, dd, pd⟩ => ?_)
  have kbd := (kb.trans kc).trans kd
  refine WP.mono (testCounter_ok d n (by omega) ((kbd.gpr _ (by decide)).trans ar))
    fun u ⟨zu, gu, mu, ru, wu⟩ => ?_
  have kau : Keep base a u := ⟨fun r hr => (gu r).trans (kbd.gpr r hr),
    ru.trans kbd.rd, wu.trans kbd.wr, by rw [mu]; exact kbd.mem⟩
  refine ⟨⟨kau.scr sa, (kau.gpr _ (by decide)).trans ar, ?_, kau.rd.trans (ak.2.2.1.trans h.rd),
    kau.wr.trans (ak.2.2.2.trans h.wr), ?_, ?_, ?_, ?_, ?_, ?_⟩, zu⟩
  · intro r hr
    have hrc : r ∉ clob := fun hh => hr (List.mem_cons_of_mem _ hh)
    have hrb : r ∉ [Reg.rbx] := fun hh => hr (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hh)))
    exact ((kau.gpr r hrc).trans (ak.1 r hrb)).trans (h.gpr r hr)
  · have hm := kau.mem; rw [ak.2.1] at hm; exact h.mem.trans hm
  · apply Digits.keep (o := SDIG) _ (by decide) (by decide) kau
    rw [Digits, ak.2.1]; exact h.bs
  · apply Digits.keep (o := KDIG) _ (by decide) (by decide) kau
    rw [Digits, ak.2.1]; exact h.bk
  · rw [mu]; exact dd
  · intro i hi; rw [tablePoint_keep kau i hi, ak.2.1]; exact h.tab i hi
  · intro aa ha
    rw [mu, pd, pc, bp, tablePoint_keep kc _ (abs_lt (Proof.Ed448.Wnaf.digit_bounds _)),
      tablePoint_keep kb _ (abs_lt (Proof.Ed448.Wnaf.digit_bounds _)), ak.2.1, h.tab _ (abs_lt (Proof.Ed448.Wnaf.digit_bounds _))]
    have hq := SignedWindow.signedPoint_rep (Proof.Ed448.Window.multiples_rep ha (digitAt K n).natAbs)
      (decide (digitAt K n < 0))
    rw [signed_abs] at hq
    exact round_rep (h.rep aa ha) hq

theorem loop_ok {F : Impl.X448.X86_64.Field} (hf : FieldOk F) {P : Point64.Ops} (hP : Point64.PointOk P)
    {base : Addr} {S K : Nat} {A : Spec.Ed448.Point} {s₀ : State} : ∀ n, 1 ≤ n → n ≤ 461 → ∀ s,
      Inv base S K A s₀ n s → WP isa (.loop (step F P) .ne) s (Inv base S K A s₀ 0) := by
  intro n hn hb s h
  refine WP.loop (M := isa) (fun n u => 1 ≤ n ∧ n ≤ 461 ∧ Inv base S K A s₀ n u) ?_ n s ⟨hn, hb, h⟩
  rintro m u ⟨hm, hb, hi⟩
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (pointStep_ok hf hP hi (by omega)) fun v ⟨hv, hz⟩ => ?_
  have he : isa.eval .ne v = some (!decide (j = 0)) := by simp only [eval, hz, Option.map_some]
  by_cases hj : j = 0
  · subst j; exact .inl ⟨he, hv⟩
  · refine .inr ⟨?_, j, by omega, by omega, by omega, hv⟩
    rw [he, decide_eq_false hj]; rfl

end VG.Proof.Ed448.X86_64.Wnaf
