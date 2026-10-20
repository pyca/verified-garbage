module

public import VerifiedGarbage.Proof.Ed448.X86_64.CombSelect
public import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Fn
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop
import VerifiedGarbage.Proof.Ed448.X86_64.BaseStep
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ed448.X86_64.BaseLoop

/-! The 114 iterations of the four-column Ed448 fixed-base comb. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Comb

open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64 VG.Proof.Ed448 VG.Proof.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr Index Env E Keep clob Outside)
open VG.Proof.Ed448.Comb (accScalar digit)

/-- Move the sum into the accumulator, preserving the curve constant and testing the counter. -/
theorem accept_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat}
    (ht : t < 114) (hb : s.gpr .rbx = BitVec.ofNat 64 t) :
    WP isa (.block combAccept) s fun u => Keep base s u ∧
      pt (E u.mem base) 0 1 2 = pt (E s.mem base) 3 4 5 ∧
      E u.mem base 11 = E s.mem base 11 ∧ u.zf = some (decide (t = 0)) := by
  rw [combAccept, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copySlot_ok hs 0 3) fun s1 ⟨k1, e1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copySlot_ok (k1.scr hs) 1 4) fun s2 ⟨k2, e2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copySlot_ok (k2.scr (k1.scr hs)) 2 5) fun s3 ⟨k3, e3⟩ => ?_
  refine WP.mono (testRbx_ok s3 t (by omega)
    (by rw [k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide), hb]))
    fun u ⟨zu, gu, mu, ru, wu⟩ => ?_
  refine ⟨⟨fun r hr => (gu r).trans (((k1.trans k2).trans k3).gpr r hr),
    ru.trans (k3.rd.trans (k2.rd.trans k1.rd)), wu.trans (k3.wr.trans (k2.wr.trans k1.wr)), ?_⟩,
    ?_, ?_, zu⟩
  · rw [mu]; exact (k1.mem.trans k2.mem).trans k3.mem
  · rw [mu, e3, e2, e1]; simp (disch := decide) only [pt, Function.update_self, Function.update_of_ne]
  · rw [mu, e3, e2, e1]; simp (disch := decide) only [Function.update_of_ne]

private theorem step_rep {p : Spec.Ed448.Point} {k t : Nat} (ht : t < 114)
    (hp : Rep p (accScalar k (t + 1) • baseAff)) :
    Rep (Spec.Ed448.pointAdd (Proof.Ed448.double p)
      (Proof.X448.basePt (Impl.Ed448.Comb.entry (digit k t)))) (accScalar k t • baseAff) := by
  have h := pointAdd_rep (double_rep hp) (Proof.Ed448.Comb.entry_rep _ (Proof.Ed448.Comb.digit_lt k t))
  rw [← two_nsmul, smul_smul, ← add_nsmul, ← Proof.Ed448.Comb.accScalar_step k t ht] at h
  exact h

variable {P : Point64.Ops} (hP : Point64.PointOk P)

include hP in
theorem step_ok {s : State} {base : Addr} (hs : Scr s base) {k t : Nat} (ht : t < 114)
    (hb : s.gpr .rbx = BitVec.ofNat 64 (t + 1)) (bs : Bits base k s)
    (hd : E s.mem base 11 = Spec.Ed448.d)
    (hp : Rep (pt (E s.mem base) 0 1 2) (accScalar k (t + 1) • baseAff)) :
    WP isa (combStep P) s fun u =>
      u.gpr .rbx = BitVec.ofNat 64 t ∧ u.zf = some (decide (t = 0)) ∧
      (∀ r, r ∉ .rbx :: clob → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
      Outside base 64 1584 s.mem u.mem ∧ E u.mem base 11 = Spec.Ed448.d ∧
      Rep (pt (E u.mem base) 0 1 2) (accScalar k t • baseAff) := by
  rw [combStep]
  refine WP.seq (WP.mono (dec_ok s hb) fun s1 ⟨b1, g1, m1, rd1, wr1⟩ => ?_)
  have hs1 : Scr s1 base := ⟨(g1 _ (by decide)).trans hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  refine WP.seq (WP.mono (hP.dbl hs1) fun s2 ⟨k2, e2⟩ => ?_)
  have bs2 : Bits base k s2 := (show Bits base k s1 from by intro i hi; rw [m1]; exact bs i hi).keep k2
  have b2 : s2.gpr .rbx = BitVec.ofNat 64 t := by rw [k2.gpr _ (by decide), b1]
  refine WP.seq (WP.mono (select_ok (k2.scr hs1) ht b2 bs2) fun s3 ⟨k3, q3, f3⟩ => ?_)
  have d3 : E s3.mem base 11 = Spec.Ed448.d := by
    rw [f3 11 (by decide) (by decide) (by decide) (by decide), e2,
      doubleOps_keep _ _ (Or.inl (by decide)), m1, hd]
  have p3 : pt (E s3.mem base) 0 1 2 = Proof.Ed448.double (pt (E s.mem base) 0 1 2) := by
    rw [pt_congr (f3 0 (by decide) (by decide) (by decide) (by decide))
      (f3 1 (by decide) (by decide) (by decide) (by decide))
      (f3 2 (by decide) (by decide) (by decide) (by decide)), e2, doubleOps_eval, m1]
  refine WP.seq (WP.mono (hP.add (k3.scr (k2.scr hs1)) d3) fun s4 ⟨k4, e4⟩ => ?_)
  have b4 : s4.gpr .rbx = BitVec.ofNat 64 t := by
    rw [k4.gpr _ (by decide), k3.gpr _ (by decide), b2]
  refine WP.mono (accept_ok (k4.scr (k3.scr (k2.scr hs1))) ht b4) fun u ⟨ku, pu, du, zu⟩ => ?_
  have ku1 := ((k2.trans k3).trans k4).trans ku
  refine ⟨(ku.gpr _ (by decide)).trans b4, zu, fun r hr => ?_, ku1.rd.trans rd1,
    ku1.wr.trans wr1, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, not_or] at hr
    exact (ku1.gpr r hr.2).trans (g1 r hr.1)
  · rw [← m1]; exact ku1.mem
  · rw [du, e4, Point64.addAffineOps_keep _ _ (Or.inr (Or.inl (by decide))), d3]
  · rw [pu, e4, Point64.addAffineOps_eval, d3, addWith_d, p3]
    have hx := congrArg Prod.fst q3
    have hy := congrArg Prod.snd q3
    dsimp only at hx hy
    rw [hx, hy]
    exact step_rep ht hp

/-- The accumulator represents the already-processed high bits of all four columns. -/
structure Inv (base : Addr) (k : Nat) (s₀ : State) (n : Nat) (s : State) : Prop where
  scr : Scr s base
  rbx : s.gpr .rbx = BitVec.ofNat 64 n
  gpr : ∀ r, r ∉ .rbx :: clob → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base 64 1584 s₀.mem s.mem
  d : E s.mem base 11 = Spec.Ed448.d
  rep : Rep (pt (E s.mem base) 0 1 2) (accScalar k n • baseAff)

include hP in
theorem loop_ok {s₀ : State} {base : Addr} {k : Nat} (bs : Bits base k s₀) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 114 → Inv base k s₀ n s →
      WP isa (.loop (combStep P) .ne) s fun u => Inv base k s₀ 0 u := by
  intro n s hn1 hn2 hi
  refine WP.loop (M := isa) (Q := fun u => Inv base k s₀ 0 u)
    (fun m s => 1 ≤ m ∧ m ≤ 114 ∧ Inv base k s₀ m s) ?_ n s ⟨hn1, hn2, hi⟩
  rintro m s ⟨hm1, hm2, hi⟩
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  have bss : Bits base k s := by
    intro j hj
    rw [hi.mem _ (Or.inr (by
      rw [VG.Proof.X448.X86_64.ofs_off' base (by simp only [Impl.X448.X86_64.BITS]; omega)]
      simp only [Impl.X448.X86_64.BITS]; omega))]
    exact bs j hj
  refine WP.mono (step_ok hP hi.scr (by omega) hi.rbx bss hi.d hi.rep)
    fun u ⟨bu, zu, gu, ru, wu, ou, du, pu⟩ => ?_
  have inv : Inv base k s₀ t u :=
    ⟨⟨(gu _ (by decide)).trans hi.scr.rdi, wu ▸ hi.scr.wr, hi.scr.nowrap⟩, bu,
      fun r hr => (gu r hr).trans (hi.gpr r hr), ru.trans hi.rd, wu.trans hi.wr,
      hi.mem.trans ou, du, pu⟩
  simp only [eval, zu, Option.map_some]
  rcases Nat.eq_zero_or_pos t with h | h
  · subst h; exact .inl ⟨rfl, inv⟩
  · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬t = 0), Bool.not_false],
      t, by omega, h, by omega, inv⟩

end VG.Proof.Ed448.X86_64.Comb
