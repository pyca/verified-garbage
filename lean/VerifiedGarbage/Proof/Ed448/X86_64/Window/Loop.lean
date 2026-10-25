module
public import VerifiedGarbage.Proof.Ed448.Window
public import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Fn
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Memory

import VerifiedGarbage.Proof.Ed448.X86_64.Window.Round
import Mathlib.Tactic.Abel
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig

/-! The joint window loop represents `[S]B + [k](-A)` for valid decoded points. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Window

open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Window
open VG.Proof.Ed448 VG.Proof.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr E Keep FieldOk Outside off ofs clob)
open VG.Impl.X448.X86_64 (BITS)
open VG.Proof.Ed448.Window (multiples)
open VG.Proof.Ed448.SignedWindow (high magnitude negative signedPoint high_step)

private theorem round_rep {A p : Spec.Ed448.Point} {a : EdwardsLaw.EPoint dZ} (hA : Rep A a)
    {S K n : Nat} (hp : Rep p ((high S (n + 1) : Int) • baseAff + (high K (n + 1) : Int) • a)) :
    Rep (roundPt p (signedPoint (negative K (5 * n)) (multiples A (magnitude K (5 * n)))) S (5 * n))
      ((high S n : Int) • baseAff + (high K n : Int) • a) := by
  have hd := dbl5Pt_rep hp
  have hd' : Rep (dbl5Pt p) ((32 : Int) • ((high S (n + 1) : Int) • baseAff + (high K (n + 1) : Int) • a)) := by
    rw [show (32 : Int) = ((32 : Nat) : Int) from rfl, natCast_zsmul]
    exact hd
  have h := pointAdd_rep (pointAdd_rep hd' (SignedWindow.signedEntry_rep S (5 * n)))
    (SignedWindow.signedPoint_rep (Proof.Ed448.Window.multiples_rep hA (magnitude K (5 * n))) (negative K (5 * n)))
  change Rep (roundPt p (signedPoint (negative K (5 * n)) (multiples A (magnitude K (5 * n)))) S (5 * n))
    ((32 : Int) • ((high S (n + 1) : Int) • baseAff + (high K (n + 1) : Int) • a) +
      SignedWindow.digit S (5 * n) • baseAff + SignedWindow.digit K (5 * n) • a) at h
  convert h using 1
  rw [high_step S n, high_step K n, add_zsmul, add_zsmul, smul_add, smul_smul, smul_smul]
  abel

/-- The table is immutable during the loop. The representation claim is conditional on
validity of `A`, so no malformed-input path acquires a precondition. -/
structure Inv (base : Addr) (S K : Nat) (A : Spec.Ed448.Point) (s₀ : State) (n : Nat) (s : State) : Prop where
  scr : Scr s base
  rbx : s.gpr .rbx = BitVec.ofNat 64 (5 * n)
  gpr : ∀ r, r ∉ .rbx :: clob → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base 64 1584 s₀.mem s.mem
  d : E s.mem base 11 = Spec.Ed448.d
  tab : ∀ i < 17, tablePoint s.mem base i = multiples A i
  rep : ∀ a, Rep A a → Rep (pt (E s.mem base) 0 1 2)
    ((high S n : Int) • baseAff + (high K n : Int) • a)

variable {F : Impl.X448.X86_64.Field} (hf : FieldOk F) {P : Point64.Ops} (hP : Point64.PointOk P)

include hf hP in
theorem loop_ok {s₀ : State} {base : Addr} {S K o : Nat} {A : Spec.Ed448.Point}
    (ho : 2048 ≤ o) (hbnd : o + 460 ≤ 8192)
    (bs : Bits base BITS S s₀) (bk : Bits base o K s₀) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 92 → Inv base S K A s₀ n s →
      WP isa (.loop (Window.step F P o) .ne) s fun u => Inv base S K A s₀ 0 u := by
  intro n s hn1 hn2 hi
  refine WP.loop (M := isa) (Q := fun u => Inv base S K A s₀ 0 u)
    (fun m s => 1 ≤ m ∧ m ≤ 92 ∧ Inv base S K A s₀ m s) ?_ n s ⟨hn1, hn2, hi⟩
  rintro m s ⟨hm1, hm2, hi⟩
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  rw [Window.step]
  refine WP.seq (WP.mono (dec5_ok s (t := 5 * t) (by rw [hi.rbx, show 5 * (t + 1) = 5 * t + 5 by omega]))
    fun s1 ⟨b1, g1, m1, rd1, wr1⟩ => ?_)
  have hs1 : Scr s1 base := ⟨(g1 _ (by decide)).trans hi.scr.rdi, wr1 ▸ hi.scr.wr, hi.scr.nowrap⟩
  have bits1 : ∀ o, 2048 ≤ o → o + 460 ≤ 8192 → ∀ j < 461,
      s1.mem (off base (o - 1 + j)) = s₀.mem (off base (o - 1 + j)) := by
    intro o ho hb j hj
    rw [m1, hi.mem _ (Or.inr (by rw [VG.Proof.X448.X86_64.ofs_off' base (by omega)]; omega))]
  have bs1 : Bits base BITS S s1 := fun j hj => (bits1 BITS (by decide) (by decide) j hj).trans (bs j hj)
  have bk1 : Bits base o K s1 := fun j hj => (bits1 o ho hbnd j hj).trans (bk j hj)
  refine WP.mono (round_ok hf hP hs1 ho hbnd (by omega) b1 bs1 bk1 (by rw [m1]; exact hi.d))
    fun u ⟨ku, zu, du, pu⟩ => ?_
  have inv : Inv base S K A s₀ t u := by
    refine ⟨ku.scr hs1, (ku.gpr _ (by decide)).trans b1, ?_, ku.rd.trans (rd1.trans hi.rd),
      ku.wr.trans (wr1.trans hi.wr), ?_, du, ?_, ?_⟩
    · intro r hr
      simp only [List.mem_cons, not_or] at hr
      exact ((ku.gpr r hr.2).trans (g1 r hr.1)).trans (hi.gpr r (by simp only [List.mem_cons, not_or]; exact hr))
    · have hm := ku.mem
      rw [m1] at hm
      exact hi.mem.trans hm
    · intro i hi'
      rw [tablePoint_keep ku i hi', m1]; exact hi.tab i hi'
    · intro a ha
      rw [pu, m1, hi.tab _ (SignedWindow.magnitude_lt K (5 * t))]
      exact round_rep ha (hi.rep a ha)
  have ez : (5 * t = 0) = (t = 0) := propext (by omega)
  simp only [ez] at zu
  simp only [eval, zu, Option.map_some]
  rcases Nat.eq_zero_or_pos t with h | h
  · subst h; exact .inl ⟨rfl, inv⟩
  · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬t = 0), Bool.not_false],
      t, by omega, h, by omega, inv⟩

end VG.Proof.Ed448.X86_64.Window
