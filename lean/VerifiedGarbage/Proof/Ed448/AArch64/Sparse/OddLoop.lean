module

public import VerifiedGarbage.Proof.Ed448.AArch64.Window.Table
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Table
public import VerifiedGarbage.Proof.Ed448.WnafWide.Group
import VerifiedGarbage.Proof.X448.BaseAdd
import VerifiedGarbage.Proof.X448.AArch64.Base.AddGen
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Call
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! Generate eight odd multiples using one doubling and seven projective additions. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64 (TAB)
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Proof.X448.AArch64 (Scr Keeps Outside Outside2 limbs word ofs)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.X448.AArch64.Fast (BEnv Same)
open VG.Proof.Curve448.AArch64.Fast (Ib Mb)
open VG.Proof.X448.AArch64.Base (pt zero_env next_ok)
open VG.Proof.Ed448.AArch64.Window (TPt TBnd tw tabStore_ok tabStore_pt tabStore_bnd
  TPt_outside TPt_of_tw tw_outside)
open VG.Proof.Ed448.WnafWide (oddPoint)
open VG.Spec.Ed448 (Point)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

def OddTabOk (m:Mem) (base:Addr) (P:Point) (k:Nat) : Prop :=
  ∀ e<k,TPt m base e=oddPoint P e ∧ TBnd m base e

def OddFrame (base:Addr) (m m':Mem) : Prop :=
  ∀ x,(ofs base x<64 ∨ 2880≤ofs base x) →
    (ofs base x<ACC ∨ ACC+1152≤ofs base x) →
    (ofs base x<TAB ∨ TAB+1536≤ofs base x) → m' x=m x

theorem OddFrame.trans {base:Addr} {m n p:Mem} (h:OddFrame base m n) (g:OddFrame base n p) :
    OddFrame base m p:=fun x a b c => (g x a b c).trans (h x a b c)

theorem OddFrame.of_outside2 {base:Addr} {m m':Mem} (h:Outside2 base 64 2816 ACC 1152 m m') :
    OddFrame base m m':=fun x a b _ => h x a b

theorem OddFrame.of_entry {base:Addr} {m m':Mem} {e:Nat} (he:e<8)
    (h:Outside base (TAB+192*e) 192 m m') : OddFrame base m m':=fun x _ _ c =>
  h x (by simp only [TAB] at c ⊢;omega)

structure OddInv (s₀:State) (base:Addr) (P:Point) (k:Nat) (s:State) : Prop where
  bound : 1≤k ∧ k≤8
  scr : Scr s base
  env : BEnv s.mem base
  zero : ∀ w<8,limbs s.mem base (slot (19:Index).val) w=0
  counter : s.gpr .x19=BitVec.ofNat 64 k
  acc : pt (EV s.mem base) 3 4 5=oddPoint P (k-1)
  pnt : pt (EV s.mem base) 6 7 8=VG.Proof.Ed448.double P
  one : EV s.mem base 20=EV s₀.mem base 20
  tab : OddTabOk s.mem base P k
  xbound : ∀ e<k,∀ w<8,(tw s.mem base e w).toNat<Mb
  chk : s.gpr .x20=s₀.gpr .x20
  rd : s.rd=s₀.rd
  wr : s.wr=s₀.wr
  mem : OddFrame base s₀.mem s.mem

theorem oddBody_ok {s₀ s : State} {base : Addr} {P : Point} {k : Nat} (h : OddInv s₀ base P k s) (hk : k < 8) :
    WP isa tableBody s fun t => (t.gpr .x9 != 0) = decide (k + 1 ≠ 8) ∧ OddInv s₀ base P (k + 1) t := by
  obtain ⟨hb2, hs, hb, hz, hc, hacc, hpnt, hone, htab, hxb, hchk, hrd, hwr, hmem⟩ := h
  rw [tableBody, WP.seq_iff]
  refine WP.mono (Point56.addCall_ok hs hb (zero_env hz).2) fun t1 ⟨k1, b1, s1, mx1, _, _, e1, _⟩ => ?_
  have hs1 := k1.scr hs
  have hc1 : t1.gpr .x19 = BitVec.ofNat 64 k := by rw [k1.regs.1 _ (by decide)]; exact hc
  rw [WP.block_append_iff]
  refine WP.mono (tabStore_ok hs1 (by omega) hc1) fun t2 ⟨w2, o2, k2⟩ => ?_
  have hs2 : Scr t2 base := hs1.of_keeps k2 (by decide)
  have hc2 : t2.gpr .x19 = BitVec.ofNat 64 k := by rw [k2.1 _ (by decide)]; exact hc1
  refine WP.mono (next_ok t2 (n := 8) (by decide) hk hc2) fun t3 ⟨c3, n3, k3, m3⟩ => ⟨n3, ?_⟩
  -- The slots after the addition, and the entries after the store.
  have z1 : ∀ w < 8, limbs t1.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    rw [s1 19 (by decide) w hw]; exact hz w hw
  have e3 : ∀ i : Index, EV t3.mem base i = EV t1.mem base i := fun i => by
    have := i.isLt
    simp only [VG.Proof.X448.AArch64.Weak.E, VG.Proof.X448.AArch64.Weak.F]
    refine congrArg _ (VG.Proof.X448.Wide.valN_congr fun w hw => ?_)
    rw [m3, o2.limbs (Or.inl (by simp only [slot, TAB]; omega)) (by simp only [slot]; omega) (by omega)]
  have hacc1 : pt (EV t1.mem base) 3 4 5 = oddPoint P k := by
    rw [e1, Point56.genEnv_pt, (zero_env hz).1, VG.Proof.X448.AArch64.Base.genPt_eq, hacc, hpnt]
    conv_rhs => rw [show k=k-1+1 by omega, oddPoint]
  have hpnt1 : pt (EV t1.mem base) 6 7 8 = VG.Proof.Ed448.double P := by
    rw [← hpnt]; simp only [pt]
    rw [Same.env s1 (i := 6) (by decide), Same.env s1 (i := 7) (by decide), Same.env s1 (i := 8) (by decide)]
  refine ⟨⟨by omega, by omega⟩, hs2.of_keeps k3 (by decide), ?_, fun w hw => ?_, c3, ?_, ?_, ?_, fun e he => ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i w hw
    have := i.isLt
    show limbs t3.mem base (slot i.val) w < Ib
    rw [m3, o2.limbs (Or.inl (by simp only [slot, TAB]; omega)) (by simp only [slot]; omega) (by omega)]
    exact b1 i w hw
  · rw [m3, o2.limbs (Or.inl (by simp only [slot, TAB]; omega)) (by simp only [slot]; omega) (by omega)]
    exact z1 w hw
  · simp only [pt]; rw [e3 3, e3 4, e3 5, Nat.add_sub_cancel]; exact hacc1
  · simp only [pt]; rw [e3 6, e3 7, e3 8]; exact hpnt1
  · rw [e3 20, ← hone]; exact Same.env s1 (i := 20) (by decide)
  · rw [m3]
    by_cases hek : e = k
    · subst hek
      exact ⟨by rw [tabStore_pt w2, hacc1], tabStore_bnd b1 w2⟩
    · have ⟨te, tb⟩ := htab e (by omega)
      have hmem1 : ∀ w < 24, tw t1.mem base e w = tw s.mem base e w := fun w hw => by
        unfold tw
        exact k1.mem.word (Or.inr (by simp only [TAB]; omega)) (Or.inr (by simp only [ACC, TAB]; omega))
          (by simp only [TAB]; omega)
      refine ⟨?_, fun w hw => ?_⟩
      · rw [TPt_outside o2 hek (by omega), TPt_of_tw hmem1, te]
      · rw [tw_outside o2 hek (by omega) hw, hmem1 w hw]; exact tb w hw
  · intro e he w hw
    rw [m3]
    by_cases hek:e=k
    · subst e
      rw [tw,w2 w (by omega)]
      have heq:Window.src w=slot 3+8*w:=by
        simp only [Window.src,slot]
        omega
      rw [heq]
      exact mx1 w hw
    · rw [tw_outside o2 hek (by omega) (by omega)]
      have hm:tw t1.mem base e w=tw s.mem base e w:=
        k1.mem.word (Or.inr (by simp only [TAB];omega)) (Or.inr (by simp only [ACC,TAB];omega))
          (by simp only [TAB];omega)
      rw [hm]
      exact hxb e (by omega) w hw
  · rw [k3.1 _ (by decide), k2.1 _ (by decide), k1.regs.1 _ (by decide)]; exact hchk
  · rw [k3.2.1, k2.2.1, k1.regs.2.1]; exact hrd
  · rw [k3.2.2, k2.2.2, k1.regs.2.2]; exact hwr
  · rw [m3]
    exact hmem.trans ((OddFrame.of_outside2 k1.mem).trans (OddFrame.of_entry hk o2))

theorem oddLoop_ok {s₀ : State} {base : Addr} {P : Point} :
    ∀ m, ∀ s, 1 ≤ m → m ≤ 7 → OddInv s₀ base P (8 - m) s →
      WP isa (.loop tableBody (.nonzero .x .x9)) s fun t => OddInv s₀ base P 8 t := by
  intro m s h1 h2 hi
  refine WP.loop (M := isa) (body := tableBody) (c := .nonzero .x .x9)
    (Q := fun t => OddInv s₀ base P 8 t)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 7 ∧ OddInv s₀ base P (8 - m) s) ?_ m s ⟨h1, h2, hi⟩
  intro m s ⟨h1, h2, hi⟩
  refine WP.mono (oddBody_ok hi (by omega)) fun t ⟨hz, ht⟩ => ?_
  simp only [eval, State.read, BitVec.setWidth_eq, hz]
  by_cases hm : m = 1
  · subst hm
    exact .inl ⟨by decide, ht⟩
  · refine .inr ⟨congrArg some (decide_eq_true (by omega)), m - 1, by omega, by omega, by omega, ?_⟩
    rw [show 8 - (m - 1) = 8 - m + 1 by omega]
    exact ht


end VG.Proof.Ed448.AArch64.Sparse
