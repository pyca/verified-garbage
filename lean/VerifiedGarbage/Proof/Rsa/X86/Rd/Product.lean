module

public import VerifiedGarbage.Proof.Rsa.X86.RvBase
public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
public import VerifiedGarbage.Proof.Rsa.RecoverDet
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.Rd.Ops
import VerifiedGarbage.Proof.Rsa.X86.Rd.Count
import VerifiedGarbage.Proof.Rsa.X86.RvOps
import VerifiedGarbage.Proof.Rsa.X86.RvScalarOps
import VerifiedGarbage.Proof.Rsa.X86.RvSlots
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Products by the bits of a narrow multiplier (i686)

`RecoverDetRt.product y x a t z`: `32 w` steps of `RecoverDet.prodStep`
modulo `2^(32 W)`, the multiplier `[y]` narrow and halved, the multiplicand
`[x]` wide and doubled, into the wide `[a]` through `[t]`, with `[z]` zero.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt (sK sY productStep product)
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.RecoverDet (prodStep)

/-- The arrays a product names, distinct and in their views' ranges, and the arrays tracked
around it apart from them. -/
structure ProdIdx (y x a t z : Nat) (live liveW ls : List Nat) : Prop where
  y_live : y ∈ live
  x_live : x ∈ liveW
  a_live : a ∈ liveW
  z_live : z ∈ liveW
  t_lt : t < 22
  t_not : t ∉ liveW
  tz : t ≠ z
  tx : t ≠ x
  ax : a ≠ x
  az : a ≠ z
  xz : x ≠ z
  at' : a ≠ t
  live_apart : ∀ j ∈ live, j / 2 ≠ t ∧ j / 2 ≠ a ∧ j / 2 ≠ x
  liveW_apart : ∀ j ∈ liveW, y / 2 ≠ j
  sY_not : sY ∉ ls

/-- The product's state after `i` steps: the multiplier, multiplicand and sum `(Y, X, P)`. -/
def ProdS (g : Geo) (s0 : State) (A : Nat → Nat) (live : List Nat) (AW : Nat → Nat) (liveW : List Nat)
    (V : Nat → Nat) (ls : List Nat) (y x a K i : Nat) (st : Nat × Nat × Nat) (u : State) : Prop :=
  KS g s0 (upd A y st.1) live (upd (upd AW x st.2.1) a st.2.2) liveW (upd V sK (K - i)) (sK :: ls) u

section
variable {g : Geo} {s0 : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

theorem productStep_ok {y x a t z K i : Nat} {st : Nat × Nat × Nat} {u : State}
    (I : ProdIdx y x a t z live liveW ls) (zero : AW z = 0) (hi : i < K) (hK : K < 2 ^ 32)
    (h : ProdS g s0 A live AW liveW V ls y x a K i st u) :
    WP isa (productStep y x a t z) u fun v =>
      ProdS g s0 A live AW liveW V ls y x a K (i + 1) (prodStep (32 * g.W) st) v ∧
      v.zf = some (decide (K - i - 1 = 0)) := by
  obtain ⟨Y, X, P⟩ := st
  unfold ProdS at h
  simp only at h
  have tl : ∀ j ∈ live, j / 2 ≠ t := fun j hj => (I.live_apart j hj).1
  have al : ∀ j ∈ live, j / 2 ≠ a := fun j hj => (I.live_apart j hj).2.1
  have xl : ∀ j ∈ live, j / 2 ≠ x := fun j hj => (I.live_apart j hj).2.2
  unfold productStep
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine WP.seq (WP.mono (h.bitOf_w (j := y) (sl := sY) I.y_live (by decide)) fun u1 ⟨h1, _⟩ => ?_)
  refine WP.seq (WP.mono (h1.sel_W (o := t) (a := z) (b := x) (sl := sY) I.t_lt I.z_live I.x_live (by simp)
    (by simp only [upd_self]; omega) (.inl I.tz) tl) fun u2 ⟨h2, _⟩ => ?_)
  refine WP.seq (WP.mono (h2.add_W (o := a) (a := a) (b := t) (h.liveW_lt a I.a_live) (by simp [I.a_live])
    (by simp) al) fun u3 ⟨h3, _⟩ => ?_)
  refine WP.seq (WP.mono (h3.add_W (o := x) (a := x) (b := x) (h.liveW_lt x I.x_live) (by simp [I.x_live])
    (by simp [I.x_live]) xl) fun u4 ⟨h4, _⟩ => ?_)
  refine WP.seq (wp_movS rfl fun u5 U _ => WP.block_nil ?_)
  have h5 := h4.of_rest U.keeps (by decide) U.mem
  refine WP.seq (WP.mono (h5.half_w (j := y) (by simp [I.y_live]) (by rw [U.gpr]; rfl)
    (fun j hj => by
      simp only [List.mem_cons] at hj
      rcases hj with rfl | rfl | rfl | hj
      · exact I.liveW_apart _ I.x_live
      · exact I.liveW_apart _ I.a_live
      · exact (I.live_apart y I.y_live).1
      · exact I.liveW_apart j hj)) fun u6 ⟨h6, _⟩ => ?_)
  have sYK : sY ≠ sK := by decide
  have cnt : upd (upd V sK (K - i)) sY (upd A y Y y % 2) sK = K - i := by
    rw [upd_ne _ _ (Ne.symm sYK), upd_self]
  refine WP.mono (h6.countNext_ok (by simp) (by rw [cnt]; omega) (by rw [cnt]; omega))
    fun v ⟨hv, zv⟩ => ⟨?_, by rw [zv, cnt]⟩
  unfold ProdS prodStep
  refine hv.mono (fun j hj => ⟨by simp [hj], ?_⟩) (fun j hj => ⟨by simp [hj], ?_⟩)
    (fun d hd => ⟨by simp [hd], ?_⟩)
  · by_cases jy : j = y
    · subst jy; simp [upd]
    · simp [upd, jy]
  · have jt : j ≠ t := fun e => I.t_not (e ▸ hj)
    have zx : z ≠ x := Ne.symm I.xz
    have za : z ≠ a := Ne.symm I.az
    have ne := I.ax; have ne2 := I.tx; have ne3 := I.at'; have ne4 := I.tz
    by_cases jx : j = x
    · subst jx; simp [upd, Ne.symm ne, Ne.symm ne2, Nat.two_mul]
    by_cases ja : j = a
    · subst ja
      simp [upd, ne, Ne.symm ne, ne3, zx, za, zero]
    · simp [upd, jx, ja, jt]
  · by_cases dK : d = sK
    · subst dK; simp only [upd, ite_true, Ne.symm sYK, ite_false]; omega
    · have dY : d ≠ sY := fun e => I.sY_not (by simp at hd; rcases hd with h | h; exact absurd h dK; exact e ▸ h)
      simp [upd, dY, dK]

theorem product_ok {y x a t z Y X : Nat} {u : State}
    (I : ProdIdx y x a t z live liveW ls) (zero : AW z = 0)
    (h : KS g s0 (upd A y Y) live (upd (upd AW x X) a 0) liveW V ls u) :
    WP isa (product y x a t z) u fun v =>
      ProdS g s0 A live AW liveW V ls y x a (32 * g.w) (32 * g.w) ((prodStep (32 * g.W))^[32 * g.w] (Y, X, 0)) v := by
  unfold product
  refine WP.seq (WP.mono h.countN_ok fun u1 h1 => ?_)
  have up := h.upper
  have wpos : 0 < 32 * g.w := by change 0 < 32 * (2 * g.n + 2); omega
  refine countLoop (P := fun i v => ProdS g s0 A live AW liveW V ls y x a (32 * g.w) i
    ((prodStep (32 * g.W))^[i] (Y, X, 0)) v) wpos ?_ fun i v hi hv => ?_
  · exact h1
  · refine WP.mono (productStep_ok I zero hi (by change 32 * (2 * g.n + 2) < _; omega) hv) fun w ⟨hw, zw⟩ => ⟨?_, zw⟩
    rw [Function.iterate_succ_apply']
    exact hw

/-- `product_ok` from the values of the arrays it names. -/
theorem product_ok' {y x a t z Y X : Nat} {u : State}
    (I : ProdIdx y x a t z live liveW ls) (zero : AW z = 0)
    (h : KS g s0 A live AW liveW V ls u) (hy : A y = Y) (hx : AW x = X) (ha : AW a = 0) :
    WP isa (product y x a t z) u fun v =>
      ProdS g s0 A live AW liveW V ls y x a (32 * g.w) (32 * g.w) ((prodStep (32 * g.W))^[32 * g.w] (Y, X, 0)) v :=
  product_ok I zero (by rw [upd_noop hy, upd_noop hx, upd_noop ha]; exact h)

end
end VG.Proof.Rsa.X86.Recover
