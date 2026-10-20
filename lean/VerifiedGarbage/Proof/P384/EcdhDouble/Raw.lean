module

public import VerifiedGarbage.Proof.P384.Ops
public import VerifiedGarbage.Impl.P384.EcdhDouble
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Proof.P384.Linear
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.P384.EcdhDouble.Vals

/-!
# P-384's raw doubling

`raw_ok`: the raw doubling (`Impl/P384/EcdhDouble.lean`) from `p` into `o`
leaves in `o` the window's Jacobian doubling of `p` (`raw_vals`), changing
only the registers `clobX` and the slots `rcbW` and `tmp`. Its field
operations are `fprog_ok`'s, its linear combinations `linOp_ok`'s. The
conditions on its slots (`RawSlots`) are decided for each direction.
-/

@[expose] public section

-- Powers of two up to `2^384` are evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.P384.EcdhDouble
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.P384.EcdhDouble
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.P384.Ops (clobX ProgKeepX OpKeepX)
open VG.Proof.Weierstrass.AArch64.Mont (p384)
open Spec.Weierstrass

theorem K_M : K.M = Impl.P384.Ops.M := rfl

theorem _root_.VG.Proof.P384.Ops.ProgKeepX.ofOp {base : Addr} {o : Nat} {s t : State} (h : OpKeepX base o s t) :
    ProgKeepX base [o] s t :=
  ⟨h.gpr, h.rd, h.wr, h.sp, fun x hx ht => h.mem x (hx o (List.mem_singleton_self _)) ht⟩

theorem _root_.VG.Proof.P384.Ops.ProgKeepX.trans {base : Addr} {W W' : List Nat} {s t u : State} (h : ProgKeepX base W s t)
    (h' : ProgKeepX base W' t u) : ProgKeepX base (W ++ W') s u :=
  ⟨fun r hr => (h'.gpr r hr).trans (h.gpr r hr), h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp,
    fun x hx ht => (h'.mem x (fun w hw => hx w (List.mem_append_right _ hw)) ht).trans
      (h.mem x (fun w hw => hx w (List.mem_append_left _ hw)) ht)⟩

/-- What the raw doubling from `p` into `o` needs of its slots, decided for each direction. -/
structure RawSlots (p o : Pt) : Prop where
  nodup : [p.x, p.y, p.z, o.x, o.y, o.z, K.S.t0, K.S.t1, K.S.t2, K.S.t3].Nodup
  sl1 : ∀ op ∈ ops1 p o, ∀ x ∈ op.out :: op.ins, x ∈ winSlots K
  sl2 : ∀ op ∈ ops2 o, ∀ x ∈ op.out :: op.ins, x ∈ winSlots K
  out : ∀ x ∈ [o.x, o.y, o.z], x ∈ winSlots K
  rd1 : readsOk (ops1 p o) [p.x, p.y, p.z] = true
  rd2 : readsOk (ops2 o) [K.S.t0, K.S.t1, K.S.t2, K.S.t3, o.x, o.y, o.z] = true
  wr1 : ∀ x ∈ [K.S.t0, K.S.t1, K.S.t2, K.S.t3, o.x, o.y, o.z], x ∈ (ops1 p o).map FOp.out
  w1 : ∀ op ∈ ops1 p o, op.out ∈ rcbW K.S o
  w2 : ∀ op ∈ ops2 o, op.out ∈ rcbW K.S o
  other : ∀ x ∈ rcbW K.S o, x ∈ winOther K

theorem rawSlots_RD : RawSlots K.R K.D := ⟨by decide, by decide, by decide, by decide, by decide,
  by decide, by decide, by decide, by decide, by decide⟩

theorem rawSlots_DR : RawSlots K.D K.R := ⟨by decide, by decide, by decide, by decide, by decide,
  by decide, by decide, by decide, by decide, by decide⟩

/-- The raw doubling from `p` into `o`. -/
theorem raw_ok {C : Curve} (hC : C.p = p384) {base : Addr} {size : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {p o : Pt} (hS : RawSlots p o)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p (· ∈ winSlots K) V E s) (hV : ∀ x ∈ [p.x, p.y, p.z], x ∈ V) :
    WP isa (.block (raw p o)) s fun s' => KeepRegs clobX s s' ∧
      Unch base (loopW K) s.mem s'.mem ∧ ∃ E' : Nat → Fe C,
      Inv K.M base size C.p (· ∈ winSlots K) ([o.x, o.y, o.z] ++ V) E' s' ∧
      (∀ x, x ∉ rcbW K.S o → E' x = E x) ∧
      (E' o.x, E' o.y, E' o.z) = dblJF (E p.x) (E p.y) (E p.z) := by
  have mv : ∀ {ops : List FOp} {W : List Nat} {x : Nat}, x ∈ ops.map FOp.out → x ∈ validAfter ops W :=
    fun h => (mem_validAfter _ _).mpr (Or.inr h)
  have mw : ∀ {ops : List FOp} {W : List Nat} {x : Nat}, x ∈ W → x ∈ validAfter ops W :=
    fun h => (mem_validAfter _ _).mpr (Or.inl h)
  have w1 := fun x hx => mv (W := V) (hS.wr1 x hx)
  rw [raw, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  -- The operations before `d`.
  refine WP.mono (Ops.fprog_ok hC hL.lay hA.al hp (ops1 p o) hI hS.sl1 (readsOk_mono hS.rd1 hV))
    fun s₁ ⟨k₁, I₁⟩ => ?_
  -- `d = 12 x y² - 9 m²`.
  rw [WP.block_append_iff]
  refine WP.mono (Linear.linOp_ok hC hL.lay hA.al I₁ (hS.out _ (by simp)) (w1 _ (by simp))
    (w1 _ (by simp)) (by decide) (by decide)) fun s₂ ⟨k₂, I₂⟩ => ?_
  -- The operations after `d`.
  rw [WP.block_append_iff]
  refine WP.mono (Ops.fprog_ok hC hL.lay hA.al hp (ops2 o) I₂ hS.sl2
    (readsOk_mono hS.rd2 fun x hx => List.mem_cons_of_mem _ (w1 x hx))) fun s₃ ⟨k₃, I₃⟩ => ?_
  -- `x' = 4 x y² - d` and `y' = 3 d m - 8 y⁴`.
  have w3 : ∀ x ∈ [K.S.t0, K.S.t1, K.S.t3, o.y], x ∈ validAfter (ops2 o)
      (o.y :: validAfter (ops1 p o) V) := by
    intro x hx
    refine mw (List.mem_cons_of_mem _ (w1 x ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp
  rw [WP.block_append_iff]
  refine WP.mono (Linear.linOp_ok hC hL.lay hA.al I₃ (hS.out _ (by simp)) (w3 _ (by simp))
    (w3 _ (by simp)) (by decide) (by decide)) fun s₄ ⟨k₄, I₄⟩ => ?_
  refine WP.mono (Linear.linOp_ok hC hL.lay hA.al I₄ (hS.out _ (by simp))
    (List.mem_cons_of_mem _ (w3 _ (by simp))) (List.mem_cons_of_mem _ (w3 _ (by simp)))
    (by decide) (by decide)) fun s₅ ⟨k₅, I₅⟩ => ?_
  -- The frame.
  have k := ((((k₁.trans (ProgKeepX.ofOp k₂)).trans k₃).trans (ProgKeepX.ofOp k₄)).trans (ProgKeepX.ofOp k₅))
  have hw : ∀ w ∈ (ops1 p o).map FOp.out ++ [o.y] ++ (ops2 o).map FOp.out ++ [o.x] ++ [o.y],
      w ∈ rcbW K.S o := by
    intro w hw
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hw
    rcases hw with (((⟨op, hop, rfl⟩ | rfl) | ⟨op, hop, rfl⟩) | rfl) | rfl
    · exact hS.w1 op hop
    · simp [rcbW]
    · exact hS.w2 op hop
    · simp [rcbW]
    · simp [rcbW]
  refine ⟨⟨k.gpr, k.rd, k.wr, k.sp⟩, (ProgKeepX.mono (W' := rcbW K.S o) k hw).unch.mono fun w hw => ?_,
    rawEnv p o E, I₅.sub fun x hx => ?_, fun x hx => ?_, raw_vals E hS.nodup⟩
  · simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw ⊢
    rcases hw with ⟨y, hy, rfl⟩ | rfl
    · exact Or.inl ⟨y, hS.other y hy, rfl⟩
    · exact Or.inr rfl
  · rcases List.mem_append.mp hx with hx | hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mw (List.mem_cons_of_mem _ (w1 _ (by simp)))))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mw (List.mem_cons_of_mem _ (mw hx))))
  · have hy : x ≠ o.y := fun h => hx (h ▸ by simp [rcbW])
    have hx' : x ≠ o.x := fun h => hx (h ▸ by simp [rcbW])
    simp only [rawEnv, Function.update_of_ne hy, Function.update_of_ne hx']
    rw [runOps_of_not_out _ _ fun op hop h => hx (by rw [← h]; exact hS.w2 op hop), Function.update_of_ne hy,
      runOps_of_not_out _ _ fun op hop h => hx (by rw [← h]; exact hS.w1 op hop)]

end VG.Proof.P384.EcdhDouble
