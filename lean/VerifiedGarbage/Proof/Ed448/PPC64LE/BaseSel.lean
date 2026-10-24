module

public import VerifiedGarbage.Impl.Ed448.PPC64LE.ScalarBase
public import VerifiedGarbage.Proof.X448.PPC64LE.Field
public import VerifiedGarbage.Proof.X25519.PPC64LE.Cswap
public import VerifiedGarbage.Proof.X448.PPC64LE.Slots
import VerifiedGarbage.Proof.X25519.PPC64LE.Freeze
import VerifiedGarbage.Proof.X448.PPC64LE.Mul
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Ed448 on PPC64LE: the selection

`sel o q r` writes the element at `q`, or at `r` if the mask in `r11` is
`-1`, to `o` (`sel_ok`), limb by limb as X448's `cswap` swaps.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame ACC_eq upd upd_self upd_of_ne
open VG.Impl.X448.PPC64LE (ACC)
open VG.Spec.X448 (Fe)

section
variable {b : Addr}

/-- After `n` limbs of `sel o q r` from `s0`. -/
structure SelInv (b : Addr) (o q r sw : Nat) (s0 : State) (n : Nat) (s : State) : Prop where
  rest : Rest [.r5, .r7] s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 o, 4 * n⟩] s0.mem s.mem
  lo : ∀ j < n, limb s.mem b o j = X25519.PPC64LE.sel sw (limb s0.mem b q j) (limb s0.mem b r j)

theorem sel_ok {o q r : Nat} (ho : o + 56 ≤ 4096) (hq : q + 56 ≤ 4096) (hr : r + 56 ≤ 4096)
    (hoq : o + 56 ≤ q ∨ q + 56 ≤ o) (hor : o + 56 ≤ r ∨ r + 56 ≤ o)
    {s0 : State} (hc : Ctx b s0) {sw : Nat} (hsw : sw ≤ 1) (h11 : s0.gpr .r11 = 0 - BitVec.ofNat 64 sw) :
    WP isa (.block (sel o q r)) s0 (SelInv b o q r sw s0 14) := by
  refine wp_range_flatMap (M := isa) (SelInv b o q r sw s0) (fun k s hk h => ?_) 14 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hcs : Ctx b s := hc.of_rest h.rest (by decide)
  have wq : wd s.mem b (q + 4 * k) = limb s0.mem b q k :=
    wd_frame h.frame fun x hx => by
      rw [List.mem_singleton.mp hx]
      exact Offset.disjoint _ (by omega_using [hoq, hk]) (by omega_using [hq, hk]) (by omega_using [ho, hk])
  have wr : wd s.mem b (r + 4 * k) = limb s0.mem b r k :=
    wd_frame h.frame fun x hx => by
      rw [List.mem_singleton.mp hx]
      exact Offset.disjoint _ (by omega_using [hor, hk]) (by omega_using [hr, hk]) (by omega_using [ho, hk])
  unfold selStep
  refine lw0_ok hcs (d := q + 4 * k) (by omega_using [hq, hk]) fun t1 v1 => ?_
  refine lw0_ok (hcs.of_rest (v1.rest (ws := [.r5]) (by decide)) (by decide)) (d := r + 4 * k)
    (by omega_using [hr, hk]) fun t2 v2 => ?_
  refine wp_xor fun t3 v3 => wp_and fun t4 v4 => wp_xor fun t5 v5 => ?_
  have hr5 : Rest [.r5, .r7] s t5 :=
    (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans (v5.rest (by decide)))))
  have hc5 : Ctx b t5 := hcs.of_rest hr5 (by decide)
  refine sw0_ok hc5 (d := o + 4 * k) (by omega_using [ho, hk]) fun t6 v6 => WP.block_nil ?_
  have eQ : t2.gpr .r5 = (s.mem.readW (b + BitVec.ofNat 64 (q + 4 * k)) 32).setWidth 64 := by
    rw [v2.other _ (by decide), v1.gpr]
  have eR : t2.gpr .r7 = (s.mem.readW (b + BitVec.ofNat 64 (r + 4 * k)) 32).setWidth 64 := by
    rw [v2.gpr, v1.mem]
  have em : t3.gpr .r11 = 0 - BitVec.ofNat 64 sw := by
    rw [v3.other _ (by decide), v2.other _ (by decide), v1.other _ (by decide), h.rest.gpr _ (by decide), h11]
  have e5 : t5.gpr .r5 = t2.gpr .r5 ^^^ ((t2.gpr .r7 ^^^ t2.gpr .r5) &&& (0 - BitVec.ofNat 64 sw)) := by
    rw [v5.gpr, v4.other _ (by decide), v3.other _ (by decide), v4.gpr, v3.gpr, em]
  have hm6 : t6.mem = s.mem.writeW (b + BitVec.ofNat 64 (o + 4 * k)) ((t5.gpr .r5).setWidth 32) := by
    rw [v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]
  have vo : ((t5.gpr .r5).setWidth 32).toNat = X25519.PPC64LE.sel sw (limb s0.mem b q k) (limb s0.mem b r k) := by
    rw [e5, eQ, eR, ← wq, ← wr]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
    · rw [sel0r, lo32_ext]; rfl
    · rw [sel1r, lo32_ext]; rfl
  refine ⟨h.rest.trans (hr5.trans (v6.rest _)), ?_, fun j hj => ?_⟩
  · rw [hm6]
    exact (h.frame.sub fun x hx => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hx]; exact Region.sub_prefix (by omega_using [])⟩).writeW
      (List.mem_singleton_self _) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega_using []) (by omega_using [ho, hk]))
  · rw [limb, hm6]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega_using [ho, hk])]; exact h.lo j hj
    · rw [wd_write_self, vo]

/-- An element above the field area is kept by code writing only there. -/
theorem fs_above {m m' : Mem} (hf : Frame [FA b] m m') {q : Nat} (hq : ACC + 112 ≤ q)
    (hq' : q + 56 ≤ 4096) : FS m' b q = FS m b q := by
  have e : ∀ k < 14, limb m' b q k = limb m b q k :=
    limb_frame hf fun r hr k hk => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint_base b (by omega_using [hq]) (by omega_using [hq', hk])
  rw [FS, V, val32_congr e]; rfl

/-- So is a byte above it. -/
theorem byte_above {m m' : Mem} (hf : Frame [FA b] m m') {d : Nat} (hd : ACC + 112 ≤ d)
    (hd' : d < 4096) : m' (b + BitVec.ofNat 64 d) = m (b + BitVec.ofNat 64 d) :=
  hf _ fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact fun h => Offset.disjoint_base b (d := d) (n := 1) (k := ACC + 112) hd (by omega_using [hd'])
      _ (Region.contains_self _ _) h

/-- `sel o q r` as an update of the slots: `o` gets `x`, the element at `q`
above the field area, or `r`'s if `sw = 1`. -/
theorem selS {o q r : Nat} {qs : List Nat} {v : Nat → Fe} {x : Fe} (hq : Sep1 o qs = true)
    (ho : o + 56 ≤ ACC) (hq4 : ACC + 112 ≤ q) (hq5 : q + 56 ≤ 4096) (hr : r ∈ qs) (hro : r ≠ o)
    {s : State} (hc : Ctx b s) {sw : Nat} (hsw : sw ≤ 1) (h11 : s.gpr .r11 = 0 - BitVec.ofNat 64 sw)
    (hS : SlotsOk s.mem b qs v) (hx : FS s.mem b q = x) :
    WP isa (.block (sel o q r)) s fun s' => Rest [.r5, .r7] s s' ∧ Frame [FA b] s.mem s'.mem ∧
      SlotsOk s'.mem b (o :: qs) (upd v o (X25519.PPC64LE.sel sw x (v r))) := by
  have hr' := sep1_get hq hr
  have hA := ACC_eq
  refine WP.mono (sel_ok (b := b) (o := o) (q := q) (r := r) (by omega_using [hA, ho]) hq5
    (by omega_using [hA, hr']) (.inl (by omega_using [ho, hq4]))
    (by omega_using [hr', hro]) hc hsw h11) fun s' h => ⟨h.rest, ?_, fun q' hq' => ?_⟩
  · exact h.frame.sub fun x hx => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hx]; exact Offset.sub_base _ (by omega_using [ho])⟩
  · by_cases hqo : q' = o
    · subst hqo
      rw [upd_self]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
      · have e : ∀ k < 14, limb s'.mem b q' k = limb s.mem b q k := fun k hk => by rw [h.lo k hk]; rfl
        rw [FS, V, val32_congr e]; exact hx
      · have e : ∀ k < 14, limb s'.mem b q' k = limb s.mem b r k := fun k hk => by rw [h.lo k hk]; rfl
        rw [FS, V, val32_congr e]; exact hS r hr
    · rw [upd_of_ne _ _ hqo]
      exact slots_after hq ho (frame_o (h.frame : Frame [⟨b + BitVec.ofNat 64 o, 56⟩] _ _)) hS
        ((List.mem_cons.mp hq').resolve_left hqo) hqo

end

end VG.Proof.Ed448.PPC64LE
