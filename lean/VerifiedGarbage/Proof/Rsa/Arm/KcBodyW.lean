module

public import VerifiedGarbage.Proof.Rsa.Arm.KcWords
public import VerifiedGarbage.Proof.Rsa.Arm.KcChecks
import VerifiedGarbage.Proof.Rsa.Arm.InvParts

/-! # The checks of an RSA key on ARMv7: a balanced key, by words

`keyBodyW_ok`: from `BodyIn`, for `w` even and `p`, `q` of `w / 2` words, the mask is `cW` of
what the code computes: `p q mod 2^(32 w) = n` in place of the division of `n` by `p`, and the
remainders by words (`KeyDiv.divW`), modulo the divisors with their top words made not zero
(`fixT`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

/-- The products of a balanced key's checks, when their factors are below their moduli. -/
def ProdsW (g : Geo) (v : Vals) (R₁ R₂ : Nat) : Prop :=
  (v.dP < 2 * (v.p / 2) → 2 * (2 * (v.p / 2)) ≤ 2 ^ (32 * g.w) →
    R₁ = v.e % 2 ^ 33 * v.dP % (2 * (v.p / 2))) ∧
  (v.dQ < 2 * (v.q / 2) → 2 * (2 * (v.q / 2)) ≤ 2 ^ (32 * g.w) →
    R₂ = v.e % 2 ^ 33 * v.dQ % (2 * (v.q / 2)))

/-- The mask a balanced key's checks compute. -/
abbrev cW (g : Geo) (v : Vals) (R₁ R₂ : Nat) : Bool :=
  VG.Proof.Rsa.keyBitsW g.w v.n v.d v.p v.q v.dP v.dQ v.qI R₁ R₂

theorem divK_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a d : Nat} (ha : a ∈ live) (hd : d ∈ live) (hz : aZ ∈ live) (hA0 : A aZ = 0)
    (haV : a ≠ aVD) (hdV : d ≠ aVD) (hav : a ∉ [aVR, aVT, aY, aX]) (hw6 : 6 ≤ g.w)
    (hD : A d < 2 ^ (32 * (g.w / 2)))
    (hlive : ∀ j ∈ live, j = aVR ∨ j ∉ [aVR, aVT, aY, aX]) :
    WP isa (seqs (divK a d)) s (Stg g s0 (upd (upd A aVD (fixT (g.w / 2) (A d))) aVR
      (A a % fixT (g.w / 2) (A d))) (aVR :: aVD :: live) c) := by
  unfold divK
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h.copy_ok (o := aVD) (a := d) (by decide) hd (Ne.symm hdV)) fun t1 h1 => ?_
  rw [wp_seqs_cons (by simp)]
  have hD1 : upd A aVD (A d) aVD < 2 ^ (32 * (g.w / 2)) := by rw [upd_self]; exact hD
  refine WP.mono (h1.fixTop_ok (m := aVD) (by simp) hD1 (by omega)) fun t2 h2 => ?_
  rw [upd_self] at h2
  simp only [seqs]
  have ha' : a ∈ aVD :: live := List.mem_cons_of_mem _ ha
  have hz' : aZ ∈ aVD :: live := List.mem_cons_of_mem _ hz
  have hm' : aVD ∈ aVD :: live := by simp
  have e1 : upd (upd A aVD (A d)) aVD (fixT (g.w / 2) (A d)) = upd A aVD (fixT (g.w / 2) (A d)) := by
    funext j; simp only [upd]; split <;> rfl
  rw [e1] at h2
  have := h2.divW_ok (a := a) (r := aVR) (m := aVD) (t := aVT) (nm := aY) (u := aX) ha' hm' hz'
    (by rw [upd_ne _ _ (by decide : aZ ≠ aVD)]; exact hA0) (hr := by decide) (ht := by decide)
    (hnm := by decide) (hu := by decide) (hra := fun e => hav (by simp [e])) (hrt := by decide)
    (hru := by decide) (htu := by decide) (hmr := by decide) (hmt := by decide) (hmu := by decide)
    (hnr := by decide) (htn := by decide) (hnu := by decide) (hnm' := by decide) (hr0 := by decide)
    (ht0 := by decide) (hu0 := by decide) (hn0 := by decide) (hV := by decide) (hw6 := hw6)
    (hMl := by rw [upd_self]; exact fixT_lt (by omega) hD) (hMg := by rw [upd_self]; exact fixT_ge)
    (hlive := fun j hj => by
      rcases List.mem_cons.mp hj with rfl | hj'
      · right; decide
      · rcases hlive j hj' with e | e
        · left; exact e
        · right; simpa [List.mem_cons, or_comm, or_left_comm] using e)
  rw [upd_self, upd_ne _ _ haV] at this
  exact this

/-- The lists of programs the checks are made of are not empty. -/
macro "ne_nil" : tactic => `(tactic| first
  | exact List.cons_ne_nil _ _
  | exact List.append_ne_nil_of_left_ne_nil (List.cons_ne_nil _ _) _
  | (apply List.append_ne_nil_of_left_ne_nil; unfold eqA; exact List.cons_ne_nil _ _)
  | (apply List.append_ne_nil_of_left_ne_nil; unfold ltA; exact List.cons_ne_nil _ _)
  | (apply List.append_ne_nil_of_left_ne_nil; unfold mulA; exact List.cons_ne_nil _ _)
  | (apply List.append_ne_nil_of_left_ne_nil; unfold divK; exact List.cons_ne_nil _ _)
  | (unfold eqA; exact List.cons_ne_nil _ _)
  | (unfold ltA; exact List.cons_ne_nil _ _)
  | (unfold mulA; exact List.cons_ne_nil _ _)
  | (unfold divK; exact List.cons_ne_nil _ _))

theorem mulIdx_qp : MulIdx nArr aZ aY aX aA aP aT := by decide

/-- `keyBodyW`: for a balanced key, the mask is `cW` of what the checks compute. -/
theorem keyBodyW_ok {g : Geo} {v : Vals} {s : State} (h : BodyIn g v s) (hw : g.w % 2 = 0)
    (hp : v.p < 2 ^ (32 * (g.w / 2))) (hq : v.q < 2 ^ (32 * (g.w / 2))) :
    WP isa keyBodyW s fun t => ∃ R₁ R₂, ProdsW g v R₁ R₂ ∧ ∃ A live, Stg g s A live (cW g v R₁ R₂) t := by
  have kb := h.kb
  have hw6 : 6 ≤ g.w := by simp only [Geo.w]; omega
  have wle : g.w ≤ 1024 := by simp only [Geo.w]; omega
  unfold keyBodyW crtChecksW dChecksW
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [wp_seqs_cons (by ne_nil)]
  refine WP.mono (first_ok h) fun t0 h0 => ?_
  rw [wp_seqs_cons (by ne_nil)]
  refine WP.mono (h0.mulLo_ok (o := aVQ) (x := aP) (y := aQ) (by decide) (by decide) (by decide) (by decide) rfl
    (by decide) (by decide) (by decide) (by decide) hw (by omega) hp) fun t1 h1 => ?_
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h1.eqA_ok (a := aVQ) (b := aN) (by decide) (by decide) (by decide)) fun t2 h2 => ?_
  rw [wp_seqs_cons (by ne_nil)]
  refine WP.mono (h2.copy_ok (o := aM1) (a := aP) (by decide) (by decide) (by decide)) fun t3 h3 => ?_
  rw [wp_seqs_cons (by ne_nil)]
  refine WP.mono (h3.clrLow_ok (j := aM1) (by decide)) fun t4 h4 => ?_
  rw [wp_seqs_cons (by ne_nil)]
  refine WP.mono (h4.copy_ok (o := aM2) (a := aQ) (by decide) (by decide) (by decide)) fun t5 h5 => ?_
  rw [wp_seqs_cons (by ne_nil)]
  refine WP.mono (h5.clrLow_ok (j := aM2) (by decide)) fun t6 h6 => ?_
  -- `dP`.
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h6.ltA_ok (a := aDP) (b := aM1) (by decide) (by decide) (by decide)) fun t7 h7 => ?_
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h7.mulA_ok (y := aE) (x := aDP) (m := aM1) (k := 33) (by decide) (by decide) (by decide)
    (by decide) rfl mulIdx_m1 (by decide) (by decide) (by decide) (by decide) fun u _ => cnt33_ok u)
    fun t8 ⟨R₁, hR₁, h8⟩ => ?_
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h8.eqA_ok (a := aA) (b := aOne) (by decide) (by decide) (by decide)) fun t9 h9 => ?_
  -- `dQ`.
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h9.ltA_ok (a := aDQ) (b := aM2) (by decide) (by decide) (by decide)) fun t10 h10 => ?_
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h10.mulA_ok (y := aE) (x := aDQ) (m := aM2) (k := 33) (by decide) (by decide) (by decide)
    (by decide) rfl mulIdx_m2 (by decide) (by decide) (by decide) (by decide) fun u _ => cnt33_ok u)
    fun t11 ⟨R₂, hR₂, h11⟩ => ?_
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h11.eqA_ok (a := aA) (b := aOne) (by decide) (by decide) (by decide)) fun t12 h12 => ?_
  -- `qInv`.
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h12.ltA_ok (a := aQI) (b := aP) (by decide) (by decide) (by decide)) fun t13 h13 => ?_
  rw [wp_seqs_cons (by ne_nil)]
  refine WP.mono (h13.mulLo_ok (o := aT) (x := aQ) (y := aQI) (by decide) (by decide) (by decide) (by decide) rfl
    (by decide) (by decide) (by decide) (by decide) hw (by omega) hq) fun t14 h14 => ?_
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (divK_ok h14 (a := aT) (d := aP) (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    (by decide) hw6 hp (by decide)) fun t15 h15 => ?_
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h15.eqA_ok (a := aVR) (b := aOne) (by decide) (by decide) (by decide)) fun t16 h16 => ?_
  -- `d`.
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h16.ltA_ok (a := aD) (b := aN) (by decide) (by decide) (by decide)) fun t17 h17 => ?_
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  have p2 : 2 * (v.p / 2) < 2 ^ (32 * (g.w / 2)) := Nat.lt_of_le_of_lt (by omega) hp
  have q2 : 2 * (v.q / 2) < 2 ^ (32 * (g.w / 2)) := Nat.lt_of_le_of_lt (by omega) hq
  refine WP.mono (divK_ok h17 (a := aD) (d := aM1) (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    (by decide) hw6 p2 (by decide)) fun t18 h18 => ?_
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h18.eqA_ok (a := aVR) (b := aDP) (by decide) (by decide) (by decide)) fun t19 h19 => ?_
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (divK_ok h19 (a := aD) (d := aM2) (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    (by decide) hw6 q2 (by decide)) fun t20 h20 => ?_
  exact WP.mono (h20.eqA_ok (a := aVR) (b := aDQ) (by decide) (by decide) (by decide)) fun t h21 =>
    ⟨R₁, R₂, ⟨hR₁, hR₂⟩, _, _, h21⟩

end VG.Proof.Rsa.Arm.KeyCheck
