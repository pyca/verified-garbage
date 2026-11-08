module

-- separate module: its proofs (about 8 s) cost more than its imports, and its importer's
-- changes need not re-check them

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P256.Window
public import VerifiedGarbage.Impl.Ecdsa.P224.PPC64LE
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Flags
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Bits
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Loop
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Step


/-!
# `[k]P` by windows on PPC64LE, P-224

The proof of `Proof/Ecdsa/PPC64LE/P256/Window.lean` for P-224, whose
coordinates are also four words and whose `a` is also `-3`, so that its
layout is P-256's: the field programs, `R = 16 R`, the complete addition,
the table, the entries and the loop, on P-224's field. The lemmas that do not
depend on the curve (`ofN_ok`, `wstep`, the nibble's arithmetic, the masks)
are P-256's.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE.Window.P224

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Ecdsa.PPC64LE.Window
open VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE VG.Impl.Weierstrass.PPC64LE.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Proof.Weierstrass.PPC64LE.Point (KeepR tmv)
open VG.Spec.Weierstrass (Point Fe mul onCurve)
open VG.Proof.Ecdsa.PPC64LE (p224_ok)

/-- P-224. -/
abbrev W : Spec.Weierstrass.Curve := Spec.P224.curve

theorem am3 : AM3 W := by unfold AM3; decide

theorem unit : UnitMod W.p (2 ^ (64 * 4)) := unitMod_pow_two (by decide) _

/-! ## The slots -/

/-- The field: P-224's prime, of four words. -/
abbrev FP : Impl.Weierstrass.Mont.Modulus := p224.SP

instance : NeZero FP.m := ⟨by decide⟩

theorem fp_ok : ModOk FP.k FP.m := p224_ok.fp

theorem fp_m : FP.m = W.p := rfl

/-- The slots the windows' arithmetic may use: those at multiples of 32 from
zero's (past `p` and the temporary) up to the functions' own working space. -/
abbrev wS (x : Nat) : Prop := x % 32 = 0 ∧ 160 ≤ x ∧ x + 32 ≤ 3840

theorem wLay : Lay p224.MP' (own p224.MP'.n) wS :=
  ⟨fun x h => h.2.2, fun x y hx hy hne => by
    obtain ⟨h1, -, -⟩ := hx; obtain ⟨h2, -, -⟩ := hy
    show x + 8 * 4 ≤ y ∨ y + 8 * 4 ≤ x; omega,
   fun x h => by obtain ⟨-, h, -⟩ := h; show x + 8 * 4 ≤ 64 ∨ 64 + 8 * 4 ≤ x; omega,
   fun x h => by obtain ⟨-, h, -⟩ := h; show x + 8 * 4 ≤ 128 ∨ 128 + 8 * 4 ≤ x; omega⟩

/-- A point's slots hold numbers below `p` that represent `P`. -/
structure PtOk (base : Addr) (s : State) (p : Pt) (P : Point W) : Prop where
  rep : Rep W (tmv W 4 base s p.x) (tmv W 4 base s p.y) (tmv W 4 base s p.z) P
  x : wordsVal s.mem base p.x 4 < W.p
  y : wordsVal s.mem base p.y 4 < W.p
  z : wordsVal s.mem base p.z 4 < W.p

theorem PtOk.of_eq {base : Addr} {s s' : State} {p : Pt} {P : Point W} (h : PtOk base s p P)
    (ex : wordsVal s'.mem base p.x 4 = wordsVal s.mem base p.x 4)
    (ey : wordsVal s'.mem base p.y 4 = wordsVal s.mem base p.y 4)
    (ez : wordsVal s'.mem base p.z 4 = wordsVal s.mem base p.z 4) : PtOk base s' p P :=
  ⟨by simp only [tmv]; rw [ex, ey, ez]; exact h.rep, by rw [ex]; exact h.x, by rw [ey]; exact h.y,
    by rw [ez]; exact h.z⟩

theorem PtOk.move {base : Addr} {s s' : State} {p o : Pt} {P : Point W} (h : PtOk base s p P)
    (ex : wordsVal s'.mem base o.x 4 = wordsVal s.mem base p.x 4)
    (ey : wordsVal s'.mem base o.y 4 = wordsVal s.mem base p.y 4)
    (ez : wordsVal s'.mem base o.z 4 = wordsVal s.mem base p.z 4) : PtOk base s' o P :=
  ⟨by simp only [tmv]; rw [ex, ey, ez]; exact h.rep, by rw [ex]; exact h.x, by rw [ey]; exact h.y,
    by rw [ez]; exact h.z⟩

/-- The constants the windows read: `a` and `b` in Montgomery's form (`b` at
the slot `bp`), zero and Montgomery's one. -/
structure KC (bp : Nat) (base : Addr) (s : State) : Prop where
  ap : wordsVal s.mem base (p224.sl AP) 4 = W.a * 2 ^ 256 % W.p
  bp : wordsVal s.mem base (p224.sl bp) 4 = W.b * 2 ^ 256 % W.p
  zero : wordsVal s.mem base (p224.sl ZERO) 4 = 0
  onep : wordsVal s.mem base (p224.sl ONEP) 4 = 2 ^ 256 % W.p

theorem KC.of_eq {bp : Nat} {base : Addr} {s s' : State} (h : KC bp base s)
    (e : ∀ d ∈ [p224.sl AP, p224.sl bp, p224.sl ZERO, p224.sl ONEP],
      wordsVal s'.mem base d 4 = wordsVal s.mem base d 4) : KC bp base s' :=
  ⟨(e _ (by simp)).trans h.ap, (e _ (by simp)).trans h.bp, (e _ (by simp)).trans h.zero,
    (e _ (by simp)).trans h.onep⟩

/-! ## `R = 16 R` -/

/-- The complete addition's and the doublings' slots. -/
abbrev S3 : RcbSlots := Cfg.slots p224 BPs

theorem S3_eq : S3 = ⟨256, 1344, 800, 832, 864, 896, 928, 960⟩ := rfl
theorem rPt_eq : Cfg.rPt p224 = ⟨512, 544, 576⟩ := rfl
theorem dPt_eq : Cfg.dPt p224 = ⟨608, 640, 672⟩ := rfl
theorem tPt_eq : Cfg.tPt p224 = ⟨704, 736, 768⟩ := rfl
theorem zeroPt_eq : Cfg.zeroPt p224 = ⟨160, 160, 160⟩ := rfl

theorem dblJ_apart_DT : RcbApart S3 (Cfg.dPt p224) (Cfg.dPt p224) (Cfg.tPt p224) := ⟨by decide, by decide⟩
theorem dblJ_apart_TD : RcbApart S3 (Cfg.tPt p224) (Cfg.tPt p224) (Cfg.dPt p224) := ⟨by decide, by decide⟩
theorem toJ_apart : RcbApart S3 (Cfg.rPt p224) (Cfg.zeroPt p224) (Cfg.dPt p224) := ⟨by decide, by decide⟩
theorem fromJ_apart : RcbApart S3 (Cfg.dPt p224) (Cfg.zeroPt p224) (Cfg.rPt p224) := ⟨by decide, by decide⟩

/-- A Jacobian doubling from `p` to `o` (`D` to `T` or back), on `InvJ`. -/
theorem dblStep_ok (hL : Law W) {base : Addr} {s : State} {p o : Pt} (hA : RcbApart S3 p p o)
    (hsl : ∀ x ∈ rcbW S3 o ++ rcbR S3 p p, wS x) {V : List Nat} {E : Nat → Fe W}
    (hI : Inv 4 base W.p wS V E s) (hV : ∀ x ∈ rcbR S3 p p, x ∈ V) {P : Point W}
    (hP : onCurve W P = true) (hJ : InvJ W (E p.x) (E p.y) (E p.z) P) :
    WP isa (fprog FP (dblJ S3 p o)) s fun s' => KeepR 4 (fun x => x) base (rcbW S3 o) s s' ∧
      ∃ E', Inv 4 base W.p wS ([o.x, o.y, o.z] ++ V) E' s' ∧ InvJ W (E' o.x) (E' o.y) (E' o.z) (d2 P) ∧
        ∀ x, x ∉ rcbW S3 o → E' x = E x := by
  rw [dblJ_eq]
  refine WP.mono (ofN_ok (S' := FP) (M := p224.MP') fp_ok rfl wLay unit dblJN_ok hA hsl hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, InvJ.dbl' hL am3 hP hJ (v.trans (dblJN_run _)), kp⟩

/-- `R` into Jacobian coordinates in `D`. -/
theorem toJStep_ok (hL : Law W) {base : Addr} {s : State} {V : List Nat} {E : Nat → Fe W}
    (hI : Inv 4 base W.p wS V E s) (hV : ∀ x ∈ rcbR S3 (Cfg.rPt p224) (Cfg.zeroPt p224), x ∈ V) {P : Point W}
    (hR : Rep W (E 512) (E 544) (E 576) P) (hz : E 160 = 0) :
    WP isa (fprog FP (toJ S3 (Cfg.rPt p224) (Cfg.zeroPt p224) (Cfg.dPt p224))) s fun s' =>
      KeepR 4 (fun x => x) base (rcbW S3 (Cfg.dPt p224)) s s' ∧
      ∃ E', Inv 4 base W.p wS ([608, 640, 672] ++ V) E' s' ∧
        InvJ W (E' 608) (E' 640) (E' 672) P ∧
        ∀ x, x ∉ rcbW S3 (Cfg.dPt p224) → E' x = E x := by
  rw [toJ_eq]
  refine WP.mono (ofN_ok (S' := FP) (M := p224.MP') fp_ok rfl wLay unit toJN_ok toJ_apart (by decide) hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, InvJ.of_toJ hL hR hz (v.trans (toJN_run _)), kp⟩

/-- `D` back in projective coordinates in `R`. -/
theorem fromJStep_ok {base : Addr} {s : State} {V : List Nat} {E : Nat → Fe W}
    (hI : Inv 4 base W.p wS V E s) (hV : ∀ x ∈ rcbR S3 (Cfg.dPt p224) (Cfg.zeroPt p224), x ∈ V) :
    WP isa (fprog FP (fromJ S3 (Cfg.dPt p224) (Cfg.zeroPt p224) (Cfg.rPt p224))) s fun s' =>
      KeepR 4 (fun x => x) base (rcbW S3 (Cfg.rPt p224)) s s' ∧
      ∃ E', Inv 4 base W.p wS ([512, 544, 576] ++ V) E' s' ∧
        (E' 512, E' 544, E' 576) = (E 608 * E 672, E 640 + E 160, E 672 * E 672 * E 672) ∧
        ∀ x, x ∉ rcbW S3 (Cfg.rPt p224) → E' x = E x := by
  rw [fromJ_eq]
  refine WP.mono (ofN_ok (S' := FP) (M := p224.MP') fp_ok rfl wLay unit fromJN_ok fromJ_apart (by decide) hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, v.trans (fromJN_run _), kp⟩

/-- What `R = 16 R` writes: `R`, `D`, `T`, the temporaries and the
functions' own working space. -/
abbrev quadW : List (Nat × Nat) := [(512, 480), (3840, 256)]

/-- The slots its field operations write. -/
abbrev quadWl : List Nat := [800, 832, 864, 896, 928, 960, 512, 544, 576, 608, 640, 672, 704, 736, 768]

/-- `R = 16 R`, for `R` representing `P`. -/
theorem quad_ok (hL : Law W) {base : Addr} {s : State} (hw : WsReg s base) (hK : KC BPs base s) {P : Point W}
    (hP : onCurve W P = true) (hR : PtOk base s (Cfg.rPt p224) P) :
    WP isa (Cfg.quad p224 BPs) s fun s' => Rk fnClob s s' ∧ Unch base quadW s.mem s'.mem ∧
      PtOk base s' (Cfg.rPt p224) (d16 P) := by
  have hp0 : 0 < W.p := by decide
  have hn := hw.nowrap
  rw [Cfg.quad]
  simp only [progs]
  -- The start: `a`, `b`, zero and `R`.
  have hI : Inv 4 base W.p wS [256, 1344, 160, 512, 544, 576]
      (fun x => toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base x 4)) s := by
    refine ⟨hw, by decide, fun x hx => ?_, fun x _ => rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt hK.ap (Nat.mod_lt _ hp0)
    · exact lt_of_eq_of_lt hK.bp (Nat.mod_lt _ hp0)
    · exact lt_of_eq_of_lt hK.zero hp0
    exacts [hR.x, hR.y, hR.z]
  have e0 : toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base 160 4) = 0 := by
    rw [show wordsVal s.mem base 160 4 = 0 from hK.zero]; exact toM_zero _ _
  -- To Jacobian coordinates.
  refine WP.seq (WP.mono (toJStep_ok hL hI (by decide) hR.rep e0) fun s₁ ⟨k₁, E₁, I₁, J₁, p₁⟩ => ?_)
  -- Four doublings.
  refine WP.seq (WP.mono (dblStep_ok hL dblJ_apart_DT (by decide) I₁ (by decide) hP J₁)
    fun s₂ ⟨k₂, E₂, I₂, J₂, p₂⟩ => ?_)
  refine WP.seq (WP.mono (dblStep_ok hL dblJ_apart_TD (by decide) I₂ (by decide) (hL.onCurve_add hP hP) J₂)
    fun s₃ ⟨k₃, E₃, I₃, J₃, p₃⟩ => ?_)
  have h4 := hL.onCurve_add (hL.onCurve_add hP hP) (hL.onCurve_add hP hP)
  refine WP.seq (WP.mono (dblStep_ok hL dblJ_apart_DT (by decide) I₃ (by decide) h4 J₃)
    fun s₄ ⟨k₄, E₄, I₄, J₄, p₄⟩ => ?_)
  refine WP.seq (WP.mono (dblStep_ok hL dblJ_apart_TD (by decide) I₄ (by decide) (hL.onCurve_add h4 h4) J₄)
    fun s₅ ⟨k₅, E₅, I₅, J₅, p₅⟩ => ?_)
  -- Back to projective coordinates.
  refine WP.seq (WP.mono (fromJStep_ok I₅ (by decide)) fun s₆ ⟨k₆, E₆, I₆, v₆, p₆⟩ => ?_)
  have z₅ : E₅ 160 = 0 := by
    rw [p₅ _ (by decide), p₄ _ (by decide), p₃ _ (by decide), p₂ _ (by decide), p₁ _ (by decide)]; exact e0
  simp only [Prod.mk.injEq] at v₆
  obtain ⟨vx, vy, vz⟩ := v₆
  rw [z₅, Lean.Grind.AddCommMonoid.add_zero] at vy
  have hw₆ := I₆.ws
  have hn₆ := hw₆.nowrap
  have ltx := I₆.lt 512 (by decide)
  have lty := I₆.lt 544 (by decide)
  have ltz := I₆.lt 576 (by decide)
  have vx' : tmv W 4 base s₆ 512 = E₆ 512 := I₆.val 512 (by decide)
  have vy' : tmv W 4 base s₆ 544 = E₆ 544 := I₆.val 544 (by decide)
  have vz' : tmv W 4 base s₆ 576 = E₆ 576 := I₆.val 576 (by decide)
  have KK : KeepR 4 (fun x => x) base quadWl s s₆ :=
    ((((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans ((k₃.mono (by decide)).trans
      (k₄.mono (by decide)))).trans ((k₅.mono (by decide)).trans (k₆.mono (by decide))))
  have UK : Unch base quadW s.mem s₆.mem := Unch.cover (W := quadWl.map (fun w => (w, 8 * 4)) ++ [(own 4, 64 * 4)])
    KK.mem (by decide)
  have onep₆ : wordsVal s₆.mem base 224 4 = 2 ^ 256 % W.p := by
    rw [UK.wordsVal (by decide) (by decide)]; exact hK.onep
  -- `Y = 1` where `Z = 0`: the mask of `Z ≠ 0`, then the selection.
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (nonzero_ok p224 hw₆.ws hw₆.at3 (a := 576) (by decide) (by decide) (by decide))
    fun s₇ ⟨g₇, k₇, m₇⟩ => ?_)
  rw [List.singleton_append]
  refine wp_step exec_logic ?_
  have hc : (s₇.write .r10 (s₇.gpr .r5 ||| s₇.gpr .r5)).gpr .r10 =
      if decide (wordsVal s₆.mem base 576 4 ≠ 0) then BitVec.allOnes 64 else 0 := by
    simp only [write_gpr, ite_true, BitVec.or_self, g₇, mask64, decide_eq_true_eq]; rfl
  have hw₇ := (k₇.ws hw₆.ws).write .r10 (s₇.gpr .r5 ||| s₇.gpr .r5)
  refine WP.mono (sel_ok (decide (wordsVal s₆.mem base 576 4 ≠ 0)) 4 hw₇ ((k₇.at hw₆.at3).write _) hc
    (o := 544) (a := 224) (b := 544) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Or.inr (by decide)) (Or.inl (Nat.le_refl _))) fun s₈ ⟨e₈, k₈, O₈⟩ => ?_
  simp only [write_mem] at e₈ O₈
  rw [m₇] at e₈ O₈
  have ex : wordsVal s₈.mem base 512 4 = wordsVal s₆.mem base 512 4 := O₈.wordsVal (by decide) (by omega)
  have ez : wordsVal s₈.mem base 576 4 = wordsVal s₆.mem base 576 4 := O₈.wordsVal (by decide) (by omega)
  have hZ : (wordsVal s₆.mem base 576 4 ≠ 0) ↔ E₅ 672 ≠ 0 := by
    rw [ne_eq, ne_eq, ← toM_eq_zero_iff unit ltz]
    show ¬tmv W 4 base s₆ 576 = 0 ↔ _
    rw [vz', vz]
    exact not_congr ⟨fun h => Classical.byContradiction fun hz => cube_ne_zero hL hz h,
      fun h => by rw [h]; grind⟩
  have hrep := InvJ.out hL J₅
  have sub : ∀ r ∈ [Reg.r4, .r5], r ∈ fnClob := by decide
  have rk : Rk fnClob s s₈ := by
    refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
    · have h10 : r ≠ Reg.r10 := fun h => hr (h ▸ by decide)
      rw [k₈.gpr r (fun h => hr (sub r h)), write_gpr]
      simp only [h10, ↓reduceIte]
      rw [k₇.gpr r (fun h => hr (sub r h)), KK.gpr r hr]
    · rw [k₈.rd, write_rd, k₇.rd, KK.rd]
    · rw [k₈.wr, write_wr, k₇.wr, KK.wr]
    · rw [k₈.sp, write_sp, k₇.sp, KK.sp]
  refine ⟨rk, (UK.trans O₈.unch).cover (by decide), ⟨?_, ?_, ?_, ?_⟩⟩
  · show Rep W (tmv W 4 base s₈ 512) (tmv W 4 base s₈ 544) (tmv W 4 base s₈ 576) _
    simp only [tmv]
    rw [ex, ez]
    show Rep W (tmv W 4 base s₆ 512) _ (tmv W 4 base s₆ 576) _
    rw [vx', vz', vx, vz, e₈]
    by_cases h0 : E₅ 672 = 0
    · have hc : decide (wordsVal s₆.mem base 576 4 ≠ 0) = false :=
        decide_eq_false fun h => (hZ.mp h) h0
      have h0' : E₅ (Cfg.dPt p224).z = 0 := h0
      rw [show (if E₅ (Cfg.dPt p224).z = 0 then (1 : Fe W) else E₅ (Cfg.dPt p224).y) = 1 from
        by simp [h0']] at hrep
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      rw [onep₆, toM_one unit]
      exact hrep
    · have hc : decide (wordsVal s₆.mem base 576 4 ≠ 0) = true := decide_eq_true (hZ.mpr h0)
      have h0' : ¬E₅ (Cfg.dPt p224).z = 0 := h0
      rw [show (if E₅ (Cfg.dPt p224).z = 0 then (1 : Fe W) else E₅ (Cfg.dPt p224).y) =
        E₅ (Cfg.dPt p224).y from by simp [h0']] at hrep
      simp only [hc, ↓reduceIte]
      show Rep W _ (tmv W 4 base s₆ 544) _ _
      rw [vy', vy]
      exact hrep
  · show wordsVal s₈.mem base 512 4 < W.p
    rw [ex]; exact ltx
  · show wordsVal s₈.mem base 544 4 < W.p
    rw [e₈]; split
    · exact lty
    · rw [onep₆]; exact Nat.mod_lt _ (by decide)
  · show wordsVal s₈.mem base 576 4 < W.p
    rw [ez]; exact ltz

/-! ## The complete addition -/

/-- What an addition writes. -/
abbrev addW (o : Pt) : List (Nat × Nat) :=
  (rcbW S3 o).map (fun w => (w, 8 * 4)) ++ [(own 4, 64 * 4)]

/-- `o = p + q` by the complete addition, for points in slots of `wS`. -/
theorem addPt_ok (hL : Law W) {base : Addr} {s : State} (hw : WsReg s base) (hK : KC BPs base s)
    {p q o : Pt} (hA : RcbApart S3 p q o) (hsl : ∀ x ∈ rcbW S3 o ++ rcbR S3 p q, wS x)
    {P P' : Point W} (hP : onCurve W P = true) (hP' : onCurve W P' = true)
    (hp : PtOk base s p P) (hq : PtOk base s q P') :
    WP isa (fprog FP (rcb3 S3 p q o)) s fun s' =>
      Rk fnClob s s' ∧ Unch base (addW o) s.mem s'.mem ∧ PtOk base s' o (Spec.Weierstrass.add P P') := by
  have hp0 : 0 < W.p := by decide
  have hI : Inv 4 base W.p wS (rcbR S3 p q) (fun x => toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base x 4)) s := by
    refine ⟨hw, fun x hx => hsl x (List.mem_append_right _ hx), fun x hx => ?_, fun x _ => rfl⟩
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt hK.ap (Nat.mod_lt _ hp0)
    · exact lt_of_eq_of_lt hK.bp (Nat.mod_lt _ hp0)
    exacts [hp.x, hp.y, hp.z, hq.x, hq.y, hq.z]
  refine WP.mono (rcb3_ok (S' := FP) (M := p224.MP') fp_ok rfl wLay unit hA hsl hI (fun x hx => hx))
    fun s₁ ⟨k₁, I₁, t₁⟩ => ?_
  have eb : toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base (p224.sl BPs) 4) = Fin.ofNat W.p W.b := by
    rw [hK.bp, toM_mont unit]
  generalize hE : (fun x => toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base x 4)) = E at I₁ t₁
  have hrep := hL.add3 am3 hP hP' hp.rep hq.rep (X3 := runOps (rcb3 S3 p q o) E o.x)
    (Y3 := runOps (rcb3 S3 p q o) E o.y) (Z3 := runOps (rcb3 S3 p q o) E o.z)
    (by
      subst hE
      show rcbAdd3 (Fin.ofNat W.p W.b) _ _ _ _ _ _ = _
      rw [← eb]
      exact t₁.symm)
  have hm : ∀ x ∈ [o.x, o.y, o.z], x ∈ [o.x, o.y, o.z] ++ rcbR S3 p q :=
    fun x hx => List.mem_append_left _ hx
  refine ⟨⟨k₁.gpr, k₁.rd, k₁.wr, k₁.sp⟩, k₁.mem,
    ⟨?_, I₁.lt _ (hm _ (by simp)), I₁.lt _ (hm _ (by simp)), I₁.lt _ (hm _ (by simp))⟩⟩
  have vx : tmv W 4 base s₁ o.x = _ := I₁.val _ (hm _ (by simp))
  have vy : tmv W 4 base s₁ o.y = _ := I₁.val _ (hm _ (by simp))
  have vz : tmv W 4 base s₁ o.z = _ := I₁.val _ (hm _ (by simp))
  rw [vx, vy, vz]
  exact hrep


/-! ## Copies -/

/-- `o = p`, the three coordinates one after the other, for `o`'s slots in
order and `p`'s apart from them all. -/
theorem copyPt_ok {s : State} {base : Addr} (hw : WsReg s base) {o p : Pt}
    (h8 : ∀ x ∈ [o.x, o.y, o.z, p.x, p.y, p.z], x % 4 = 0 ∧ x + 32 ≤ 8192)
    (hxy : o.x + 32 ≤ o.y) (hyz : o.y + 32 ≤ o.z)
    (hp : ∀ a ∈ [p.x, p.y, p.z], a + 32 ≤ o.x ∨ o.z + 32 ≤ a) :
    WP isa (.block (Cfg.copyPt p224 o p)) s fun s' =>
      wordsVal s'.mem base o.x 4 = wordsVal s.mem base p.x 4 ∧ wordsVal s'.mem base o.y 4 = wordsVal s.mem base p.y 4 ∧
      wordsVal s'.mem base o.z 4 = wordsVal s.mem base p.z 4 ∧ Kp [.r4] s s' ∧
      Unch base [(o.x, 32), (o.y, 32), (o.z, 32)] s.mem s'.mem := by
  have hn := hw.nowrap
  have g := fun x hx => h8 x hx
  have gp := fun x hx => hp x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g gp
  obtain ⟨⟨ox8, ox⟩, ⟨oy8, oy⟩, ⟨oz8, oz⟩, ⟨px8, px⟩, ⟨py8, py⟩, ⟨pz8, pz⟩⟩ := g
  obtain ⟨hpx, hpy, hpz⟩ := gp
  rw [Cfg.copyPt, Point.copyPt, show p224.n = 4 from rfl, List.append_assoc]
  refine WP.block_append (WP.mono (copy_ok 4 hw.ws hw.at3 (o := o.x) (a := p.x) ox8 px8 (by omega) (by omega)
    (by omega)) fun s₁ ⟨e₁, r₁, O₁⟩ => ?_)
  have hw₁ := hw.of_kp r₁
  refine WP.block_append (WP.mono (copy_ok 4 hw₁.ws hw₁.at3 (o := o.y) (a := p.y) oy8 py8 (by omega) (by omega)
    (by omega)) fun s₂ ⟨e₂, r₂, O₂⟩ => ?_)
  have hw₂ := hw₁.of_kp r₂
  refine WP.mono (copy_ok 4 hw₂.ws hw₂.at3 (o := o.z) (a := p.z) oz8 pz8 (by omega) (by omega) (by omega))
    fun s₃ ⟨e₃, r₃, O₃⟩ => ⟨?_, ?_, ?_, (r₁.trans r₂).trans r₃, ?_⟩
  · rw [O₃.wordsVal (by omega) (by omega), O₂.wordsVal (by omega) (by omega), e₁]
  · rw [O₃.wordsVal (by omega) (by omega), e₂, O₁.wordsVal (by omega) (by omega)]
  · rw [e₃, O₂.wordsVal (by omega) (by omega), O₁.wordsVal (by omega) (by omega)]
  · exact ((O₁.unch.trans O₂.unch).trans O₃.unch).mono (by simp)

/-! ## The table -/

/-- Entry `e`'s slots. -/
abbrev ent (e : Nat) : Pt := Cfg.entry p224 e

theorem ent_eq (e : Nat) : ent e = ⟨4864 + 96 * e, 4864 + 96 * e + 32, 4864 + 96 * e + 64⟩ := rfl

/-- `P`'s slots: ECDH's peer point, with `Z = 1`. -/
abbrev gPt : Pt := p224.pt Impl.Ecdh.PPC64LE.PX Impl.Ecdh.PPC64LE.PY ONEP

theorem gPt_eq : gPt = ⟨1280, 1440, 224⟩ := rfl

/-- The table up to entry `m`: `[e]Q` in entry `e`. -/
abbrev TabTo (base : Addr) (s : State) (Q : Point W) (m : Nat) : Prop := ∀ e ≤ m, PtOk base s (ent e) (mul e Q)

theorem TabTo.of_eq {base : Addr} {s s' : State} {Q : Point W} {m : Nat} (h : TabTo base s Q m)
    (he : ∀ d, 4864 ≤ d → d + 32 ≤ 6400 → wordsVal s'.mem base d 4 = wordsVal s.mem base d 4) (hm : m ≤ 15) :
    TabTo base s' Q m :=
  fun e hlt => (h e hlt).of_eq (he (4864 + 96 * e) (by omega) (by omega))
    (he (4864 + 96 * e + 32) (by omega) (by omega)) (he (4864 + 96 * e + 64) (by omega) (by omega))

/-- What the table's additions write: `D`, `T`, the temporaries, the
functions' own working space and the table. -/
abbrev addsW : List (Nat × Nat) := [(608, 384), (3840, 256), (4864, 1536)]

theorem rcbW_S3 (o : Pt) : rcbW S3 o = [800, 832, 864, 896, 928, 960, o.x, o.y, o.z] := rfl

/-- What the table's construction reads and keeps: the constants and `P`. -/
structure BPre (base : Addr) (s : State) (Q : Point W) : Prop where
  ws : WsReg s base
  kc : KC BPs base s
  g : PtOk base s gPt Q
  on : onCurve W Q = true

theorem far_addsW {d : Nat} (h : d + 32 ≤ 608 ∨ (992 ≤ d ∧ d + 32 ≤ 3840)) :
    ∀ w ∈ addsW, d + 8 * 4 ≤ w.1 ∨ w.1 + w.2 ≤ d := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> (simp only; omega)

theorem BPre.of_eq {base : Addr} {s s' : State} {Q : Point W} (h : BPre base s Q) (hw : WsReg s' base)
    (e : ∀ d, d + 32 ≤ 608 ∨ (992 ≤ d ∧ d + 32 ≤ 3840) → wordsVal s'.mem base d 4 = wordsVal s.mem base d 4) :
    BPre base s' Q :=
  ⟨hw, h.kc.of_eq fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> exact e _ (by decide),
    h.g.of_eq (e _ (by decide)) (e _ (by decide)) (e _ (by decide)), h.on⟩

/-- The additions of `[e]Q` for `e = 2 … m + 1`, from `D = Q`: `D = [m + 1]Q`. -/
theorem adds_ok (hL : Law W) {base : Addr} {Q : Point W} :
    ∀ m ≤ 14, ∀ {s : State}, BPre base s Q → TabTo base s Q 1 → PtOk base s (Cfg.dPt p224) Q →
      WP isa (Cfg.adds p224 Impl.Ecdh.PPC64LE.PX Impl.Ecdh.PPC64LE.PY BPs m) s fun s' =>
        Rk fnClob s s' ∧ Unch base addsW s.mem s'.mem ∧ BPre base s' Q ∧ TabTo base s' Q (m + 1) ∧
          PtOk base s' (Cfg.dPt p224) (mul (m + 1) Q)
  | 0, _, s, hp, hT, hD => WP.block_nil ⟨Rk.refl _ _, Unch.refl _ _ _, hp, hT, by rw [mul_one']; exact hD⟩
  | m + 1, hm, s, hp, hT, hD => by
    rw [Cfg.adds]
    refine WP.seq (WP.mono (adds_ok hL m (by omega) hp hT hD) fun s₁ ⟨k₁, U₁, B₁, T₁, D₁⟩ => ?_)
    have hn := B₁.ws.nowrap
    -- `T = D + Q`.
    refine WP.seq (WP.mono (addPt_ok hL B₁.ws B₁.kc (p := Cfg.dPt p224) (q := gPt) (o := Cfg.tPt p224)
      ⟨by decide, by decide⟩ (by decide) (hL.onCurve_mul B₁.on _) B₁.on D₁ B₁.g) fun s₂ ⟨k₂, U₂, p₂⟩ => ?_)
    rw [mul_succ' hL B₁.on] at p₂
    have hw₂ := B₁.ws.of_rk k₂
    -- Entry `m + 2` and `D`.
    have hm2 : m + 2 < 16 := by omega
    refine WP.block_append (WP.mono (copyPt_ok hw₂ (o := ent (m + 2)) (p := Cfg.tPt p224)
      (by rw [ent_eq, tPt_eq]; simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro x (rfl | rfl | rfl | rfl | rfl | rfl) <;> omega)
      (by rw [ent_eq]; try omega) (by rw [ent_eq]; try omega)
      (by rw [ent_eq, tPt_eq]; simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro x (rfl | rfl | rfl) <;> omega))
      fun s₃ ⟨x₃, y₃, z₃, k₃, U₃⟩ => ?_)
    have hw₃ := hw₂.of_kp k₃
    refine WP.mono (copyPt_ok hw₃ (o := Cfg.dPt p224) (p := Cfg.tPt p224) (by decide) (by decide) (by decide)
      (by decide)) fun s₄ ⟨x₄, y₄, z₄, k₄, U₄⟩ => ?_
    have hw₄ := hw₃.of_kp k₄
    rw [ent_eq] at U₃ x₃ y₃ z₃
    rw [dPt_eq] at U₄ x₄ y₄ z₄
    rw [tPt_eq] at x₃ y₃ z₃ x₄ y₄ z₄
    simp only at U₃ U₄ x₃ y₃ z₃ x₄ y₄ z₄
    have U₃₄ : Unch base [(4864 + 96 * (m + 2), 96), (608, 96)] s₂.mem s₄.mem :=
      (U₃.trans U₄).cover fun w hw => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., by simp only; omega, by simp only; omega⟩
        · exact ⟨_, List.mem_cons_self .., by simp only; omega, by simp only; omega⟩
        · exact ⟨_, List.mem_cons_self .., by simp only; omega, by simp only; omega⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by simp only; omega, by simp only; omega⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by simp only; omega, by simp only; omega⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by simp only; omega, by simp only; omega⟩
    have hU : Unch base addsW s.mem s₄.mem := by
      refine ((U₁.trans U₂).trans U₃₄).cover fun w hw => ?_
      rcases List.mem_append.mp hw with hw | hw
      · rcases List.mem_append.mp hw with hw | hw
        · exact ⟨w, hw, Nat.le_refl _, Nat.le_refl _⟩
        · have := (by decide : ∀ w ∈ addW (Cfg.tPt p224), ∃ w' ∈ addsW, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2) w hw
          exact this
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact ⟨(4864, 1536), by simp, by simp only; omega, by simp only; omega⟩
        · exact ⟨(608, 384), by simp, by simp only; omega, by simp only; omega⟩
    -- What each part leaves apart.
    have f₂ : ∀ d, d + 32 ≤ 704 ∨ (992 ≤ d ∧ d + 32 ≤ 3840) ∨ 4096 ≤ d → d + 32 ≤ 8192 →
        wordsVal s₂.mem base d 4 = wordsVal s₁.mem base d 4 := fun d h h' =>
      U₂.wordsVal (fun w hw => by
        have := (by decide : ∀ w ∈ addW (Cfg.tPt p224), 704 ≤ w.1 ∧ w.1 + w.2 ≤ 992 ∨ w = (3840, 256)) w hw
        rcases this with h1 | rfl
        · omega
        · simp only; omega) (by omega)
    have f₄ : ∀ d, (d + 32 ≤ 608 ∨ 704 ≤ d) → (d + 32 ≤ 4864 + 96 * (m + 2) ∨ 4864 + 96 * (m + 2) + 96 ≤ d) →
        d + 32 ≤ 8192 → wordsVal s₄.mem base d 4 = wordsVal s₂.mem base d 4 := fun d h h2 h' =>
      U₃₄.wordsVal (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> (simp only; omega)) (by omega)
    have B₄ : BPre base s₄ Q := B₁.of_eq hw₄ fun d hd => by
      rw [f₄ d (by omega) (by omega) (by omega), f₂ d (by omega) (by omega)]
    refine ⟨(k₁.trans (k₂.mono (by decide))).trans ⟨fun r hr => ?_, ?_, ?_, ?_⟩, hU, B₄, fun e he => ?_, ?_⟩
    · rw [k₄.gpr r (fun h => hr (by simp only [List.mem_singleton] at h; subst h; decide)),
        k₃.gpr r (fun h => hr (by simp only [List.mem_singleton] at h; subst h; decide))]
    · rw [k₄.rd, k₃.rd]
    · rw [k₄.wr, k₃.wr]
    · rw [k₄.sp, k₃.sp]
    · rcases Nat.lt_or_ge e (m + 2) with h | h
      · have pe := T₁ e (by omega)
        rw [ent_eq] at pe ⊢
        refine pe.of_eq ?_ ?_ ?_ <;> simp only
        · rw [f₄ _ (by omega) (by omega) (by omega), f₂ _ (by omega) (by omega)]
        · rw [f₄ _ (by omega) (by omega) (by omega), f₂ _ (by omega) (by omega)]
        · rw [f₄ _ (by omega) (by omega) (by omega), f₂ _ (by omega) (by omega)]
      · obtain rfl : e = m + 2 := by omega
        rw [ent_eq]
        refine p₂.move ?_ ?_ ?_ <;> rw [tPt_eq] <;> simp only
        · rw [U₄.wordsVal (by simp; omega) (by omega), x₃]
        · rw [U₄.wordsVal (by simp; omega) (by omega), y₃]
        · rw [U₄.wordsVal (by simp; omega) (by omega), z₃]
    · rw [show m + 1 + 1 = m + 2 by omega]
      refine p₂.move ?_ ?_ ?_ <;> rw [dPt_eq, tPt_eq] <;> simp only
      · rw [x₄, ← U₃.wordsVal (by simp; omega) (by omega)]
      · rw [y₄, ← U₃.wordsVal (by simp; omega) (by omega)]
      · rw [z₄, ← U₃.wordsVal (by simp; omega) (by omega)]

/-- The table of `[e]Q`, for `e < 16`, and `D = [15]Q`. -/
theorem build_ok (hL : Law W) {base : Addr} {Q : Point W} {s : State} (hp : BPre base s Q) :
    WP isa (Cfg.build p224 Impl.Ecdh.PPC64LE.PX Impl.Ecdh.PPC64LE.PY BPs) s fun s' =>
      Rk fnClob s s' ∧ Unch base addsW s.mem s'.mem ∧ BPre base s' Q ∧ TabTo base s' Q 15 := by
  have hw := hp.ws
  have hn := hw.nowrap
  have hp0 : 0 < W.p := by decide
  rw [Cfg.build, List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (copyPt_ok hw (o := ent 0) (p := p224.pt ZERO ONEP ZERO) (by decide)
    (by decide) (by decide) (by decide)) fun s₁ ⟨x₁, y₁, z₁, k₁, U₁⟩ => ?_))
  have hw₁ := hw.of_kp k₁
  refine WP.block_append (WP.mono (copyPt_ok hw₁ (o := ent 1) (p := gPt) (by decide) (by decide)
    (by decide) (by decide)) fun s₂ ⟨x₂, y₂, z₂, k₂, U₂⟩ => ?_)
  have hw₂ := hw₁.of_kp k₂
  refine WP.mono (copyPt_ok hw₂ (o := Cfg.dPt p224) (p := gPt) (by decide) (by decide)
    (by decide) (by decide)) fun s₃ ⟨x₃, y₃, z₃, k₃, U₃⟩ => ?_
  have hw₃ := hw₂.of_kp k₃
  rw [ent_eq] at x₁ y₁ z₁ U₁ x₂ y₂ z₂ U₂
  rw [dPt_eq] at x₃ y₃ z₃ U₃
  rw [gPt_eq] at x₂ y₂ z₂ x₃ y₃ z₃
  rw [show p224.pt ZERO ONEP ZERO = ⟨160, 224, 160⟩ from rfl] at x₁ y₁ z₁
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd] at x₁ y₁ z₁ U₁ x₂ y₂ z₂ U₂ x₃ y₃ z₃ U₃
  have U₃' : Unch base addsW s.mem s₃.mem := ((U₁.trans U₂).trans U₃).cover (by decide)
  have f : ∀ d, d + 32 ≤ 608 ∨ (992 ≤ d ∧ d + 32 ≤ 3840) → wordsVal s₃.mem base d 4 = wordsVal s.mem base d 4 :=
    fun d h => U₃'.wordsVal (far_addsW h) (by omega)
  have B₃ : BPre base s₃ Q := hp.of_eq hw₃ f
  have zv : wordsVal s.mem base 160 4 = 0 := hp.kc.zero
  have ov : wordsVal s.mem base 224 4 = 2 ^ 256 % W.p := hp.kc.onep
  have g1 : ∀ d, d + 32 ≤ 4864 ∨ 4960 ≤ d → d + 32 ≤ 8192 → wordsVal s₁.mem base d 4 = wordsVal s.mem base d 4 := fun d h h' =>
    U₁.wordsVal (by simp; omega) (by omega)
  have g2 : ∀ d, d + 32 ≤ 4960 ∨ 5056 ≤ d → d + 32 ≤ 8192 → wordsVal s₂.mem base d 4 = wordsVal s₁.mem base d 4 := fun d h h' =>
    U₂.wordsVal (by simp; omega) (by omega)
  have g3 : ∀ d, d + 32 ≤ 608 ∨ 704 ≤ d → d + 32 ≤ 8192 → wordsVal s₃.mem base d 4 = wordsVal s₂.mem base d 4 := fun d h h' =>
    U₃.wordsVal (by simp; omega) (by omega)
  have hT : TabTo base s₃ Q 1 := by
    intro e he
    rcases Nat.lt_or_ge e 1 with h | h
    · obtain rfl : e = 0 := by omega
      rw [mul_zero', ent_eq]
      simp only [Nat.mul_zero, Nat.add_zero]
      have e0x : wordsVal s₃.mem base 4864 4 = 0 := by
        rw [g3 _ (by omega) (by omega), g2 _ (by omega) (by omega), x₁, zv]
      have e0y : wordsVal s₃.mem base 4896 4 = 2 ^ 256 % W.p := by
        rw [g3 _ (by omega) (by omega), g2 _ (by omega) (by omega), y₁, ov]
      have e0z : wordsVal s₃.mem base 4928 4 = 0 := by
        rw [g3 _ (by omega) (by omega), g2 _ (by omega) (by omega), z₁, zv]
      refine ⟨?_, ?_, ?_, ?_⟩
      · show Rep W (toM W.p (2 ^ (64 * 4)) (wordsVal s₃.mem base 4864 4))
          (toM W.p (2 ^ (64 * 4)) (wordsVal s₃.mem base 4896 4)) (toM W.p (2 ^ (64 * 4)) (wordsVal s₃.mem base 4928 4)) _
        rw [e0x, e0y, e0z, toM_zero, toM_one unit]
        exact rep_infinity' hL
      · show wordsVal s₃.mem base 4864 4 < W.p; rw [e0x]; exact hp0
      · show wordsVal s₃.mem base 4896 4 < W.p; rw [e0y]; exact Nat.mod_lt _ hp0
      · show wordsVal s₃.mem base 4928 4 < W.p; rw [e0z]; exact hp0
    · obtain rfl : e = 1 := by omega
      rw [mul_one', ent_eq]
      simp only [Nat.mul_one]
      refine hp.g.move ?_ ?_ ?_ <;> rw [gPt_eq] <;> simp only
      · rw [g3 _ (by omega) (by omega), x₂, g1 _ (by omega) (by omega)]
      · rw [g3 _ (by omega) (by omega), y₂, g1 _ (by omega) (by omega)]
      · rw [g3 _ (by omega) (by omega), z₂, g1 _ (by omega) (by omega)]
  have hD : PtOk base s₃ (Cfg.dPt p224) Q := by
    refine hp.g.move ?_ ?_ ?_ <;> rw [gPt_eq, dPt_eq] <;> simp only
    · rw [x₃, g2 _ (by omega) (by omega), g1 _ (by omega) (by omega)]
    · rw [y₃, g2 _ (by omega) (by omega), g1 _ (by omega) (by omega)]
    · rw [z₃, g2 _ (by omega) (by omega), g1 _ (by omega) (by omega)]
  refine WP.mono (adds_ok hL 14 (Nat.le_refl _) B₃ hT hD) fun s₄ ⟨k₄, U₄, B₄, T₄, _⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, (U₃'.trans U₄).cover (by decide), B₄, T₄⟩
  · have h4 : r ∉ [Reg.r4] := fun h => hr (by simp only [List.mem_singleton] at h; subst h; decide)
    rw [k₄.gpr r hr, k₃.gpr r h4, k₂.gpr r h4, k₁.gpr r h4]
  · rw [k₄.rd, k₃.rd, k₂.rd, k₁.rd]
  · rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr]
  · rw [k₄.sp, k₃.sp, k₂.sp, k₁.sp]

/-! ## The nibble and the entry -/

/-- The nibble `k_j` into `r9`, for `j` in `r31`, from the table of `k`'s
bits. -/
theorem nibble_ok {s : State} {base : Addr} (hw : WsReg s base) {k j : Nat} (hj : j < 64)
    (h31 : s.gpr .r31 = BitVec.ofNat 64 j)
    (ht : ∀ t < 256, s.mem (off base (4096 + t)) = if k.testBit t then 1 else 0) :
    WP isa (.block (Cfg.nibble p224)) s fun s' =>
      s'.gpr .r9 = BitVec.ofNat 64 ((k >>> (4 * j)) % 16) ∧ Kp [.r4, .r5, .r9] s s' ∧ s'.mem = s.mem := by
  have hs := hw.ws
  have h3 := hw.at3
  rw [Cfg.nibble, show bitsAt p224.n 0 = 4096 from rfl]
  have a₄ : s.gpr .r3 + s.gpr .r31 <<< 2 = off base (4 * j) := by
    rw [h3, h31]
    simp only [off]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  refine wp_step (exec_lsl (by decide)) ?_
  refine wp_step exec_add ?_
  refine wp_step (lbz_ok (base := base) (size := 8192) (by repeat (first | exact hs | refine Ws.write ?_ _ _))
    (by simp only [At, write_gpr, ite_true, reduceCtorEq, ite_false]; exact a₄) (by decide) (by omega)) ?_
  refine wp_step exec_add ?_
  refine wp_step (lbz_ok (base := base) (size := 8192) (by repeat (first | exact hs | refine Ws.write ?_ _ _))
    (by simp only [At, write_gpr, ite_true, reduceCtorEq, ite_false]; exact a₄) (by decide) (by omega)) ?_
  refine wp_step exec_add ?_
  refine wp_step exec_add ?_
  refine wp_step (lbz_ok (base := base) (size := 8192) (by repeat (first | exact hs | refine Ws.write ?_ _ _))
    (by simp only [At, write_gpr, ite_true, reduceCtorEq, ite_false]; exact a₄) (by decide) (by omega)) ?_
  refine wp_step exec_add ?_
  refine wp_step exec_add ?_
  refine wp_step (lbz_ok (base := base) (size := 8192) (by repeat (first | exact hs | refine Ws.write ?_ _ _))
    (by simp only [At, write_gpr, ite_true, reduceCtorEq, ite_false]; exact a₄) (by decide) (by omega)) ?_
  refine wp_step exec_add (WP.block_nil ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩)
  · simp only [write_gpr, write_mem, ite_true, reduceCtorEq, ite_false]
    rw [show 4 * j + (4096 + 3) = 4096 + (4 * j + 3) by omega, show 4 * j + (4096 + 2) = 4096 + (4 * j + 2) by omega,
      show 4 * j + (4096 + 1) = 4096 + (4 * j + 1) by omega, show 4 * j + 4096 = 4096 + 4 * j by omega,
      ht _ (by omega), ht _ (by omega), ht _ (by omega), ht _ (by omega), byte_bit, byte_bit, byte_bit, byte_bit,
      nib_eq]
    exact horner_eq _ _ _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, hr.1, hr.2.1, hr.2.2, ite_false]

/-- `D = entry e` if the mask `r10` is all ones (`c`), else `D`. -/
theorem selD_ok {s : State} {base : Addr} (hw : WsReg s base) (c : Bool)
    (hc : s.gpr .r10 = (if c then BitVec.allOnes 64 else 0)) {e : Nat} (he : e < 16) :
    WP isa (.block (selPt 4 (Cfg.dPt p224) (Cfg.dPt p224) (ent e))) s fun s' =>
      (∀ i < 3, wordsVal s'.mem base (608 + 32 * i) 4 =
        if c then wordsVal s.mem base (4864 + 96 * e + 32 * i) 4 else wordsVal s.mem base (608 + 32 * i) 4) ∧
      Kp [.r4, .r5] s s' ∧ Unch base [(608, 96)] s.mem s'.mem := by
  have hs := hw.ws
  have h3 := hw.at3
  have hn := hw.nowrap
  rw [selPt, dPt_eq, ent_eq, List.append_assoc]
  simp only
  refine WP.block_append (WP.mono (sel_ok c 4 hs h3 hc (o := 608) (a := 608) (b := 4864 + 96 * e)
    (by decide) (by decide) (by omega) (by decide) (by decide) (by omega) (Or.inl (Nat.le_refl _))
    (Or.inl (by omega))) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
  refine WP.block_append (WP.mono (sel_ok c 4 (k₁.ws hs) (k₁.at h3) (by rw [k₁.g]; exact hc) (o := 640) (a := 640)
    (b := 4864 + 96 * e + 32) (by decide) (by decide) (by omega) (by decide) (by decide) (by omega)
    (Or.inl (Nat.le_refl _)) (Or.inl (by omega))) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  refine WP.mono (sel_ok c 4 (k₂.ws (k₁.ws hs)) (k₂.at (k₁.at h3)) (by rw [k₂.g, k₁.g]; exact hc) (o := 672) (a := 672)
    (b := 4864 + 96 * e + 64) (by decide) (by decide) (by omega) (by decide) (by decide) (by omega)
    (Or.inl (Nat.le_refl _)) (Or.inl (by omega))) fun s₃ ⟨e₃, k₃, O₃⟩ => ⟨fun i hi => ?_, (k₁.trans k₂).trans k₃,
      ((O₁.unch.trans O₂.unch).trans O₃.unch).cover (by decide)⟩
  have a₁ : ∀ d, d + 32 ≤ 608 ∨ 640 ≤ d → d + 32 ≤ 8192 → wordsVal s₁.mem base d 4 = wordsVal s.mem base d 4 :=
    fun d h h' => O₁.wordsVal (by omega) (by omega)
  have a₂ : ∀ d, d + 32 ≤ 640 ∨ 672 ≤ d → d + 32 ≤ 8192 → wordsVal s₂.mem base d 4 = wordsVal s₁.mem base d 4 :=
    fun d h h' => O₂.wordsVal (by omega) (by omega)
  have a₃ : ∀ d, d + 32 ≤ 672 ∨ 704 ≤ d → d + 32 ≤ 8192 → wordsVal s₃.mem base d 4 = wordsVal s₂.mem base d 4 :=
    fun d h h' => O₃.wordsVal (by omega) (by omega)
  have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases this with rfl | rfl | rfl
  · rw [show 608 + 32 * 0 = 608 from rfl, show 4864 + 96 * e + 32 * 0 = 4864 + 96 * e by omega,
      a₃ _ (by omega) (by omega), a₂ _ (by omega) (by omega), e₁]
  · rw [show 608 + 32 * 1 = 640 from rfl, show 4864 + 96 * e + 32 * 1 = 4864 + 96 * e + 32 by omega,
      a₃ _ (by omega) (by omega), e₂, a₁ _ (by omega) (by omega), a₁ _ (by omega) (by omega)]
  · rw [show 608 + 32 * 2 = 672 from rfl, show 4864 + 96 * e + 32 * 2 = 4864 + 96 * e + 64 by omega, e₃,
      a₂ _ (by omega) (by omega), a₂ _ (by omega) (by omega), a₁ _ (by omega) (by omega), a₁ _ (by omega) (by omega)]

/-- The entries below `e` scanned: `D` holds entry `a` if `a < e`, where `r9 = a`. -/
theorem scans_ok {base : Addr} {a : Nat} (ha : a < 16) : ∀ e ≤ 16, ∀ {s : State}, WsReg s base →
    s.gpr .r9 = BitVec.ofNat 64 a →
    WP isa (.block ((List.range e).flatMap (Cfg.scanEntry p224))) s fun s' =>
      (a < e → ∀ i < 3, wordsVal s'.mem base (608 + 32 * i) 4 = wordsVal s.mem base (4864 + 96 * a + 32 * i) 4) ∧
      Kp [.r4, .r5, .r10] s s' ∧ Unch base [(608, 96)] s.mem s'.mem
  | 0, _, s, _, _ => WP.block_nil ⟨fun h => absurd h (by omega), Kp.refl _ _, Unch.refl _ _ _⟩
  | e + 1, he, s, hw, h9 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (scans_ok ha e (by omega) hw h9) fun s₁ ⟨v₁, k₁, U₁⟩ => ?_)
    have hw₁ := hw.of_kp k₁
    rw [Cfg.scanEntry]
    refine WP.block_append (WP.mono (eqMask_ok ha (e := e) (by omega) (by rw [k₁.g]; exact h9))
      fun s₂ ⟨c₂, k₂, m₂⟩ => ?_)
    have hw₂ := hw₁.of_kp k₂
    refine WP.mono (selD_ok hw₂ _ c₂ (e := e) (by omega)) fun s₃ ⟨v₃, k₃, U₃⟩ => ⟨fun hae i hi => ?_,
      ((k₁.trans (k₂.mono (by decide))).trans (k₃.mono (by decide))), ?_⟩
    · have hn := hw.nowrap
      have ent_u : ∀ d, 4864 ≤ d → d + 32 ≤ 6400 → wordsVal s₂.mem base d 4 = wordsVal s.mem base d 4 := fun d h h' => by
        rw [m₂]; exact U₁.wordsVal (by simp; omega) (by omega)
      rw [v₃ i hi]
      by_cases h : a = e
      · subst h
        simp only [decide_true, ↓reduceIte]
        exact ent_u _ (by omega) (by omega)
      · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
        rw [m₂]; exact v₁ (by omega) i hi
    · rw [m₂] at U₃; exact (U₁.trans U₃).cover (by decide)

/-- The window's entry `[k_j]Q` to `D`. -/
theorem select_ok {s : State} {base : Addr} (hw : WsReg s base) {k j : Nat} (hj : j < 64)
    (h31 : s.gpr .r31 = BitVec.ofNat 64 j)
    (ht : ∀ t < 256, s.mem (off base (4096 + t)) = if k.testBit t then 1 else 0)
    {Q : Point W} (hT : TabTo base s Q 15) :
    WP isa (.block (Cfg.select p224)) s fun s' =>
      PtOk base s' (Cfg.dPt p224) (mul ((k >>> (4 * j)) % 16) Q) ∧ Kp [.r4, .r5, .r9, .r10] s s' ∧
        Unch base [(608, 96)] s.mem s'.mem := by
  rw [Cfg.select]
  refine WP.block_append (WP.mono (nibble_ok hw hj h31 ht) fun s₁ ⟨v₁, k₁, m₁⟩ => ?_)
  have ha : (k >>> (4 * j)) % 16 < 16 := Nat.mod_lt _ (by decide)
  refine WP.mono (scans_ok ha 16 (Nat.le_refl _) (hw.of_kp k₁) v₁) fun s₂ ⟨v₂, k₂, U₂⟩ => ⟨?_,
    (k₁.mono (by decide)).trans (k₂.mono (by decide)), by rw [← m₁]; exact U₂⟩
  have pe := hT ((k >>> (4 * j)) % 16) (by omega)
  rw [ent_eq] at pe
  rw [m₁] at v₂
  refine pe.move ?_ ?_ ?_ <;> rw [dPt_eq] <;> simp only
  · have := v₂ ha 0 (by decide); simpa using this
  · have := v₂ ha 1 (by decide); simpa using this
  · have := v₂ ha 2 (by decide); simpa using this

/-! ## The windows -/

/-- What the windows read and keep, from `s₀`. -/
structure WFix (base : Addr) (s₀ : State) (Q : Point W) (k : Nat) : Prop where
  kc : KC BPs base s₀
  tab : TabTo base s₀ Q 15
  bits : Bits base s₀ k
  q : onCurve W Q = true

/-- What the windows write: `R`, `D`, `T`, the temporaries and the functions'
own working space. -/
abbrev stepW : List (Nat × Nat) := [(512, 480), (3840, 256)]

/-- The loop's invariant at `r31 = j`: `R` represents `[k >>> 4 j]Q`. -/
structure WInv (base : Addr) (s₀ s : State) (Q : Point W) (k j : Nat) : Prop where
  ws : WsReg s base
  ctr : s.gpr .r31 = BitVec.ofNat 64 j
  keep : Rk powClob s₀ s
  unch : Unch base stepW s₀.mem s.mem
  rep : PtOk base s (Cfg.rPt p224) (wpt Q k j)

theorem far_stepW {d : Nat} (h : d + 32 ≤ 512 ∨ (992 ≤ d ∧ d + 32 ≤ 3840) ∨ 4096 ≤ d) :
    ∀ w ∈ stepW, d + 8 * 4 ≤ w.1 ∨ w.1 + w.2 ≤ d := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl <;> (simp only; omega)

/-- A window. -/
theorem step_ok (hL : Law W) {base : Addr} {s₀ : State} {Q : Point W} {k : Nat} (hP : WFix base s₀ Q k)
    {j : Nat} (hj1 : 1 ≤ j) (hj : j ≤ 64) {s : State} (hI : WInv base s₀ s Q k j) :
    WP isa (Cfg.step p224 BPs) s fun s' => WInv base s₀ s' Q k (j - 1) := by
  have hn := hI.ws.nowrap
  have uS : ∀ d, d + 32 ≤ 512 ∨ (992 ≤ d ∧ d + 32 ≤ 3840) ∨ 4096 ≤ d → d + 32 ≤ 8192 →
      wordsVal s.mem base d 4 = wordsVal s₀.mem base d 4 := fun d h h' =>
    hI.unch.wordsVal (far_stepW h) (by omega)
  rw [Cfg.step]
  refine WP.seq (wp_decCounter hj1 hI.ctr (WP.block_nil ?_))
  generalize hs₁ : s.write .r31 (BitVec.ofNat 64 (j - 1)) = s₁
  have k₁ : Kp [.r31] s s₁ := hs₁ ▸ Kp.write _ _ (by decide)
  have c₁ : s₁.gpr .r31 = BitVec.ofNat 64 (j - 1) := by rw [← hs₁, write_gpr]; simp
  have m₁ : s₁.mem = s.mem := by rw [← hs₁]; rfl
  have hw₁ := hI.ws.of_kp k₁
  have hK₁ : KC BPs base s₁ := hP.kc.of_eq fun d hd => by
    rw [m₁]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> exact uS _ (by decide) (by decide)
  have pR₁ : PtOk base s₁ (Cfg.rPt p224) (wpt Q k j) := hI.rep.of_eq (by rw [m₁]) (by rw [m₁]) (by rw [m₁])
  have hX := hL.onCurve_mul hP.q (k >>> (4 * j))
  have h2 := hL.onCurve_add hX hX
  have h4 := hL.onCurve_add h2 h2
  have h8 := hL.onCurve_add h4 h4
  have h16 := hL.onCurve_add h8 h8
  have hE := hL.onCurve_mul hP.q ((k >>> (4 * (j - 1))) % 16)
  -- `R = 16 R`.
  refine WP.seq (WP.mono (quad_ok hL hw₁ hK₁ hX pR₁) fun s₂ ⟨K₂, U₂, pR₂⟩ => ?_)
  have hw₂ := hw₁.of_rk K₂
  have u₂ : ∀ d, d + 32 ≤ 512 ∨ (992 ≤ d ∧ d + 32 ≤ 3840) ∨ 4096 ≤ d → d + 32 ≤ 8192 →
      wordsVal s₂.mem base d 4 = wordsVal s₀.mem base d 4 := fun d h h' => by
    rw [U₂.wordsVal (far_stepW h) (by omega), m₁]; exact uS d h h'
  have hT₂ : TabTo base s₂ Q 15 := hP.tab.of_eq (fun d h1 h2 => u₂ d (by omega) (by omega)) (by decide)
  have hBs : Bits base s k := hP.bits.of_unch hI.unch (by decide)
  have hB₁ : Bits base s₁ k := fun t ht => by rw [m₁]; exact hBs t ht
  have hB₂ : Bits base s₂ k := hB₁.of_unch U₂ (by decide)
  -- The entry.
  refine WP.seq (WP.mono (select_ok hw₂ (j := j - 1) (by omega) (by rw [K₂.gpr _ (by decide)]; exact c₁)
    (fun t ht => hB₂ t ht) hT₂) fun s₃ ⟨pE, k₃, U₃⟩ => ?_)
  have hw₃ := hw₂.of_kp k₃
  have pR₃ : PtOk base s₃ (Cfg.rPt p224) (d16 (wpt Q k j)) :=
    pR₂.of_eq (U₃.wordsVal (by decide) (by decide)) (U₃.wordsVal (by decide) (by decide))
      (U₃.wordsVal (by decide) (by decide))
  have hK₃ : KC BPs base s₃ := hP.kc.of_eq fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      exact (U₃.wordsVal (by decide) (by decide)).trans (u₂ _ (by decide) (by decide))
  -- `T = R + D`.
  refine WP.seq (WP.mono (addPt_ok hL hw₃ hK₃ (p := Cfg.rPt p224) (q := Cfg.dPt p224)
    (o := Cfg.tPt p224) ⟨by decide, by decide⟩ (by decide) h16 hE pR₃ pE) fun s₄ ⟨K₄, U₄, pT⟩ => ?_)
  have hw₄ := hw₃.of_rk K₄
  -- `R = T`.
  refine WP.mono (copyPt_ok hw₄ (o := Cfg.rPt p224) (p := Cfg.tPt p224) (by decide) (by decide)
    (by decide) (by decide)) fun s₅ ⟨x₅, y₅, z₅, k₅, U₅⟩ => ?_
  refine ⟨hw₄.of_kp k₅, ?_, ?_, ?_, ?_⟩
  · rw [k₅.gpr _ (by decide), K₄.gpr _ (by decide), k₃.gpr _ (by decide), K₂.gpr _ (by decide), c₁]
  · exact ((((hI.keep.trans (rk_of_kp k₁)).trans (rk_mono K₂)).trans (rk_of_kp k₃)).trans (rk_mono K₄)).trans
      (rk_of_kp k₅)
  · have U₁ : Unch base [] s.mem s₁.mem := fun x _ => by rw [m₁]
    exact (((((hI.unch.trans U₁).trans U₂).trans U₃).trans U₄).trans U₅).cover (by decide)
  · have e := wstep hL hP.q k (j - 1)
    rw [show j - 1 + 1 = j by omega] at e
    rw [← e]
    exact pT.move x₅ y₅ z₅

/-- What `mul` writes. -/
abbrev mulW : List (Nat × Nat) := [(512, 480), (3840, 256), (4864, 1536)]

/-- What `mul` reads: the constants, `Q` at the peer point's slots, and the
table of `k`'s bits. -/
structure MPre (base : Addr) (s : State) (Q : Point W) (k : Nat) : Prop where
  ws : WsReg s base
  kc : KC BPs base s
  g : PtOk base s gPt Q
  on : onCurve W Q = true
  bits : Bits base s k
  lt : k < 2 ^ 256

/-- `R = [k]Q`. -/
theorem mul_ok (hL : Law W) {base : Addr} {s : State} {Q : Point W} {k : Nat} (hp : MPre base s Q k) :
    WP isa (Cfg.mul p224 Impl.Ecdh.PPC64LE.PX Impl.Ecdh.PPC64LE.PY BPs) s fun s' =>
      Rk powClob s s' ∧ Unch base mulW s.mem s'.mem ∧ PtOk base s' (Cfg.rPt p224) (mul k Q) := by
  have hn := hp.ws.nowrap
  have hp0 : 0 < W.p := by decide
  rw [Window.Cfg.mul]
  refine WP.seq (WP.mono (build_ok hL ⟨hp.ws, hp.kc, hp.g, hp.on⟩) fun s₁ ⟨K₁, U₁, B₁, T₁⟩ => ?_)
  have hw₁ := B₁.ws
  refine WP.seq (WP.block_append (WP.mono (copyPt_ok hw₁ (o := Cfg.rPt p224) (p := p224.pt ZERO ONEP ZERO)
    (by decide) (by decide) (by decide) (by decide)) fun s₂ ⟨x₂, y₂, z₂, r₂, U₂⟩ => ?_))
  have hw₂ := hw₁.of_kp r₂
  refine wp_step (exec_li (imm := 64) (by decide)) (WP.block_nil ?_)
  generalize hs₃ : s₂.write .r31 (BitVec.ofNat 64 64) = s₃
  have ku₃ : Kp [.r31] s₂ s₃ := hs₃ ▸ Kp.write _ _ (by decide)
  have m₃ : s₃.mem = s₂.mem := by rw [← hs₃]; rfl
  have c₃ : s₃.gpr .r31 = BitVec.ofNat 64 64 := by rw [← hs₃, write_gpr]; simp
  have hw₃ : WsReg s₃ base := hw₂.of_kp ku₃
  have U₃ : Unch base [(512, 96)] s₁.mem s₃.mem := by rw [m₃]; exact U₂.cover (by decide)
  have k₃ : ∀ d, d + 32 ≤ 512 ∨ 608 ≤ d → d + 32 ≤ 8192 → wordsVal s₃.mem base d 4 = wordsVal s₁.mem base d 4 :=
    fun d h h' => U₃.wordsVal (by simp; omega) (by omega)
  have hP : WFix base s₃ Q k :=
    ⟨B₁.kc.of_eq fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> exact k₃ _ (by decide) (by decide),
     T₁.of_eq (fun d h1 h2 => k₃ d (by omega) (by omega)) (by decide),
     (hp.bits.of_unch U₁ (by decide)).of_unch U₃ (by decide), hp.on⟩
  have zv : wordsVal s₁.mem base 160 4 = 0 := B₁.kc.zero
  have ov : wordsVal s₁.mem base 224 4 = 2 ^ 256 % W.p := B₁.kc.onep
  rw [rPt_eq, show p224.pt ZERO ONEP ZERO = ⟨160, 224, 160⟩ from rfl] at x₂ y₂ z₂
  have rx : wordsVal s₃.mem base 512 4 = 0 := by rw [m₃]; exact x₂.trans zv
  have ry : wordsVal s₃.mem base 544 4 = 2 ^ 256 % W.p := by rw [m₃]; exact y₂.trans ov
  have rz : wordsVal s₃.mem base 576 4 = 0 := by rw [m₃]; exact z₂.trans zv
  have hI : WInv base s₃ s₃ Q k 64 := by
    refine ⟨hw₃, c₃, Rk.refl _ _, Unch.refl _ _ _, ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [wpt_top _ hp.lt]
      show Rep W (toM W.p (2 ^ (64 * 4)) (wordsVal s₃.mem base 512 4))
        (toM W.p (2 ^ (64 * 4)) (wordsVal s₃.mem base 544 4)) (toM W.p (2 ^ (64 * 4)) (wordsVal s₃.mem base 576 4)) _
      rw [rx, ry, rz, toM_zero, toM_one unit]
      exact rep_infinity' hL
    · show wordsVal _ _ 512 4 < _; rw [rx]; exact hp0
    · show wordsVal _ _ 544 4 < _; rw [ry]; exact Nat.mod_lt _ hp0
    · show wordsVal _ _ 576 4 < _; rw [rz]; exact hp0
  refine countLoop_ok (Inv := fun j s' => WInv base s₃ s' Q k j) (n := 64) (fun j s' hi => hi.ctr)
    (fun j s' h1 h2 hi => step_ok hL hP h1 h2 hi) (fun s' hi => ?_) (by decide) (by decide) hI
  refine ⟨((rk_mono K₁).trans (rk_of_kp ((r₂.mono (rs' := [.r4, .r31]) (by decide)).trans
    (ku₃.mono (by decide))))).trans hi.keep, ((U₁.trans U₃).trans hi.unch).cover (by decide), ?_⟩
  have e : wpt Q k 0 = mul k Q := by simp only [wpt, Nat.mul_zero, Nat.shiftRight_zero]
  rw [← e]
  exact hi.rep

end VG.Proof.Ecdsa.PPC64LE.Window.P224
