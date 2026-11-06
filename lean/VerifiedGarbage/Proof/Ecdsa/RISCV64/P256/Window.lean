module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Window
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.Joint
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.MulVerified
public import VerifiedGarbage.Proof.Weierstrass.Jac
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Weierstrass.PointFacts
import VerifiedGarbage.Proof.P256.Point
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
import VerifiedGarbage.Proof.Ecdh.RISCV64.Masks
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.WindowLit
meta import VerifiedGarbage.Impl.Ecdsa.RISCV64.Window
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.Joint
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.MulVerified
meta import VerifiedGarbage.Proof.Weierstrass.Jac
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Weierstrass.PointFacts
meta import VerifiedGarbage.Proof.P256.Point
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.Masks
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.WindowLit

/-!
# `vg_p256_mul` by windows on RISC-V: the proofs

`R = 16 R` (`quad_ok`): `R`'s representative of `P` into Jacobian
coordinates stands for `P` (`InvJ.of_toJ`), each doubling doubles it
(`InvJ.dbl'`), and back in projective coordinates, with `Y = 1` where `Z`
is zero, it is a representative of `16 P` again (`InvJ.out`). The
arithmetic is `ofN_ok`'s, on the slots of `wS`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.Window

open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.Window
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.P256 (W field_ok unit)
open VG.Proof.Ecdsa.RISCV64.Joint (PtOk mul_one' mul_zero')
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Point Fe mul onCurve)

/-! ## The points -/

section
variable {C : Spec.Weierstrass.Curve}

/-- `2 P`. -/
abbrev d2 (P : Point C) : Point C := Spec.Weierstrass.add P P

/-- `16 P`, by four doublings. -/
abbrev d16 (P : Point C) : Point C := d2 (d2 (d2 (d2 P)))

/-- `R` before window `j - 1`: `[k >>> 4 j]Q`. -/
abbrev wpt (Q : Point C) (k j : Nat) : Point C := mul (k >>> (4 * j)) Q

theorem shr_four (k j : Nat) : k >>> (4 * j) = 16 * (k >>> (4 * (j + 1))) + (k >>> (4 * j)) % 16 := by
  rw [show 4 * (j + 1) = 4 * j + 4 by omega, Nat.shiftRight_add, Nat.shiftRight_eq_div_pow (k >>> (4 * j)) 4]
  omega

/-- A window: `16 R + [k_j]Q`, for `R` before it, is `R` after it. -/
theorem wstep (hL : Law C) {Q : Point C} (hQ : onCurve C Q = true) (k j : Nat) :
    Spec.Weierstrass.add (d16 (wpt Q k (j + 1))) (mul ((k >>> (4 * j)) % 16) Q) = wpt Q k j := by
  have ek := shr_four k j
  simp only [wpt, d16, d2]
  generalize (k >>> (4 * j)) % 16 = a at ek ⊢
  rw [ek]
  generalize k >>> (4 * (j + 1)) = m
  have hX := hL.onCurve_mul hQ m
  have h2 := hL.onCurve_add hX hX
  have h4 := hL.onCurve_add h2 h2
  have h8 := hL.onCurve_add h4 h4
  have h16 := hL.onCurve_add h8 h8
  obtain ⟨M, _, f, hf⟩ := hL.group
  apply hf.inj (hL.onCurve_add h16 (hL.onCurve_mul hQ _)) (hL.onCurve_mul hQ _)
  rw [hf.add h16 (hL.onCurve_mul hQ _), hf.add h8 h8, hf.add h4 h4, hf.add h2 h2, hf.add hX hX,
    hf.mul hQ, hf.mul hQ, hf.mul hQ]
  have hu : ((16 * m + a : Nat) : Int) = m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + a := by
    omega
  rw [hu]
  simp only [Lean.Grind.IntModule.add_zsmul]
  grind

/-- Before the first window: `O`. -/
theorem wpt_top (Q : Point C) {k : Nat} (hk : k < 2 ^ 256) : wpt Q k 64 = .infinity := by
  rw [wpt, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by simpa using hk), Spec.Weierstrass.mul]; rfl

end

/-! ## The slots -/

/-- The slots the windows' arithmetic may use: those at multiples of 32 from
zero's (past `p` and the field's temporary) up to the functions' own working
space. -/
abbrev wS (x : Nat) : Prop := x % 32 = 0 ∧ 160 ≤ x ∧ x + 32 ≤ 3840

theorem wLay : Lay p256.MP' (own 4) wS :=
  ⟨fun x h => h.2.2, fun x y hx hy hne => by
    obtain ⟨h1, -, -⟩ := hx; obtain ⟨h2, -, -⟩ := hy
    show x + 8 * 4 ≤ y ∨ y + 8 * 4 ≤ x; omega,
   fun x h => by obtain ⟨-, h, -⟩ := h; show x + 8 * 4 ≤ 64 ∨ 64 + 8 * 4 ≤ x; omega,
   fun x h => by obtain ⟨-, h, -⟩ := h; show x + 8 * 4 ≤ 128 ∨ 128 + 8 * 4 ≤ x; omega⟩

theorem wShort : Short wS := fun x h => by obtain ⟨-, -, h⟩ := h; omega

/-- The Jacobian programs' slots: `S` with `b` at slot 40. -/
abbrev S3 : RcbSlots := Cfg.rcb3Slots p256

/-- What the field operations of `R = 16 R` write: `R`, `D`, `T`, the
temporaries and the functions' own working space. -/
abbrev quadW : List (Nat × Nat) := [(512, 480), (3840, 256)]

/-- The slots they write. -/
abbrev quadWl : List Nat :=
  [p256.sl T0, p256.sl T1, p256.sl T2, p256.sl T3, p256.sl T4, p256.sl T5, p256.sl RX, p256.sl RY, p256.sl RZ,
    p256.sl DX, p256.sl DY, p256.sl DZ, p256.sl TX, p256.sl TY, p256.sl TZ]

/-- The constants the windows read. -/
structure KC (base : Addr) (s : State) : Prop where
  ap : wordsVal s.mem base (p256.sl AP) 4 = W.a * 2 ^ 256 % W.p
  bp : wordsVal s.mem base (p256.sl 40) 4 = W.b * 2 ^ 256 % W.p
  zero : wordsVal s.mem base (p256.sl ZERO) 4 = 0
  onep : wordsVal s.mem base (p256.sl ONEP) 4 = 2 ^ 256 % W.p

theorem KC.of_eq {base : Addr} {s s' : State} (h : KC base s)
    (e : ∀ d ∈ [p256.sl AP, p256.sl 40, p256.sl ZERO, p256.sl ONEP], wordsVal s'.mem base d 4 = wordsVal s.mem base d 4) :
    KC base s' :=
  ⟨(e _ (by simp)).trans h.ap, (e _ (by simp)).trans h.bp, (e _ (by simp)).trans h.zero, (e _ (by simp)).trans h.onep⟩

/-! ## `R = 16 R` -/

theorem dblJ_apart_DT : RcbApart S3 (p256.pt DX DY DZ) (p256.pt DX DY DZ) (p256.pt TX TY TZ) :=
  ⟨by decide, by decide⟩
theorem dblJ_apart_TD : RcbApart S3 (p256.pt TX TY TZ) (p256.pt TX TY TZ) (p256.pt DX DY DZ) :=
  ⟨by decide, by decide⟩
theorem toJ_apart : RcbApart S3 (p256.pt RX RY RZ) (Cfg.zeroPt p256) (p256.pt DX DY DZ) := ⟨by decide, by decide⟩
theorem fromJ_apart : RcbApart S3 (p256.pt DX DY DZ) (Cfg.zeroPt p256) (p256.pt RX RY RZ) := ⟨by decide, by decide⟩

/-- A Jacobian doubling from `p` to `o` (`D` to `T` or back), on `InvJ`. -/
theorem dblStep_ok (hL : Law W) {base : Addr} {s : State} {p o : Pt} (hA : RcbApart S3 p p o)
    (hsl : ∀ x ∈ rcbW S3 o ++ rcbR S3 p p, wS x) {V : List Nat} {E : Nat → Fe W}
    (hI : Inv 4 base W.p wS V E s) (hV : ∀ x ∈ rcbR S3 p p, x ∈ V) {P : Point W}
    (hP : onCurve W P = true) (hJ : InvJ W (E p.x) (E p.y) (E p.z) P) :
    WP isa (fprog p256Field (dblJ S3 p o)) s fun s' => KeepR 4 base (rcbW S3 o) s s' ∧
      ∃ E', Inv 4 base W.p wS ([o.x, o.y, o.z] ++ V) E' s' ∧ InvJ W (E' o.x) (E' o.y) (E' o.z) (d2 P) ∧
        ∀ x, x ∉ rcbW S3 o → E' x = E x := by
  rw [dblJ_eq]
  refine WP.mono (ofN_ok (F := p256Field) field_ok rfl wLay wShort unit dblJN_ok hA hsl hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, InvJ.dbl' hL Comb.am3 hP hJ (v.trans (dblJN_run _)), kp⟩

/-- `R` into Jacobian coordinates in `D`. -/
theorem toJStep_ok (hL : Law W) {base : Addr} {s : State} {V : List Nat} {E : Nat → Fe W}
    (hI : Inv 4 base W.p wS V E s) (hV : ∀ x ∈ rcbR S3 (p256.pt RX RY RZ) (Cfg.zeroPt p256), x ∈ V) {P : Point W}
    (hR : Rep W (E (p256.sl RX)) (E (p256.sl RY)) (E (p256.sl RZ)) P) (hz : E (p256.sl ZERO) = 0) :
    WP isa (fprog p256Field (toJ S3 (p256.pt RX RY RZ) (Cfg.zeroPt p256) (p256.pt DX DY DZ))) s fun s' =>
      KeepR 4 base (rcbW S3 (p256.pt DX DY DZ)) s s' ∧
      ∃ E', Inv 4 base W.p wS ([p256.sl DX, p256.sl DY, p256.sl DZ] ++ V) E' s' ∧
        InvJ W (E' (p256.sl DX)) (E' (p256.sl DY)) (E' (p256.sl DZ)) P ∧
        ∀ x, x ∉ rcbW S3 (p256.pt DX DY DZ) → E' x = E x := by
  rw [toJ_eq]
  refine WP.mono (ofN_ok (F := p256Field) field_ok rfl wLay wShort unit toJN_ok toJ_apart (by decide) hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, InvJ.of_toJ hL hR hz (v.trans (toJN_run _)), kp⟩

/-- `D` back in projective coordinates in `R`. -/
theorem fromJStep_ok {base : Addr} {s : State} {V : List Nat} {E : Nat → Fe W}
    (hI : Inv 4 base W.p wS V E s) (hV : ∀ x ∈ rcbR S3 (p256.pt DX DY DZ) (Cfg.zeroPt p256), x ∈ V) :
    WP isa (fprog p256Field (fromJ S3 (p256.pt DX DY DZ) (Cfg.zeroPt p256) (p256.pt RX RY RZ))) s fun s' =>
      KeepR 4 base (rcbW S3 (p256.pt RX RY RZ)) s s' ∧
      ∃ E', Inv 4 base W.p wS ([p256.sl RX, p256.sl RY, p256.sl RZ] ++ V) E' s' ∧
        (E' (p256.sl RX), E' (p256.sl RY), E' (p256.sl RZ)) =
          (E (p256.sl DX) * E (p256.sl DZ), E (p256.sl DY) + E (p256.sl ZERO),
            E (p256.sl DZ) * E (p256.sl DZ) * E (p256.sl DZ)) ∧
        ∀ x, x ∉ rcbW S3 (p256.pt RX RY RZ) → E' x = E x := by
  rw [fromJ_eq]
  refine WP.mono (ofN_ok (F := p256Field) field_ok rfl wLay wShort unit fromJN_ok fromJ_apart (by decide) hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, v.trans (fromJN_run _), kp⟩

/-- `R = 16 R`, for `R` representing `P`. -/
theorem quad_ok (hL : Law W) {base : Addr} {s : State} (hw : WsReg s base) (hK : KC base s) {P : Point W}
    (hP : onCurve W P = true) (hR : PtOk base s (p256.pt RX RY RZ) P) :
    WP isa (Cfg.quad p256) s fun s' => Kp s s' ∧ Unch base quadW s.mem s'.mem ∧
      PtOk base s' (p256.pt RX RY RZ) (d16 P) := by
  have hp0 : 0 < W.p := by decide
  have hn := hw.nowrap
  rw [Cfg.quad]
  simp only [progs]
  -- The start: `a`, `b`, zero and `R`.
  have hI : Inv 4 base W.p wS [p256.sl AP, p256.sl 40, p256.sl ZERO, p256.sl RX, p256.sl RY, p256.sl RZ]
      (fun x => toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base x 4)) s := by
    refine ⟨hw, by decide, fun x hx => ?_, fun x _ => rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hK.ap]; exact Nat.mod_lt _ hp0
    · rw [hK.bp]; exact Nat.mod_lt _ hp0
    · rw [hK.zero]; exact hp0
    exacts [hR.x, hR.y, hR.z]
  have e0 : toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base (p256.sl ZERO) 4) = 0 := by
    rw [hK.zero]; exact toM_zero _ _
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
  have z₅ : E₅ (p256.sl ZERO) = 0 := by
    rw [p₅ _ (by decide), p₄ _ (by decide), p₃ _ (by decide), p₂ _ (by decide), p₁ _ (by decide)]; exact e0
  simp only [Prod.mk.injEq] at v₆
  obtain ⟨vx, vy, vz⟩ := v₆
  rw [z₅, Lean.Grind.AddCommMonoid.add_zero] at vy
  have hw₆ := I₆.ws
  have hn₆ := hw₆.nowrap
  have ltx := I₆.lt (p256.sl RX) (by decide)
  have lty := I₆.lt (p256.sl RY) (by decide)
  have ltz := I₆.lt (p256.sl RZ) (by decide)
  have vx' : tmv W 4 base s₆ (p256.sl RX) = E₆ (p256.sl RX) := I₆.val (p256.sl RX) (by decide)
  have vy' : tmv W 4 base s₆ (p256.sl RY) = E₆ (p256.sl RY) := I₆.val (p256.sl RY) (by decide)
  have vz' : tmv W 4 base s₆ (p256.sl RZ) = E₆ (p256.sl RZ) := I₆.val (p256.sl RZ) (by decide)
  -- `Y = 1` where `Z = 0`.
  have KK : KeepR 4 base quadWl s s₆ :=
    ((((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans ((k₃.mono (by decide)).trans
      (k₄.mono (by decide)))).trans ((k₅.mono (by decide)).trans (k₆.mono (by decide))))
  have UK : Unch base (quadWl.map (fun w => (w, 8 * 4)) ++ [(own 4, 64 * 4)]) s.mem s₆.mem := KK.mem
  have onep₆ : wordsVal s₆.mem base (p256.sl ONEP) 4 = 2 ^ 256 % W.p := by
    rw [UK.wordsVal (by decide) (by decide)]; exact hK.onep
  refine WP.block_append (WP.mono (zeroMask_ok hw₆ (n := 4) (a := p256.sl RZ) (by decide) (by decide))
    fun s₇ ⟨r₇, m₇, a7₇⟩ => ?_)
  have hw₇ := hw₆.of_rest r₇
  refine WP.mono (sel_ok (decide (wordsVal s₆.mem base (p256.sl RZ) 4 = 0)) 4 hw₇ a7₇
    (o := p256.sl RY) (a := p256.sl RY) (b := p256.sl ONEP) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (Or.inl (Nat.le_refl _)) (by decide)) fun s₈ ⟨e₈, r₈, O₈⟩ => ?_
  rw [m₇] at e₈ O₈
  have ex : wordsVal s₈.mem base (p256.sl RX) 4 = wordsVal s₆.mem base (p256.sl RX) 4 :=
    O₈.wordsVal (by decide) (by decide)
  have ez : wordsVal s₈.mem base (p256.sl RZ) 4 = wordsVal s₆.mem base (p256.sl RZ) 4 :=
    O₈.wordsVal (by decide) (by decide)
  have hZ : (wordsVal s₆.mem base (p256.sl RZ) 4 = 0) ↔ E₅ (p256.sl DZ) = 0 := by
    rw [← toM_eq_zero_iff unit ltz]
    show tmv W 4 base s₆ (p256.sl RZ) = 0 ↔ _
    rw [vz', vz]
    exact ⟨fun h => by_contra fun hz => cube_ne_zero hL hz h, fun h => by rw [h]; grind⟩
  have hrep := InvJ.out hL J₅
  refine ⟨KK.kp.trans ((Kp.of_rest r₇).trans (Kp.of_rest r₈)), (UK.trans O₈.unch).cover (by decide), ⟨?_, ?_, ?_, ?_⟩⟩
  · show Rep W (tmv W 4 base s₈ (p256.sl RX)) (tmv W 4 base s₈ (p256.sl RY)) (tmv W 4 base s₈ (p256.sl RZ)) _
    simp only [tmv]
    rw [ex, ez]
    show Rep W (tmv W 4 base s₆ (p256.sl RX)) _ (tmv W 4 base s₆ (p256.sl RZ)) _
    rw [vx', vz', vx, vz, e₈]
    by_cases h0 : E₅ (p256.sl DZ) = 0
    · have hc : decide (wordsVal s₆.mem base (p256.sl RZ) 4 = 0) = true := decide_eq_true (hZ.mpr h0)
      have h0' : E₅ (p256.pt DX DY DZ).z = 0 := h0
      rw [show (if E₅ (p256.pt DX DY DZ).z = 0 then (1 : Fe W) else E₅ (p256.pt DX DY DZ).y) = 1 from
        by simp [h0']] at hrep
      simp only [hc, ↓reduceIte]
      rw [onep₆, toM_one unit]
      exact hrep
    · have hc : decide (wordsVal s₆.mem base (p256.sl RZ) 4 = 0) = false :=
        decide_eq_false fun h => h0 (hZ.mp h)
      have h0' : ¬E₅ (p256.pt DX DY DZ).z = 0 := h0
      rw [show (if E₅ (p256.pt DX DY DZ).z = 0 then (1 : Fe W) else E₅ (p256.pt DX DY DZ).y) =
        E₅ (p256.pt DX DY DZ).y from by simp [h0']] at hrep
      simp only [hc, ↓reduceIte, Bool.false_eq_true]
      show Rep W _ (tmv W 4 base s₆ (p256.sl RY)) _ _
      rw [vy', vy]
      exact hrep
  · show wordsVal s₈.mem base (p256.sl RX) 4 < W.p
    rw [ex]; exact ltx
  · show wordsVal s₈.mem base (p256.sl RY) 4 < W.p
    rw [e₈]; split
    · rw [onep₆]; exact Nat.mod_lt _ (by decide)
    · exact lty
  · show wordsVal s₈.mem base (p256.sl RZ) 4 < W.p
    rw [ez]; exact ltz

/-! ## The complete additions and the table -/

/-- What an addition writes. -/
abbrev addW (o : Pt) : List (Nat × Nat) :=
  (rcbW S3 o).map (fun w => (w, 8 * 4)) ++ [(own 4, 64 * 4)]

/-- `o = p + q` by the complete addition, for points in slots of `wS`. -/
theorem addPt_ok (hL : Law W) {base : Addr} {s : State} (hw : WsReg s base) (hK : KC base s)
    {p q o : Pt} (hA : RcbApart S3 p q o) (hsl : ∀ x ∈ rcbW S3 o ++ rcbR S3 p q, wS x)
    {P P' : Point W} (hP : onCurve W P = true) (hP' : onCurve W P' = true)
    (hp : PtOk base s p P) (hq : PtOk base s q P') :
    WP isa (Cfg.addPt p256 p q o) s fun s' =>
      Kp s s' ∧ Unch base (addW o) s.mem s'.mem ∧ PtOk base s' o (Spec.Weierstrass.add P P') := by
  have hp0 : 0 < W.p := by decide
  rw [Cfg.addPt]
  have hI : Inv 4 base W.p wS (rcbR S3 p q) (fun x => toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base x 4)) s := by
    refine ⟨hw, fun x hx => hsl x (List.mem_append_right _ hx), fun x hx => ?_, fun x _ => rfl⟩
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show wordsVal _ _ (p256.sl AP) 4 < _; rw [hK.ap]; exact Nat.mod_lt _ hp0
    · show wordsVal _ _ (p256.sl 40) 4 < _; rw [hK.bp]; exact Nat.mod_lt _ hp0
    exacts [hp.x, hp.y, hp.z, hq.x, hq.y, hq.z]
  refine WP.mono (rcb3_ok (F := p256Field) field_ok rfl wLay wShort unit hA hsl hI (fun x hx => hx))
    fun s₁ ⟨k₁, I₁, t₁⟩ => ?_
  have eb : toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base (p256.sl 40) 4) = Fin.ofNat W.p W.b := by
    rw [hK.bp, toM_mont unit]
  generalize hE : (fun x => toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base x 4)) = E at I₁ t₁
  have hrep := hL.add3 Comb.am3 hP hP' hp.rep hq.rep (X3 := runOps (rcb3 S3 p q o) E o.x)
    (Y3 := runOps (rcb3 S3 p q o) E o.y) (Z3 := runOps (rcb3 S3 p q o) E o.z)
    (by
      subst hE
      show rcbAdd3 (Fin.ofNat W.p W.b) _ _ _ _ _ _ = _
      rw [← eb]
      exact t₁.symm)
  have hm : ∀ x ∈ [o.x, o.y, o.z], x ∈ [o.x, o.y, o.z] ++ rcbR S3 p q :=
    fun x hx => List.mem_append_left _ hx
  refine ⟨k₁.kp, k₁.mem, ⟨?_, I₁.lt _ (hm _ (by simp)), I₁.lt _ (hm _ (by simp)), I₁.lt _ (hm _ (by simp))⟩⟩
  have vx : tmv W 4 base s₁ o.x = _ := I₁.val _ (hm _ (by simp))
  have vy : tmv W 4 base s₁ o.y = _ := I₁.val _ (hm _ (by simp))
  have vz : tmv W 4 base s₁ o.z = _ := I₁.val _ (hm _ (by simp))
  rw [vx, vy, vz]
  exact hrep

/-- Entry `e`'s slots. -/
abbrev ent (e : Nat) : Pt := Cfg.entry p256 e

theorem ent_eq (e : Nat) : ent e = ⟨2048 + 96 * e, 2048 + 96 * e + 32, 2048 + 96 * e + 64⟩ := rfl

theorem rcbW_S3 (o : Pt) : rcbW S3 o = [800, 832, 864, 896, 928, 960, o.x, o.y, o.z] := rfl
/-- `[n + 1]Q = [n]Q + Q`. -/
theorem mul_succ' (hL : Law W) {Q : Point W} (hQ : onCurve W Q = true) (n : Nat) :
    Spec.Weierstrass.add (mul n Q) Q = mul (n + 1) Q := by
  obtain ⟨M, _, f, hf⟩ := hL.group
  apply hf.inj (hL.onCurve_add (hL.onCurve_mul hQ _) hQ) (hL.onCurve_mul hQ _)
  rw [hf.add (hL.onCurve_mul hQ _) hQ, hf.mul hQ, hf.mul hQ, show ((n + 1 : Nat) : Int) = n + 1 by omega]
  simp only [Lean.Grind.IntModule.add_zsmul, Lean.Grind.IntModule.one_zsmul]

/-- The table up to entry `m`: `[e]Q` in entry `e`. -/
abbrev TabTo (base : Addr) (s : State) (Q : Point W) (m : Nat) : Prop := ∀ e ≤ m, PtOk base s (ent e) (mul e Q)

/-- What the table's additions write. -/
abbrev addsW : List (Nat × Nat) := [(800, 192), (2048, 1536), (3840, 256)]

/-- An addition's writes into entry `e`, within `addsW`, and apart from the
other entries and below byte 3840. -/
theorem addW_ent {e : Nat} (_he : e < 16) : ∀ w ∈ addW (ent e),
    ∃ w' ∈ addsW, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := by
  intro w hw
  simp only [addW, rcbW_S3, ent_eq, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false, own, VG.Proof.Weierstrass.RISCV64.rvOwn_le (show 4 ≤ 6 by decide), Impl.Weierstrass.Mont.ownAt,
    Impl.Weierstrass.Mont.ownBytes] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact ⟨(800, 192), List.mem_cons_self .., by simp only; omega, by simp only; omega⟩
    | exact ⟨(2048, 1536), List.mem_cons_of_mem _ List.mem_cons_self, by simp only; omega, by simp only; omega⟩
    | exact ⟨(3840, 256), List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), by simp only; omega,
        by simp only; omega⟩

theorem addW_apart {e d : Nat} (_he : e < 16) (hd : d < 16) (hne : d ≠ e) (c : Nat) (hc : c < 3) :
    ∀ w ∈ addW (ent e), 2048 + 96 * d + 32 * c + 8 * 4 ≤ w.1 ∨ w.1 + w.2 ≤ 2048 + 96 * d + 32 * c := by
  intro w hw
  simp only [addW, rcbW_S3, ent_eq, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false, own, VG.Proof.Weierstrass.RISCV64.rvOwn_le (show 4 ≤ 6 by decide), Impl.Weierstrass.Mont.ownAt,
    Impl.Weierstrass.Mont.ownBytes] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega

/-- The additions of `[e]Q` for `e = 2 … m + 1`. -/
theorem adds_ok (hL : Law W) {base : Addr} {Q : Point W} (hQ : onCurve W Q = true) :
    ∀ m ≤ 14, ∀ {s : State}, WsReg s base → KC base s → TabTo base s Q 1 →
      WP isa (Cfg.adds p256 m) s fun s' => Kp s s' ∧ Unch base addsW s.mem s'.mem ∧ TabTo base s' Q (m + 1)
  | 0, _, s, hw, hK, hT => WP.block_nil ⟨Kp.refl _, Unch.refl _ _ _, hT⟩
  | m + 1, hm, s, hw, hK, hT => by
    rw [Cfg.adds]
    refine WP.seq (WP.mono (adds_ok hL hQ m (by omega) hw hK hT) fun s₁ ⟨k₁, U₁, T₁⟩ => ?_)
    have hw₁ := hw.of_kp k₁
    have hn := hw₁.nowrap
    have hK₁ : KC base s₁ := hK.of_eq fun d hd => U₁.wordsVal (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> decide)
    have hA : RcbApart S3 (ent (m + 1)) (ent 1) (ent (m + 2)) :=
      ⟨(by decide : ∀ m < 14, (rcbW S3 (ent (m + 2))).Nodup) m (by omega),
        (by decide : ∀ m < 14, ∀ x ∈ rcbR S3 (ent (m + 1)) (ent 1), x ∉ rcbW S3 (ent (m + 2))) m (by omega)⟩
    have hsl : ∀ x ∈ rcbW S3 (ent (m + 2)) ++ rcbR S3 (ent (m + 1)) (ent 1), wS x :=
      (by decide : ∀ m < 14, ∀ x ∈ rcbW S3 (ent (m + 2)) ++ rcbR S3 (ent (m + 1)) (ent 1), wS x) m (by omega)
    refine WP.mono (addPt_ok hL hw₁ hK₁ hA hsl (hL.onCurve_mul hQ _) (hL.onCurve_mul hQ 1) (T₁ (m + 1) (by omega))
      (T₁ 1 (by omega))) fun s₂ ⟨k₂, U₂, p₂⟩ => ?_
    rw [mul_one' Q, mul_succ' hL hQ] at p₂
    refine ⟨k₁.trans k₂, (U₁.trans U₂).cover fun w hw => ?_, fun e he => ?_⟩
    · rcases List.mem_append.mp hw with hw | hw
      · exact ⟨w, hw, Nat.le_refl _, Nat.le_refl _⟩
      · exact addW_ent (by omega) w hw
    · rcases Nat.lt_or_ge e (m + 2) with h | h
      · have pe := T₁ e (by omega)
        have ec : ∀ c < 3, wordsVal s₂.mem base (2048 + 96 * e + 32 * c) 4 = wordsVal s₁.mem base (2048 + 96 * e + 32 * c) 4 :=
          fun c hc => U₂.wordsVal (addW_apart (by omega) (by omega) (by omega) c hc) (by omega)
        refine pe.of_eq ?_ ?_ ?_
        · show wordsVal s₂.mem base (2048 + 96 * e) 4 = wordsVal s₁.mem base (2048 + 96 * e) 4
          simpa using ec 0 (by decide)
        · show wordsVal s₂.mem base (2048 + 96 * e + 32) 4 = wordsVal s₁.mem base (2048 + 96 * e + 32) 4
          simpa using ec 1 (by decide)
        · show wordsVal s₂.mem base (2048 + 96 * e + 64) 4 = wordsVal s₁.mem base (2048 + 96 * e + 64) 4
          simpa using ec 2 (by decide)
      · obtain rfl : e = m + 2 := by omega
        exact p₂

/-- `o = p`, the three coordinates one after the other, for `o`'s slots in
order and `p`'s apart from them all. -/
theorem copyPt_ok {s : State} {base : Addr} (hw : WsReg s base) {o p : Pt}
    (h8 : ∀ x ∈ [o.x, o.y, o.z, p.x, p.y, p.z], x % 8 = 0 ∧ x + 32 ≤ 4096)
    (hxy : o.x + 32 ≤ o.y) (hyz : o.y + 32 ≤ o.z)
    (hp : ∀ a ∈ [p.x, p.y, p.z], a + 32 ≤ o.x ∨ o.z + 32 ≤ a) :
    WP isa (.block (Cfg.copyPt p256 o p)) s fun s' =>
      wordsVal s'.mem base o.x 4 = wordsVal s.mem base p.x 4 ∧ wordsVal s'.mem base o.y 4 = wordsVal s.mem base p.y 4 ∧
      wordsVal s'.mem base o.z 4 = wordsVal s.mem base p.z 4 ∧ Rest [.t0] s s' ∧
      Unch base [(o.x, 32), (o.y, 32), (o.z, 32)] s.mem s'.mem := by
  have hn := hw.nowrap
  have g := fun x hx => h8 x hx
  have gp := fun x hx => hp x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g gp
  obtain ⟨⟨ox8, ox⟩, ⟨oy8, oy⟩, ⟨oz8, oz⟩, ⟨px8, px⟩, ⟨py8, py⟩, ⟨pz8, pz⟩⟩ := g
  obtain ⟨hpx, hpy, hpz⟩ := gp
  rw [Cfg.copyPt, show p256.n = 4 from rfl, List.append_assoc]
  refine WP.block_append (WP.mono (copy_ok 4 hw (o := o.x) (a := p.x) ox8 px8 (by omega) (by omega) (by omega))
    fun s₁ ⟨e₁, r₁, O₁⟩ => ?_)
  have hw₁ := hw.of_rest r₁
  refine WP.block_append (WP.mono (copy_ok 4 hw₁ (o := o.y) (a := p.y) oy8 py8 (by omega) (by omega) (by omega))
    fun s₂ ⟨e₂, r₂, O₂⟩ => ?_)
  have hw₂ := hw₁.of_rest r₂
  refine WP.mono (copy_ok 4 hw₂ (o := o.z) (a := p.z) oz8 pz8 (by omega) (by omega) (by omega))
    fun s₃ ⟨e₃, r₃, O₃⟩ => ⟨?_, ?_, ?_, (r₁.trans r₂).trans r₃ |>.mono (by simp), ?_⟩
  · rw [O₃.wordsVal (by omega) (by omega), O₂.wordsVal (by omega) (by omega), e₁]
  · rw [O₃.wordsVal (by omega) (by omega), e₂, O₁.wordsVal (by omega) (by omega)]
  · rw [e₃, O₂.wordsVal (by omega) (by omega), O₁.wordsVal (by omega) (by omega)]
  · exact ((O₁.unch.trans O₂.unch).trans O₃.unch).mono (by simp)

/-- `Q`, the affine point of `R`'s first two slots. -/
abbrev qOf (base : Addr) (s : State) : Point W := .affine (tmv W 4 base s (p256.sl RX)) (tmv W 4 base s (p256.sl RY))

/-- What the table's construction writes. -/
abbrev buildW : List (Nat × Nat) := [(1344, 32), (800, 192), (2048, 1536), (3840, 256)]

/-- What `vg_p256_mul`'s body reads at the start. -/
structure WPre (base : Addr) (s : State) : Prop where
  ws : WsReg s base
  ap : wordsVal s.mem base (p256.sl AP) 4 = W.a * 2 ^ 256 % W.p
  zero : wordsVal s.mem base (p256.sl ZERO) 4 = 0
  onep : wordsVal s.mem base (p256.sl ONEP) 4 = 2 ^ 256 % W.p
  x : wordsVal s.mem base (p256.sl RX) 4 < W.p
  y : wordsVal s.mem base (p256.sl RY) 4 < W.p
  on : onCurve W (qOf base s) = true

/-- `b R mod p` to slot 40, and the table of `[e]Q`. -/
theorem build_ok (hL : Law W) {base : Addr} {s : State} (hp : WPre base s) :
    WP isa (Cfg.build p256) s fun s' => Kp s s' ∧ Unch base buildW s.mem s'.mem ∧ KC base s' ∧
      TabTo base s' (qOf base s) 15 := by
  have hw := hp.ws
  have hn := hw.nowrap
  have hp0 : 0 < W.p := by decide
  rw [Cfg.build, List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (setConst_ok 4 hw (o := p256.sl 40)
    (x := VG.Impl.Ecdh.RISCV64.Cfg.mont p256 p256.C.b) (by decide) (by decide)) fun s₁ ⟨r₁, O₁, e₁⟩ => ?_))
  have hw₁ := hw.of_rest r₁
  have O₁' : Outside base 1344 32 s.mem s₁.mem := O₁
  have e₁' : wordsVal s₁.mem base 1344 4 = W.b * 2 ^ 256 % W.p := by
    refine e₁.trans (Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hp0) (by decide)))
  have k₁ : ∀ d, d + 32 ≤ 1344 ∨ 1376 ≤ d → d + 32 ≤ 4096 → wordsVal s₁.mem base d 4 = wordsVal s.mem base d 4 :=
    fun d h h' => O₁'.wordsVal (by omega) (by omega)
  refine WP.block_append (WP.mono (copyPt_ok hw₁ (o := ent 0) (p := p256.pt ZERO ONEP ZERO) (by decide) (by decide)
    (by decide) (by decide)) fun s₂ ⟨x₂, y₂, z₂, r₂, U₂⟩ => ?_)
  have hw₂ := hw₁.of_rest r₂
  refine WP.mono (copyPt_ok hw₂ (o := ent 1) (p := p256.pt RX RY ONEP) (by decide) (by decide)
    (by decide) (by decide)) fun s₃ ⟨x₃, y₃, z₃, r₃, U₃⟩ => ?_
  have hw₃ := hw₂.of_rest r₃
  have U₂' : Unch base [(2048, 32), (2080, 32), (2112, 32)] s₁.mem s₂.mem := U₂
  have U₃' : Unch base [(2144, 32), (2176, 32), (2208, 32)] s₂.mem s₃.mem := U₃
  have x₂' : wordsVal s₂.mem base 2048 4 = wordsVal s₁.mem base 160 4 := x₂
  have y₂' : wordsVal s₂.mem base 2080 4 = wordsVal s₁.mem base 224 4 := y₂
  have z₂' : wordsVal s₂.mem base 2112 4 = wordsVal s₁.mem base 160 4 := z₂
  have x₃' : wordsVal s₃.mem base 2144 4 = wordsVal s₂.mem base 512 4 := x₃
  have y₃' : wordsVal s₃.mem base 2176 4 = wordsVal s₂.mem base 544 4 := y₃
  have z₃' : wordsVal s₃.mem base 2208 4 = wordsVal s₂.mem base 224 4 := z₃
  have k₃ : ∀ d, d + 32 ≤ 1344 ∨ 1376 ≤ d → d + 32 ≤ 2048 → wordsVal s₃.mem base d 4 = wordsVal s.mem base d 4 :=
    fun d h h' => by
      rw [U₃'.wordsVal (by simp; omega) (by omega), U₂'.wordsVal (by simp; omega) (by omega), k₁ d h (by omega)]
  have k₂ : ∀ d, d + 32 ≤ 1344 ∨ 1376 ≤ d → d + 32 ≤ 2048 → wordsVal s₂.mem base d 4 = wordsVal s.mem base d 4 :=
    fun d h h' => by rw [U₂'.wordsVal (by simp; omega) (by omega), k₁ d h (by omega)]
  have hK₃ : KC base s₃ :=
    ⟨(k₃ 256 (by decide) (by decide)).trans hp.ap, by
      show wordsVal s₃.mem base 1344 4 = _
      rw [U₃'.wordsVal (by simp) (by omega), U₂'.wordsVal (by simp) (by omega)]; exact e₁',
      (k₃ 160 (by decide) (by decide)).trans hp.zero, (k₃ 224 (by decide) (by decide)).trans hp.onep⟩
  have h1 : tmv W 4 base s (p256.sl ONEP) = 1 := by
    simp only [tmv]; rw [hp.onep]; exact toM_one unit
  have h0 : tmv W 4 base s (p256.sl ZERO) = 0 := by
    simp only [tmv]; rw [hp.zero]; exact toM_zero _ _
  have zv : wordsVal s.mem base 160 4 = 0 := hp.zero
  have ov : wordsVal s.mem base 224 4 = 2 ^ 256 % W.p := hp.onep
  have e0x : wordsVal s₃.mem base 2048 4 = wordsVal s.mem base 160 4 := by
    rw [U₃'.wordsVal (by simp) (by omega), x₂', k₁ 160 (by decide) (by decide)]
  have e0y : wordsVal s₃.mem base 2080 4 = wordsVal s.mem base 224 4 := by
    rw [U₃'.wordsVal (by simp) (by omega), y₂', k₁ 224 (by decide) (by decide)]
  have e0z : wordsVal s₃.mem base 2112 4 = wordsVal s.mem base 160 4 := by
    rw [U₃'.wordsVal (by simp) (by omega), z₂', k₁ 160 (by decide) (by decide)]
  have e1x : wordsVal s₃.mem base 2144 4 = wordsVal s.mem base 512 4 := by rw [x₃', k₂ 512 (by decide) (by decide)]
  have e1y : wordsVal s₃.mem base 2176 4 = wordsVal s.mem base 544 4 := by rw [y₃', k₂ 544 (by decide) (by decide)]
  have e1z : wordsVal s₃.mem base 2208 4 = wordsVal s.mem base 224 4 := by rw [z₃', k₂ 224 (by decide) (by decide)]
  have hT : TabTo base s₃ (qOf base s) 1 := by
    intro e he
    rcases Nat.lt_or_ge e 1 with h | h
    · obtain rfl : e = 0 := by omega
      rw [mul_zero']
      refine ⟨?_, ?_, ?_, ?_⟩
      · show Rep W (toM W.p (2 ^ (64 * 4)) (wordsVal s₃.mem base 2048 4)) (toM W.p (2 ^ (64 * 4)) (wordsVal s₃.mem base 2080 4))
          (toM W.p (2 ^ (64 * 4)) (wordsVal s₃.mem base 2112 4)) _
        rw [e0x, e0y, e0z, zv, ov, toM_zero, toM_one unit]
        exact ⟨rfl, hL.one_ne_zero, rfl⟩
      · show wordsVal s₃.mem base 2048 4 < W.p; rw [e0x, zv]; exact hp0
      · show wordsVal s₃.mem base 2080 4 < W.p; rw [e0y, ov]; exact Nat.mod_lt _ hp0
      · show wordsVal s₃.mem base 2112 4 < W.p; rw [e0z, zv]; exact hp0
    · obtain rfl : e = 1 := by omega
      rw [mul_one']
      refine ⟨?_, ?_, ?_, ?_⟩
      · show Rep W (toM W.p (2 ^ (64 * 4)) (wordsVal s₃.mem base 2144 4)) (toM W.p (2 ^ (64 * 4)) (wordsVal s₃.mem base 2176 4))
          (toM W.p (2 ^ (64 * 4)) (wordsVal s₃.mem base 2208 4)) _
        rw [e1x, e1y, e1z, ov, toM_one unit]
        exact ⟨hL.one_ne_zero, (Lean.Grind.Semiring.mul_one _).symm, (Lean.Grind.Semiring.mul_one _).symm⟩
      · show wordsVal s₃.mem base 2144 4 < W.p; rw [e1x]; exact hp.x
      · show wordsVal s₃.mem base 2176 4 < W.p; rw [e1y]; exact hp.y
      · show wordsVal s₃.mem base 2208 4 < W.p; rw [e1z, ov]; exact Nat.mod_lt _ hp0
  refine WP.mono (adds_ok hL hp.on 14 (Nat.le_refl _) hw₃ hK₃ hT) fun s₄ ⟨k₄, U₄, T₄⟩ => ?_
  refine ⟨((Kp.of_rest r₁).trans (Kp.of_rest r₂)).trans ((Kp.of_rest r₃).trans k₄), ?_, ?_, T₄⟩
  · exact (((O₁'.unch.trans U₂').trans U₃').trans U₄).cover (by decide)
  · exact hK₃.of_eq fun d hd => U₄.wordsVal (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> decide)

/-! ## The nibble and the entry -/

theorem four_bits (x : BitVec 64) (u : Nat) {j : Nat}
    (h : ∀ i < 4, x.getLsbD (4 * j % 64 + i) = u.testBit (4 * j + i)) :
    (x >>> (4 * j % 64)) &&& BitVec.ofInt 64 15 = BitVec.ofNat 64 ((u >>> (4 * j)) % 16) := by
  rw [show (u >>> (4 * j)) % 16 = (u >>> (4 * j)) % 2 ^ 4 from rfl]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, show (BitVec.ofInt 64 15) = BitVec.ofNat 64 (2 ^ 4 - 1) from rfl,
    BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight]
  by_cases h4 : i < 4
  · simp only [h4, decide_true, Bool.and_true, Bool.true_and, hi]
    exact h i h4
  · simp [h4]

/-- The nibble `k_j` into `t2`, for `j` in `s1`. -/
theorem nibble_ok {s : State} {base : Addr} (hw : WsReg s base) {j : Nat} (hj : j < 64)
    (h1 : s.gpr .s1 = BitVec.ofNat 64 j) :
    WP isa (.block (Cfg.nibble p256)) s fun s' =>
      s'.gpr .t2 = BitVec.ofNat 64 ((wordsVal s.mem base (p256.sl K) 4 >>> (4 * j)) % 16) ∧
      Rest [.t0, .t1, .t2] s s' ∧ s'.mem = s.mem := by
  have hn := hw.nowrap
  have hal := hw.al
  have hq : j / 16 ≤ 3 := by omega
  rw [Cfg.nibble]
  refine wp_srl (by decide) fun s₁ u₁ => wp_sll (by decide) fun s₂ u₂ => wp_add fun s₃ u₃ => ?_
  have e₃' : s₃.gpr .t0 = base + BitVec.ofNat 64 (8 * (j / 16)) := by
    rw [u₃.gpr, u₂.gpr, u₂.other .s0 (by decide), u₁.gpr, u₁.other .s0 (by decide), hw.s0, h1]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.reducePow]
    rw [Nat.mod_eq_of_lt (by omega : j < 18446744073709551616),
      Nat.mod_eq_of_lt (by omega : j / 16 * 8 < 18446744073709551616),
      Nat.mod_eq_of_lt (by omega : 8 * (j / 16) < 18446744073709551616)]
    omega
  have e₃ : ∀ d, s₃.gpr .t0 + BitVec.ofNat 64 d = off base (d + 8 * (j / 16)) := by
    intro d
    rw [e₃', BitVec.add_assoc, BitVec.ofNat_add_ofNat, off, Nat.add_comm]
  have r₃ : Rest [.t0] s s₃ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (u₃.rest (by decide)))
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have hK : p256.sl K = 1056 := rfl
  refine wp_ld (by decide) (e₃ (p256.sl K))
    (by simp only [off]; rw [BitVec.toNat_add, BitVec.toNat_ofNat, hK]; omega)
    ⟨_, List.mem_append_right _ (r₃.wr ▸ hw.wr), Offset.contains_base base (by rw [hK]; omega) (by omega)⟩
    fun s₄ u₄ => ?_
  refine wp_sll (by decide) fun s₅ u₅ => wp_srlReg fun s₆ u₆ => wp_andi (by decide) fun s₇ u₇ => WP.block_nil ⟨?_, ?_, ?_⟩
  · have t1₅ : (s₅.gpr .t1).toNat % 64 = 4 * j % 64 := by
      rw [u₅.gpr, u₄.other .s1 (by decide), r₃.gpr .s1 (by decide), h1, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
      simp only [Nat.shiftLeft_eq, Nat.reducePow]
      omega
    have hu := four_bits (s₄.gpr .t2) (wordsVal s.mem base (p256.sl K) 4) (j := j) fun i hi => by
      rw [u₄.gpr, m₃, BitVec.getLsbD, show 4 * j % 64 + i = (4 * j + i) % 64 by omega,
        ← testBit_wordsVal s.mem base 4 (p256.sl K) (4 * j + i) (by omega),
        show (4 * j + i) / 64 = j / 16 by omega, Nat.add_comm]
    rw [u₇.gpr, u₆.gpr, t1₅, u₅.other .t2 (by decide), hu]
  · exact (r₃.mono (by decide)).trans ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans
      ((u₆.rest (by decide)).trans (u₇.rest (by decide)))))
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃]

open VG.Proof.Ecdsa.RISCV64.Joint (scansJ_ok masks4_ok selRegs wordsVal_of_words) in
open VG.Impl.Ecdsa.RISCV64.Comb (maskReg treeRegs) in
/-- The window's entry `[k_j]Q` to `E`. -/
theorem select_ok {s : State} {base : Addr} (hw : WsReg s base) {j : Nat} (hj : j < 64)
    (h1 : s.gpr .s1 = BitVec.ofNat 64 j) {Q : Point W} (hT : TabTo base s Q 15) :
    WP isa (.block (Cfg.select p256)) s fun s' =>
      PtOk base s' (p256.pt EX EY EZ) (mul ((wordsVal s.mem base (p256.sl K) 4 >>> (4 * j)) % 16) Q) ∧
      Outside base 1920 96 s.mem s'.mem ∧ Rest selRegs s s' := by
  have hn := hw.nowrap
  rw [Cfg.select]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (nibble_ok hw hj h1) fun s₁ ⟨v₁, r₁, m₁⟩ => ?_)
  generalize ha : (wordsVal s.mem base (p256.sl K) 4 >>> (4 * j)) % 16 = a at v₁
  have ha16 : a < 16 := ha ▸ Nat.mod_lt _ (by decide)
  have hw₁ := hw.of_rest r₁
  refine WP.block_append (WP.mono masks4_ok fun s₂ ⟨v₂, r₂, m₂⟩ => ?_)
  have hw₂ := hw₁.of_rest r₂
  rw [List.cons_append, List.cons_append, List.nil_append]
  refine wp_addi (by decide) fun s₃ u₃ => wp_addi (by decide) fun s₄ u₄ => ?_
  have r₄ : Rest [.a0] s₂ s₄ := (u₃.rest (by decide)).trans (u₄.rest (by decide))
  have hw₄ := hw₂.of_rest r₄
  have h0 : s₄.gpr .a0 = base + BitVec.ofNat 64 2048 := by
    rw [u₄.gpr, u₃.gpr, r₂.gpr _ (by decide), r₁.gpr _ (by decide), hw.s0, BitVec.add_assoc]; rfl
  have hm : ∀ c < 4, s₄.gpr (maskReg c) = maskOf (a.testBit c) := fun c hc => by
    rw [r₄.gpr _ (by
      have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> decide), v₂ c hc, v₁, BitVec.getLsbD_ofNat]
    simp [show c < 64 by omega]
  have hs : (List.range (3 * p256.n)).flatMap (Cfg.scanWord p256) =
      (List.range 12).flatMap (VG.Impl.Ecdsa.RISCV64.Verify.Cfg.scanWord p256) := rfl
  rw [hs]
  refine WP.mono (WP.rdwr (scansJ_ok p256 (by decide) (by decide) (by decide) (by decide) (by decide) 12
    (Nat.le_refl _) hw₄ h0 hm)) fun s₅ ⟨⟨v₅, O₅, k₅⟩, rd₅, wr₅, sp₅⟩ => ?_
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, m₂, m₁]
  rw [m₄] at v₅ O₅
  rw [Nat.mod_eq_of_lt ha16] at v₅
  have v₅' : ∀ q < 12, word s₅.mem base (1920 + 8 * q) = word s.mem base (2048 + 8 * q + 96 * a) := v₅
  have O₅' : Outside base 1920 (8 * 12) s.mem s₅.mem := O₅
  have he : PtOk base s (ent a) (mul a Q) := hT a (by omega)
  have wv : ∀ c < 3, wordsVal s₅.mem base (1920 + 32 * c) 4 = wordsVal s.mem base (2048 + 96 * a + 32 * c) 4 :=
    fun c hc => wordsVal_of_words 4 fun q hq => by
      rw [show 1920 + 32 * c + 8 * q = 1920 + 8 * (4 * c + q) by omega, v₅' _ (by omega)]
      congr 1; omega
  refine ⟨he.move (wv 0 (by decide)) (wv 1 (by decide)) (wv 2 (by decide)), O₅'.mono (Nat.le_refl _) (by omega), ?_⟩
  exact ((r₁.mono (by decide)).trans ((r₂.mono (by decide)).trans ((r₄.mono (by decide)).trans
    ⟨fun r hr => k₅.1 r (fun h => hr ((by decide : ∀ r ∈ treeRegs, r ∈ selRegs) r h)),
      rd₅, wr₅, sp₅⟩)))

/-! ## The windows -/

/-- What the windows read and keep, from `s₀`. -/
structure WFix (base : Addr) (s₀ : State) (Q : Point W) (k : Nat) : Prop where
  kc : KC base s₀
  tab : TabTo base s₀ Q 15
  kk : wordsVal s₀.mem base (p256.sl K) 4 = k
  q : onCurve W Q = true

/-- What the windows write. -/
abbrev stepW : List (Nat × Nat) := [(512, 480), (1920, 96), (3840, 256)]

/-- The loop's invariant at `s1 = j`: `R` represents `[k >>> 4 j]Q`. -/
structure WInv (base : Addr) (s₀ s : State) (Q : Point W) (k j : Nat) : Prop where
  ws : WsReg s base
  ctr : s.gpr .s1 = BitVec.ofNat 64 j
  keep : Kc s₀ s
  unch : Unch base stepW s₀.mem s.mem
  rep : PtOk base s (p256.pt RX RY RZ) (wpt Q k j)

theorem TabTo.of_eq {base : Addr} {s s' : State} {Q : Point W} {m : Nat} (h : TabTo base s Q m)
    (he : ∀ d, 2048 ≤ d → d + 32 ≤ 3584 → wordsVal s'.mem base d 4 = wordsVal s.mem base d 4) (hm : m ≤ 15) :
    TabTo base s' Q m :=
  fun e hlt => (h e hlt).of_eq (he (2048 + 96 * e) (by omega) (by omega))
    (he (2048 + 96 * e + 32) (by omega) (by omega)) (he (2048 + 96 * e + 64) (by omega) (by omega))

/-- A window. -/
theorem step_ok (hL : Law W) {base : Addr} {s₀ : State} {Q : Point W} {k : Nat} (hP : WFix base s₀ Q k)
    {j : Nat} (hj1 : 1 ≤ j) (hj : j ≤ 64) {s : State} (hI : WInv base s₀ s Q k j) :
    WP isa (Cfg.step p256) s fun s' => WInv base s₀ s' Q k (j - 1) := by
  have hn := hI.ws.nowrap
  have uS : ∀ d, (d + 32 ≤ 512 ∨ 992 ≤ d) → (d + 32 ≤ 1920 ∨ 2016 ≤ d) → d + 32 ≤ 3840 →
      wordsVal s.mem base d 4 = wordsVal s₀.mem base d 4 := fun d h1 h2 h3 =>
    hI.unch.wordsVal (by simp; omega) (by omega)
  have hT : TabTo base s Q 15 := hP.tab.of_eq (fun d h1 h2 => uS d (by omega) (by omega) (by omega)) (by decide)
  rw [Cfg.step]
  refine WP.seq (wp_decCounter hj1 hI.ctr fun s₁ u₁ => ?_)
  have hw₁ := hI.ws.of_kc (Kc.of_rest (u₁.rest (ws := [.s1]) (by decide)))
  refine WP.mono (select_ok hw₁ (j := j - 1) (by omega) u₁.gpr
    (hT.of_eq (fun d _ _ => by rw [u₁.mem]) (by decide))) fun s₂ ⟨pE, O₂, r₂⟩ => ?_
  rw [u₁.mem, uS _ (by decide) (by decide) (by decide), hP.kk] at pE
  rw [u₁.mem] at O₂
  have hw₂ := hw₁.of_rest r₂
  have e₂ : ∀ d, (d + 32 ≤ 512 ∨ 992 ≤ d) → (d + 32 ≤ 1920 ∨ 2016 ≤ d) → d + 32 ≤ 3840 →
      wordsVal s₂.mem base d 4 = wordsVal s₀.mem base d 4 := fun d h1 h2 h3 => by
    rw [O₂.wordsVal (by omega) (by omega), uS d h1 h2 h3]
  have pR₂ : PtOk base s₂ (p256.pt RX RY RZ) (wpt Q k j) :=
    hI.rep.of_eq (O₂.wordsVal (by decide) (by decide)) (O₂.wordsVal (by decide) (by decide))
      (O₂.wordsVal (by decide) (by decide))
  have hK₂ : KC base s₂ := hP.kc.of_eq fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> exact e₂ _ (by decide) (by decide) (by decide)
  have hX := hL.onCurve_mul hP.q (k >>> (4 * j))
  have h2 := hL.onCurve_add hX hX
  have h4 := hL.onCurve_add h2 h2
  have h8 := hL.onCurve_add h4 h4
  have h16 := hL.onCurve_add h8 h8
  have hE := hL.onCurve_mul hP.q ((k >>> (4 * (j - 1))) % 16)
  -- `R = 16 R`.
  refine WP.seq (WP.mono (quad_ok hL hw₂ hK₂ hX pR₂) fun s₃ ⟨K₃, U₃, pR₃⟩ => ?_)
  have hw₃ := hw₂.of_kp K₃
  have k₃ : ∀ d, (d + 32 ≤ 512 ∨ 992 ≤ d) → d + 32 ≤ 3840 → wordsVal s₃.mem base d 4 = wordsVal s₂.mem base d 4 :=
    fun d h1 h2 => U₃.wordsVal (by simp; omega) (by omega)
  have pE₃ := pE.of_eq (k₃ _ (by decide) (by decide)) (k₃ _ (by decide) (by decide)) (k₃ _ (by decide) (by decide))
  have hK₃ : KC base s₃ := hK₂.of_eq fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> exact k₃ _ (by decide) (by decide)
  -- `T = R + E`.
  refine WP.seq (WP.mono (addPt_ok hL hw₃ hK₃ (p := p256.pt RX RY RZ) (q := p256.pt EX EY EZ)
    (o := p256.pt TX TY TZ) ⟨by decide, by decide⟩ (by decide) h16 hE pR₃ pE₃) fun s₄ ⟨K₄, U₄, pT⟩ => ?_)
  have hw₄ := hw₃.of_kp K₄
  -- `R = T`.
  refine WP.mono (copyPt_ok hw₄ (o := p256.pt RX RY RZ) (p := p256.pt TX TY TZ) (by decide) (by decide)
    (by decide) (by decide)) fun s₅ ⟨x₅, y₅, z₅, r₅, U₅⟩ => ?_
  refine ⟨hw₄.of_rest r₅, ?_, ?_, ?_, ?_⟩
  · rw [r₅.gpr _ (by decide), K₄.gpr _ (by decide), K₃.gpr _ (by decide), r₂.gpr _ (by decide), u₁.gpr]
  · exact ((hI.keep.trans (Kc.of_rest (u₁.rest (ws := [.s1]) (by decide)))).trans (Kc.of_rest r₂)).trans
      (K₃.kc.trans (K₄.kc.trans (Kc.of_rest r₅)))
  · exact ((((hI.unch.trans (show Unch base [(1920, 96)] s.mem s₂.mem from O₂.unch)).trans U₃).trans U₄).trans
      U₅).cover (by decide)
  · have e := wstep hL hP.q k (j - 1)
    rw [show j - 1 + 1 = j by omega] at e
    rw [← e]
    exact pT.move x₅ y₅ z₅

/-- What the body writes. -/
abbrev bodyW : List (Nat × Nat) := [(512, 480), (1344, 32), (1920, 96), (2048, 1536), (3840, 256)]

/-- `R = [k]Q`, for `k` at `K`'s slot and `Q` affine in `R`'s first two. -/
theorem body_ok (hL : Law W) {base : Addr} {s : State} (hp : WPre base s) :
    WP isa (Cfg.body p256) s fun s' => Kc s s' ∧ Unch base bodyW s.mem s'.mem ∧
      PtOk base s' (p256.pt RX RY RZ) (mul (wordsVal s.mem base (p256.sl K) 4) (qOf base s)) := by
  have hn := hp.ws.nowrap
  have hp0 : 0 < W.p := by decide
  rw [Cfg.body]
  refine WP.seq (WP.mono (build_ok hL hp) fun s₁ ⟨K₁, U₁, hK₁, T₁⟩ => ?_)
  have hw₁ := hp.ws.of_kp K₁
  refine WP.seq (WP.block_append (WP.mono (copyPt_ok hw₁ (o := p256.pt RX RY RZ) (p := p256.pt ZERO ONEP ZERO)
    (by decide) (by decide) (by decide) (by decide)) fun s₂ ⟨x₂, y₂, z₂, r₂, U₂⟩ => ?_))
  have hw₂ := hw₁.of_rest r₂
  refine wp_li (imm := 64) (by decide) fun s₃ u₃ => WP.block_nil ?_
  have hw₃ : WsReg s₃ base := hw₂.of_kc (Kc.of_rest (u₃.rest (ws := [.s1]) (by decide)))
  have U₃ : Unch base [(512, 96)] s₁.mem s₃.mem := by rw [u₃.mem]; exact U₂.cover (by decide)
  have k₃ : ∀ d, d + 32 ≤ 512 ∨ 608 ≤ d → d + 32 ≤ 4096 → wordsVal s₃.mem base d 4 = wordsVal s₁.mem base d 4 :=
    fun d h h' => U₃.wordsVal (by simp; omega) (by omega)
  have hP : WFix base s₃ (qOf base s) (wordsVal s.mem base (p256.sl K) 4) :=
    ⟨hK₁.of_eq fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> exact k₃ _ (by decide) (by decide),
     T₁.of_eq (fun d h1 h2 => k₃ d (by omega) (by omega)) (by decide),
     by rw [k₃ _ (by decide) (by decide), U₁.wordsVal (by decide) (by decide)], hp.on⟩
  have zv : wordsVal s₁.mem base (p256.sl ZERO) 4 = 0 := hK₁.zero
  have ov : wordsVal s₁.mem base (p256.sl ONEP) 4 = 2 ^ 256 % W.p := hK₁.onep
  have rx : wordsVal s₃.mem base (p256.sl RX) 4 = 0 := by rw [u₃.mem]; exact x₂.trans zv
  have ry : wordsVal s₃.mem base (p256.sl RY) 4 = 1 * 2 ^ 256 % W.p := by
    rw [u₃.mem, Nat.one_mul]; exact y₂.trans ov
  have rz : wordsVal s₃.mem base (p256.sl RZ) 4 = 0 := by rw [u₃.mem]; exact z₂.trans zv
  have hk : wordsVal s.mem base (p256.sl K) 4 < 2 ^ 256 := wordsVal_lt _ _ _ _
  have hI : WInv base s₃ s₃ (qOf base s) (wordsVal s.mem base (p256.sl K) 4) 64 := by
    refine ⟨hw₃, u₃.gpr, ⟨fun _ _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [wpt_top _ hk]
      show Rep W (tmv W 4 base s₃ (p256.sl RX)) (tmv W 4 base s₃ (p256.sl RY)) (tmv W 4 base s₃ (p256.sl RZ)) _
      simp only [tmv]
      rw [rx, ry, rz, toM_zero, Nat.one_mul, toM_one unit]
      exact rep_infinity' hL
    · show wordsVal _ _ (p256.sl RX) 4 < _; rw [rx]; exact hp0
    · show wordsVal _ _ (p256.sl RY) 4 < _; rw [ry]; exact Nat.mod_lt _ hp0
    · show wordsVal _ _ (p256.sl RZ) 4 < _; rw [rz]; exact hp0
  refine countLoop_ok (Inv := fun j s' => WInv base s₃ s' (qOf base s) (wordsVal s.mem base (p256.sl K) 4) j)
    (n := 64) (fun j s' hi => hi.ctr) (fun j s' h1 h2 hi => step_ok hL hP h1 h2 hi) (fun s' hi => ?_)
    (by decide) (by decide) hI
  refine ⟨(K₁.kc.trans (Kc.of_rest ((r₂.mono (by decide)).trans (u₃.rest (ws := [.t0, .s1]) (by decide))))).trans
    hi.keep, ((U₁.trans U₃).trans hi.unch).cover (by decide), ?_⟩
  have e : wpt (qOf base s) (wordsVal s.mem base (p256.sl K) 4) 0 = mul (wordsVal s.mem base (p256.sl K) 4) (qOf base s) := by
    simp only [wpt, Nat.mul_zero, Nat.shiftRight_zero]
  rw [← e]
  exact hi.rep

/-! ## The function and its contract -/

open VG.Proof.Ecdsa.RISCV64.P256 (MC mulRVc coordAt_eq represents_of_rep saves satState sat_consts sat_point sv)

/-- What the function writes, as the contract's own working space and result read it. -/
abbrev fnW : List (Nat × Nat) :=
  [(1504, 8), (1512, 8), (1520, 8), (512, 480), (1344, 32), (1920, 96), (2048, 1536), (3840, 256)]

/-- What the function writes is its own working space or the result's. -/
theorem keeps_of_unch {ws : Addr} {m m' : Mem} (hu : Unch ws fnW m m') : MC.Keeps ws m m' := by
  intro i hi hown hp
  have h8 : Impl.Weierstrass.Mont.wsBytes = 8192 := rfl
  refine hu _ fun w hw => ?_
  rw [show ws + BitVec.ofNat 64 i = off ws i from rfl, ofs_off0 ws (by omega)]
  have hw' := (by decide : ∀ w ∈ fnW, (512 ≤ w.1 ∧ w.1 + w.2 ≤ 1056) ∨ (1344 ≤ w.1 ∧ w.1 + w.2 ≤ 1376) ∨
    1504 ≤ w.1) w hw
  simp only [Impl.Weierstrass.Mul.Curve.Own, Impl.Weierstrass.Mul.Curve.slot, Impl.Weierstrass.Mul.Curve.tmpAt,
    Impl.Weierstrass.Mul.Curve.bitsAt, Impl.Weierstrass.Mul.Curve.pAt, Impl.Weierstrass.Mul.Curve.ptBytes,
    MC, Impl.Weierstrass.Mul.p256, true_and] at hown hp
  omega

/-- The windowed `vg_p256_mul` meets `mulRVc`, given the group law. -/
theorem mul_rv (hL : Law W) (s : State) (hs : mulRVc.pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.Window.mulP256 s t s' ∧ abiPreserved s s' ∧ mulRVc.post s s' := by
  obtain ⟨-, hwr, hfit, hal, ⟨-, hz, hone, ha, -⟩, ⟨hx, hy, hon⟩⟩ := hs
  generalize hb : s.gpr .a0 = base at hwr hfit hal hz hone ha hx hy hon
  have hwr' : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_singleton_self _
  have hpR := unit
  have hp0 : 0 < W.p := by decide
  have ca : ∀ (m : Mem) {o : Nat}, o < 4096 → MC.toPoint.coordAt m base o = wordsVal m base o 4 :=
    fun m _ ho => coordAt_eq m base (by omega)
  have dq : ∀ x, MC.toPoint.dec x = toM W.p (2 ^ 256) x :=
    VG.Proof.Weierstrass.Point.dec_eq MC.toPoint hL.one_ne_zero (VG.Proof.Weierstrass.Point.fermat_of_law hL) hpR
  suffices h : WP isa Impl.Ecdsa.RISCV64.Window.mulP256 s fun s' => abiPreserved s s' ∧ mulRVc.post s s' by
    obtain ⟨t, s', he, h⟩ := h; exact ⟨t, s', he, h⟩
  rw [Impl.Ecdsa.RISCV64.Window.mulP256, Window.Cfg.mulFn, show p256.mulSave = 1504 from rfl]
  refine WP.seq (sd_a0 hb hwr' hal (d := 1504) (by decide) (by decide) fun s₁ u₁ => ?_)
  refine sd_a0 (by rw [u₁.gpr]; exact hb) (by rw [u₁.wr]; exact hwr') hal (d := 1512) (by decide)
    (by decide) fun s₂ u₂ => ?_
  refine sd_a0 (by rw [u₂.gpr, u₁.gpr]; exact hb) (by rw [u₂.wr, u₁.wr]; exact hwr') hal (d := 1520)
    (by decide) (by decide) fun s₃ u₃ => wp_mv fun s₄ u₄ => WP.block_nil ?_
  have g₄ : ∀ r, r ≠ .s0 → s₄.gpr r = s.gpr r := fun r hr => by
    rw [u₄.other r hr, u₃.gpr, u₂.gpr, u₁.gpr]
  have hw₄ : WsReg s₄ base := ⟨by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, hb],
    by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hwr', hfit, hal⟩
  have m₄ : s₄.mem = ((s.mem.writeW (off base 1504) (s.gpr .s0)).writeW (off base 1512) (s.gpr .s1)).writeW
      (off base 1520) (s.gpr .ra) := by
    simp only [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr]
  have O₄ : Unch base saves s.mem s₄.mem := by
    rw [m₄]
    exact (((writeW_outside _ _ _ (by omega)).unch.trans (writeW_outside _ _ _ (by omega)).unch).trans
      (writeW_outside _ _ _ (by omega)).unch)
  have sv₄ : ∀ i, i < 45 → sv base s₄ i = sv base s i := fun i hi =>
    O₄.wordsVal (fun w hw => by
      simp only [saves, List.mem_cons, List.not_mem_nil, or_false] at hw
      have : p256.sl i + 32 ≤ 1504 := by simp only [Cfg.sl, slot, p256]; omega
      rcases hw with rfl | rfl | rfl <;> (simp only; omega)) (by simp only [Cfg.sl, slot, p256]; omega)
  have cs : ∀ i, i < 45 → MC.toPoint.coordAt s.mem base (p256.sl i) = sv base s i := fun i hi =>
    ca s.mem (by simp only [Cfg.sl, slot, p256]; omega)
  have hz' : sv base s₄ ZERO = 0 := by rw [sv₄ _ (by decide)]; exact (cs ZERO (by decide)).symm.trans hz
  have hone' : sv base s₄ ONEP = 2 ^ 256 % W.p := by
    rw [sv₄ _ (by decide)]; refine (cs ONEP (by decide)).symm.trans (hone.trans ?_)
    simp only [Impl.Weierstrass.Mul.Curve.mont, Nat.one_mul]; rfl
  have ha' : sv base s₄ AP = W.a * 2 ^ 256 % W.p := by
    rw [sv₄ _ (by decide)]; refine (cs AP (by decide)).symm.trans (ha.trans ?_)
    simp only [Impl.Weierstrass.Mul.Curve.mont]; rw [Nat.mul_comm]; rfl
  have qx : (MC.qCoords base s.mem).1 = sv base s₄ RX := by rw [sv₄ _ (by decide)]; exact cs RX (by decide)
  have qy : (MC.qCoords base s.mem).2 = sv base s₄ RY := by
    rw [sv₄ _ (by decide), ← cs RY (by decide)]; rfl
  have eP : MC.point base s.mem = qOf base s₄ := by
    unfold Impl.Weierstrass.Mul.Curve.point
    rw [qx, qy, dq, dq]
    rfl
  have hon' := hon
  rw [eP] at hon'
  -- The body.
  refine WP.seq (WP.mono (body_ok hL ⟨hw₄, ha', hz', hone', by show sv base s₄ RX < W.p; rw [← qx]; exact hx,
    by show sv base s₄ RY < W.p; rw [← qy]; exact hy, hon'⟩)
    fun s₅ ⟨K₅, U₅, R₅⟩ => ?_)
  -- The loads.
  have hw₅ := hw₄.of_kc K₅
  have far : ∀ d ∈ [1504, 1512, 1520], word s₅.mem base d = word s₄.mem base d := fun d hd =>
    U₅.word (fun w hw => by
      have := (by decide : ∀ w ∈ bodyW, w.1 + w.2 ≤ 1504 ∨ 1920 ≤ w.1) w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      omega) (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; omega)
  have w20 : word s₅.mem base 1520 = s.gpr .ra := by
    rw [far 1520 (by simp), m₄, word_writeW_self]
  have w12 : word s₅.mem base 1512 = s.gpr .s1 := by
    rw [far 1512 (by simp), m₄, (writeW_outside (d := 1520) _ base _ (by omega)).word (by omega) (by omega), word_writeW_self]
  have w04 : word s₅.mem base 1504 = s.gpr .s0 := by
    rw [far 1504 (by simp), m₄, (writeW_outside (d := 1520) _ base _ (by omega)).word (by omega) (by omega),
      (writeW_outside (d := 1512) _ base _ (by omega)).word (by omega) (by omega), word_writeW_self]
  refine ld_ws hw₅ (d := 1520) (by decide) (by decide) fun s₆ u₆ => ?_
  refine ld_ws (hw₅.of_kp (Kp.of_upd u₆)) (d := 1512) (by decide) (by decide) fun s₇ u₇ => ?_
  have hw₇ : WsReg s₇ base := ⟨by rw [u₇.other .s0 (by decide), u₆.other .s0 (by decide)]; exact hw₅.s0,
    by rw [u₇.wr, u₆.wr]; exact hw₅.wr, hfit, hal⟩
  refine ld_ws hw₇ (d := 1504) (by decide) (by decide) fun s₈ u₈ => WP.block_nil ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · have m₇ : s₇.mem = s₅.mem := by rw [u₇.mem, u₆.mem]
    by_cases h0 : r = .s0
    · subst h0; rw [u₈.gpr, m₇, w04]
    by_cases h1 : r = .s1
    · subst h1; rw [u₈.other _ (by decide), u₇.gpr, u₆.mem, w12]
    rw [u₈.other _ h0, u₇.other _ h1, u₆.other _ (fun e => by subst e; revert hr; decide),
      K₅.gpr r hr h1, g₄ r h0]
  · rw [u₈.sp, u₇.sp, u₆.sp, K₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, w20]
  · have m₈ : s₈.mem = s₅.mem := by rw [u₈.mem, u₇.mem, u₆.mem]
    show MC.ResultInRange _ _ (s.gpr .a0) s.mem s₈.mem
    rw [hb, eP, m₈]
    refine ⟨fun _ _ => ?_, keeps_of_unch ((O₄.trans U₅).cover (by decide))⟩
    have e : MC.scalar base s.mem = sv base s₄ K := by rw [sv₄ _ (by decide)]; exact cs K (by decide)
    have c5 : ∀ i, i < 45 → MC.toPoint.coordAt s₅.mem base (p256.sl i) = sv base s₅ i := fun i hi =>
      ca s₅.mem (by simp only [Cfg.sl, slot, p256]; omega)
    have x0 : MC.toPoint.coordAt s₅.mem base MC.pAt = sv base s₅ RX := c5 RX (by decide)
    have x1 : MC.toPoint.coordAt s₅.mem base (MC.pAt + Impl.Weierstrass.Point.elemBytes MC.toPoint.k) =
        sv base s₅ RY := c5 RY (by decide)
    have x2 : MC.toPoint.coordAt s₅.mem base (MC.pAt + 2 * Impl.Weierstrass.Point.elemBytes MC.toPoint.k) =
        sv base s₅ RZ := c5 RZ (by decide)
    rw [e]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x0]; exact R₅.x
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x1]; exact R₅.y
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x2]; exact R₅.z
    · rw [Impl.Weierstrass.Point.Curve.pointAt, x0, x1, x2, dq, dq, dq]
      exact represents_of_rep R₅.rep

end VG.Proof.Ecdsa.RISCV64.Window
