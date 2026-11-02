module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.WindowA
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.Joint
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.WindowA
public import VerifiedGarbage.Proof.Weierstrass.JacDbl0
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Weierstrass.PointFacts
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
import VerifiedGarbage.Proof.Ecdh.RISCV64.Masks
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes

/-!
# `vg_secp256k1_mul` by four-bit windows on RISC-V: the body

`WindowA.Cfg.body secp256k1 dblJ0` leaves in `R` a representative of
`[k]Q` (`body_ok`), for `k` at `K`'s slot and `Q` affine in `R`'s first two:

* `quad_ok`: `R = 16 R`: `R`'s representative of `P` into Jacobian
  coordinates stands for `P` (`InvJ.of_toJ`), each doubling `dblJ0`, for
  `a = 0`, doubles it (`InvJ.dbl0`), and back in projective coordinates,
  with `Y = 1` where `Z` is zero, it is a representative of `16 P` again
  (`InvJ.out`);
* `build_ok`: the table of `[e]Q` from byte 2048, stored through `a6` as
  verification's is (the joint ladder's `PtOk`, `addPt_ok`);
* `select_ok`: the nibble's entry to `E`, by verification's selection;
* `step_ok`, `body_ok`: the windows, from `R = O`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.Secp256k1.Window

open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.WindowA
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.Secp256k1 (W field_ok unit)
open VG.Proof.Ecdsa.RISCV64.Secp256k1.Joint (PtOk addPt_ok addW keepU jSl)
open VG.Proof.Ecdsa.RISCV64.WindowA
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Point Fe mul onCurve)
open VG.Impl.Ecdsa.RISCV64.Window (windows)
open VG.Impl.Ecdsa.RISCV64.Verify (EX EY EZ)

/-- The curve as the code has it. -/
abbrev c : Cfg := secp256k1

/-! ## The slots -/

/-- The slots of `R = 16 R`'s arithmetic. -/
abbrev wSl : List Nat :=
  [c.sl AP, c.sl B3P, c.sl ZERO, c.sl T0, c.sl T1, c.sl T2, c.sl T3, c.sl T4, c.sl T5,
    c.sl RX, c.sl RY, c.sl RZ, c.sl DX, c.sl DY, c.sl DZ, c.sl TX, c.sl TY, c.sl TZ]

theorem wLay : Lay c.MP' (own 4) (· ∈ wSl) :=
  ⟨by decide, fun x y hx hy => (by decide : ∀ x ∈ wSl, ∀ y ∈ wSl, x ≠ y → x + 8 * 4 ≤ y ∨ y + 8 * 4 ≤ x)
    x hx y hy, by decide, by decide⟩

theorem wShort : Short (· ∈ wSl) := by decide

/-- The slots the windows' complete additions and Jacobian doublings use. -/
abbrev S : RcbSlots := Cfg.rcbSlots c

/-- What the field operations of `R = 16 R` write: `R`, `D`, `T`, the
temporaries and the functions' own working space. -/
abbrev quadW : List (Nat × Nat) := [(512, 480), (3840, 256)]

/-- The slots they write. -/
abbrev quadWl : List Nat :=
  [c.sl T0, c.sl T1, c.sl T2, c.sl T3, c.sl T4, c.sl T5, c.sl RX, c.sl RY, c.sl RZ,
    c.sl DX, c.sl DY, c.sl DZ, c.sl TX, c.sl TY, c.sl TZ]

/-- The constants the windows read. -/
structure KC (base : Addr) (s : State) : Prop where
  ap : wordsVal s.mem base (c.sl AP) 4 = W.a * 2 ^ 256 % W.p
  bp : wordsVal s.mem base (c.sl B3P) 4 = 3 * W.b * 2 ^ 256 % W.p
  zero : wordsVal s.mem base (c.sl ZERO) 4 = 0
  onep : wordsVal s.mem base (c.sl ONEP) 4 = 2 ^ 256 % W.p

theorem KC.of_eq {base : Addr} {s s' : State} (h : KC base s)
    (e : ∀ d ∈ [c.sl AP, c.sl B3P, c.sl ZERO, c.sl ONEP], wordsVal s'.mem base d 4 = wordsVal s.mem base d 4) :
    KC base s' :=
  ⟨(e _ (by simp)).trans h.ap, (e _ (by simp)).trans h.bp, (e _ (by simp)).trans h.zero, (e _ (by simp)).trans h.onep⟩

/-! ## `R = 16 R` -/

theorem dbl_apart_DT : RcbApart S (c.pt DX DY DZ) (c.pt DX DY DZ) (c.pt TX TY TZ) := ⟨by decide, by decide⟩
theorem dbl_apart_TD : RcbApart S (c.pt TX TY TZ) (c.pt TX TY TZ) (c.pt DX DY DZ) := ⟨by decide, by decide⟩
theorem toJ_apart : RcbApart S (c.pt RX RY RZ) (Cfg.zeroPt c) (c.pt DX DY DZ) := ⟨by decide, by decide⟩
theorem fromJ_apart : RcbApart S (c.pt DX DY DZ) (Cfg.zeroPt c) (c.pt RX RY RZ) := ⟨by decide, by decide⟩

/-- A Jacobian doubling from `p` to `o` (`D` to `T` or back), on `InvJ`,
with `a` at `AP`. -/
theorem dblStep_ok (hL : Law W) {base : Addr} {s : State} {p o : Pt} (hA : RcbApart S p p o)
    (hsl : ∀ x ∈ rcbW S o ++ rcbR S p p, x ∈ wSl) {V : List Nat} {E : Nat → Fe W}
    (hI : Inv 4 base W.p (· ∈ wSl) V E s) (hV : ∀ x ∈ rcbR S p p, x ∈ V)
    {P : Point W}
    (hP : onCurve W P = true) (hJ : InvJ W (E p.x) (E p.y) (E p.z) P) :
    WP isa (fprog secp256k1Field (dblJ0 S p o)) s fun s' => KeepR 4 base (rcbW S o) s s' ∧
      ∃ E', Inv 4 base W.p (· ∈ wSl) ([o.x, o.y, o.z] ++ V) E' s' ∧ InvJ W (E' o.x) (E' o.y) (E' o.z) (d2 P) ∧
        ∀ x, x ∉ rcbW S o → E' x = E x := by
  rw [dblJ0_eq]
  refine WP.mono (ofN_ok (F := secp256k1Field) field_ok rfl wLay wShort unit dblJ0N_ok hA hsl hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, ?_, kp⟩
  have h := v.trans (dblJ0N_run _)
  simp only [Prod.ext_iff] at h
  obtain ⟨ex, ey, ez⟩ := h
  rw [ex, ey, ez]
  exact InvJ.dbl0 hL rfl hP hJ

/-- `R` into Jacobian coordinates in `D`. -/
theorem toJStep_ok (hL : Law W) {base : Addr} {s : State} {V : List Nat} {E : Nat → Fe W}
    (hI : Inv 4 base W.p (· ∈ wSl) V E s) (hV : ∀ x ∈ rcbR S (c.pt RX RY RZ) (Cfg.zeroPt c), x ∈ V) {P : Point W}
    (hR : Rep W (E (c.sl RX)) (E (c.sl RY)) (E (c.sl RZ)) P) (hz : E (c.sl ZERO) = 0) :
    WP isa (fprog secp256k1Field (toJ S (c.pt RX RY RZ) (Cfg.zeroPt c) (c.pt DX DY DZ))) s fun s' =>
      KeepR 4 base (rcbW S (c.pt DX DY DZ)) s s' ∧
      ∃ E', Inv 4 base W.p (· ∈ wSl) ([c.sl DX, c.sl DY, c.sl DZ] ++ V) E' s' ∧
        InvJ W (E' (c.sl DX)) (E' (c.sl DY)) (E' (c.sl DZ)) P ∧
        ∀ x, x ∉ rcbW S (c.pt DX DY DZ) → E' x = E x := by
  rw [toJ_eq]
  refine WP.mono (ofN_ok (F := secp256k1Field) field_ok rfl wLay wShort unit toJN_ok toJ_apart (by decide) hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, InvJ.of_toJ hL hR hz (v.trans (toJN_run _)), kp⟩

/-- `D` back in projective coordinates in `R`. -/
theorem fromJStep_ok {base : Addr} {s : State} {V : List Nat} {E : Nat → Fe W}
    (hI : Inv 4 base W.p (· ∈ wSl) V E s) (hV : ∀ x ∈ rcbR S (c.pt DX DY DZ) (Cfg.zeroPt c), x ∈ V) :
    WP isa (fprog secp256k1Field (fromJ S (c.pt DX DY DZ) (Cfg.zeroPt c) (c.pt RX RY RZ))) s fun s' =>
      KeepR 4 base (rcbW S (c.pt RX RY RZ)) s s' ∧
      ∃ E', Inv 4 base W.p (· ∈ wSl) ([c.sl RX, c.sl RY, c.sl RZ] ++ V) E' s' ∧
        (E' (c.sl RX), E' (c.sl RY), E' (c.sl RZ)) =
          (E (c.sl DX) * E (c.sl DZ), E (c.sl DY) + E (c.sl ZERO),
            E (c.sl DZ) * E (c.sl DZ) * E (c.sl DZ)) ∧
        ∀ x, x ∉ rcbW S (c.pt RX RY RZ) → E' x = E x := by
  rw [fromJ_eq]
  refine WP.mono (ofN_ok (F := secp256k1Field) field_ok rfl wLay wShort unit fromJN_ok fromJ_apart (by decide) hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, v.trans (fromJN_run _), kp⟩

/-- `R = 16 R`, for `R` representing `P`. -/
theorem quad_ok (hL : Law W) {base : Addr} {s : State} (hw : WsReg s base) (hK : KC base s) {P : Point W}
    (hP : onCurve W P = true) (hR : PtOk base s (c.pt RX RY RZ) P) :
    WP isa (Cfg.quad c dblJ0) s fun s' => Kp s s' ∧ Unch base quadW s.mem s'.mem ∧
      PtOk base s' (c.pt RX RY RZ) (d16 P) := by
  have hp0 : 0 < W.p := by decide
  have hn := hw.nowrap
  rw [Cfg.quad]
  simp only [progs]
  -- The start: `a`, `b`, zero and `R`.
  have hI : Inv 4 base W.p (· ∈ wSl) [c.sl AP, c.sl B3P, c.sl ZERO, c.sl RX, c.sl RY, c.sl RZ]
      (fun x => toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base x 4)) s := by
    refine ⟨hw, by decide, fun x hx => ?_, fun x _ => rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hK.ap]; exact Nat.mod_lt _ hp0
    · rw [hK.bp]; exact Nat.mod_lt _ hp0
    · rw [hK.zero]; exact hp0
    exacts [hR.x, hR.y, hR.z]
  have e0 : toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base (c.sl ZERO) 4) = 0 := by
    rw [hK.zero]; exact toM_zero _ _
  -- To Jacobian coordinates.
  refine WP.seq (WP.mono (toJStep_ok hL hI (by decide) hR.rep e0) fun s₁ ⟨k₁, E₁, I₁, J₁, p₁⟩ => ?_)
  -- Four doublings.
  refine WP.seq (WP.mono (dblStep_ok hL dbl_apart_DT (by decide) I₁ (by decide) hP J₁)
    fun s₂ ⟨k₂, E₂, I₂, J₂, p₂⟩ => ?_)
  refine WP.seq (WP.mono (dblStep_ok hL dbl_apart_TD (by decide) I₂ (by decide) (hL.onCurve_add hP hP) J₂)
    fun s₃ ⟨k₃, E₃, I₃, J₃, p₃⟩ => ?_)
  have h4 := hL.onCurve_add (hL.onCurve_add hP hP) (hL.onCurve_add hP hP)
  refine WP.seq (WP.mono (dblStep_ok hL dbl_apart_DT (by decide) I₃ (by decide) h4 J₃)
    fun s₄ ⟨k₄, E₄, I₄, J₄, p₄⟩ => ?_)
  refine WP.seq (WP.mono (dblStep_ok hL dbl_apart_TD (by decide) I₄ (by decide) (hL.onCurve_add h4 h4) J₄)
    fun s₅ ⟨k₅, E₅, I₅, J₅, p₅⟩ => ?_)
  -- Back to projective coordinates.
  refine WP.seq (WP.mono (fromJStep_ok I₅ (by decide)) fun s₆ ⟨k₆, E₆, I₆, v₆, p₆⟩ => ?_)
  have z₅ : E₅ (c.sl ZERO) = 0 := by
    rw [p₅ _ (by decide), p₄ _ (by decide), p₃ _ (by decide), p₂ _ (by decide), p₁ _ (by decide)]; exact e0
  simp only [Prod.mk.injEq] at v₆
  obtain ⟨vx, vy, vz⟩ := v₆
  rw [z₅, Lean.Grind.AddCommMonoid.add_zero] at vy
  have hw₆ := I₆.ws
  have hn₆ := hw₆.nowrap
  have ltx := I₆.lt (c.sl RX) (by decide)
  have lty := I₆.lt (c.sl RY) (by decide)
  have ltz := I₆.lt (c.sl RZ) (by decide)
  have vx' : tmv W 4 base s₆ (c.sl RX) = E₆ (c.sl RX) := I₆.val (c.sl RX) (by decide)
  have vy' : tmv W 4 base s₆ (c.sl RY) = E₆ (c.sl RY) := I₆.val (c.sl RY) (by decide)
  have vz' : tmv W 4 base s₆ (c.sl RZ) = E₆ (c.sl RZ) := I₆.val (c.sl RZ) (by decide)
  -- `Y = 1` where `Z = 0`.
  have KK : KeepR 4 base quadWl s s₆ :=
    ((((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans ((k₃.mono (by decide)).trans
      (k₄.mono (by decide)))).trans ((k₅.mono (by decide)).trans (k₆.mono (by decide))))
  have UK : Unch base (quadWl.map (fun w => (w, 8 * 4)) ++ [(own 4, 64 * 4)]) s.mem s₆.mem := KK.mem
  have onep₆ : wordsVal s₆.mem base (c.sl ONEP) 4 = 2 ^ 256 % W.p := by
    rw [UK.wordsVal (by decide) (by decide)]; exact hK.onep
  refine WP.block_append (WP.mono (zeroMask_ok hw₆ (n := 4) (a := c.sl RZ) (by decide) (by decide))
    fun s₇ ⟨r₇, m₇, a7₇⟩ => ?_)
  have hw₇ := hw₆.of_rest r₇
  refine WP.mono (sel_ok (decide (wordsVal s₆.mem base (c.sl RZ) 4 = 0)) 4 hw₇ a7₇
    (o := c.sl RY) (a := c.sl RY) (b := c.sl ONEP) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (Or.inl (Nat.le_refl _)) (by decide)) fun s₈ ⟨e₈, r₈, O₈⟩ => ?_
  rw [m₇] at e₈ O₈
  have ex : wordsVal s₈.mem base (c.sl RX) 4 = wordsVal s₆.mem base (c.sl RX) 4 :=
    O₈.wordsVal (by decide) (by decide)
  have ez : wordsVal s₈.mem base (c.sl RZ) 4 = wordsVal s₆.mem base (c.sl RZ) 4 :=
    O₈.wordsVal (by decide) (by decide)
  have hZ : (wordsVal s₆.mem base (c.sl RZ) 4 = 0) ↔ E₅ (c.sl DZ) = 0 := by
    rw [← toM_eq_zero_iff unit ltz]
    show tmv W 4 base s₆ (c.sl RZ) = 0 ↔ _
    rw [vz', vz]
    exact ⟨fun h => by_contra fun hz => cube_ne_zero hL hz h, fun h => by rw [h]; grind⟩
  have hrep := InvJ.out hL J₅
  refine ⟨KK.kp.trans ((Kp.of_rest r₇).trans (Kp.of_rest r₈)), (UK.trans O₈.unch).cover (by decide), ⟨?_, ?_, ?_, ?_⟩⟩
  · show Rep W (tmv W 4 base s₈ (c.sl RX)) (tmv W 4 base s₈ (c.sl RY)) (tmv W 4 base s₈ (c.sl RZ)) _
    simp only [tmv]
    rw [ex, ez]
    show Rep W (tmv W 4 base s₆ (c.sl RX)) _ (tmv W 4 base s₆ (c.sl RZ)) _
    rw [vx', vz', vx, vz, e₈]
    by_cases h0 : E₅ (c.sl DZ) = 0
    · have hc : decide (wordsVal s₆.mem base (c.sl RZ) 4 = 0) = true := decide_eq_true (hZ.mpr h0)
      have h0' : E₅ (c.pt DX DY DZ).z = 0 := h0
      rw [show (if E₅ (c.pt DX DY DZ).z = 0 then (1 : Fe W) else E₅ (c.pt DX DY DZ).y) = 1 from
        by simp [h0']] at hrep
      simp only [hc, ↓reduceIte]
      rw [onep₆, toM_one unit]
      exact hrep
    · have hc : decide (wordsVal s₆.mem base (c.sl RZ) 4 = 0) = false :=
        decide_eq_false fun h => h0 (hZ.mp h)
      have h0' : ¬E₅ (c.pt DX DY DZ).z = 0 := h0
      rw [show (if E₅ (c.pt DX DY DZ).z = 0 then (1 : Fe W) else E₅ (c.pt DX DY DZ).y) =
        E₅ (c.pt DX DY DZ).y from by simp [h0']] at hrep
      simp only [hc, ↓reduceIte, Bool.false_eq_true]
      show Rep W _ (tmv W 4 base s₆ (c.sl RY)) _ _
      rw [vy', vy]
      exact hrep
  · show wordsVal s₈.mem base (c.sl RX) 4 < W.p
    rw [ex]; exact ltx
  · show wordsVal s₈.mem base (c.sl RY) 4 < W.p
    rw [e₈]; split
    · rw [onep₆]; exact Nat.mod_lt _ (by decide)
    · exact lty
  · show wordsVal s₈.mem base (c.sl RZ) 4 < W.p
    rw [ez]; exact ltz

/-! ## The table -/

/-- Entry `e`'s slots. -/
abbrev ent (e : Nat) : Pt := ⟨2048 + 96 * e, 2048 + 96 * e + 32, 2048 + 96 * e + 64⟩

/-- The table up to entry `m`: `[e]Q` in entry `e`. -/
abbrev TabTo (base : Addr) (s : State) (Q : Point W) (m : Nat) : Prop := ∀ e ≤ m, PtOk base s (ent e) (mul e Q)

theorem TabTo.of_eq {base : Addr} {s s' : State} {Q : Point W} {m : Nat} (h : TabTo base s Q m)
    (he : ∀ d, 2048 ≤ d → d + 32 ≤ 3584 → wordsVal s'.mem base d 4 = wordsVal s.mem base d 4) (hm : m ≤ 15) :
    TabTo base s' Q m :=
  fun e hlt => (h e hlt).of_eq (he (2048 + 96 * e) (by omega) (by omega))
    (he (2048 + 96 * e + 32) (by omega) (by omega)) (he (2048 + 96 * e + 64) (by omega) (by omega))

/-- `o = p`, the three coordinates one after the other, for `o`'s slots in
order and `p`'s apart from them all. -/
theorem copyPt_ok {s : State} {base : Addr} (hw : WsReg s base) {o p : Pt}
    (h8 : ∀ x ∈ [o.x, o.y, o.z, p.x, p.y, p.z], x % 8 = 0 ∧ x + 32 ≤ 2048)
    (hxy : o.x + 32 ≤ o.y) (hyz : o.y + 32 ≤ o.z)
    (hp : ∀ a ∈ [p.x, p.y, p.z], a + 32 ≤ o.x ∨ o.z + 32 ≤ a) :
    WP isa (.block (Cfg.copyPt c o p)) s fun s' =>
      wordsVal s'.mem base o.x 4 = wordsVal s.mem base p.x 4 ∧ wordsVal s'.mem base o.y 4 = wordsVal s.mem base p.y 4 ∧
      wordsVal s'.mem base o.z 4 = wordsVal s.mem base p.z 4 ∧ Rest [.t0] s s' ∧
      Unch base [(o.x, 32), (o.y, 32), (o.z, 32)] s.mem s'.mem := by
  have hn := hw.nowrap
  have g := fun x hx => h8 x hx
  have gp := fun x hx => hp x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g gp
  obtain ⟨⟨ox8, ox⟩, ⟨oy8, oy⟩, ⟨oz8, oz⟩, ⟨px8, px⟩, ⟨py8, py⟩, ⟨pz8, pz⟩⟩ := g
  obtain ⟨hpx, hpy, hpz⟩ := gp
  rw [Cfg.copyPt, show c.n = 4 from rfl, List.append_assoc]
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

/-- `D`'s slots, as `copyPt` writes them. -/
theorem dSl : ∀ w ∈ ([((c.pt DX DY DZ).x, 32), ((c.pt DX DY DZ).y, 32), ((c.pt DX DY DZ).z, 32)] : List (Nat × Nat)),
    608 ≤ w.1 ∧ w.1 + w.2 ≤ 704 := by decide

/-- A point in slots below byte 2048 to entry `e`. -/
theorem store_ok {s : State} {base : Addr} (hw : WsReg s base) {e : Nat} (he : e < 16) {p : Pt}
    (hs : ∀ x ∈ [p.x, p.y, p.z], x % 8 = 0 ∧ x + 32 ≤ 2048) {P : Point W} (hp : PtOk base s p P) :
    WP isa (.block (Verify.Cfg.storePt c e p)) s fun s' => PtOk base s' (ent e) P ∧ Rest [.t0, .a6] s s' ∧
      Outside base (2048 + 96 * e) 96 s.mem s'.mem := by
  have hn := hw.nowrap
  have g := fun x hx => hs x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g
  obtain ⟨⟨hx8, hx⟩, ⟨hy8, hy⟩, ⟨hz8, hz⟩⟩ := g
  refine WP.mono (Joint.storePt_ok c hw (e := e) (by decide) (by show 2048 + 96 * e + 96 ≤ 8192; omega)
    (by show 96 * e + 96 ≤ 4095; omega) ⟨hx8, by show _ + 32 ≤ 4095; omega, by show _ + 32 ≤ 2048; omega⟩
    ⟨hy8, by show _ + 32 ≤ 4095; omega, by show _ + 32 ≤ 2048; omega⟩
    ⟨hz8, by show _ + 32 ≤ 4095; omega, by show _ + 32 ≤ 2048; omega⟩) fun s' ⟨ex, ey, ez, r, O⟩ => ?_
  simp only [show c.jt = 2048 from rfl, show Verify.Cfg.jb c = 96 from rfl, show c.n = 4 from rfl,
    Nat.reduceMul] at ex ey ez O
  exact ⟨hp.move ex ey ez, r, O⟩

/-- While the table is built: the constants, the table up to entry `m + 1`,
`[m + 1]Q` in `D` and `Q` in `R`'s first two slots and one's. -/
structure AI (base : Addr) (s : State) (Q : Point W) (m : Nat) : Prop where
  ws : WsReg s base
  kc : KC base s
  tab : TabTo base s Q (m + 1)
  d : PtOk base s (c.pt DX DY DZ) (mul (m + 1) Q)
  q : PtOk base s (c.pt RX RY ONEP) Q

/-- What the table's additions write. -/
abbrev addsW : List (Nat × Nat) := [(608, 384), (2048, 1536), (3840, 256)]

/-- An addition's writes into `T`, within `addsW`, and apart from the table. -/
theorem addW_T : ∀ w ∈ addW (c.pt TX TY TZ), (∃ w' ∈ addsW, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2) ∧
    (w.1 + w.2 ≤ 2048 ∨ 3584 ≤ w.1) := by decide

/-- `copyPt`'s writes into `D`, within `addsW`. -/
theorem dW : ∀ w ∈ ([((c.pt DX DY DZ).x, 32), ((c.pt DX DY DZ).y, 32), ((c.pt DX DY DZ).z, 32)] : List (Nat × Nat)),
    ∃ w' ∈ addsW, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := by decide

/-- Entry `e`'s bytes, within `addsW`. -/
theorem entW {e : Nat} (he : e < 16) : ∃ w' ∈ addsW, w'.1 ≤ 2048 + 96 * e ∧ 2048 + 96 * e + 96 ≤ w'.1 + w'.2 :=
  ⟨(2048, 1536), List.mem_cons_of_mem _ List.mem_cons_self, by simp only; omega, by simp only; omega⟩

/-- Entry `e`, kept by memory unchanged there. -/
theorem ent_of {base : Addr} {s s' : State} {e : Nat} {P : Point W} (h : PtOk base s (ent e) P)
    (k : ∀ d, 2048 + 96 * e ≤ d → d + 32 ≤ 2048 + 96 * e + 96 → wordsVal s'.mem base d 4 = wordsVal s.mem base d 4) :
    PtOk base s' (ent e) P :=
  h.of_eq (k (2048 + 96 * e) (Nat.le_refl _) (by omega)) (k (2048 + 96 * e + 32) (by omega) (by omega))
    (k (2048 + 96 * e + 64) (by omega) (by omega))

/-- The additions of `[e]Q` for `e = 2 … m + 1`. -/
theorem adds_ok (hL : Law W) {base : Addr} {Q : Point W} (hQ : onCurve W Q = true) :
    ∀ m ≤ 14, ∀ {s : State}, AI base s Q 0 →
      WP isa (Cfg.adds c m) s fun s' => Kp s s' ∧ Unch base addsW s.mem s'.mem ∧ AI base s' Q m
  | 0, _, s, h => WP.block_nil ⟨Kp.refl _, Unch.refl _ _ _, h⟩
  | m + 1, hm, s, h => by
    rw [Cfg.adds]
    refine WP.seq (WP.mono (adds_ok hL hQ m (by omega) h) fun s₁ ⟨k₁, U₁, A₁⟩ => ?_)
    have hw₁ := A₁.ws
    have hn := hw₁.nowrap
    -- `T = D + Q`.
    refine WP.seq (WP.mono (addPt_ok hL hw₁ A₁.kc.ap A₁.kc.bp (p := c.pt DX DY DZ) (q := c.pt RX RY ONEP)
      (o := c.pt TX TY TZ) ⟨by decide, by decide⟩ (by decide) (hL.onCurve_mul hQ _) hQ A₁.d A₁.q)
      fun s₂ ⟨k₂, U₂, p₂⟩ => ?_)
    rw [mul_succ' hL hQ, show m + 1 + 1 = m + 2 by omega] at p₂
    have hw₂ := hw₁.of_kp k₂
    have e₂ : ∀ d ∈ [c.sl AP, c.sl B3P, c.sl ZERO, c.sl ONEP] ++ [c.sl RX, c.sl RY], wordsVal s₂.mem base d 4 =
        wordsVal s₁.mem base d 4 := keepU U₂ (by decide)
    have far₂ : ∀ d, 2048 ≤ d → d + 32 ≤ 3584 → wordsVal s₂.mem base d 4 = wordsVal s₁.mem base d 4 :=
      fun d h1 h2 => U₂.wordsVal (fun w hw => by have := (addW_T w hw).2; omega) (by omega)
    -- Stored to entry `m + 2`.
    refine WP.block_append (WP.mono (store_ok hw₂ (e := m + 2) (by omega) (by decide) p₂)
      fun s₃ ⟨p₃, r₃, O₃⟩ => ?_)
    have hw₃ := hw₂.of_rest r₃
    have e₃ : ∀ d, d + 32 ≤ 2048 → wordsVal s₃.mem base d 4 = wordsVal s₂.mem base d 4 := fun d hd =>
      O₃.wordsVal (by omega) (by omega)
    have pT₃ : PtOk base s₃ (c.pt TX TY TZ) (mul (m + 2) Q) :=
      p₂.of_eq (e₃ _ (by decide)) (e₃ _ (by decide)) (e₃ _ (by decide))
    -- `D = T`.
    refine WP.mono (copyPt_ok hw₃ (o := c.pt DX DY DZ) (p := c.pt TX TY TZ) (by decide) (by decide) (by decide)
      (by decide)) fun s₄ ⟨x₄, y₄, z₄, r₄, U₄⟩ => ?_
    have e₄ : ∀ d, (d + 32 ≤ 608 ∨ 704 ≤ d) → d + 32 ≤ 8192 → wordsVal s₄.mem base d 4 = wordsVal s₃.mem base d 4 :=
      fun d h1 h2 => U₄.wordsVal (fun w hw => by have := dSl w hw; omega) (by omega)
    have kd : ∀ d ∈ [c.sl AP, c.sl B3P, c.sl ZERO, c.sl ONEP] ++ [c.sl RX, c.sl RY],
        wordsVal s₄.mem base d 4 = wordsVal s₁.mem base d 4 := fun d hd => by
      have hd' : d + 32 ≤ 608 := (by decide : ∀ d ∈ [c.sl AP, c.sl B3P, c.sl ZERO, c.sl ONEP] ++ [c.sl RX, c.sl RY],
        d + 32 ≤ 608) d hd
      rw [e₄ d (.inl hd') (by omega), e₃ d (by omega), e₂ d hd]
    refine ⟨k₁.trans (k₂.trans ((Kp.of_rest r₃).trans (Kp.of_rest r₄))), ?_, ⟨hw₃.of_rest r₄, ?_, ?_, ?_, ?_⟩⟩
    · refine (((U₁.trans U₂).trans O₃.unch).trans U₄).cover fun w hw => ?_
      rcases List.mem_append.mp hw with hw | hw
      · rcases List.mem_append.mp hw with hw | hw
        · rcases List.mem_append.mp hw with hw | hw
          · exact ⟨w, hw, Nat.le_refl _, Nat.le_refl _⟩
          · exact (addW_T w hw).1
        · rw [List.mem_singleton] at hw
          subst hw
          exact entW (by omega)
      · exact dW w hw
    · exact A₁.kc.of_eq fun d hd => kd d (List.mem_append_left _ hd)
    · intro e he
      rcases Nat.lt_or_ge e (m + 2) with h | h
      · have pe := A₁.tab e (by omega)
        exact ent_of pe fun d h1 h2 => by
          rw [e₄ d (.inr (by omega)) (by omega), O₃.wordsVal (by omega) (by omega), far₂ d (by omega) (by omega)]
      · obtain rfl : e = m + 2 := by omega
        exact ent_of p₃ fun d h1 h2 => e₄ d (.inr (by omega_using [h1])) (by omega_using [h2, hm])
    · exact pT₃.move x₄ y₄ z₄
    · exact A₁.q.of_eq (kd _ (by decide)) (kd _ (by decide)) (kd _ (by decide))

/-- `Q`, the affine point of `R`'s first two slots. -/
abbrev qOf (base : Addr) (s : State) : Point W := .affine (tmv W 4 base s (c.sl RX)) (tmv W 4 base s (c.sl RY))

/-- What the table's construction writes. -/
abbrev buildW : List (Nat × Nat) := [(608, 384), (2048, 1536), (3840, 256)]

/-- What `vg_secp256k1_mul`'s body reads at the start. -/
structure WPre (base : Addr) (s : State) : Prop where
  ws : WsReg s base
  kc : KC base s
  x : wordsVal s.mem base (c.sl RX) 4 < W.p
  y : wordsVal s.mem base (c.sl RY) 4 < W.p
  on : onCurve W (qOf base s) = true

/-- The table of `[e]Q`. -/
theorem build_ok (hL : Law W) {base : Addr} {s : State} (hp : WPre base s) :
    WP isa (Cfg.build c) s fun s' => Kp s s' ∧ Unch base buildW s.mem s'.mem ∧ KC base s' ∧
      TabTo base s' (qOf base s) 15 ∧
      ∀ d, d + 32 ≤ 608 → wordsVal s'.mem base d 4 = wordsVal s.mem base d 4 := by
  have hw := hp.ws
  have hn := hw.nowrap
  have hp0 : 0 < W.p := by decide
  have hK := hp.kc
  have h1 : tmv W 4 base s (c.sl ONEP) = 1 := by
    simp only [tmv]; rw [hK.onep]; exact toM_one unit
  have h0 : tmv W 4 base s (c.sl ZERO) = 0 := by
    simp only [tmv]; rw [hK.zero]; exact toM_zero _ _
  have pO : PtOk base s (c.pt ZERO ONEP ZERO) (mul 0 (qOf base s)) := by
    refine ⟨?_, show wordsVal _ _ (c.sl ZERO) 4 < _ by rw [hK.zero]; exact hp0,
      show wordsVal _ _ (c.sl ONEP) 4 < _ by rw [hK.onep]; exact Nat.mod_lt _ hp0,
      show wordsVal _ _ (c.sl ZERO) 4 < _ by rw [hK.zero]; exact hp0⟩
    show Rep W (tmv W 4 base s (c.sl ZERO)) (tmv W 4 base s (c.sl ONEP)) (tmv W 4 base s (c.sl ZERO)) _
    rw [h0, h1, Joint.mul_zero']
    exact rep_infinity' hL
  have pQ : PtOk base s (c.pt RX RY ONEP) (qOf base s) := by
    refine ⟨?_, hp.x, hp.y, show wordsVal _ _ (c.sl ONEP) 4 < _ by rw [hK.onep]; exact Nat.mod_lt _ hp0⟩
    show Rep W (tmv W 4 base s (c.sl RX)) (tmv W 4 base s (c.sl RY)) (tmv W 4 base s (c.sl ONEP)) _
    rw [h1]
    exact rep_affine' hL _ _
  rw [Cfg.build, List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (store_ok hw (e := 0) (by decide) (by decide) pO)
    fun s₁ ⟨p₁, r₁, O₁⟩ => ?_))
  have hw₁ := hw.of_rest r₁
  have e₁ : ∀ d, d + 32 ≤ 2048 → wordsVal s₁.mem base d 4 = wordsVal s.mem base d 4 := fun d hd =>
    O₁.wordsVal (by omega) (by omega)
  refine WP.block_append (WP.mono (store_ok hw₁ (e := 1) (by decide) (by decide)
    (pQ.of_eq (e₁ _ (by decide)) (e₁ _ (by decide)) (e₁ _ (by decide)))) fun s₂ ⟨p₂, r₂, O₂⟩ => ?_)
  have hw₂ := hw₁.of_rest r₂
  have e₂ : ∀ d, d + 32 ≤ 2048 → wordsVal s₂.mem base d 4 = wordsVal s.mem base d 4 := fun d hd => by
    rw [O₂.wordsVal (by omega) (by omega), e₁ d hd]
  refine WP.mono (copyPt_ok hw₂ (o := c.pt DX DY DZ) (p := c.pt RX RY ONEP) (by decide) (by decide) (by decide)
    (by decide)) fun s₃ ⟨x₃, y₃, z₃, r₃, U₃⟩ => ?_
  have hw₃ := hw₂.of_rest r₃
  have e₃ : ∀ d, (d + 32 ≤ 608 ∨ 704 ≤ d) → d + 32 ≤ 8192 → wordsVal s₃.mem base d 4 = wordsVal s₂.mem base d 4 :=
    fun d h1 h2 => U₃.wordsVal (fun w hw => by have := dSl w hw; omega) (by omega)
  have pQ₃ : PtOk base s₃ (c.pt RX RY ONEP) (qOf base s) :=
    pQ.of_eq ((e₃ _ (.inl (by decide)) (by decide)).trans (e₂ _ (by decide)))
      ((e₃ _ (.inl (by decide)) (by decide)).trans (e₂ _ (by decide)))
      ((e₃ _ (.inl (by decide)) (by decide)).trans (e₂ _ (by decide)))
  have hA : AI base s₃ (qOf base s) 0 := by
    refine ⟨hw₃, hK.of_eq fun d hd => ?_, fun e he => ?_, ?_, pQ₃⟩
    · have hd' : d + 32 ≤ 608 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl <;> decide
      rw [e₃ d (.inl hd') (by omega), e₂ d (by omega)]
    · rcases Nat.lt_or_ge e 1 with h | h
      · obtain rfl : e = 0 := by omega
        exact p₁.of_eq ((e₃ _ (.inr (by decide)) (by decide)).trans (O₂.wordsVal (by decide) (by decide)))
          ((e₃ _ (.inr (by decide)) (by decide)).trans (O₂.wordsVal (by decide) (by decide)))
          ((e₃ _ (.inr (by decide)) (by decide)).trans (O₂.wordsVal (by decide) (by decide)))
      · obtain rfl : e = 1 := by omega
        rw [Joint.mul_one']
        exact p₂.of_eq (e₃ _ (.inr (by decide)) (by decide)) (e₃ _ (.inr (by decide)) (by decide))
          (e₃ _ (.inr (by decide)) (by decide))
    · rw [Joint.mul_one']
      exact (pQ.of_eq (e₂ _ (by decide)) (e₂ _ (by decide)) (e₂ _ (by decide))).move x₃ y₃ z₃
  refine WP.mono (adds_ok hL hp.on 14 (Nat.le_refl _) hA) fun s₄ ⟨k₄, U₄, A₄⟩ => ?_
  refine ⟨((Kp.of_rest r₁).trans (Kp.of_rest r₂)).trans ((Kp.of_rest r₃).trans k₄), ?_, A₄.kc, A₄.tab, ?_⟩
  · refine (((O₁.unch.trans O₂.unch).trans U₃).trans U₄).cover fun w hw => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with (((hw | hw) | hw) | hw)
    · subst hw; exact ⟨(2048, 1536), by simp, by decide, by decide⟩
    · subst hw; exact ⟨(2048, 1536), by simp, by decide, by decide⟩
    · rcases hw with rfl | rfl | rfl <;> exact ⟨(608, 384), by simp, by decide, by decide⟩
    · exact ⟨w, by simpa using hw, Nat.le_refl _, Nat.le_refl _⟩
  · intro d hd
    rw [U₄.wordsVal (by simp; omega) (by omega), e₃ d (.inl hd) (by omega), e₂ d (by omega)]

/-! ## The nibble's entry -/

open VG.Proof.Ecdsa.RISCV64.Joint (scansJ_ok masks4_ok wordsVal_of_words wp_addAt) in
open VG.Proof.Ecdsa.RISCV64.Secp256k1.Joint (selRegs) in
open VG.Impl.Ecdsa.RISCV64.Comb (maskReg treeRegs) in
/-- The window's entry `[k_j]Q` to `E`. -/
theorem select_ok {s : State} {base : Addr} (hw : WsReg s base) {j : Nat} (hj : j < 64)
    (h1 : s.gpr .s1 = BitVec.ofNat 64 j) {Q : Point W} (hT : TabTo base s Q 15) :
    WP isa (.block (Cfg.select c)) s fun s' =>
      PtOk base s' (c.pt EX EY EZ) (mul ((wordsVal s.mem base (c.sl K) 4 >>> (4 * j)) % 16) Q) ∧
      Outside base 1920 96 s.mem s'.mem ∧ Rest selRegs s s' := by
  have hn := hw.nowrap
  rw [Cfg.select]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (nibble_ok c hw hj (by decide) h1) fun s₁ ⟨v₁, r₁, m₁⟩ => ?_)
  simp only [show c.n = 4 from rfl] at v₁
  generalize ha : (wordsVal s.mem base (c.sl K) 4 >>> (4 * j)) % 16 = a at v₁
  have ha16 : a < 16 := ha ▸ Nat.mod_lt _ (by decide)
  have hw₁ := hw.of_rest r₁
  refine WP.block_append (WP.mono masks4_ok fun s₂ ⟨v₂, r₂, m₂⟩ => ?_)
  have hw₂ := hw₁.of_rest r₂
  refine wp_addAt (by decide) fun s₄ u₄ => ?_
  have r₄ : Rest [.a0] s₂ s₄ := u₄.rest (by decide)
  have hw₄ := hw₂.of_rest r₄
  have h0 : s₄.gpr .a0 = base + BitVec.ofNat 64 c.jt := by
    rw [u₄.gpr, r₂.gpr _ (by decide), r₁.gpr _ (by decide), hw.s0]
  have hm : ∀ b < 4, s₄.gpr (maskReg b) = maskOf (a.testBit b) := fun b hb => by
    rw [r₄.gpr _ (by
      have : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> decide), v₂ b hb, v₁, BitVec.getLsbD_ofNat]
    simp [show b < 64 by omega]
  refine WP.mono (WP.rdwr (scansJ_ok c (by decide) (by decide) (by decide) (by decide) (by decide) 12
    (Nat.le_refl _) hw₄ h0 hm)) fun s₅ ⟨⟨v₅, O₅, k₅⟩, rd₅, wr₅, sp₅⟩ => ?_
  simp only [show c.jt = 2048 from rfl, show c.sl EX = 1920 from rfl, show c.n = 4 from rfl,
    Nat.reduceMul] at v₅ O₅
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, m₂, m₁]
  rw [m₄] at v₅ O₅
  rw [Nat.mod_eq_of_lt ha16] at v₅
  have he : PtOk base s (ent a) (mul a Q) := hT a (by omega)
  have wv : ∀ b < 3, wordsVal s₅.mem base (1920 + 32 * b) 4 = wordsVal s.mem base (2048 + 96 * a + 32 * b) 4 :=
    fun b hb => wordsVal_of_words 4 fun q hq => by
      rw [show 1920 + 32 * b + 8 * q = 1920 + 8 * (4 * b + q) by omega, v₅ _ (by omega)]
      congr 1; omega
  refine ⟨he.move (wv 0 (by decide)) (wv 1 (by decide)) (wv 2 (by decide)), O₅.mono (Nat.le_refl _) (by omega), ?_⟩
  exact ((r₁.mono (by decide)).trans ((r₂.mono (by decide)).trans ((r₄.mono (by decide)).trans
    ⟨fun r hr => k₅.1 r (fun h => hr ((by decide : ∀ r ∈ treeRegs, r ∈ selRegs) r h)),
      rd₅, wr₅, sp₅⟩)))

/-! ## The windows -/

/-- What the windows read and keep, from `s₀`. -/
structure WFix (base : Addr) (s₀ : State) (Q : Point W) (k : Nat) : Prop where
  kc : KC base s₀
  tab : TabTo base s₀ Q 15
  kk : wordsVal s₀.mem base (c.sl K) 4 = k
  q : onCurve W Q = true

/-- What the windows write. -/
abbrev stepW : List (Nat × Nat) := [(512, 480), (1920, 96), (3840, 256)]

/-- The loop's invariant at `s1 = j`: `R` represents `[k >>> 4 j]Q`. -/
structure WInv (base : Addr) (s₀ s : State) (Q : Point W) (k j : Nat) : Prop where
  ws : WsReg s base
  ctr : s.gpr .s1 = BitVec.ofNat 64 j
  keep : Kc s₀ s
  unch : Unch base stepW s₀.mem s.mem
  rep : PtOk base s (c.pt RX RY RZ) (wpt Q k j)

/-- Slots apart from what a window writes. -/
theorem stepW_far {base : Addr} {m m' : Mem} (U : Unch base stepW m m') {d : Nat}
    (h1 : d + 32 ≤ 512 ∨ 992 ≤ d) (h2 : d + 32 ≤ 1920 ∨ 2016 ≤ d) (h3 : d + 32 ≤ 3840) :
    wordsVal m' base d 4 = wordsVal m base d 4 :=
  U.wordsVal (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega) (by omega)

/-- A window. -/
theorem step_ok (hL : Law W) {base : Addr} {s₀ : State} {Q : Point W} {k : Nat} (hP : WFix base s₀ Q k)
    {j : Nat} (hj1 : 1 ≤ j) (hj : j ≤ 64) {s : State} (hI : WInv base s₀ s Q k j) :
    WP isa (Cfg.step c dblJ0) s fun s' => WInv base s₀ s' Q k (j - 1) := by
  have hn := hI.ws.nowrap
  have hT : TabTo base s Q 15 := hP.tab.of_eq (fun d h1 h2 => stepW_far hI.unch (.inr (by omega))
    (.inr (by omega)) (by omega)) (by decide)
  rw [Cfg.step]
  refine WP.seq (wp_decCounter hj1 hI.ctr fun s₁ u₁ => ?_)
  have hw₁ := hI.ws.of_kc (Kc.of_rest (u₁.rest (ws := [.s1]) (by decide)))
  refine WP.mono (select_ok hw₁ (j := j - 1) (by omega) u₁.gpr
    (hT.of_eq (fun d _ _ => by rw [u₁.mem]) (by decide))) fun s₂ ⟨pE, O₂, r₂⟩ => ?_
  rw [u₁.mem, stepW_far hI.unch (d := c.sl K) (.inr (by decide)) (.inl (by decide)) (by decide), hP.kk] at pE
  rw [u₁.mem] at O₂
  have hw₂ := hw₁.of_rest r₂
  have e₂ : ∀ d, (d + 32 ≤ 512 ∨ 992 ≤ d) → (d + 32 ≤ 1920 ∨ 2016 ≤ d) → d + 32 ≤ 3840 →
      wordsVal s₂.mem base d 4 = wordsVal s₀.mem base d 4 := fun d h1 h2 h3 => by
    rw [O₂.wordsVal (by omega) (by omega), stepW_far hI.unch h1 h2 h3]
  have pR₂ : PtOk base s₂ (c.pt RX RY RZ) (wpt Q k j) :=
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
    fun d h1 h2 => U₃.wordsVal (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega)
      (by omega)
  have pE₃ := pE.of_eq (k₃ _ (by decide) (by decide)) (k₃ _ (by decide) (by decide)) (k₃ _ (by decide) (by decide))
  have hK₃ : KC base s₃ := hK₂.of_eq fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> exact k₃ _ (by decide) (by decide)
  -- `T = R + E`.
  refine WP.seq (WP.mono (addPt_ok hL hw₃ hK₃.ap hK₃.bp (p := c.pt RX RY RZ) (q := c.pt EX EY EZ)
    (o := c.pt TX TY TZ) ⟨by decide, by decide⟩ (by decide) h16 hE pR₃ pE₃) fun s₄ ⟨K₄, U₄, pT⟩ => ?_)
  have hw₄ := hw₃.of_kp K₄
  -- `R = T`.
  refine WP.mono (copyPt_ok hw₄ (o := c.pt RX RY RZ) (p := c.pt TX TY TZ) (by decide) (by decide)
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

/-! ## The body -/

/-- What the body writes. -/
abbrev bodyW : List (Nat × Nat) := [(512, 480), (1920, 96), (2048, 1536), (3840, 256)]

/-- `R = [k]Q`, for `k` at `K`'s slot and `Q` affine in `R`'s first two. -/
theorem body_ok (hL : Law W) {base : Addr} {s : State} (hp : WPre base s) :
    WP isa (Cfg.body c dblJ0) s fun s' => Kc s s' ∧ Unch base bodyW s.mem s'.mem ∧
      PtOk base s' (c.pt RX RY RZ) (mul (wordsVal s.mem base (c.sl K) 4) (qOf base s)) := by
  have hn := hp.ws.nowrap
  have hp0 : 0 < W.p := by decide
  rw [Cfg.body]
  refine WP.seq (WP.mono (build_ok hL hp) fun s₁ ⟨K₁, U₁, hK₁, T₁, e₁⟩ => ?_)
  have hw₁ := hp.ws.of_kp K₁
  refine WP.seq (WP.block_append (WP.mono (copyPt_ok hw₁ (o := c.pt RX RY RZ) (p := c.pt ZERO ONEP ZERO)
    (by decide) (by decide) (by decide) (by decide)) fun s₂ ⟨x₂, y₂, z₂, r₂, U₂⟩ => ?_))
  have hw₂ := hw₁.of_rest r₂
  refine wp_li (imm := 64) (by decide) fun s₃ u₃ => WP.block_nil ?_
  have hw₃ : WsReg s₃ base := hw₂.of_kc (Kc.of_rest (u₃.rest (ws := [.s1]) (by decide)))
  have U₃ : Unch base [(512, 96)] s₁.mem s₃.mem := by rw [u₃.mem]; exact U₂.cover (by decide)
  have k₃ : ∀ d, d + 32 ≤ 512 ∨ 608 ≤ d → d + 32 ≤ 8192 → wordsVal s₃.mem base d 4 = wordsVal s₁.mem base d 4 :=
    fun d h h' => U₃.wordsVal (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; omega)
      (by omega)
  have hP : WFix base s₃ (qOf base s) (wordsVal s.mem base (c.sl K) 4) :=
    ⟨hK₁.of_eq fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> exact k₃ _ (by decide) (by decide),
     T₁.of_eq (fun d h1 h2 => k₃ d (by omega) (by omega)) (by decide),
     by rw [k₃ _ (by decide) (by decide), U₁.wordsVal (by decide) (by decide)], hp.on⟩
  have zv : wordsVal s₁.mem base (c.sl ZERO) 4 = 0 := hK₁.zero
  have ov : wordsVal s₁.mem base (c.sl ONEP) 4 = 2 ^ 256 % W.p := hK₁.onep
  have rx : wordsVal s₃.mem base (c.sl RX) 4 = 0 := by rw [u₃.mem]; exact x₂.trans zv
  have ry : wordsVal s₃.mem base (c.sl RY) 4 = 1 * 2 ^ 256 % W.p := by
    rw [u₃.mem, Nat.one_mul]; exact y₂.trans ov
  have rz : wordsVal s₃.mem base (c.sl RZ) 4 = 0 := by rw [u₃.mem]; exact z₂.trans zv
  have hk : wordsVal s.mem base (c.sl K) 4 < 2 ^ (64 * 4) := wordsVal_lt _ _ _ _
  have hI : WInv base s₃ s₃ (qOf base s) (wordsVal s.mem base (c.sl K) 4) 64 := by
    refine ⟨hw₃, u₃.gpr, ⟨fun _ _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [show (64 : Nat) = 16 * 4 from rfl, wpt_top _ hk]
      show Rep W (tmv W 4 base s₃ (c.sl RX)) (tmv W 4 base s₃ (c.sl RY)) (tmv W 4 base s₃ (c.sl RZ)) _
      simp only [tmv]
      rw [rx, ry, rz, toM_zero, Nat.one_mul, toM_one unit]
      exact rep_infinity' hL
    · show wordsVal _ _ (c.sl RX) 4 < _; rw [rx]; exact hp0
    · show wordsVal _ _ (c.sl RY) 4 < _; rw [ry]; exact Nat.mod_lt _ hp0
    · show wordsVal _ _ (c.sl RZ) 4 < _; rw [rz]; exact hp0
  refine countLoop_ok (Inv := fun j s' => WInv base s₃ s' (qOf base s) (wordsVal s.mem base (c.sl K) 4) j)
    (n := 64) (fun j s' hi => hi.ctr) (fun j s' h1 h2 hi => step_ok hL hP h1 h2 hi) (fun s' hi => ?_)
    (by decide) (by decide) hI
  refine ⟨(K₁.kc.trans (Kc.of_rest ((r₂.mono (by decide)).trans (u₃.rest (ws := [.t0, .s1]) (by decide))))).trans
    hi.keep, ((U₁.trans U₃).trans hi.unch).cover (by decide), ?_⟩
  rw [← wpt_zero]
  exact hi.rep

end VG.Proof.Ecdsa.RISCV64.Secp256k1.Window
