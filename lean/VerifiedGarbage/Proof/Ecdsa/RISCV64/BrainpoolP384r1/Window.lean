module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.WindowA
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP384r1.Joint
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.WindowA
public import VerifiedGarbage.Proof.Weierstrass.JacDblA
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Weierstrass.PointFacts
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
import VerifiedGarbage.Proof.Ecdh.RISCV64.Masks
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes

/-!
# `vg_brainpoolp384r1_mul` by four-bit windows on RISC-V: the body

`WindowA.Cfg.body brainpoolp384r1 dblJa` leaves in `R` a representative of
`[k]Q` (`body_ok`), for `k` at `K`'s slot and `Q` affine in `R`'s first two:

* `quad_ok`: `R = 16 R`: `R`'s representative of `P` into Jacobian
  coordinates stands for `P` (`InvJ.of_toJ`), each doubling `dblJa` of the
  curve's `a` doubles it (`InvJ.dblA'`), and back in projective coordinates,
  with `Y = 1` where `Z` is zero, it is a representative of `16 P` again
  (`InvJ.out`);
* `build_ok`: the table of `[e]Q` from byte 4096, stored through `a6` as
  verification's is (the joint ladder's `PtOk`, `addPt_ok`);
* `select_ok`: the nibble's entry to `E`, by verification's selection;
* `step_ok`, `body_ok`: the windows, from `R = O`.
-/

@[expose] public section

-- `p`, below `2^384`, is evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.Ecdsa.RISCV64.BrainpoolP384r1.Window

open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.WindowA
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.BrainpoolP384r1 (W field_ok unit)
open VG.Proof.Ecdsa.RISCV64.BrainpoolP384r1.Joint (PtOk addPt_ok addW keepU jSl)
open VG.Proof.Ecdsa.RISCV64.WindowA
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Point Fe mul onCurve)
open VG.Impl.Ecdsa.RISCV64.Window (windows)

/-- The curve as the code has it. -/
abbrev c : Cfg := brainpoolp384r1

/-! ## The slots -/

/-- The slots of `R = 16 R`'s arithmetic. -/
abbrev wSl : List Nat :=
  [c.sl AP, c.sl B3P, c.sl ZERO, c.sl T0, c.sl T1, c.sl T2, c.sl T3, c.sl T4, c.sl T5,
    c.sl RX, c.sl RY, c.sl RZ, c.sl DX, c.sl DY, c.sl DZ, c.sl TX, c.sl TY, c.sl TZ]

theorem wLay : Lay c.MP' (own 6) (· ∈ wSl) :=
  ⟨by decide, fun x y hx hy => (by decide : ∀ x ∈ wSl, ∀ y ∈ wSl, x ≠ y → x + 8 * 6 ≤ y ∨ y + 8 * 6 ≤ x)
    x hx y hy, by decide, by decide⟩

theorem wShort : Short (· ∈ wSl) := by decide

/-- The slots the windows' complete additions and Jacobian doublings use. -/
abbrev S : RcbSlots := Cfg.rcbSlots c

/-- What the field operations of `R = 16 R` write: `R`, `D`, `T`, the
temporaries and the functions' own working space. -/
abbrev quadW : List (Nat × Nat) := [(736, 720), (3712, 384)]

/-- The slots they write. -/
abbrev quadWl : List Nat :=
  [c.sl T0, c.sl T1, c.sl T2, c.sl T3, c.sl T4, c.sl T5, c.sl RX, c.sl RY, c.sl RZ,
    c.sl DX, c.sl DY, c.sl DZ, c.sl TX, c.sl TY, c.sl TZ]

/-- The constants the windows read. -/
structure KC (base : Addr) (s : State) : Prop where
  ap : wordsVal s.mem base (c.sl AP) 6 = W.a * 2 ^ 384 % W.p
  bp : wordsVal s.mem base (c.sl B3P) 6 = 3 * W.b * 2 ^ 384 % W.p
  zero : wordsVal s.mem base (c.sl ZERO) 6 = 0
  onep : wordsVal s.mem base (c.sl ONEP) 6 = 2 ^ 384 % W.p

theorem KC.of_eq {base : Addr} {s s' : State} (h : KC base s)
    (e : ∀ d ∈ [c.sl AP, c.sl B3P, c.sl ZERO, c.sl ONEP], wordsVal s'.mem base d 6 = wordsVal s.mem base d 6) :
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
    (hI : Inv 6 base W.p (· ∈ wSl) V E s) (hV : ∀ x ∈ rcbR S p p, x ∈ V)
    (ha : E (c.sl AP) = Fin.ofNat W.p W.a) {P : Point W}
    (hP : onCurve W P = true) (hJ : InvJ W (E p.x) (E p.y) (E p.z) P) :
    WP isa (fprog brainpoolp384r1Field (dblJa S p o)) s fun s' => KeepR 6 base (rcbW S o) s s' ∧
      ∃ E', Inv 6 base W.p (· ∈ wSl) ([o.x, o.y, o.z] ++ V) E' s' ∧ InvJ W (E' o.x) (E' o.y) (E' o.z) (d2 P) ∧
        ∀ x, x ∉ rcbW S o → E' x = E x := by
  rw [dblJa_eq]
  refine WP.mono (ofN_ok (F := brainpoolp384r1Field) field_ok rfl wLay wShort unit dblJaN_ok hA hsl hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, InvJ.dblA' hL hP hJ ha (v.trans (dblJaN_run _)), kp⟩

/-- `R` into Jacobian coordinates in `D`. -/
theorem toJStep_ok (hL : Law W) {base : Addr} {s : State} {V : List Nat} {E : Nat → Fe W}
    (hI : Inv 6 base W.p (· ∈ wSl) V E s) (hV : ∀ x ∈ rcbR S (c.pt RX RY RZ) (Cfg.zeroPt c), x ∈ V) {P : Point W}
    (hR : Rep W (E (c.sl RX)) (E (c.sl RY)) (E (c.sl RZ)) P) (hz : E (c.sl ZERO) = 0) :
    WP isa (fprog brainpoolp384r1Field (toJ S (c.pt RX RY RZ) (Cfg.zeroPt c) (c.pt DX DY DZ))) s fun s' =>
      KeepR 6 base (rcbW S (c.pt DX DY DZ)) s s' ∧
      ∃ E', Inv 6 base W.p (· ∈ wSl) ([c.sl DX, c.sl DY, c.sl DZ] ++ V) E' s' ∧
        InvJ W (E' (c.sl DX)) (E' (c.sl DY)) (E' (c.sl DZ)) P ∧
        ∀ x, x ∉ rcbW S (c.pt DX DY DZ) → E' x = E x := by
  rw [toJ_eq]
  refine WP.mono (ofN_ok (F := brainpoolp384r1Field) field_ok rfl wLay wShort unit toJN_ok toJ_apart (by decide) hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, InvJ.of_toJ hL hR hz (v.trans (toJN_run _)), kp⟩

/-- `D` back in projective coordinates in `R`. -/
theorem fromJStep_ok {base : Addr} {s : State} {V : List Nat} {E : Nat → Fe W}
    (hI : Inv 6 base W.p (· ∈ wSl) V E s) (hV : ∀ x ∈ rcbR S (c.pt DX DY DZ) (Cfg.zeroPt c), x ∈ V) :
    WP isa (fprog brainpoolp384r1Field (fromJ S (c.pt DX DY DZ) (Cfg.zeroPt c) (c.pt RX RY RZ))) s fun s' =>
      KeepR 6 base (rcbW S (c.pt RX RY RZ)) s s' ∧
      ∃ E', Inv 6 base W.p (· ∈ wSl) ([c.sl RX, c.sl RY, c.sl RZ] ++ V) E' s' ∧
        (E' (c.sl RX), E' (c.sl RY), E' (c.sl RZ)) =
          (E (c.sl DX) * E (c.sl DZ), E (c.sl DY) + E (c.sl ZERO),
            E (c.sl DZ) * E (c.sl DZ) * E (c.sl DZ)) ∧
        ∀ x, x ∉ rcbW S (c.pt RX RY RZ) → E' x = E x := by
  rw [fromJ_eq]
  refine WP.mono (ofN_ok (F := brainpoolp384r1Field) field_ok rfl wLay wShort unit fromJN_ok fromJ_apart (by decide) hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, v.trans (fromJN_run _), kp⟩

/-- `R = 16 R`, for `R` representing `P`. -/
theorem quad_ok (hL : Law W) {base : Addr} {s : State} (hw : WsReg s base) (hK : KC base s) {P : Point W}
    (hP : onCurve W P = true) (hR : PtOk base s (c.pt RX RY RZ) P) :
    WP isa (Cfg.quad c dblJa) s fun s' => Kp s s' ∧ Unch base quadW s.mem s'.mem ∧
      PtOk base s' (c.pt RX RY RZ) (d16 P) := by
  have hp0 : 0 < W.p := by decide
  have hn := hw.nowrap
  rw [Cfg.quad]
  simp only [progs]
  -- The start: `a`, `b`, zero and `R`.
  have hI : Inv 6 base W.p (· ∈ wSl) [c.sl AP, c.sl B3P, c.sl ZERO, c.sl RX, c.sl RY, c.sl RZ]
      (fun x => toM W.p (2 ^ (64 * 6)) (wordsVal s.mem base x 6)) s := by
    refine ⟨hw, by decide, fun x hx => ?_, fun x _ => rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hK.ap]; exact Nat.mod_lt _ hp0
    · rw [hK.bp]; exact Nat.mod_lt _ hp0
    · rw [hK.zero]; exact hp0
    exacts [hR.x, hR.y, hR.z]
  have e0 : toM W.p (2 ^ (64 * 6)) (wordsVal s.mem base (c.sl ZERO) 6) = 0 := by
    rw [hK.zero]; exact toM_zero _ _
  have ea : toM W.p (2 ^ (64 * 6)) (wordsVal s.mem base (c.sl AP) 6) = Fin.ofNat W.p W.a := by
    rw [hK.ap, toM_mont unit]
  -- To Jacobian coordinates.
  refine WP.seq (WP.mono (toJStep_ok hL hI (by decide) hR.rep e0) fun s₁ ⟨k₁, E₁, I₁, J₁, p₁⟩ => ?_)
  have a₁ : E₁ (c.sl AP) = Fin.ofNat W.p W.a := (p₁ _ (by decide)).trans ea
  -- Four doublings.
  refine WP.seq (WP.mono (dblStep_ok hL dbl_apart_DT (by decide) I₁ (by decide) a₁ hP J₁)
    fun s₂ ⟨k₂, E₂, I₂, J₂, p₂⟩ => ?_)
  have a₂ : E₂ (c.sl AP) = Fin.ofNat W.p W.a := (p₂ _ (by decide)).trans a₁
  refine WP.seq (WP.mono (dblStep_ok hL dbl_apart_TD (by decide) I₂ (by decide) a₂ (hL.onCurve_add hP hP) J₂)
    fun s₃ ⟨k₃, E₃, I₃, J₃, p₃⟩ => ?_)
  have a₃ : E₃ (c.sl AP) = Fin.ofNat W.p W.a := (p₃ _ (by decide)).trans a₂
  have h4 := hL.onCurve_add (hL.onCurve_add hP hP) (hL.onCurve_add hP hP)
  refine WP.seq (WP.mono (dblStep_ok hL dbl_apart_DT (by decide) I₃ (by decide) a₃ h4 J₃)
    fun s₄ ⟨k₄, E₄, I₄, J₄, p₄⟩ => ?_)
  have a₄ : E₄ (c.sl AP) = Fin.ofNat W.p W.a := (p₄ _ (by decide)).trans a₃
  refine WP.seq (WP.mono (dblStep_ok hL dbl_apart_TD (by decide) I₄ (by decide) a₄ (hL.onCurve_add h4 h4) J₄)
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
  have vx' : tmv W 6 base s₆ (c.sl RX) = E₆ (c.sl RX) := I₆.val (c.sl RX) (by decide)
  have vy' : tmv W 6 base s₆ (c.sl RY) = E₆ (c.sl RY) := I₆.val (c.sl RY) (by decide)
  have vz' : tmv W 6 base s₆ (c.sl RZ) = E₆ (c.sl RZ) := I₆.val (c.sl RZ) (by decide)
  -- `Y = 1` where `Z = 0`.
  have KK : KeepR 6 base quadWl s s₆ :=
    ((((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans ((k₃.mono (by decide)).trans
      (k₄.mono (by decide)))).trans ((k₅.mono (by decide)).trans (k₆.mono (by decide))))
  have UK : Unch base (quadWl.map (fun w => (w, 8 * 6)) ++ [(own 6, 64 * 6)]) s.mem s₆.mem := KK.mem
  have onep₆ : wordsVal s₆.mem base (c.sl ONEP) 6 = 2 ^ 384 % W.p := by
    rw [UK.wordsVal (by decide) (by decide)]; exact hK.onep
  refine WP.block_append (WP.mono (zeroMask_ok hw₆ (n := 6) (a := c.sl RZ) (by decide) (by decide))
    fun s₇ ⟨r₇, m₇, a7₇⟩ => ?_)
  have hw₇ := hw₆.of_rest r₇
  refine WP.mono (sel_ok (decide (wordsVal s₆.mem base (c.sl RZ) 6 = 0)) 6 hw₇ a7₇
    (o := c.sl RY) (a := c.sl RY) (b := c.sl ONEP) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (Or.inl (Nat.le_refl _)) (by decide)) fun s₈ ⟨e₈, r₈, O₈⟩ => ?_
  rw [m₇] at e₈ O₈
  have ex : wordsVal s₈.mem base (c.sl RX) 6 = wordsVal s₆.mem base (c.sl RX) 6 :=
    O₈.wordsVal (by decide) (by decide)
  have ez : wordsVal s₈.mem base (c.sl RZ) 6 = wordsVal s₆.mem base (c.sl RZ) 6 :=
    O₈.wordsVal (by decide) (by decide)
  have hZ : (wordsVal s₆.mem base (c.sl RZ) 6 = 0) ↔ E₅ (c.sl DZ) = 0 := by
    rw [← toM_eq_zero_iff unit ltz]
    show tmv W 6 base s₆ (c.sl RZ) = 0 ↔ _
    rw [vz', vz]
    exact ⟨fun h => by_contra fun hz => cube_ne_zero hL hz h, fun h => by rw [h]; grind⟩
  have hrep := InvJ.out hL J₅
  refine ⟨KK.kp.trans ((Kp.of_rest r₇).trans (Kp.of_rest r₈)), (UK.trans O₈.unch).cover (by decide), ⟨?_, ?_, ?_, ?_⟩⟩
  · show Rep W (tmv W 6 base s₈ (c.sl RX)) (tmv W 6 base s₈ (c.sl RY)) (tmv W 6 base s₈ (c.sl RZ)) _
    simp only [tmv]
    rw [ex, ez]
    show Rep W (tmv W 6 base s₆ (c.sl RX)) _ (tmv W 6 base s₆ (c.sl RZ)) _
    rw [vx', vz', vx, vz, e₈]
    by_cases h0 : E₅ (c.sl DZ) = 0
    · have hc : decide (wordsVal s₆.mem base (c.sl RZ) 6 = 0) = true := decide_eq_true (hZ.mpr h0)
      have h0' : E₅ (c.pt DX DY DZ).z = 0 := h0
      rw [show (if E₅ (c.pt DX DY DZ).z = 0 then (1 : Fe W) else E₅ (c.pt DX DY DZ).y) = 1 from
        by simp [h0']] at hrep
      simp only [hc, ↓reduceIte]
      rw [onep₆, toM_one unit]
      exact hrep
    · have hc : decide (wordsVal s₆.mem base (c.sl RZ) 6 = 0) = false :=
        decide_eq_false fun h => h0 (hZ.mp h)
      have h0' : ¬E₅ (c.pt DX DY DZ).z = 0 := h0
      rw [show (if E₅ (c.pt DX DY DZ).z = 0 then (1 : Fe W) else E₅ (c.pt DX DY DZ).y) =
        E₅ (c.pt DX DY DZ).y from by simp [h0']] at hrep
      simp only [hc, ↓reduceIte, Bool.false_eq_true]
      show Rep W _ (tmv W 6 base s₆ (c.sl RY)) _ _
      rw [vy', vy]
      exact hrep
  · show wordsVal s₈.mem base (c.sl RX) 6 < W.p
    rw [ex]; exact ltx
  · show wordsVal s₈.mem base (c.sl RY) 6 < W.p
    rw [e₈]; split
    · rw [onep₆]; exact Nat.mod_lt _ (by decide)
    · exact lty
  · show wordsVal s₈.mem base (c.sl RZ) 6 < W.p
    rw [ez]; exact ltz

/-! ## The table -/

/-- Entry `e`'s slots. -/
abbrev ent (e : Nat) : Pt := ⟨4096 + 144 * e, 4096 + 144 * e + 48, 4096 + 144 * e + 96⟩

/-- The table up to entry `m`: `[e]Q` in entry `e`. -/
abbrev TabTo (base : Addr) (s : State) (Q : Point W) (m : Nat) : Prop := ∀ e ≤ m, PtOk base s (ent e) (mul e Q)

theorem TabTo.of_eq {base : Addr} {s s' : State} {Q : Point W} {m : Nat} (h : TabTo base s Q m)
    (he : ∀ d, 4096 ≤ d → d + 48 ≤ 6400 → wordsVal s'.mem base d 6 = wordsVal s.mem base d 6) (hm : m ≤ 15) :
    TabTo base s' Q m :=
  fun e hlt => (h e hlt).of_eq (he (4096 + 144 * e) (by omega) (by omega))
    (he (4096 + 144 * e + 48) (by omega) (by omega)) (he (4096 + 144 * e + 96) (by omega) (by omega))

/-- `o = p`, the three coordinates one after the other, for `o`'s slots in
order and `p`'s apart from them all. -/
theorem copyPt_ok {s : State} {base : Addr} (hw : WsReg s base) {o p : Pt}
    (h8 : ∀ x ∈ [o.x, o.y, o.z, p.x, p.y, p.z], x % 8 = 0 ∧ x + 48 ≤ 4096)
    (hxy : o.x + 48 ≤ o.y) (hyz : o.y + 48 ≤ o.z)
    (hp : ∀ a ∈ [p.x, p.y, p.z], a + 48 ≤ o.x ∨ o.z + 48 ≤ a) :
    WP isa (.block (Cfg.copyPt c o p)) s fun s' =>
      wordsVal s'.mem base o.x 6 = wordsVal s.mem base p.x 6 ∧ wordsVal s'.mem base o.y 6 = wordsVal s.mem base p.y 6 ∧
      wordsVal s'.mem base o.z 6 = wordsVal s.mem base p.z 6 ∧ Rest [.t0] s s' ∧
      Unch base [(o.x, 48), (o.y, 48), (o.z, 48)] s.mem s'.mem := by
  have hn := hw.nowrap
  have g := fun x hx => h8 x hx
  have gp := fun x hx => hp x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g gp
  obtain ⟨⟨ox8, ox⟩, ⟨oy8, oy⟩, ⟨oz8, oz⟩, ⟨px8, px⟩, ⟨py8, py⟩, ⟨pz8, pz⟩⟩ := g
  obtain ⟨hpx, hpy, hpz⟩ := gp
  rw [Cfg.copyPt, show c.n = 6 from rfl, List.append_assoc]
  refine WP.block_append (WP.mono (copy_ok 6 hw (o := o.x) (a := p.x) ox8 px8 (by omega) (by omega) (by omega))
    fun s₁ ⟨e₁, r₁, O₁⟩ => ?_)
  have hw₁ := hw.of_rest r₁
  refine WP.block_append (WP.mono (copy_ok 6 hw₁ (o := o.y) (a := p.y) oy8 py8 (by omega) (by omega) (by omega))
    fun s₂ ⟨e₂, r₂, O₂⟩ => ?_)
  have hw₂ := hw₁.of_rest r₂
  refine WP.mono (copy_ok 6 hw₂ (o := o.z) (a := p.z) oz8 pz8 (by omega) (by omega) (by omega))
    fun s₃ ⟨e₃, r₃, O₃⟩ => ⟨?_, ?_, ?_, (r₁.trans r₂).trans r₃ |>.mono (by simp), ?_⟩
  · rw [O₃.wordsVal (by omega) (by omega), O₂.wordsVal (by omega) (by omega), e₁]
  · rw [O₃.wordsVal (by omega) (by omega), e₂, O₁.wordsVal (by omega) (by omega)]
  · rw [e₃, O₂.wordsVal (by omega) (by omega), O₁.wordsVal (by omega) (by omega)]
  · exact ((O₁.unch.trans O₂.unch).trans O₃.unch).mono (by simp)

/-- `D`'s slots, as `copyPt` writes them. -/
theorem dSl : ∀ w ∈ ([((c.pt DX DY DZ).x, 48), ((c.pt DX DY DZ).y, 48), ((c.pt DX DY DZ).z, 48)] : List (Nat × Nat)),
    880 ≤ w.1 ∧ w.1 + w.2 ≤ 1024 := by decide

/-- A point in slots below byte 4095 to entry `e`. -/
theorem store_ok {s : State} {base : Addr} (hw : WsReg s base) {e : Nat} (he : e < 16) {p : Pt}
    (hs : ∀ x ∈ [p.x, p.y, p.z], x % 8 = 0 ∧ x + 48 ≤ 4095) {P : Point W} (hp : PtOk base s p P) :
    WP isa (.block (Verify.Cfg.storePt c e p)) s fun s' => PtOk base s' (ent e) P ∧ Rest [.t0, .a6] s s' ∧
      Outside base (4096 + 144 * e) 144 s.mem s'.mem := by
  have hn := hw.nowrap
  have g := fun x hx => hs x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g
  obtain ⟨⟨hx8, hx⟩, ⟨hy8, hy⟩, ⟨hz8, hz⟩⟩ := g
  refine WP.mono (Joint.storePt_ok c hw (e := e) (by decide) (by show 4096 + 144 * e + 144 ≤ 8192; omega)
    (by show 144 * e + 144 ≤ 4095; omega) ⟨hx8, by show _ + 48 ≤ 4095; omega, by show _ + 48 ≤ 4096; omega⟩
    ⟨hy8, by show _ + 48 ≤ 4095; omega, by show _ + 48 ≤ 4096; omega⟩
    ⟨hz8, by show _ + 48 ≤ 4095; omega, by show _ + 48 ≤ 4096; omega⟩) fun s' ⟨ex, ey, ez, r, O⟩ => ?_
  simp only [show c.jt = 4096 from rfl, show Verify.Cfg.jb c = 144 from rfl, show c.n = 6 from rfl,
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
abbrev addsW : List (Nat × Nat) := [(880, 576), (4096, 2304), (3712, 384)]

/-- An addition's writes into `T`, within `addsW`, and apart from the table. -/
theorem addW_T : ∀ w ∈ addW (c.pt TX TY TZ), (∃ w' ∈ addsW, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2) ∧
    (w.1 + w.2 ≤ 4096 ∨ 6400 ≤ w.1) := by decide

/-- `copyPt`'s writes into `D`, within `addsW`. -/
theorem dW : ∀ w ∈ ([((c.pt DX DY DZ).x, 48), ((c.pt DX DY DZ).y, 48), ((c.pt DX DY DZ).z, 48)] : List (Nat × Nat)),
    ∃ w' ∈ addsW, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := by decide

/-- Entry `e`'s bytes, within `addsW`. -/
theorem entW {e : Nat} (he : e < 16) : ∃ w' ∈ addsW, w'.1 ≤ 4096 + 144 * e ∧ 4096 + 144 * e + 144 ≤ w'.1 + w'.2 :=
  ⟨(4096, 2304), List.mem_cons_of_mem _ List.mem_cons_self, by simp only; omega, by simp only; omega⟩

/-- Entry `e`, kept by memory unchanged there. -/
theorem ent_of {base : Addr} {s s' : State} {e : Nat} {P : Point W} (h : PtOk base s (ent e) P)
    (k : ∀ d, 4096 + 144 * e ≤ d → d + 48 ≤ 4096 + 144 * e + 144 → wordsVal s'.mem base d 6 = wordsVal s.mem base d 6) :
    PtOk base s' (ent e) P :=
  h.of_eq (k (4096 + 144 * e) (Nat.le_refl _) (by omega)) (k (4096 + 144 * e + 48) (by omega) (by omega))
    (k (4096 + 144 * e + 96) (by omega) (by omega))

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
    have e₂ : ∀ d ∈ [c.sl AP, c.sl B3P, c.sl ZERO, c.sl ONEP] ++ [c.sl RX, c.sl RY], wordsVal s₂.mem base d 6 =
        wordsVal s₁.mem base d 6 := keepU U₂ (by decide)
    have far₂ : ∀ d, 4096 ≤ d → d + 48 ≤ 6400 → wordsVal s₂.mem base d 6 = wordsVal s₁.mem base d 6 :=
      fun d h1 h2 => U₂.wordsVal (fun w hw => by have := (addW_T w hw).2; omega) (by omega)
    -- Stored to entry `m + 2`.
    refine WP.block_append (WP.mono (store_ok hw₂ (e := m + 2) (by omega) (by decide) p₂)
      fun s₃ ⟨p₃, r₃, O₃⟩ => ?_)
    have hw₃ := hw₂.of_rest r₃
    have e₃ : ∀ d, d + 48 ≤ 4095 → wordsVal s₃.mem base d 6 = wordsVal s₂.mem base d 6 := fun d hd =>
      O₃.wordsVal (by omega) (by omega)
    have pT₃ : PtOk base s₃ (c.pt TX TY TZ) (mul (m + 2) Q) :=
      p₂.of_eq (e₃ _ (by decide)) (e₃ _ (by decide)) (e₃ _ (by decide))
    -- `D = T`.
    refine WP.mono (copyPt_ok hw₃ (o := c.pt DX DY DZ) (p := c.pt TX TY TZ) (by decide) (by decide) (by decide)
      (by decide)) fun s₄ ⟨x₄, y₄, z₄, r₄, U₄⟩ => ?_
    have e₄ : ∀ d, (d + 48 ≤ 880 ∨ 1024 ≤ d) → d + 48 ≤ 8192 → wordsVal s₄.mem base d 6 = wordsVal s₃.mem base d 6 :=
      fun d h1 h2 => U₄.wordsVal (fun w hw => by have := dSl w hw; omega) (by omega)
    have kd : ∀ d ∈ [c.sl AP, c.sl B3P, c.sl ZERO, c.sl ONEP] ++ [c.sl RX, c.sl RY],
        wordsVal s₄.mem base d 6 = wordsVal s₁.mem base d 6 := fun d hd => by
      have hd' : d + 48 ≤ 880 := (by decide : ∀ d ∈ [c.sl AP, c.sl B3P, c.sl ZERO, c.sl ONEP] ++ [c.sl RX, c.sl RY],
        d + 48 ≤ 880) d hd
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
abbrev qOf (base : Addr) (s : State) : Point W := .affine (tmv W 6 base s (c.sl RX)) (tmv W 6 base s (c.sl RY))

/-- What the table's construction writes. -/
abbrev buildW : List (Nat × Nat) := [(880, 576), (4096, 2304), (3712, 384)]

/-- What `vg_brainpoolp384r1_mul`'s body reads at the start. -/
structure WPre (base : Addr) (s : State) : Prop where
  ws : WsReg s base
  kc : KC base s
  x : wordsVal s.mem base (c.sl RX) 6 < W.p
  y : wordsVal s.mem base (c.sl RY) 6 < W.p
  on : onCurve W (qOf base s) = true

/-- The table of `[e]Q`. -/
theorem build_ok (hL : Law W) {base : Addr} {s : State} (hp : WPre base s) :
    WP isa (Cfg.build c) s fun s' => Kp s s' ∧ Unch base buildW s.mem s'.mem ∧ KC base s' ∧
      TabTo base s' (qOf base s) 15 ∧
      ∀ d, d + 48 ≤ 880 → wordsVal s'.mem base d 6 = wordsVal s.mem base d 6 := by
  have hw := hp.ws
  have hn := hw.nowrap
  have hp0 : 0 < W.p := by decide
  have hK := hp.kc
  have h1 : tmv W 6 base s (c.sl ONEP) = 1 := by
    simp only [tmv]; rw [hK.onep]; exact toM_one unit
  have h0 : tmv W 6 base s (c.sl ZERO) = 0 := by
    simp only [tmv]; rw [hK.zero]; exact toM_zero _ _
  have pO : PtOk base s (c.pt ZERO ONEP ZERO) (mul 0 (qOf base s)) := by
    refine ⟨?_, show wordsVal _ _ (c.sl ZERO) 6 < _ by rw [hK.zero]; exact hp0,
      show wordsVal _ _ (c.sl ONEP) 6 < _ by rw [hK.onep]; exact Nat.mod_lt _ hp0,
      show wordsVal _ _ (c.sl ZERO) 6 < _ by rw [hK.zero]; exact hp0⟩
    show Rep W (tmv W 6 base s (c.sl ZERO)) (tmv W 6 base s (c.sl ONEP)) (tmv W 6 base s (c.sl ZERO)) _
    rw [h0, h1, Joint.mul_zero']
    exact rep_infinity' hL
  have pQ : PtOk base s (c.pt RX RY ONEP) (qOf base s) := by
    refine ⟨?_, hp.x, hp.y, show wordsVal _ _ (c.sl ONEP) 6 < _ by rw [hK.onep]; exact Nat.mod_lt _ hp0⟩
    show Rep W (tmv W 6 base s (c.sl RX)) (tmv W 6 base s (c.sl RY)) (tmv W 6 base s (c.sl ONEP)) _
    rw [h1]
    exact rep_affine' hL _ _
  rw [Cfg.build, List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (store_ok hw (e := 0) (by decide) (by decide) pO)
    fun s₁ ⟨p₁, r₁, O₁⟩ => ?_))
  have hw₁ := hw.of_rest r₁
  have e₁ : ∀ d, d + 48 ≤ 4095 → wordsVal s₁.mem base d 6 = wordsVal s.mem base d 6 := fun d hd =>
    O₁.wordsVal (by omega) (by omega)
  refine WP.block_append (WP.mono (store_ok hw₁ (e := 1) (by decide) (by decide)
    (pQ.of_eq (e₁ _ (by decide)) (e₁ _ (by decide)) (e₁ _ (by decide)))) fun s₂ ⟨p₂, r₂, O₂⟩ => ?_)
  have hw₂ := hw₁.of_rest r₂
  have e₂ : ∀ d, d + 48 ≤ 4095 → wordsVal s₂.mem base d 6 = wordsVal s.mem base d 6 := fun d hd => by
    rw [O₂.wordsVal (by omega) (by omega), e₁ d hd]
  refine WP.mono (copyPt_ok hw₂ (o := c.pt DX DY DZ) (p := c.pt RX RY ONEP) (by decide) (by decide) (by decide)
    (by decide)) fun s₃ ⟨x₃, y₃, z₃, r₃, U₃⟩ => ?_
  have hw₃ := hw₂.of_rest r₃
  have e₃ : ∀ d, (d + 48 ≤ 880 ∨ 1024 ≤ d) → d + 48 ≤ 8192 → wordsVal s₃.mem base d 6 = wordsVal s₂.mem base d 6 :=
    fun d h1 h2 => U₃.wordsVal (fun w hw => by have := dSl w hw; omega) (by omega)
  have pQ₃ : PtOk base s₃ (c.pt RX RY ONEP) (qOf base s) :=
    pQ.of_eq ((e₃ _ (.inl (by decide)) (by decide)).trans (e₂ _ (by decide)))
      ((e₃ _ (.inl (by decide)) (by decide)).trans (e₂ _ (by decide)))
      ((e₃ _ (.inl (by decide)) (by decide)).trans (e₂ _ (by decide)))
  have hA : AI base s₃ (qOf base s) 0 := by
    refine ⟨hw₃, hK.of_eq fun d hd => ?_, fun e he => ?_, ?_, pQ₃⟩
    · have hd' : d + 48 ≤ 880 := by
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
    · subst hw; exact ⟨(4096, 2304), by simp, by decide, by decide⟩
    · subst hw; exact ⟨(4096, 2304), by simp, by decide, by decide⟩
    · rcases hw with rfl | rfl | rfl <;> exact ⟨(880, 576), by simp, by decide, by decide⟩
    · exact ⟨w, by simpa using hw, Nat.le_refl _, Nat.le_refl _⟩
  · intro d hd
    rw [U₄.wordsVal (by simp; omega) (by omega), e₃ d (.inl hd) (by omega), e₂ d (by omega)]

/-! ## The nibble's entry -/

open VG.Proof.Ecdsa.RISCV64.Joint (scansJ_ok masks4_ok wordsVal_of_words wp_addAt) in
open VG.Proof.Ecdsa.RISCV64.BrainpoolP384r1.Joint (selRegs) in
open VG.Impl.Ecdsa.RISCV64.Comb (maskReg treeRegs) in
/-- The window's entry `[k_j]Q` to `E`. -/
theorem select_ok {s : State} {base : Addr} (hw : WsReg s base) {j : Nat} (hj : j < 96)
    (h1 : s.gpr .s1 = BitVec.ofNat 64 j) {Q : Point W} (hT : TabTo base s Q 15) :
    WP isa (.block (Cfg.select c)) s fun s' =>
      PtOk base s' (c.pt c.EX c.EY c.EZ) (mul ((wordsVal s.mem base (c.sl K) 6 >>> (4 * j)) % 16) Q) ∧
      Outside base 2848 144 s.mem s'.mem ∧ Rest selRegs s s' := by
  have hn := hw.nowrap
  rw [Cfg.select]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (nibble_ok c hw hj (by decide) h1) fun s₁ ⟨v₁, r₁, m₁⟩ => ?_)
  simp only [show c.n = 6 from rfl] at v₁
  generalize ha : (wordsVal s.mem base (c.sl K) 6 >>> (4 * j)) % 16 = a at v₁
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
  refine WP.mono (WP.rdwr (scansJ_ok c (by decide) (by decide) (by decide) (by decide) (by decide) 18
    (Nat.le_refl _) hw₄ h0 hm)) fun s₅ ⟨⟨v₅, O₅, k₅⟩, rd₅, wr₅, sp₅⟩ => ?_
  simp only [show c.jt = 4096 from rfl, show c.sl c.EX = 2848 from rfl, show c.n = 6 from rfl,
    Nat.reduceMul] at v₅ O₅
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, m₂, m₁]
  rw [m₄] at v₅ O₅
  rw [Nat.mod_eq_of_lt ha16] at v₅
  have he : PtOk base s (ent a) (mul a Q) := hT a (by omega)
  have wv : ∀ b < 3, wordsVal s₅.mem base (2848 + 48 * b) 6 = wordsVal s.mem base (4096 + 144 * a + 48 * b) 6 :=
    fun b hb => wordsVal_of_words 6 fun q hq => by
      rw [show 2848 + 48 * b + 8 * q = 2848 + 8 * (6 * b + q) by omega, v₅ _ (by omega)]
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
  kk : wordsVal s₀.mem base (c.sl K) 6 = k
  q : onCurve W Q = true

/-- What the windows write. -/
abbrev stepW : List (Nat × Nat) := [(736, 720), (2848, 144), (3712, 384)]

/-- The loop's invariant at `s1 = j`: `R` represents `[k >>> 4 j]Q`. -/
structure WInv (base : Addr) (s₀ s : State) (Q : Point W) (k j : Nat) : Prop where
  ws : WsReg s base
  ctr : s.gpr .s1 = BitVec.ofNat 64 j
  keep : Kc s₀ s
  unch : Unch base stepW s₀.mem s.mem
  rep : PtOk base s (c.pt RX RY RZ) (wpt Q k j)

/-- Slots apart from what a window writes. -/
theorem stepW_far {base : Addr} {m m' : Mem} (U : Unch base stepW m m') {d : Nat}
    (h1 : d + 48 ≤ 736 ∨ 1456 ≤ d) (h2 : d + 48 ≤ 2848 ∨ 2992 ≤ d) (h3 : d + 48 ≤ 3712 ∨ 4096 ≤ d ∧ d + 48 ≤ 8192) :
    wordsVal m' base d 6 = wordsVal m base d 6 :=
  U.wordsVal (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega) (by omega)

/-- A window. -/
theorem step_ok (hL : Law W) {base : Addr} {s₀ : State} {Q : Point W} {k : Nat} (hP : WFix base s₀ Q k)
    {j : Nat} (hj1 : 1 ≤ j) (hj : j ≤ 96) {s : State} (hI : WInv base s₀ s Q k j) :
    WP isa (Cfg.step c dblJa) s fun s' => WInv base s₀ s' Q k (j - 1) := by
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
  have e₂ : ∀ d, (d + 48 ≤ 736 ∨ 1456 ≤ d) → (d + 48 ≤ 2848 ∨ 2992 ≤ d) → (d + 48 ≤ 3712 ∨ 4096 ≤ d ∧ d + 48 ≤ 8192) →
      wordsVal s₂.mem base d 6 = wordsVal s₀.mem base d 6 := fun d h1 h2 h3 => by
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
  have k₃ : ∀ d, (d + 48 ≤ 736 ∨ 1456 ≤ d) → (d + 48 ≤ 3712 ∨ 4096 ≤ d ∧ d + 48 ≤ 8192) → wordsVal s₃.mem base d 6 = wordsVal s₂.mem base d 6 :=
    fun d h1 h2 => U₃.wordsVal (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega)
      (by omega)
  have pE₃ := pE.of_eq (k₃ _ (by decide) (by decide)) (k₃ _ (by decide) (by decide)) (k₃ _ (by decide) (by decide))
  have hK₃ : KC base s₃ := hK₂.of_eq fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> exact k₃ _ (by decide) (by decide)
  -- `T = R + E`.
  refine WP.seq (WP.mono (addPt_ok hL hw₃ hK₃.ap hK₃.bp (p := c.pt RX RY RZ) (q := c.pt c.EX c.EY c.EZ)
    (o := c.pt TX TY TZ) ⟨by decide, by decide⟩ (by decide) h16 hE pR₃ pE₃) fun s₄ ⟨K₄, U₄, pT⟩ => ?_)
  have hw₄ := hw₃.of_kp K₄
  -- `R = T`.
  refine WP.mono (copyPt_ok hw₄ (o := c.pt RX RY RZ) (p := c.pt TX TY TZ) (by decide) (by decide)
    (by decide) (by decide)) fun s₅ ⟨x₅, y₅, z₅, r₅, U₅⟩ => ?_
  refine ⟨hw₄.of_rest r₅, ?_, ?_, ?_, ?_⟩
  · rw [r₅.gpr _ (by decide), K₄.gpr _ (by decide), K₃.gpr _ (by decide), r₂.gpr _ (by decide), u₁.gpr]
  · exact ((hI.keep.trans (Kc.of_rest (u₁.rest (ws := [.s1]) (by decide)))).trans (Kc.of_rest r₂)).trans
      (K₃.kc.trans (K₄.kc.trans (Kc.of_rest r₅)))
  · exact ((((hI.unch.trans (show Unch base [(2848, 144)] s.mem s₂.mem from O₂.unch)).trans U₃).trans U₄).trans
      U₅).cover (by decide)
  · have e := wstep hL hP.q k (j - 1)
    rw [show j - 1 + 1 = j by omega] at e
    rw [← e]
    exact pT.move x₅ y₅ z₅

/-! ## The body -/

/-- What the body writes. -/
abbrev bodyW : List (Nat × Nat) := [(736, 720), (2848, 144), (4096, 2304), (3712, 384)]

/-- `R = [k]Q`, for `k` at `K`'s slot and `Q` affine in `R`'s first two. -/
theorem body_ok (hL : Law W) {base : Addr} {s : State} (hp : WPre base s) :
    WP isa (Cfg.body c dblJa) s fun s' => Kc s s' ∧ Unch base bodyW s.mem s'.mem ∧
      PtOk base s' (c.pt RX RY RZ) (mul (wordsVal s.mem base (c.sl K) 6) (qOf base s)) := by
  have hn := hp.ws.nowrap
  have hp0 : 0 < W.p := by decide
  rw [Cfg.body]
  refine WP.seq (WP.mono (build_ok hL hp) fun s₁ ⟨K₁, U₁, hK₁, T₁, e₁⟩ => ?_)
  have hw₁ := hp.ws.of_kp K₁
  refine WP.seq (WP.block_append (WP.mono (copyPt_ok hw₁ (o := c.pt RX RY RZ) (p := c.pt ZERO ONEP ZERO)
    (by decide) (by decide) (by decide) (by decide)) fun s₂ ⟨x₂, y₂, z₂, r₂, U₂⟩ => ?_))
  have hw₂ := hw₁.of_rest r₂
  refine wp_li (imm := 96) (by decide) fun s₃ u₃ => WP.block_nil ?_
  have hw₃ : WsReg s₃ base := hw₂.of_kc (Kc.of_rest (u₃.rest (ws := [.s1]) (by decide)))
  have U₃ : Unch base [(736, 144)] s₁.mem s₃.mem := by rw [u₃.mem]; exact U₂.cover (by decide)
  have k₃ : ∀ d, d + 48 ≤ 736 ∨ 880 ≤ d → d + 48 ≤ 8192 → wordsVal s₃.mem base d 6 = wordsVal s₁.mem base d 6 :=
    fun d h h' => U₃.wordsVal (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; omega)
      (by omega)
  have hP : WFix base s₃ (qOf base s) (wordsVal s.mem base (c.sl K) 6) :=
    ⟨hK₁.of_eq fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> exact k₃ _ (by decide) (by decide),
     T₁.of_eq (fun d h1 h2 => k₃ d (by omega) (by omega)) (by decide),
     by rw [k₃ _ (by decide) (by decide), U₁.wordsVal (by decide) (by decide)], hp.on⟩
  have zv : wordsVal s₁.mem base (c.sl ZERO) 6 = 0 := hK₁.zero
  have ov : wordsVal s₁.mem base (c.sl ONEP) 6 = 2 ^ 384 % W.p := hK₁.onep
  have rx : wordsVal s₃.mem base (c.sl RX) 6 = 0 := by rw [u₃.mem]; exact x₂.trans zv
  have ry : wordsVal s₃.mem base (c.sl RY) 6 = 1 * 2 ^ 384 % W.p := by
    rw [u₃.mem, Nat.one_mul]; exact y₂.trans ov
  have rz : wordsVal s₃.mem base (c.sl RZ) 6 = 0 := by rw [u₃.mem]; exact z₂.trans zv
  have hk : wordsVal s.mem base (c.sl K) 6 < 2 ^ (64 * 6) := wordsVal_lt _ _ _ _
  have hI : WInv base s₃ s₃ (qOf base s) (wordsVal s.mem base (c.sl K) 6) 96 := by
    refine ⟨hw₃, u₃.gpr, ⟨fun _ _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [show (96 : Nat) = 16 * 6 from rfl, wpt_top _ hk]
      show Rep W (tmv W 6 base s₃ (c.sl RX)) (tmv W 6 base s₃ (c.sl RY)) (tmv W 6 base s₃ (c.sl RZ)) _
      simp only [tmv]
      rw [rx, ry, rz, toM_zero, Nat.one_mul, toM_one unit]
      exact rep_infinity' hL
    · show wordsVal _ _ (c.sl RX) 6 < _; rw [rx]; exact hp0
    · show wordsVal _ _ (c.sl RY) 6 < _; rw [ry]; exact Nat.mod_lt _ hp0
    · show wordsVal _ _ (c.sl RZ) 6 < _; rw [rz]; exact hp0
  refine countLoop_ok (Inv := fun j s' => WInv base s₃ s' (qOf base s) (wordsVal s.mem base (c.sl K) 6) j)
    (n := 96) (fun j s' hi => hi.ctr) (fun j s' h1 h2 hi => step_ok hL hP h1 h2 hi) (fun s' hi => ?_)
    (by decide) (by decide) hI
  refine ⟨(K₁.kc.trans (Kc.of_rest ((r₂.mono (by decide)).trans (u₃.rest (ws := [.t0, .s1]) (by decide))))).trans
    hi.keep, ((U₁.trans U₃).trans hi.unch).cover (by decide), ?_⟩
  rw [← wpt_zero]
  exact hi.rep

end VG.Proof.Ecdsa.RISCV64.BrainpoolP384r1.Window
