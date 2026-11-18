module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Window
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.WindowA
public import VerifiedGarbage.Proof.Weierstrass.Joint
public import VerifiedGarbage.Proof.Weierstrass.Jac
import VerifiedGarbage.Proof.Ecdsa.RISCV64.Joint.Table
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Weierstrass.PointFacts
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes

/-!
# `vg_<curve>_mul` by windows on RISC-V, for the curves of four words: the body

`Window.Cfg.body c` (`Impl/Ecdsa/RISCV64/Window.lean`) leaves in `R` a
representative of `[k]Q` (`Kit.body_ok`), for `k` at `K`'s slot and `Q`
affine in `R`'s first two, once for every curve of four words with `a = -3`:
what the proof needs of a curve is its `Kit`: the code's configuration, of
four words, the three steps of `R = 16 R` on the field's programs
(`dblStep_ok`, `toJStep_ok`, `fromJStep_ok`) and its complete addition
(`addPt_ok`).

The layout of four words is the same for every such curve, so the slots here
are numbers (`slot 4 i`, `pt4`, `rs3`), the layout's facts are closed and
`decide` proves them once; the code's own slots, which are the
configuration's, become these where the code is unfolded (`k4`).

* `quad_ok`: `R = 16 R`: `R`'s representative of `P` into Jacobian
  coordinates, four doublings, and back in projective coordinates, with
  `Y = 1` where `Z` is zero;
* `build_ok`: `b R mod p` to slot 40, and the table of `[e]Q`;
* `select_ok`: the nibble's entry to `E`, by verification's selection;
* `step_ok`, `body_ok`: the windows, from `R = O`.

Each `<Curve>/Window.lean` is the curve's kit, the statements about it that
other modules use, and the function's contract (`mul_rv`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.Window4All

open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.Window
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.WindowA (d2 d16 wpt wstep mul_succ' four_bits)
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Point Fe mul onCurve)

/-! ## What the statements are about -/

theorem mul_zero' {C : Spec.Weierstrass.Curve} (P : Point C) : mul 0 P = .infinity := by
  rw [Spec.Weierstrass.mul]; rfl

theorem mul_one' {C : Spec.Weierstrass.Curve} (P : Point C) : mul 1 P = P := by
  rw [Spec.Weierstrass.mul, ite_eq_right (by decide), show (1 : Nat) / 2 = 0 from rfl, mul_zero',
    ite_eq_right (by decide)]
  rfl

/-- Before the first window, for `k` of four words: `O`. -/
theorem wpt_top {C : Spec.Weierstrass.Curve} (Q : Point C) {k : Nat} (hk : k < 2 ^ 256) : wpt Q k 64 = .infinity :=
  WindowA.wpt_top (n := 4) Q hk

/-- The registers the selection writes. -/
abbrev selRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a3, .a4]

/-- The slots `x`, `y` and `z` of four words, as a point's. -/
abbrev pt4 (x y z : Nat) : Pt := ⟨slot 4 x, slot 4 y, slot 4 z⟩

/-- The Jacobian programs' slots: the complete addition's, with `b` at slot 40. -/
abbrev rs3 : RcbSlots := ⟨slot 4 AP, slot 4 40, slot 4 T0, slot 4 T1, slot 4 T2, slot 4 T3, slot 4 T4, slot 4 T5⟩

/-- Entry `e`'s slots. -/
abbrev ent (e : Nat) : Pt := ⟨2048 + 96 * e, 2048 + 96 * e + 32, 2048 + 96 * e + 64⟩

/-- A point in the slots `p`: its coordinates below `p`, representing `P`. -/
structure PtOk (C : Spec.Weierstrass.Curve) (base : Addr) (s : State) (p : Pt) (P : Point C) : Prop where
  rep : Rep C (tmv C 4 base s p.x) (tmv C 4 base s p.y) (tmv C 4 base s p.z) P
  x : wordsVal s.mem base p.x 4 < C.p
  y : wordsVal s.mem base p.y 4 < C.p
  z : wordsVal s.mem base p.z 4 < C.p

theorem PtOk.of_eq {C : Spec.Weierstrass.Curve} {base : Addr} {s s' : State} {p : Pt} {P : Point C}
    (h : PtOk C base s p P) (hx : wordsVal s'.mem base p.x 4 = wordsVal s.mem base p.x 4)
    (hy : wordsVal s'.mem base p.y 4 = wordsVal s.mem base p.y 4)
    (hz : wordsVal s'.mem base p.z 4 = wordsVal s.mem base p.z 4) : PtOk C base s' p P :=
  ⟨by simp only [tmv]; rw [hx, hy, hz]; exact h.rep, by rw [hx]; exact h.x, by rw [hy]; exact h.y,
    by rw [hz]; exact h.z⟩

/-- A point copied to other slots. -/
theorem PtOk.move {C : Spec.Weierstrass.Curve} {base : Addr} {s s' : State} {p q : Pt} {P : Point C}
    (h : PtOk C base s p P) (hx : wordsVal s'.mem base q.x 4 = wordsVal s.mem base p.x 4)
    (hy : wordsVal s'.mem base q.y 4 = wordsVal s.mem base p.y 4)
    (hz : wordsVal s'.mem base q.z 4 = wordsVal s.mem base p.z 4) : PtOk C base s' q P :=
  ⟨by simp only [tmv]; rw [hx, hy, hz]; exact h.rep, by rw [hx]; exact h.x, by rw [hy]; exact h.y,
    by rw [hz]; exact h.z⟩

section
variable (C : Spec.Weierstrass.Curve)

/-- The slots the windows' arithmetic may use: those at multiples of 32 from
zero's (past `p` and the field's temporary) up to the functions' own working
space. -/
abbrev wS (x : Nat) : Prop := x % 32 = 0 ∧ 160 ≤ x ∧ x + 32 ≤ 3840

/-- What the field operations of `R = 16 R` write: `R`, `D`, `T`, the
temporaries and the functions' own working space. -/
abbrev quadW : List (Nat × Nat) := [(512, 480), (3840, 256)]

/-- The slots they write. -/
abbrev quadWl : List Nat :=
  [slot 4 T0, slot 4 T1, slot 4 T2, slot 4 T3, slot 4 T4, slot 4 T5, slot 4 RX, slot 4 RY, slot 4 RZ,
    slot 4 DX, slot 4 DY, slot 4 DZ, slot 4 TX, slot 4 TY, slot 4 TZ]

/-- The constants the windows read. -/
structure KC (base : Addr) (s : State) : Prop where
  ap : wordsVal s.mem base (slot 4 AP) 4 = C.a * 2 ^ 256 % C.p
  bp : wordsVal s.mem base (slot 4 40) 4 = C.b * 2 ^ 256 % C.p
  zero : wordsVal s.mem base (slot 4 ZERO) 4 = 0
  onep : wordsVal s.mem base (slot 4 ONEP) 4 = 2 ^ 256 % C.p

theorem KC.of_eq {C : Spec.Weierstrass.Curve} {base : Addr} {s s' : State} (h : KC C base s)
    (e : ∀ d ∈ [slot 4 AP, slot 4 40, slot 4 ZERO, slot 4 ONEP], wordsVal s'.mem base d 4 = wordsVal s.mem base d 4) :
    KC C base s' :=
  ⟨(e _ (by simp)).trans h.ap, (e _ (by simp)).trans h.bp, (e _ (by simp)).trans h.zero, (e _ (by simp)).trans h.onep⟩

/-- What an addition writes. -/
abbrev addW (o : Pt) : List (Nat × Nat) :=
  (rcbW rs3 o).map (fun w => (w, 8 * 4)) ++ [(own 4, 64 * 4)]

/-- The table up to entry `m`: `[e]Q` in entry `e`. -/
abbrev TabTo (base : Addr) (s : State) (Q : Point C) (m : Nat) : Prop := ∀ e ≤ m, PtOk C base s (ent e) (mul e Q)

/-- What the table's additions write. -/
abbrev addsW : List (Nat × Nat) := [(800, 192), (2048, 1536), (3840, 256)]

/-- `Q`, the affine point of `R`'s first two slots. -/
abbrev qOf (base : Addr) (s : State) : Point C := .affine (tmv C 4 base s (slot 4 RX)) (tmv C 4 base s (slot 4 RY))

/-- What the table's construction writes. -/
abbrev buildW : List (Nat × Nat) := [(1344, 32), (800, 192), (2048, 1536), (3840, 256)]

/-- What `vg_<curve>_mul`'s body reads at the start. -/
structure WPre (base : Addr) (s : State) : Prop where
  ws : WsReg s base
  ap : wordsVal s.mem base (slot 4 AP) 4 = C.a * 2 ^ 256 % C.p
  zero : wordsVal s.mem base (slot 4 ZERO) 4 = 0
  onep : wordsVal s.mem base (slot 4 ONEP) 4 = 2 ^ 256 % C.p
  x : wordsVal s.mem base (slot 4 RX) 4 < C.p
  y : wordsVal s.mem base (slot 4 RY) 4 < C.p
  on : onCurve C (qOf C base s) = true

/-- What the windows read and keep, from `s₀`. -/
structure WFix (base : Addr) (s₀ : State) (Q : Point C) (k : Nat) : Prop where
  kc : KC C base s₀
  tab : TabTo C base s₀ Q 15
  kk : wordsVal s₀.mem base (slot 4 K) 4 = k
  q : onCurve C Q = true

/-- What the windows write. -/
abbrev stepW : List (Nat × Nat) := [(512, 480), (1920, 96), (3840, 256)]

/-- The loop's invariant at `s1 = j`: `R` represents `[k >>> 4 j]Q`. -/
structure WInv (base : Addr) (s₀ s : State) (Q : Point C) (k j : Nat) : Prop where
  ws : WsReg s base
  ctr : s.gpr .s1 = BitVec.ofNat 64 j
  keep : Kc s₀ s
  unch : Unch base stepW s₀.mem s.mem
  rep : PtOk C base s (pt4 RX RY RZ) (wpt Q k j)

theorem TabTo.of_eq {C : Spec.Weierstrass.Curve} {base : Addr} {s s' : State} {Q : Point C} {m : Nat} (h : TabTo C base s Q m)
    (he : ∀ d, 2048 ≤ d → d + 32 ≤ 3584 → wordsVal s'.mem base d 4 = wordsVal s.mem base d 4) (hm : m ≤ 15) :
    TabTo C base s' Q m :=
  fun e hlt => (h e hlt).of_eq (he (2048 + 96 * e) (by omega_using []) (by omega_using [hm, hlt]))
    (he (2048 + 96 * e + 32) (by omega_using []) (by omega_using [hm, hlt])) (he (2048 + 96 * e + 64) (by omega_using [])
        (by omega_using [hm, hlt]))

/-- What the body writes. -/
abbrev bodyW : List (Nat × Nat) := [(512, 480), (1344, 32), (1920, 96), (2048, 1536), (3840, 256)]
end

/-! ## The kit -/

/-- What the proof needs of a curve. -/
structure Kit where
  c : Cfg
  /-- The layout: four words, the table at byte 2048 and the entry `E` at slot 58. -/
  n4 : c.n = 4
  jt : c.jt = 2048
  ve : c.ve = 58
  p0 : 0 < c.C.p
  plt : c.C.p < 2 ^ (64 * 4)
  unit : UnitMod c.C.p (2 ^ (64 * 4))
  /-- The steps of `R = 16 R` on the field's programs. -/
  dblStep_ok : Law c.C → ∀ {base : Addr} {s : State} {p o : Pt}, RcbApart rs3 p p o →
    (∀ x ∈ rcbW rs3 o ++ rcbR rs3 p p, wS x) → ∀ {V : List Nat} {E : Nat → Fe c.C},
    Inv 4 base c.C.p wS V E s → (∀ x ∈ rcbR rs3 p p, x ∈ V) → ∀ {P : Point c.C},
    onCurve c.C P = true → InvJ c.C (E p.x) (E p.y) (E p.z) P →
    WP isa (fprog c.FP (dblJ rs3 p o)) s fun s' => KeepR 4 base (rcbW rs3 o) s s' ∧
      ∃ E', Inv 4 base c.C.p wS ([o.x, o.y, o.z] ++ V) E' s' ∧ InvJ c.C (E' o.x) (E' o.y) (E' o.z) (d2 P) ∧
        ∀ x, x ∉ rcbW rs3 o → E' x = E x
  toJStep_ok : Law c.C → ∀ {base : Addr} {s : State} {V : List Nat} {E : Nat → Fe c.C},
    Inv 4 base c.C.p wS V E s → (∀ x ∈ rcbR rs3 (pt4 RX RY RZ) (pt4 ZERO ZERO ZERO), x ∈ V) → ∀ {P : Point c.C},
    Rep c.C (E (slot 4 RX)) (E (slot 4 RY)) (E (slot 4 RZ)) P → E (slot 4 ZERO) = 0 →
    WP isa (fprog c.FP (toJ rs3 (pt4 RX RY RZ) (pt4 ZERO ZERO ZERO) (pt4 DX DY DZ))) s fun s' =>
      KeepR 4 base (rcbW rs3 (pt4 DX DY DZ)) s s' ∧
      ∃ E', Inv 4 base c.C.p wS ([slot 4 DX, slot 4 DY, slot 4 DZ] ++ V) E' s' ∧
        InvJ c.C (E' (slot 4 DX)) (E' (slot 4 DY)) (E' (slot 4 DZ)) P ∧
        ∀ x, x ∉ rcbW rs3 (pt4 DX DY DZ) → E' x = E x
  fromJStep_ok : ∀ {base : Addr} {s : State} {V : List Nat} {E : Nat → Fe c.C},
    Inv 4 base c.C.p wS V E s → (∀ x ∈ rcbR rs3 (pt4 DX DY DZ) (pt4 ZERO ZERO ZERO), x ∈ V) →
    WP isa (fprog c.FP (fromJ rs3 (pt4 DX DY DZ) (pt4 ZERO ZERO ZERO) (pt4 RX RY RZ))) s fun s' =>
      KeepR 4 base (rcbW rs3 (pt4 RX RY RZ)) s s' ∧
      ∃ E', Inv 4 base c.C.p wS ([slot 4 RX, slot 4 RY, slot 4 RZ] ++ V) E' s' ∧
        (E' (slot 4 RX), E' (slot 4 RY), E' (slot 4 RZ)) =
          (E (slot 4 DX) * E (slot 4 DZ), E (slot 4 DY) + E (slot 4 ZERO),
            E (slot 4 DZ) * E (slot 4 DZ) * E (slot 4 DZ)) ∧
        ∀ x, x ∉ rcbW rs3 (pt4 RX RY RZ) → E' x = E x
  /-- The complete addition, for points in slots of `wS`. -/
  addPt_ok : Law c.C → ∀ {base : Addr} {s : State}, WsReg s base → KC c.C base s → ∀ {p q o : Pt},
    RcbApart rs3 p q o → (∀ x ∈ rcbW rs3 o ++ rcbR rs3 p q, wS x) → ∀ {P P' : Point c.C},
    onCurve c.C P = true → onCurve c.C P' = true → PtOk c.C base s p P → PtOk c.C base s q P' →
    WP isa (Cfg.addPt c p q o) s fun s' =>
      Kp s s' ∧ Unch base (addW o) s.mem s'.mem ∧ PtOk c.C base s' o (Spec.Weierstrass.add P P')

namespace Kit

/-! ## The code's slots, as numbers -/

theorem sl_eq (Kt : Kit) (i : Nat) : Kt.c.sl i = slot 4 i := by rw [Cfg.sl, Kt.n4]

theorem pt_eq (Kt : Kit) (x y z : Nat) : Kt.c.pt x y z = pt4 x y z := by simp only [Cfg.pt, Kt.sl_eq]

theorem zeroPt_eq (Kt : Kit) : Cfg.zeroPt Kt.c = pt4 ZERO ZERO ZERO := Kt.pt_eq _ _ _

theorem rcb3_eq (Kt : Kit) : Kt.c.rcb3Slots = rs3 := by simp only [Cfg.rcb3Slots, Cfg.rcbSlots, Kt.sl_eq]

theorem entry_eq (Kt : Kit) (e : Nat) :
    Cfg.entry Kt.c e = ⟨2048 + 24 * 4 * e, 2048 + 24 * 4 * e + 8 * 4, 2048 + 24 * 4 * e + 16 * 4⟩ := by
  rw [Cfg.entry, Cfg.eb, Kt.n4]

theorem windows_eq (Kt : Kit) : windows Kt.c = 16 * 4 := by rw [windows, Kt.n4]

theorem mont_eq (Kt : Kit) (x : Nat) : VG.Impl.Ecdh.RISCV64.Cfg.mont Kt.c x = x * 2 ^ (64 * 4) % Kt.c.C.p := by
  rw [VG.Impl.Ecdh.RISCV64.Cfg.mont, Kt.n4]

theorem EX_eq (Kt : Kit) : Kt.c.EX = 58 := Kt.ve

/-- The code's slots and sizes, which are the configuration's, as the numbers of the layout, for the kit `k`. -/
local macro "k4" k:ident loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Kit.n4 $k, Kit.jt $k, Kit.sl_eq $k, Kit.pt_eq $k, Kit.zeroPt_eq $k, Kit.rcb3_eq $k,
    Kit.entry_eq $k, Kit.windows_eq $k, Kit.mont_eq $k, Kit.EX_eq $k] $[$loc]?)

/-- A fact of the layout stated on the configuration of the kit `k`: on its numbers, by `decide`. -/
local macro "k4d" k:ident : tactic =>
  `(tactic| (simp only [Kit.n4 $k, Kit.jt $k, Kit.sl_eq $k, Kit.EX_eq $k]; first | done | decide))

/-! ## `R = 16 R` -/

theorem dblJ_apart_DT : RcbApart rs3 (pt4 DX DY DZ) (pt4 DX DY DZ) (pt4 TX TY TZ) :=
  ⟨by decide, by decide⟩
theorem dblJ_apart_TD : RcbApart rs3 (pt4 TX TY TZ) (pt4 TX TY TZ) (pt4 DX DY DZ) :=
  ⟨by decide, by decide⟩

/-- `R = 16 R`, for `R` representing `P`. -/
theorem quad_ok (Kt : Kit) (hL : Law Kt.c.C) {base : Addr} {s : State} (hw : WsReg s base) (hK : KC Kt.c.C base s) {P : Point Kt.c.C}
    (hP : onCurve Kt.c.C P = true) (hR : PtOk Kt.c.C base s (pt4 RX RY RZ) P) :
    WP isa (Cfg.quad Kt.c) s fun s' => Kp s s' ∧ Unch base quadW s.mem s'.mem ∧
      PtOk Kt.c.C base s' (pt4 RX RY RZ) (d16 P) := by
  obtain hp0 : 0 < Kt.c.C.p := Kt.p0
  have hn := hw.nowrap
  rw [Cfg.quad]
  k4 Kt
  simp only [progs]
  -- The start: `a`, `b`, zero and `R`.
  obtain hI : Inv 4 base Kt.c.C.p wS [slot 4 AP, slot 4 40, slot 4 ZERO, slot 4 RX, slot 4 RY, slot 4 RZ]
      (fun x => toM Kt.c.C.p (2 ^ (64 * 4)) (wordsVal s.mem base x 4)) s := by
    refine ⟨hw, by decide, fun x hx => ?_, fun x _ => rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hK.ap]; exact Nat.mod_lt _ hp0
    · rw [hK.bp]; exact Nat.mod_lt _ hp0
    · rw [hK.zero]; exact hp0
    exacts [hR.x, hR.y, hR.z]
  obtain e0 : toM Kt.c.C.p (2 ^ (64 * 4)) (wordsVal s.mem base (slot 4 ZERO) 4) = 0 := by
    rw [hK.zero]; exact toM_zero _ _
  -- To Jacobian coordinates.
  refine WP.seq (WP.mono (Kt.toJStep_ok hL hI (by decide) hR.rep e0) fun s₁ ⟨k₁, E₁, I₁, J₁, p₁⟩ => ?_)
  -- Four doublings.
  refine WP.seq (WP.mono (Kt.dblStep_ok hL dblJ_apart_DT (by decide) I₁ (by decide) hP J₁)
    fun s₂ ⟨k₂, E₂, I₂, J₂, p₂⟩ => ?_)
  refine WP.seq (WP.mono (Kt.dblStep_ok hL dblJ_apart_TD (by decide) I₂ (by decide) (hL.onCurve_add hP hP) J₂)
    fun s₃ ⟨k₃, E₃, I₃, J₃, p₃⟩ => ?_)
  obtain h4 := hL.onCurve_add (hL.onCurve_add hP hP) (hL.onCurve_add hP hP)
  refine WP.seq (WP.mono (Kt.dblStep_ok hL dblJ_apart_DT (by decide) I₃ (by decide) h4 J₃)
    fun s₄ ⟨k₄, E₄, I₄, J₄, p₄⟩ => ?_)
  refine WP.seq (WP.mono (Kt.dblStep_ok hL dblJ_apart_TD (by decide) I₄ (by decide) (hL.onCurve_add h4 h4) J₄)
    fun s₅ ⟨k₅, E₅, I₅, J₅, p₅⟩ => ?_)
  -- Back to projective coordinates.
  refine WP.seq (WP.mono (Kt.fromJStep_ok I₅ (by decide)) fun s₆ ⟨k₆, E₆, I₆, v₆, p₆⟩ => ?_)
  obtain z₅ : E₅ (slot 4 ZERO) = 0 := by
    rw [p₅ _ (by decide), p₄ _ (by decide), p₃ _ (by decide), p₂ _ (by decide), p₁ _ (by decide)]; exact e0
  simp only [Prod.mk.injEq] at v₆
  obtain ⟨vx, vy, vz⟩ := v₆
  rw [z₅, Lean.Grind.AddCommMonoid.add_zero] at vy
  have hw₆ := I₆.ws
  have hn₆ := hw₆.nowrap
  obtain ltx := I₆.lt (slot 4 RX) (by decide)
  obtain lty := I₆.lt (slot 4 RY) (by decide)
  obtain ltz := I₆.lt (slot 4 RZ) (by decide)
  obtain vx' : tmv Kt.c.C 4 base s₆ (slot 4 RX) = E₆ (slot 4 RX) := I₆.val (slot 4 RX) (by decide)
  obtain vy' : tmv Kt.c.C 4 base s₆ (slot 4 RY) = E₆ (slot 4 RY) := I₆.val (slot 4 RY) (by decide)
  obtain vz' : tmv Kt.c.C 4 base s₆ (slot 4 RZ) = E₆ (slot 4 RZ) := I₆.val (slot 4 RZ) (by decide)
  -- `Y = 1` where `Z = 0`.
  obtain KK : KeepR 4 base quadWl s s₆ :=
    ((((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans ((k₃.mono (by decide)).trans
      (k₄.mono (by decide)))).trans ((k₅.mono (by decide)).trans (k₆.mono (by decide))))
  have UK : Unch base (quadWl.map (fun w => (w, 8 * 4)) ++ [(own 4, 64 * 4)]) s.mem s₆.mem := KK.mem
  obtain onep₆ : wordsVal s₆.mem base (slot 4 ONEP) 4 = 2 ^ 256 % Kt.c.C.p := by
    rw [UK.wordsVal (by decide) (by decide)]; exact hK.onep
  refine WP.block_append (WP.mono (zeroMask_ok hw₆ (n := 4) (a := slot 4 RZ) (by decide) (by decide))
    fun s₇ ⟨r₇, m₇, a7₇⟩ => ?_)
  obtain hw₇ := hw₆.of_rest r₇
  refine WP.mono (sel_ok (decide (wordsVal s₆.mem base (slot 4 RZ) 4 = 0)) 4 hw₇ a7₇
    (o := slot 4 RY) (a := slot 4 RY) (b := slot 4 ONEP) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (Or.inl (Nat.le_refl _)) (by decide)) fun s₈ ⟨e₈, r₈, O₈⟩ => ?_
  rw [m₇] at e₈ O₈
  obtain ex : wordsVal s₈.mem base (slot 4 RX) 4 = wordsVal s₆.mem base (slot 4 RX) 4 :=
    O₈.wordsVal (by decide) (by decide)
  obtain ez : wordsVal s₈.mem base (slot 4 RZ) 4 = wordsVal s₆.mem base (slot 4 RZ) 4 :=
    O₈.wordsVal (by decide) (by decide)
  obtain hZ : (wordsVal s₆.mem base (slot 4 RZ) 4 = 0) ↔ E₅ (slot 4 DZ) = 0 := by
    rw [← toM_eq_zero_iff Kt.unit ltz]
    show tmv Kt.c.C 4 base s₆ (slot 4 RZ) = 0 ↔ _
    rw [vz', vz]
    exact ⟨fun h => by_contra fun hz => cube_ne_zero hL hz h, fun h => by rw [h]; grind⟩
  obtain hrep := InvJ.out hL J₅
  refine ⟨KK.kp.trans ((Kp.of_rest r₇).trans (Kp.of_rest r₈)), (UK.trans O₈.unch).cover (by decide), ⟨?_, ?_, ?_, ?_⟩⟩
  · show Rep Kt.c.C (tmv Kt.c.C 4 base s₈ (slot 4 RX)) (tmv Kt.c.C 4 base s₈ (slot 4 RY)) (tmv Kt.c.C 4 base s₈ (slot 4 RZ)) _
    simp only [tmv]
    rw [ex, ez]
    show Rep Kt.c.C (tmv Kt.c.C 4 base s₆ (slot 4 RX)) _ (tmv Kt.c.C 4 base s₆ (slot 4 RZ)) _
    rw [vx', vz', vx, vz, e₈]
    by_cases h0 : E₅ (slot 4 DZ) = 0
    · have hc : decide (wordsVal s₆.mem base (slot 4 RZ) 4 = 0) = true := decide_eq_true (hZ.mpr h0)
      have h0' : E₅ (pt4 DX DY DZ).z = 0 := h0
      rw [show (if E₅ (pt4 DX DY DZ).z = 0 then (1 : Fe Kt.c.C) else E₅ (pt4 DX DY DZ).y) = 1 from
        by simp [h0']] at hrep
      simp only [hc, ↓reduceIte]
      rw [onep₆, toM_one Kt.unit]
      exact hrep
    · have hc : decide (wordsVal s₆.mem base (slot 4 RZ) 4 = 0) = false :=
        decide_eq_false fun h => h0 (hZ.mp h)
      have h0' : ¬E₅ (pt4 DX DY DZ).z = 0 := h0
      rw [show (if E₅ (pt4 DX DY DZ).z = 0 then (1 : Fe Kt.c.C) else E₅ (pt4 DX DY DZ).y) =
        E₅ (pt4 DX DY DZ).y from by simp [h0']] at hrep
      simp only [hc, ↓reduceIte, Bool.false_eq_true]
      show Rep Kt.c.C _ (tmv Kt.c.C 4 base s₆ (slot 4 RY)) _ _
      rw [vy', vy]
      exact hrep
  · show wordsVal s₈.mem base (slot 4 RX) 4 < Kt.c.C.p
    rw [ex]; exact ltx
  · show wordsVal s₈.mem base (slot 4 RY) 4 < Kt.c.C.p
    rw [e₈]; split
    · rw [onep₆]; exact Nat.mod_lt _ (Kt.p0)
    · exact lty
  · show wordsVal s₈.mem base (slot 4 RZ) 4 < Kt.c.C.p
    rw [ez]; exact ltz

/-! ## The complete additions and the table -/

theorem ent_eq (e : Nat) : ent e = ⟨2048 + 96 * e, 2048 + 96 * e + 32, 2048 + 96 * e + 64⟩ := rfl

theorem rcbW_S3 (o : Pt) : rcbW rs3 o = [800, 832, 864, 896, 928, 960, o.x, o.y, o.z] := rfl

/-- An addition's writes into entry `e`, within `addsW`, and apart from the
other entries and below byte 3840. -/
theorem addW_ent {e : Nat} (_he : e < 16) : ∀ w ∈ addW (ent e),
    ∃ w' ∈ addsW, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := by
  intro w hw
  simp only [addW, rcbW_S3, ent_eq, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false, own, VG.Proof.Weierstrass.RISCV64.rvOwn_le (show 4 ≤ 6 by decide),
        Impl.Weierstrass.Mont.ownAt,
    Impl.Weierstrass.Mont.ownBytes] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact ⟨(800, 192), List.mem_cons_self .., by simp only; omega_using [], by simp only; omega⟩
    | exact ⟨(2048, 1536), List.mem_cons_of_mem _ List.mem_cons_self, by simp only; omega_using [], by simp only; omega⟩
    | exact ⟨(3840, 256), List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), by simp only; omega_using [],
        by simp only; omega_using []⟩

theorem addW_apart {e d : Nat} (_he : e < 16) (hd : d < 16) (hne : d ≠ e) (c : Nat) (hc : c < 3) :
    ∀ w ∈ addW (ent e), 2048 + 96 * d + 32 * c + 8 * 4 ≤ w.1 ∨ w.1 + w.2 ≤ 2048 + 96 * d + 32 * c := by
  intro w hw
  simp only [addW, rcbW_S3, ent_eq, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false, own, VG.Proof.Weierstrass.RISCV64.rvOwn_le (show 4 ≤ 6 by decide),
        Impl.Weierstrass.Mont.ownAt,
    Impl.Weierstrass.Mont.ownBytes] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega_arith

/-- The additions of `[e]Q` for `e = 2 … m + 1`. -/
theorem adds_ok (Kt : Kit) (hL : Law Kt.c.C) {base : Addr} {Q : Point Kt.c.C} (hQ : onCurve Kt.c.C Q = true) :
    ∀ m ≤ 14, ∀ {s : State}, WsReg s base → KC Kt.c.C base s → TabTo Kt.c.C base s Q 1 →
      WP isa (Cfg.adds Kt.c m) s fun s' => Kp s s' ∧ Unch base addsW s.mem s'.mem ∧ TabTo Kt.c.C base s' Q (m + 1)
  | 0, _, s, hw, hK, hT => WP.block_nil ⟨Kp.refl _, Unch.refl _ _ _, hT⟩
  | m + 1, hm, s, hw, hK, hT => by
    rw [Cfg.adds]
    k4 Kt
    refine WP.seq (WP.mono (Kt.adds_ok hL hQ m (by omega_using [hm]) hw hK hT) fun s₁ ⟨k₁, U₁, T₁⟩ => ?_)
    obtain hw₁ := hw.of_kp k₁
    have hn := hw₁.nowrap
    obtain hK₁ : KC Kt.c.C base s₁ := hK.of_eq fun d hd => U₁.wordsVal (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> decide)
    obtain hA : RcbApart rs3 (ent (m + 1)) (ent 1) (ent (m + 2)) :=
      ⟨(by decide : ∀ m < 14, (rcbW rs3 (ent (m + 2))).Nodup) m (by omega_using [hm]),
        (by decide : ∀ m < 14, ∀ x ∈ rcbR rs3 (ent (m + 1)) (ent 1), x ∉ rcbW rs3 (ent (m + 2))) m (by omega_using [hm])⟩
    obtain hsl : ∀ x ∈ rcbW rs3 (ent (m + 2)) ++ rcbR rs3 (ent (m + 1)) (ent 1), wS x :=
      (by decide : ∀ m < 14, ∀ x ∈ rcbW rs3 (ent (m + 2)) ++ rcbR rs3 (ent (m + 1)) (ent 1), wS x) m (by omega_using [hm])
    refine WP.mono (Kt.addPt_ok hL hw₁ hK₁ hA hsl (hL.onCurve_mul hQ _) (hL.onCurve_mul hQ 1) (T₁ (m + 1) (by omega_using []))
      (T₁ 1 (by omega_using []))) fun s₂ ⟨k₂, U₂, p₂⟩ => ?_
    rw [mul_one' Q, mul_succ' hL hQ] at p₂
    refine ⟨k₁.trans k₂, (U₁.trans U₂).cover fun w hw => ?_, fun e he => ?_⟩
    · rcases List.mem_append.mp hw with hw | hw
      · exact ⟨w, hw, Nat.le_refl _, Nat.le_refl _⟩
      · exact addW_ent (by omega_using [hm]) w hw
    · rcases Nat.lt_or_ge e (m + 2) with h | h
      · have pe := T₁ e (by omega_using [h])
        obtain ec : ∀ c < 3, wordsVal s₂.mem base (2048 + 96 * e + 32 * c) 4 = wordsVal s₁.mem base (2048 + 96 * e + 32 * c) 4 :=
          fun c hc => U₂.wordsVal (addW_apart (by omega_using [hm]) (by omega_using [hm, he]) (by omega_using [h]) c hc)
              (by omega_using [hm, he, hc])
        refine pe.of_eq ?_ ?_ ?_
        · show wordsVal s₂.mem base (2048 + 96 * e) 4 = wordsVal s₁.mem base (2048 + 96 * e) 4
          simpa using ec 0 (by decide)
        · show wordsVal s₂.mem base (2048 + 96 * e + 32) 4 = wordsVal s₁.mem base (2048 + 96 * e + 32) 4
          simpa using ec 1 (by decide)
        · show wordsVal s₂.mem base (2048 + 96 * e + 64) 4 = wordsVal s₁.mem base (2048 + 96 * e + 64) 4
          simpa using ec 2 (by decide)
      · obtain rfl : e = m + 2 := by omega_using [he, h]
        exact p₂

/-- `o = p`, the three coordinates one after the other, for `o`'s slots in
order and `p`'s apart from them all. -/
theorem copyPt_ok (Kt : Kit) {s : State} {base : Addr} (hw : WsReg s base) {o p : Pt}
    (h8 : ∀ x ∈ [o.x, o.y, o.z, p.x, p.y, p.z], x % 8 = 0 ∧ x + 32 ≤ 4096)
    (hxy : o.x + 32 ≤ o.y) (hyz : o.y + 32 ≤ o.z)
    (hp : ∀ a ∈ [p.x, p.y, p.z], a + 32 ≤ o.x ∨ o.z + 32 ≤ a) :
    WP isa (.block (Cfg.copyPt Kt.c o p)) s fun s' =>
      wordsVal s'.mem base o.x 4 = wordsVal s.mem base p.x 4 ∧ wordsVal s'.mem base o.y 4 = wordsVal s.mem base p.y 4 ∧
      wordsVal s'.mem base o.z 4 = wordsVal s.mem base p.z 4 ∧ Rest [.t0] s s' ∧
      Unch base [(o.x, 32), (o.y, 32), (o.z, 32)] s.mem s'.mem := by
  have hn := hw.nowrap
  obtain g := fun x hx => h8 x hx
  obtain gp := fun x hx => hp x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g gp
  obtain ⟨⟨ox8, ox⟩, ⟨oy8, oy⟩, ⟨oz8, oz⟩, ⟨px8, px⟩, ⟨py8, py⟩, ⟨pz8, pz⟩⟩ := g
  obtain ⟨hpx, hpy, hpz⟩ := gp
  rw [Cfg.copyPt, Kt.n4, List.append_assoc]
  refine WP.block_append (WP.mono (copy_ok 4 hw (o := o.x) (a := p.x) ox8 px8 (by omega_using [ox]) (by omega_using [px])
      (by omega_using [hxy, hyz, ox8, ox, oy8, oy, oz8, oz, px8, px, py8, py, pz8, pz, hpx, hpy, hpz]))
    fun s₁ ⟨e₁, r₁, O₁⟩ => ?_)
  obtain hw₁ := hw.of_rest r₁
  refine WP.block_append (WP.mono (copy_ok 4 hw₁ (o := o.y) (a := p.y) oy8 py8 (by omega_using [oy]) (by omega_using [py])
      (by omega_using [hxy, hyz, hpy]))
    fun s₂ ⟨e₂, r₂, O₂⟩ => ?_)
  obtain hw₂ := hw₁.of_rest r₂
  refine WP.mono (copy_ok 4 hw₂ (o := o.z) (a := p.z) oz8 pz8 (by omega_using [oz]) (by omega_using [pz])
      (by omega_using [hxy, hyz, ox8, ox, oy8, oy, oz8, oz, px8, px, py8, py, pz8, pz, hpx, hpy, hpz]))
    fun s₃ ⟨e₃, r₃, O₃⟩ => ⟨?_, ?_, ?_, (r₁.trans r₂).trans r₃ |>.mono (by simp), ?_⟩
  · rw [O₃.wordsVal (by omega_using [hxy, hyz]) (by omega_using [ox]), O₂.wordsVal (by omega_using [hxy]) (by omega_using [ox]), e₁]
  · rw [O₃.wordsVal (by omega_using [hyz]) (by omega_using [oy]), e₂, O₁.wordsVal
      (by omega_using [hxy, hyz, ox8, ox, oy8, oy, oz8, oz, px8, px, py8, py, pz8, pz, hpx, hpy, hpz]) (by omega_using [py])]
  · rw [e₃, O₂.wordsVal (by omega_using [hxy, hyz, hpz]) (by omega_using [pz]), O₁.wordsVal
      (by omega_using [hxy, hyz, ox8, ox, oy8, oy, oz8, oz, px8, px, py8, py, pz8, pz, hpx, hpy, hpz]) (by omega_using [pz])]
  · exact ((O₁.unch.trans O₂.unch).trans O₃.unch).mono (by simp)

/-- `b R mod p` to slot 40, and the table of `[e]Q`. -/
theorem build_ok (Kt : Kit) (hL : Law Kt.c.C) {base : Addr} {s : State} (hp : WPre Kt.c.C base s) :
    WP isa (Cfg.build Kt.c) s fun s' => Kp s s' ∧ Unch base buildW s.mem s'.mem ∧ KC Kt.c.C base s' ∧
      TabTo Kt.c.C base s' (qOf Kt.c.C base s) 15 := by
  have hw := hp.ws
  have hn := hw.nowrap
  obtain hp0 : 0 < Kt.c.C.p := Kt.p0
  rw [Cfg.build, List.append_assoc]
  k4 Kt
  refine WP.seq (WP.block_append (WP.mono (setConst_ok 4 hw (o := slot 4 40)
    (x := Kt.c.C.b * 2 ^ (64 * 4) % Kt.c.C.p) (by decide) (by decide)) fun s₁ ⟨r₁, O₁, e₁⟩ => ?_))
  obtain hw₁ := hw.of_rest r₁
  have O₁' : Outside base 1344 32 s.mem s₁.mem := O₁
  obtain e₁' : wordsVal s₁.mem base 1344 4 = Kt.c.C.b * 2 ^ 256 % Kt.c.C.p := by
    refine e₁.trans (Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hp0) (Kt.plt)))
  obtain k₁ : ∀ d, d + 32 ≤ 1344 ∨ 1376 ≤ d → d + 32 ≤ 4096 → wordsVal s₁.mem base d 4 = wordsVal s.mem base d 4 :=
    fun d h h' => O₁'.wordsVal (by omega_using [h]) (by omega_using [h'])
  refine WP.block_append (WP.mono (Kt.copyPt_ok hw₁ (o := ent 0) (p := pt4 ZERO ONEP ZERO) (by decide) (by decide)
    (by decide) (by decide)) fun s₂ ⟨x₂, y₂, z₂, r₂, U₂⟩ => ?_)
  obtain hw₂ := hw₁.of_rest r₂
  refine WP.mono (Kt.copyPt_ok hw₂ (o := ent 1) (p := pt4 RX RY ONEP) (by decide) (by decide)
    (by decide) (by decide)) fun s₃ ⟨x₃, y₃, z₃, r₃, U₃⟩ => ?_
  obtain hw₃ := hw₂.of_rest r₃
  have U₂' : Unch base [(2048, 32), (2080, 32), (2112, 32)] s₁.mem s₂.mem := U₂
  have U₃' : Unch base [(2144, 32), (2176, 32), (2208, 32)] s₂.mem s₃.mem := U₃
  have x₂' : wordsVal s₂.mem base 2048 4 = wordsVal s₁.mem base 160 4 := x₂
  have y₂' : wordsVal s₂.mem base 2080 4 = wordsVal s₁.mem base 224 4 := y₂
  have z₂' : wordsVal s₂.mem base 2112 4 = wordsVal s₁.mem base 160 4 := z₂
  have x₃' : wordsVal s₃.mem base 2144 4 = wordsVal s₂.mem base 512 4 := x₃
  have y₃' : wordsVal s₃.mem base 2176 4 = wordsVal s₂.mem base 544 4 := y₃
  have z₃' : wordsVal s₃.mem base 2208 4 = wordsVal s₂.mem base 224 4 := z₃
  obtain k₃ : ∀ d, d + 32 ≤ 1344 ∨ 1376 ≤ d → d + 32 ≤ 2048 → wordsVal s₃.mem base d 4 = wordsVal s.mem base d 4 :=
    fun d h h' => by
      rw [U₃'.wordsVal (by simp; omega_using [h']) (by omega_using [h']), U₂'.wordsVal (by simp; omega_using [h'])
          (by omega_using [h']), k₁ d h (by omega_using [h'])]
  obtain k₂ : ∀ d, d + 32 ≤ 1344 ∨ 1376 ≤ d → d + 32 ≤ 2048 → wordsVal s₂.mem base d 4 = wordsVal s.mem base d 4 :=
    fun d h h' => by rw [U₂'.wordsVal (by simp; omega_using [h']) (by omega_using [h']), k₁ d h (by omega_using [h'])]
  obtain hK₃ : KC Kt.c.C base s₃ :=
    ⟨(k₃ 256 (by decide) (by decide)).trans hp.ap, by
      show wordsVal s₃.mem base 1344 4 = _
      rw [U₃'.wordsVal (by simp) (by omega_using []), U₂'.wordsVal (by simp) (by omega_using [])]; exact e₁',
      (k₃ 160 (by decide) (by decide)).trans hp.zero, (k₃ 224 (by decide) (by decide)).trans hp.onep⟩
  obtain h1 : tmv Kt.c.C 4 base s (slot 4 ONEP) = 1 := by
    simp only [tmv]; rw [hp.onep]; exact toM_one Kt.unit
  obtain h0 : tmv Kt.c.C 4 base s (slot 4 ZERO) = 0 := by
    simp only [tmv]; rw [hp.zero]; exact toM_zero _ _
  have zv : wordsVal s.mem base 160 4 = 0 := hp.zero
  have ov : wordsVal s.mem base 224 4 = 2 ^ 256 % Kt.c.C.p := hp.onep
  obtain e0x : wordsVal s₃.mem base 2048 4 = wordsVal s.mem base 160 4 := by
    rw [U₃'.wordsVal (by simp) (by omega_using []), x₂', k₁ 160 (by decide) (by decide)]
  obtain e0y : wordsVal s₃.mem base 2080 4 = wordsVal s.mem base 224 4 := by
    rw [U₃'.wordsVal (by simp) (by omega_using []), y₂', k₁ 224 (by decide) (by decide)]
  obtain e0z : wordsVal s₃.mem base 2112 4 = wordsVal s.mem base 160 4 := by
    rw [U₃'.wordsVal (by simp) (by omega_using []), z₂', k₁ 160 (by decide) (by decide)]
  obtain e1x : wordsVal s₃.mem base 2144 4 = wordsVal s.mem base 512 4 := by rw [x₃', k₂ 512 (by decide) (by decide)]
  obtain e1y : wordsVal s₃.mem base 2176 4 = wordsVal s.mem base 544 4 := by rw [y₃', k₂ 544 (by decide) (by decide)]
  obtain e1z : wordsVal s₃.mem base 2208 4 = wordsVal s.mem base 224 4 := by rw [z₃', k₂ 224 (by decide) (by decide)]
  obtain hT : TabTo Kt.c.C base s₃ (qOf Kt.c.C base s) 1 := by
    intro e he
    rcases Nat.lt_or_ge e 1 with h | h
    · obtain rfl : e = 0 := by omega_using [h]
      rw [mul_zero']
      refine ⟨?_, ?_, ?_, ?_⟩
      · show Rep Kt.c.C (toM Kt.c.C.p (2 ^ (64 * 4)) (wordsVal s₃.mem base 2048 4)) (toM Kt.c.C.p (2 ^ (64 * 4))
          (wordsVal s₃.mem base 2080 4))
          (toM Kt.c.C.p (2 ^ (64 * 4)) (wordsVal s₃.mem base 2112 4)) _
        rw [e0x, e0y, e0z, zv, ov, toM_zero, toM_one Kt.unit]
        exact ⟨rfl, hL.one_ne_zero, rfl⟩
      · show wordsVal s₃.mem base 2048 4 < Kt.c.C.p; rw [e0x, zv]; exact hp0
      · show wordsVal s₃.mem base 2080 4 < Kt.c.C.p; rw [e0y, ov]; exact Nat.mod_lt _ hp0
      · show wordsVal s₃.mem base 2112 4 < Kt.c.C.p; rw [e0z, zv]; exact hp0
    · obtain rfl : e = 1 := by omega_using [he, h]
      rw [mul_one']
      refine ⟨?_, ?_, ?_, ?_⟩
      · show Rep Kt.c.C (toM Kt.c.C.p (2 ^ (64 * 4)) (wordsVal s₃.mem base 2144 4)) (toM Kt.c.C.p (2 ^ (64 * 4))
          (wordsVal s₃.mem base 2176 4))
          (toM Kt.c.C.p (2 ^ (64 * 4)) (wordsVal s₃.mem base 2208 4)) _
        rw [e1x, e1y, e1z, ov, toM_one Kt.unit]
        exact ⟨hL.one_ne_zero, (Lean.Grind.Semiring.mul_one _).symm, (Lean.Grind.Semiring.mul_one _).symm⟩
      · show wordsVal s₃.mem base 2144 4 < Kt.c.C.p; rw [e1x]; exact hp.x
      · show wordsVal s₃.mem base 2176 4 < Kt.c.C.p; rw [e1y]; exact hp.y
      · show wordsVal s₃.mem base 2208 4 < Kt.c.C.p; rw [e1z, ov]; exact Nat.mod_lt _ hp0
  refine WP.mono (Kt.adds_ok hL hp.on 14 (Nat.le_refl _) hw₃ hK₃ hT) fun s₄ ⟨k₄, U₄, T₄⟩ => ?_
  refine ⟨((Kp.of_rest r₁).trans (Kp.of_rest r₂)).trans ((Kp.of_rest r₃).trans k₄), ?_, ?_, T₄⟩
  · exact (((O₁'.unch.trans U₂').trans U₃').trans U₄).cover (by decide)
  · exact hK₃.of_eq fun d hd => U₄.wordsVal (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> decide)

/-! ## The nibble and the entry -/

/-- The nibble `k_j` into `t2`, for `j` in `s1`. -/
theorem nibble_ok (Kt : Kit) {s : State} {base : Addr} (hw : WsReg s base) {j : Nat} (hj : j < 64)
    (h1 : s.gpr .s1 = BitVec.ofNat 64 j) :
    WP isa (.block (Cfg.nibble Kt.c)) s fun s' =>
      s'.gpr .t2 = BitVec.ofNat 64 ((wordsVal s.mem base (slot 4 K) 4 >>> (4 * j)) % 16) ∧
      Rest [.t0, .t1, .t2] s s' ∧ s'.mem = s.mem := by
  have hn := hw.nowrap
  have hal := hw.al
  obtain hq : j / 16 ≤ 3 := by omega_using [hj]
  rw [Cfg.nibble]
  k4 Kt
  refine wp_srl (by decide) fun s₁ u₁ => wp_sll (by decide) fun s₂ u₂ => wp_add fun s₃ u₃ => ?_
  obtain e₃' : s₃.gpr .t0 = base + BitVec.ofNat 64 (8 * (j / 16)) := by
    rw [u₃.gpr, u₂.gpr, u₂.other .s0 (by decide), u₁.gpr, u₁.other .s0 (by decide), hw.s0, h1]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.reducePow]
    rw [Nat.mod_eq_of_lt (by omega_using [hj] : j < 18446744073709551616),
      Nat.mod_eq_of_lt (by omega_using [hj] : j / 16 * 8 < 18446744073709551616),
      Nat.mod_eq_of_lt (by omega_using [hj] : 8 * (j / 16) < 18446744073709551616)]
    omega_using []
  obtain e₃ : ∀ d, s₃.gpr .t0 + BitVec.ofNat 64 d = off base (d + 8 * (j / 16)) := by
    intro d
    rw [e₃', BitVec.add_assoc, BitVec.ofNat_add_ofNat, off, Nat.add_comm]
  obtain r₃ : Rest [.t0] s s₃ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (u₃.rest (by decide)))
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have hK : slot 4 K = 1056 := rfl
  refine wp_ld (by decide) (e₃ (slot 4 K))
    (by simp only [off]; rw [BitVec.toNat_add, BitVec.toNat_ofNat, hK]; omega_using [hal])
    ⟨_, List.mem_append_right _ (r₃.wr ▸ hw.wr), Offset.contains_base base (by rw [hK]; omega_using [hj]) (by omega_using [hj, hK])⟩
    fun s₄ u₄ => ?_
  refine wp_sll (by decide) fun s₅ u₅ => wp_srlReg fun s₆ u₆ => wp_andi (by decide) fun s₇ u₇ => WP.block_nil ⟨?_, ?_, ?_⟩
  · have t1₅ : (s₅.gpr .t1).toNat % 64 = 4 * j % 64 := by
      rw [u₅.gpr, u₄.other .s1 (by decide), r₃.gpr .s1 (by decide), h1, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
      simp only [Nat.shiftLeft_eq, Nat.reducePow]
      omega_using []
    obtain hu := four_bits (s₄.gpr .t2) (wordsVal s.mem base (slot 4 K) 4) (j := j) fun i hi => by
      rw [u₄.gpr, m₃, BitVec.getLsbD, show 4 * j % 64 + i = (4 * j + i) % 64 by omega_using [hi],
        ← testBit_wordsVal s.mem base 4 (slot 4 K) (4 * j + i) (by omega_using [hj, hi]),
        show (4 * j + i) / 64 = j / 16 by omega_using [hi], Nat.add_comm]
    rw [u₇.gpr, u₆.gpr, t1₅, u₅.other .t2 (by decide), hu]
  · exact (r₃.mono (by decide)).trans ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans
      ((u₆.rest (by decide)).trans (u₇.rest (by decide)))))
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃]

open VG.Proof.Ecdsa.RISCV64.Joint (scansJ_ok masks4_ok wordsVal_of_words) in
open VG.Impl.Ecdsa.RISCV64.Comb (maskReg treeRegs) in
/-- The window's entry `[k_j]Q` to `E`. -/
theorem select_ok (Kt : Kit) {s : State} {base : Addr} (hw : WsReg s base) {j : Nat} (hj : j < 64)
    (h1 : s.gpr .s1 = BitVec.ofNat 64 j) {Q : Point Kt.c.C} (hT : TabTo Kt.c.C base s Q 15) :
    WP isa (.block (Cfg.select Kt.c)) s fun s' =>
      PtOk Kt.c.C base s' (pt4 EX EY EZ) (mul ((wordsVal s.mem base (slot 4 K) 4 >>> (4 * j)) % 16) Q) ∧
      Outside base 1920 96 s.mem s'.mem ∧ Rest selRegs s s' := by
  have hn := hw.nowrap
  rw [Cfg.select]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (Kt.nibble_ok hw hj h1) fun s₁ ⟨v₁, r₁, m₁⟩ => ?_)
  generalize ha : (wordsVal s.mem base (slot 4 K) 4 >>> (4 * j)) % 16 = a at v₁
  obtain ha16 : a < 16 := ha ▸ Nat.mod_lt _ (by decide)
  obtain hw₁ := hw.of_rest r₁
  refine WP.block_append (WP.mono masks4_ok fun s₂ ⟨v₂, r₂, m₂⟩ => ?_)
  obtain hw₂ := hw₁.of_rest r₂
  rw [List.cons_append, List.cons_append, List.nil_append]
  refine wp_addi (by decide) fun s₃ u₃ => wp_addi (by decide) fun s₄ u₄ => ?_
  obtain r₄ : Rest [.a0] s₂ s₄ := (u₃.rest (by decide)).trans (u₄.rest (by decide))
  obtain hw₄ := hw₂.of_rest r₄
  obtain h0 : s₄.gpr .a0 = base + BitVec.ofNat 64 2048 := by
    rw [u₄.gpr, u₃.gpr, r₂.gpr _ (by decide), r₁.gpr _ (by decide), hw.s0, BitVec.add_assoc]; rfl
  obtain hm : ∀ c < 4, s₄.gpr (maskReg c) = maskOf (a.testBit c) := fun c hc => by
    rw [r₄.gpr _ (by
      have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega_using [hc]
      rcases this with rfl | rfl | rfl | rfl <;> decide), v₂ c hc, v₁, BitVec.getLsbD_ofNat]
    simp [show c < 64 by omega_using [hc]]
  have hs : (List.range (3 * Kt.c.n)).flatMap (Cfg.scanWord Kt.c) =
      (List.range 12).flatMap (VG.Impl.Ecdsa.RISCV64.Verify.Cfg.scanWord Kt.c) := by
    rw [Kt.n4]
    refine congrArg (fun f => List.flatMap f (List.range 12)) (funext fun q => ?_)
    rw [Cfg.scanWord, VG.Impl.Ecdsa.RISCV64.Verify.Cfg.scanWord, Kt.EX_eq]; rfl
  rw [hs]
  refine WP.mono (WP.rdwr (scansJ_ok Kt.c (by k4d Kt) (by k4d Kt) (by k4d Kt) (by k4d Kt) (by k4d Kt) 12
    (by k4d Kt) hw₄ (by rw [Kt.jt]; exact h0) hm)) fun s₅ ⟨⟨v₅, O₅, k₅⟩, rd₅, wr₅, sp₅⟩ => ?_
  k4 Kt at v₅ O₅
  obtain m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, m₂, m₁]
  rw [m₄] at v₅ O₅
  rw [Nat.mod_eq_of_lt ha16] at v₅
  have v₅' : ∀ q < 12, word s₅.mem base (1920 + 8 * q) = word s.mem base (2048 + 8 * q + 96 * a) := v₅
  have O₅' : Outside base 1920 (8 * 12) s.mem s₅.mem := O₅
  obtain he : PtOk Kt.c.C base s (ent a) (mul a Q) := hT a (by omega_using [ha])
  obtain wv : ∀ c < 3, wordsVal s₅.mem base (1920 + 32 * c) 4 = wordsVal s.mem base (2048 + 96 * a + 32 * c) 4 :=
    fun c hc => wordsVal_of_words 4 fun q hq => by
      rw [show 1920 + 32 * c + 8 * q = 1920 + 8 * (4 * c + q) by omega_using [], v₅' _ (by omega_using [hc, hq])]
      congr 1; omega_using []
  refine ⟨he.move (wv 0 (by decide)) (wv 1 (by decide)) (wv 2 (by decide)), O₅'.mono (Nat.le_refl _) (by omega_using []), ?_⟩
  exact ((r₁.mono (by decide)).trans ((r₂.mono (by decide)).trans ((r₄.mono (by decide)).trans
    ⟨fun r hr => k₅.1 r (fun h => hr ((by decide : ∀ r ∈ treeRegs, r ∈ selRegs) r h)),
      rd₅, wr₅, sp₅⟩)))

/-! ## The windows -/

/-- A window. -/
theorem step_ok (Kt : Kit) (hL : Law Kt.c.C) {base : Addr} {s₀ : State} {Q : Point Kt.c.C} {k : Nat} (hP : WFix Kt.c.C base s₀ Q k)
    {j : Nat} (hj1 : 1 ≤ j) (hj : j ≤ 64) {s : State} (hI : WInv Kt.c.C base s₀ s Q k j) :
    WP isa (Cfg.step Kt.c) s fun s' => WInv Kt.c.C base s₀ s' Q k (j - 1) := by
  have hn := hI.ws.nowrap
  obtain uS : ∀ d, (d + 32 ≤ 512 ∨ 992 ≤ d) → (d + 32 ≤ 1920 ∨ 2016 ≤ d) → d + 32 ≤ 3840 →
      wordsVal s.mem base d 4 = wordsVal s₀.mem base d 4 := fun d h1 h2 h3 =>
    hI.unch.wordsVal (by simp; omega_using [h1, h2, h3]) (by omega_using [h3])
  obtain hT : TabTo Kt.c.C base s Q 15 := hP.tab.of_eq (fun d h1 h2 => uS d (by omega_using [h1]) (by omega_using [h1])
      (by omega_using [h2])) (by decide)
  rw [Cfg.step]
  k4 Kt
  refine WP.seq (wp_decCounter hj1 hI.ctr fun s₁ u₁ => ?_)
  obtain hw₁ := hI.ws.of_kc (Kc.of_rest (u₁.rest (ws := [.s1]) (by decide)))
  refine WP.mono (Kt.select_ok hw₁ (j := j - 1) (by omega_using [hj]) u₁.gpr
    (hT.of_eq (fun d _ _ => by rw [u₁.mem]) (by decide))) fun s₂ ⟨pE, O₂, r₂⟩ => ?_
  rw [u₁.mem, uS _ (by decide) (by decide) (by decide), hP.kk] at pE
  rw [u₁.mem] at O₂
  obtain hw₂ := hw₁.of_rest r₂
  obtain e₂ : ∀ d, (d + 32 ≤ 512 ∨ 992 ≤ d) → (d + 32 ≤ 1920 ∨ 2016 ≤ d) → d + 32 ≤ 3840 →
      wordsVal s₂.mem base d 4 = wordsVal s₀.mem base d 4 := fun d h1 h2 h3 => by
    rw [O₂.wordsVal (by omega_using [h2]) (by omega_using [h3]), uS d h1 h2 h3]
  obtain pR₂ : PtOk Kt.c.C base s₂ (pt4 RX RY RZ) (wpt Q k j) :=
    hI.rep.of_eq (O₂.wordsVal (by decide) (by decide)) (O₂.wordsVal (by decide) (by decide))
      (O₂.wordsVal (by decide) (by decide))
  obtain hK₂ : KC Kt.c.C base s₂ := hP.kc.of_eq fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> exact e₂ _ (by decide) (by decide) (by decide)
  obtain hX := hL.onCurve_mul hP.q (k >>> (4 * j))
  obtain h2 := hL.onCurve_add hX hX
  obtain h4 := hL.onCurve_add h2 h2
  obtain h8 := hL.onCurve_add h4 h4
  obtain h16 := hL.onCurve_add h8 h8
  obtain hE := hL.onCurve_mul hP.q ((k >>> (4 * (j - 1))) % 16)
  -- `R = 16 R`.
  refine WP.seq (WP.mono (Kt.quad_ok hL hw₂ hK₂ hX pR₂) fun s₃ ⟨K₃, U₃, pR₃⟩ => ?_)
  obtain hw₃ := hw₂.of_kp K₃
  obtain k₃ : ∀ d, (d + 32 ≤ 512 ∨ 992 ≤ d) → d + 32 ≤ 3840 → wordsVal s₃.mem base d 4 = wordsVal s₂.mem base d 4 :=
    fun d h1 h2 => U₃.wordsVal (by simp; omega_using [h1, h2]) (by omega_using [h2])
  obtain pE₃ := pE.of_eq (k₃ _ (by decide) (by decide)) (k₃ _ (by decide) (by decide)) (k₃ _ (by decide) (by decide))
  obtain hK₃ : KC Kt.c.C base s₃ := hK₂.of_eq fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> exact k₃ _ (by decide) (by decide)
  -- `T = R + E`.
  refine WP.seq (WP.mono (Kt.addPt_ok hL hw₃ hK₃ (p := pt4 RX RY RZ) (q := pt4 EX EY EZ)
    (o := pt4 TX TY TZ) ⟨by decide, by decide⟩ (by decide) h16 hE pR₃ pE₃) fun s₄ ⟨K₄, U₄, pT⟩ => ?_)
  obtain hw₄ := hw₃.of_kp K₄
  -- `R = T`.
  refine WP.mono (Kt.copyPt_ok hw₄ (o := pt4 RX RY RZ) (p := pt4 TX TY TZ) (by decide) (by decide)
    (by decide) (by decide)) fun s₅ ⟨x₅, y₅, z₅, r₅, U₅⟩ => ?_
  refine ⟨hw₄.of_rest r₅, ?_, ?_, ?_, ?_⟩
  · rw [r₅.gpr _ (by decide), K₄.gpr _ (by decide), K₃.gpr _ (by decide), r₂.gpr _ (by decide), u₁.gpr]
  · exact ((hI.keep.trans (Kc.of_rest (u₁.rest (ws := [.s1]) (by decide)))).trans (Kc.of_rest r₂)).trans
      (K₃.kc.trans (K₄.kc.trans (Kc.of_rest r₅)))
  · exact ((((hI.unch.trans (show Unch base [(1920, 96)] s.mem s₂.mem from O₂.unch)).trans U₃).trans U₄).trans
      U₅).cover (by decide)
  · have e := wstep hL hP.q k (j - 1)
    rw [show j - 1 + 1 = j by omega_using [hj1]] at e
    rw [← e]
    exact pT.move x₅ y₅ z₅

/-- `R = [k]Q`, for `k` at `K`'s slot and `Q` affine in `R`'s first two. -/
theorem body_ok (Kt : Kit) (hL : Law Kt.c.C) {base : Addr} {s : State} (hp : WPre Kt.c.C base s) :
    WP isa (Cfg.body Kt.c) s fun s' => Kc s s' ∧ Unch base bodyW s.mem s'.mem ∧
      PtOk Kt.c.C base s' (pt4 RX RY RZ) (mul (wordsVal s.mem base (slot 4 K) 4) (qOf Kt.c.C base s)) := by
  have hn := hp.ws.nowrap
  obtain hp0 : 0 < Kt.c.C.p := Kt.p0
  rw [Cfg.body]
  k4 Kt
  refine WP.seq (WP.mono (Kt.build_ok hL hp) fun s₁ ⟨K₁, U₁, hK₁, T₁⟩ => ?_)
  obtain hw₁ := hp.ws.of_kp K₁
  refine WP.seq (WP.block_append (WP.mono (Kt.copyPt_ok hw₁ (o := pt4 RX RY RZ) (p := pt4 ZERO ONEP ZERO)
    (by decide) (by decide) (by decide) (by decide)) fun s₂ ⟨x₂, y₂, z₂, r₂, U₂⟩ => ?_))
  obtain hw₂ := hw₁.of_rest r₂
  refine wp_li (imm := 64) (by decide) fun s₃ u₃ => WP.block_nil ?_
  obtain hw₃ : WsReg s₃ base := hw₂.of_kc (Kc.of_rest (u₃.rest (ws := [.s1]) (by decide)))
  obtain U₃ : Unch base [(512, 96)] s₁.mem s₃.mem := by rw [u₃.mem]; exact U₂.cover (by decide)
  obtain k₃ : ∀ d, d + 32 ≤ 512 ∨ 608 ≤ d → d + 32 ≤ 4096 → wordsVal s₃.mem base d 4 = wordsVal s₁.mem base d 4 :=
    fun d h h' => U₃.wordsVal (by simp; omega_using [h]) (by omega_using [h'])
  obtain hP : WFix Kt.c.C base s₃ (qOf Kt.c.C base s) (wordsVal s.mem base (slot 4 K) 4) :=
    ⟨hK₁.of_eq fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> exact k₃ _ (by decide) (by decide),
     T₁.of_eq (fun d h1 h2 => k₃ d (by omega_using [h1]) (by omega_using [h2])) (by decide),
     by rw [k₃ _ (by decide) (by decide), U₁.wordsVal (by decide) (by decide)], hp.on⟩
  have zv : wordsVal s₁.mem base (slot 4 ZERO) 4 = 0 := hK₁.zero
  have ov : wordsVal s₁.mem base (slot 4 ONEP) 4 = 2 ^ 256 % Kt.c.C.p := hK₁.onep
  obtain rx : wordsVal s₃.mem base (slot 4 RX) 4 = 0 := by rw [u₃.mem]; exact x₂.trans zv
  obtain ry : wordsVal s₃.mem base (slot 4 RY) 4 = 1 * 2 ^ 256 % Kt.c.C.p := by
    rw [u₃.mem, Nat.one_mul]; exact y₂.trans ov
  obtain rz : wordsVal s₃.mem base (slot 4 RZ) 4 = 0 := by rw [u₃.mem]; exact z₂.trans zv
  obtain hk : wordsVal s.mem base (slot 4 K) 4 < 2 ^ 256 := wordsVal_lt _ _ _ _
  obtain hI : WInv Kt.c.C base s₃ s₃ (qOf Kt.c.C base s) (wordsVal s.mem base (slot 4 K) 4) 64 := by
    refine ⟨hw₃, u₃.gpr, ⟨fun _ _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [wpt_top _ hk]
      show Rep Kt.c.C (tmv Kt.c.C 4 base s₃ (slot 4 RX)) (tmv Kt.c.C 4 base s₃ (slot 4 RY)) (tmv Kt.c.C 4 base s₃ (slot 4 RZ)) _
      simp only [tmv]
      rw [rx, ry, rz, toM_zero, Nat.one_mul, toM_one Kt.unit]
      exact rep_infinity' hL
    · show wordsVal _ _ (slot 4 RX) 4 < _; rw [rx]; exact hp0
    · show wordsVal _ _ (slot 4 RY) 4 < _; rw [ry]; exact Nat.mod_lt _ hp0
    · show wordsVal _ _ (slot 4 RZ) 4 < _; rw [rz]; exact hp0
  refine countLoop_ok (Inv := fun j s' => WInv Kt.c.C base s₃ s' (qOf Kt.c.C base s) (wordsVal s.mem base (slot 4 K) 4) j)
    (n := 64) (fun j s' hi => hi.ctr) (fun j s' h1 h2 hi => Kt.step_ok hL hP h1 h2 hi) (fun s' hi => ?_)
    (by decide) (by decide) hI
  refine ⟨(K₁.kc.trans (Kc.of_rest ((r₂.mono (by decide)).trans (u₃.rest (ws := [.t0, .s1]) (by decide))))).trans
    hi.keep, ((U₁.trans U₃).trans hi.unch).cover (by decide), ?_⟩
  obtain e : wpt (qOf Kt.c.C base s) (wordsVal s.mem base (slot 4 K) 4) 0 = mul (wordsVal s.mem base (slot 4 K) 4) (qOf Kt.c.C base s) := by
    simp only [wpt, Nat.mul_zero, Nat.shiftRight_zero]
  rw [← e]
  exact hi.rep
end Kit

end VG.Proof.Ecdsa.RISCV64.Window4All
