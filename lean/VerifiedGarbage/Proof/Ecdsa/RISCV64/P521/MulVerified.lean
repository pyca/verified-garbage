module

public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.MulFn
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Weierstrass.PointFacts
import VerifiedGarbage.Proof.P521.Point
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Copy
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.MulLit
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.MulFn
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Weierstrass.PointFacts
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.MulLit
public meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
public meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.WindowU
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Unsat.Fprog
public import VerifiedGarbage.Proof.Weierstrass.Jac
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.WindowA
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Joint.Table
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
meta import VerifiedGarbage.Impl.Ecdsa.RISCV64.WindowU
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Unsat.Fprog
meta import VerifiedGarbage.Proof.Weierstrass.Jac
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.WindowA
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.Joint.Table
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes

/-! ### `Ecdsa.RISCV64.P521.Window`, which this module and modules that import it used -/

section

/-!
# `vg_p521_mul` by four-bit windows in 58-bit limbs on RISC-V: the body

`WindowU.body` leaves in `R` a representative of `[k]Q` (`body_ok`), for `k`
at `K`'s slot and `Q` in limbs in `R`'s first two slots, as
`WindowA.Cfg.body` does in Montgomery's form, the coordinates being what
tight limbs stand for (`uf`, `PtOk`), and the field programs'
`Proof/Weierstrass/RISCV64/P521Unsat/Fprog.lean`'s:

* `quad_ok`: `R = 16 R`: `R`'s representative of `P` into Jacobian
  coordinates stands for `P` (`InvJ.of_toJ`), each doubling `dblJ`, for
  `a = -3`, doubles it (`InvJ.dbl'`), and back in projective coordinates,
  with `Y = 1` where `Z`'s residue is zero, it is a representative of `16 P`
  again (`InvJ.out`);
* `build_ok`: the table of `[e]Q` from byte 4096, stored through `a6` as
  verification's is (`addPt_ok`, the complete addition for any `a`);
* `select_ok`: the nibble's entry to `E`, by verification's selection;
* `step_ok`, `body_ok`: the windows, from `R = O`.
-/

@[expose] public section

-- `p`, below `2^576`, is evaluated.
set_option exponentiation.threshold 1024

namespace VG.Proof.Ecdsa.RISCV64.P521.Window

open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.WindowU
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Weierstrass.RISCV64.P521Unsat (W uf LInv ULay urcb_ok uofN_ok Tight uv packCall_ok lw)
open VG.Proof.Ecdsa.RISCV64.WindowA
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Point Fe mul onCurve)
open VG.Impl.Ecdsa.RISCV64.Window (windows)
open VG.Impl.Ecdsa.RISCV64.WindowA.Cfg (copyPt zeroPt select)

/-! ## Zero -/

theorem lw_zero (i : Nat) : lw 0 i = 0 := by simp [lw]

theorem tight_zero : Tight 0 := ⟨fun i _ => by rw [lw_zero]; decide, by rw [lw_zero]; decide⟩

theorem uf_zero : uf 0 = 0 := by
  apply Fin.ext
  simp [uf, uv, P521Unsat.lv, lw_zero]

/-- P-521's `a` is `-3`, as the doublings need. -/
theorem am3 : AM3 W := by unfold AM3; decide

theorem mul_zero' {C : Spec.Weierstrass.Curve} (P : Point C) : mul 0 P = .infinity := by
  rw [Spec.Weierstrass.mul]; rfl

theorem mul_one' {C : Spec.Weierstrass.Curve} (P : Point C) : mul 1 P = P := by
  rw [Spec.Weierstrass.mul, ite_eq_right (by decide), show (1 : Nat) / 2 = 0 from rfl, mul_zero',
    ite_eq_right (by decide)]
  rfl

/-- The registers the selection writes. -/
abbrev selRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a3, .a4]

/-- The element at slot `x`. -/
abbrev ev (base : Addr) (s : State) (x : Nat) : Fe W := uf (wordsVal s.mem base x 9)

/-- A point in the slots `p`: its coordinates tight limbs, representing `P`. -/
structure PtOk (base : Addr) (s : State) (p : Pt) (P : Point W) : Prop where
  rep : Rep W (ev base s p.x) (ev base s p.y) (ev base s p.z) P
  x : Tight (wordsVal s.mem base p.x 9)
  y : Tight (wordsVal s.mem base p.y 9)
  z : Tight (wordsVal s.mem base p.z 9)

theorem PtOk.of_eq {base : Addr} {s s' : State} {p : Pt} {P : Point W} (h : PtOk base s p P)
    (hx : wordsVal s'.mem base p.x 9 = wordsVal s.mem base p.x 9)
    (hy : wordsVal s'.mem base p.y 9 = wordsVal s.mem base p.y 9)
    (hz : wordsVal s'.mem base p.z 9 = wordsVal s.mem base p.z 9) : PtOk base s' p P :=
  ⟨by simp only [ev]; rw [hx, hy, hz]; exact h.rep, by rw [hx]; exact h.x, by rw [hy]; exact h.y,
    by rw [hz]; exact h.z⟩

/-- A point copied to other slots. -/
theorem PtOk.move {base : Addr} {s s' : State} {p q : Pt} {P : Point W} (h : PtOk base s p P)
    (hx : wordsVal s'.mem base q.x 9 = wordsVal s.mem base p.x 9)
    (hy : wordsVal s'.mem base q.y 9 = wordsVal s.mem base p.y 9)
    (hz : wordsVal s'.mem base q.z 9 = wordsVal s.mem base p.z 9) : PtOk base s' q P :=
  ⟨by simp only [ev]; rw [hx, hy, hz]; exact h.rep, by rw [hx]; exact h.x, by rw [hy]; exact h.y,
    by rw [hz]; exact h.z⟩

theorem keepU {base : Addr} {Wl : List (Nat × Nat)} {m m' : Mem} (U : Unch base Wl m m') {D : List Nat}
    (hD : ∀ d ∈ D, (∀ w ∈ Wl, d + 8 * 9 ≤ w.1 ∨ w.1 + w.2 ≤ d) ∧ d + 72 ≤ 4095) :
    ∀ d ∈ D, wordsVal m' base d 9 = wordsVal m base d 9 := fun d hd =>
  U.wordsVal (hD d hd).1 (by have := (hD d hd).2; omega_using [this])

/-! ## The constants -/

/-- The constants the windows read: `a`, `3 b` and one in limbs, and zero. -/
structure KC (base : Addr) (s : State) : Prop where
  ta : Tight (wordsVal s.mem base (c.sl UA) 9)
  va : ev base s (c.sl UA) = Fin.ofNat W.p W.a
  tb : Tight (wordsVal s.mem base (c.sl UB) 9)
  vb : ev base s (c.sl UB) = Fin.ofNat W.p (3 * W.b)
  zero : wordsVal s.mem base (c.sl ZERO) 9 = 0
  to : Tight (wordsVal s.mem base (c.sl UONE) 9)
  vo : ev base s (c.sl UONE) = 1

/-- The constants' slots. -/
abbrev kSl : List Nat := [c.sl UA, c.sl UB, c.sl ZERO, c.sl UONE]

theorem KC.of_eq {base : Addr} {s s' : State} (h : KC base s)
    (e : ∀ d ∈ kSl, wordsVal s'.mem base d 9 = wordsVal s.mem base d 9) : KC base s' := by
  obtain ea := e (c.sl UA) (by simp)
  obtain eb := e (c.sl UB) (by simp)
  obtain ez := e (c.sl ZERO) (by simp)
  obtain eo := e (c.sl UONE) (by simp)
  exact ⟨by rw [ea]; exact h.ta, by simp only [ev]; rw [ea]; exact h.va, by rw [eb]; exact h.tb,
    by simp only [ev]; rw [eb]; exact h.vb, ez.trans h.zero, by rw [eo]; exact h.to,
    by simp only [ev]; rw [eo]; exact h.vo⟩

/-! ## The complete additions -/

/-- The slots of the windows' additions. -/
abbrev jSl : List Nat :=
  [c.sl UA, c.sl UB, c.sl T0, c.sl T1, c.sl T2, c.sl T3, c.sl T4, c.sl T5,
    c.sl RX, c.sl RY, c.sl RZ, c.sl DX, c.sl DY, c.sl DZ, c.sl TX, c.sl TY, c.sl TZ,
    c.sl UONE, c.sl c.EX, c.sl c.EY, c.sl c.EZ]

theorem jLay : ULay (· ∈ jSl) :=
  ⟨by decide, fun x y hx hy => (by decide : ∀ x ∈ jSl, ∀ y ∈ jSl, x ≠ y → x + 72 ≤ y ∨ y + 72 ≤ x)
    x hx y hy, by decide⟩

/-- What the additions write. -/
abbrev addW (o : Pt) : List (Nat × Nat) :=
  (rcbW S o).map (fun w => (w, 8 * 9)) ++ [(own 9, 64 * 9)]

/-- `o = p + q` by the complete addition, for points in slots of `jSl`. -/
theorem addPt_ok (hL : Law W) {base : Addr} {s : State} (hw : WsReg s base) (hK : KC base s)
    {p q o : Pt} (hA : RcbApart S p q o)
    (hsl : ∀ x ∈ rcbW S o ++ rcbR S p q, x ∈ jSl)
    {P P' : Point W} (hP : onCurve W P = true) (hP' : onCurve W P' = true)
    (hp : PtOk base s p P) (hq : PtOk base s q P') :
    WP isa (addPt p q o) s fun s' =>
      Kp s s' ∧ Unch base (addW o) s.mem s'.mem ∧ PtOk base s' o (Spec.Weierstrass.add P P') := by
  rw [addPt]
  obtain hI : LInv base (· ∈ jSl) (rcbR S p q) (fun x => ev base s x) s := by
    refine ⟨hw, fun x hx => hsl x (List.mem_append_right _ hx), fun x hx => ?_, fun x _ => rfl⟩
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hK.ta, hK.tb, hp.x, hp.y, hp.z, hq.x, hq.y, hq.z]
  refine WP.mono (urcb_ok jLay hA hsl hI (fun x hx => hx)) fun s₁ ⟨k₁, I₁, t₁⟩ => ?_
  generalize hE : (fun x => ev base s x) = E at I₁ t₁
  obtain hrep := Rep.add hL hP hP' hp.rep hq.rep (X3 := runOps (rcb S p q o) E o.x)
    (Y3 := runOps (rcb S p q o) E o.y) (Z3 := runOps (rcb S p q o) E o.z)
    (by
      subst hE
      show rcbAdd (Fin.ofNat W.p W.a) (Fin.ofNat W.p (3 * W.b)) _ _ _ _ _ _ = _
      rw [← hK.va, ← hK.vb]
      exact t₁.1.symm)
  obtain hm : ∀ x ∈ [o.x, o.y, o.z], x ∈ rcbW S o ++ rcbR S p q :=
    fun x hx => List.mem_append_left _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [rcbW])
  refine ⟨k₁.kp, k₁.mem, ⟨?_, I₁.tight _ (hm _ (by simp)), I₁.tight _ (hm _ (by simp)),
    I₁.tight _ (hm _ (by simp))⟩⟩
  obtain vx : ev base s₁ o.x = _ := I₁.val _ (hm _ (by simp))
  obtain vy : ev base s₁ o.y = _ := I₁.val _ (hm _ (by simp))
  obtain vz : ev base s₁ o.z = _ := I₁.val _ (hm _ (by simp))
  rw [vx, vy, vz]
  exact hrep

/-! ## The slots -/

/-- The slots of `R = 16 R`'s arithmetic. -/
abbrev wSl : List Nat :=
  [c.sl UA, c.sl UB, c.sl ZERO, c.sl T0, c.sl T1, c.sl T2, c.sl T3, c.sl T4, c.sl T5,
    c.sl RX, c.sl RY, c.sl RZ, c.sl DX, c.sl DY, c.sl DZ, c.sl TX, c.sl TY, c.sl TZ]

theorem wLay : ULay (· ∈ wSl) :=
  ⟨by decide, fun x y hx hy => (by decide : ∀ x ∈ wSl, ∀ y ∈ wSl, x ≠ y → x + 72 ≤ y ∨ y + 72 ≤ x)
    x hx y hy, by decide⟩

/-- What the field operations of `R = 16 R` write: `R`, `D`, `T`, the
temporaries and the functions' own working space. -/
abbrev quadW : List (Nat × Nat) := [(1072, 1080), (7616, 576)]

/-- The slots they write. -/
abbrev quadWl : List Nat :=
  [c.sl T0, c.sl T1, c.sl T2, c.sl T3, c.sl T4, c.sl T5, c.sl RX, c.sl RY, c.sl RZ,
    c.sl DX, c.sl DY, c.sl DZ, c.sl TX, c.sl TY, c.sl TZ]

/-! ## `R = 16 R` -/

theorem dbl_apart_DT : RcbApart S (c.pt DX DY DZ) (c.pt DX DY DZ) (c.pt TX TY TZ) := ⟨by decide, by decide⟩
theorem dbl_apart_TD : RcbApart S (c.pt TX TY TZ) (c.pt TX TY TZ) (c.pt DX DY DZ) := ⟨by decide, by decide⟩
theorem toJ_apart : RcbApart S (c.pt RX RY RZ) (zeroPt c) (c.pt DX DY DZ) := ⟨by decide, by decide⟩
theorem fromJ_apart : RcbApart S (c.pt DX DY DZ) (zeroPt c) (c.pt RX RY RZ) := ⟨by decide, by decide⟩

/-- A Jacobian doubling from `p` to `o` (`D` to `T` or back). -/
theorem dblStep_ok (hL : Law W) {base : Addr} {s : State} {p o : Pt} (hA : RcbApart S p p o)
    (hsl : ∀ x ∈ rcbW S o ++ rcbR S p p, x ∈ wSl) {V : List Nat} {E : Nat → Fe W}
    (hI : LInv base (· ∈ wSl) V E s) (hV : ∀ x ∈ rcbR S p p, x ∈ V) {P : Point W}
    (hP : onCurve W P = true) (hJ : InvJ W (E p.x) (E p.y) (E p.z) P) :
    WP isa (fprog F (dblJ S p o)) s fun s' => KeepR 9 base (rcbW S o) s s' ∧
      ∃ E', LInv base (· ∈ wSl) ([o.x, o.y, o.z] ++ V) E' s' ∧ InvJ W (E' o.x) (E' o.y) (E' o.z) (d2 P) ∧
        ∀ x, x ∉ rcbW S o → E' x = E x := by
  rw [dblJ_eq]
  refine WP.mono (uofN_ok wLay dblJN_ok hA hsl hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, InvJ.dbl' hL am3 hP hJ (v.trans (dblJN_run _)), kp⟩

/-- `R` into Jacobian coordinates in `D`. -/
theorem toJStep_ok (hL : Law W) {base : Addr} {s : State} {V : List Nat} {E : Nat → Fe W}
    (hI : LInv base (· ∈ wSl) V E s) (hV : ∀ x ∈ rcbR S (c.pt RX RY RZ) (zeroPt c), x ∈ V) {P : Point W}
    (hR : Rep W (E (c.sl RX)) (E (c.sl RY)) (E (c.sl RZ)) P) (hz : E (c.sl ZERO) = 0) :
    WP isa (fprog F (toJ S (c.pt RX RY RZ) (zeroPt c) (c.pt DX DY DZ))) s fun s' =>
      KeepR 9 base (rcbW S (c.pt DX DY DZ)) s s' ∧
      ∃ E', LInv base (· ∈ wSl) ([c.sl DX, c.sl DY, c.sl DZ] ++ V) E' s' ∧
        InvJ W (E' (c.sl DX)) (E' (c.sl DY)) (E' (c.sl DZ)) P ∧
        ∀ x, x ∉ rcbW S (c.pt DX DY DZ) → E' x = E x := by
  rw [toJ_eq]
  refine WP.mono (uofN_ok wLay toJN_ok toJ_apart (by decide) hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, InvJ.of_toJ hL hR hz (v.trans (toJN_run _)), kp⟩

/-- `D` back in projective coordinates in `R`. -/
theorem fromJStep_ok {base : Addr} {s : State} {V : List Nat} {E : Nat → Fe W}
    (hI : LInv base (· ∈ wSl) V E s) (hV : ∀ x ∈ rcbR S (c.pt DX DY DZ) (zeroPt c), x ∈ V) :
    WP isa (fprog F (fromJ S (c.pt DX DY DZ) (zeroPt c) (c.pt RX RY RZ))) s fun s' =>
      KeepR 9 base (rcbW S (c.pt RX RY RZ)) s s' ∧
      ∃ E', LInv base (· ∈ wSl) ([c.sl RX, c.sl RY, c.sl RZ] ++ V) E' s' ∧
        (E' (c.sl RX), E' (c.sl RY), E' (c.sl RZ)) =
          (E (c.sl DX) * E (c.sl DZ), E (c.sl DY) + E (c.sl ZERO),
            E (c.sl DZ) * E (c.sl DZ) * E (c.sl DZ)) ∧
        ∀ x, x ∉ rcbW S (c.pt RX RY RZ) → E' x = E x := by
  rw [fromJ_eq]
  refine WP.mono (uofN_ok wLay fromJN_ok fromJ_apart (by decide) hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, v.trans (fromJN_run _), kp⟩

/-- The residue packed is zero exactly where the element is. -/
theorem pack_zero_iff {X : Nat} : X % P521Unsat.p = 0 ↔ (Fin.ofNat W.p X : Fe W) = 0 := by
  rw [Fin.ext_iff]
  simp only [Fin.val_ofNat]
  rfl

/-- `R = 16 R`, for `R` representing `P`. -/
theorem quad_ok (hL : Law W) {base : Addr} {s : State} (hw : WsReg s base) (hK : KC base s) {P : Point W}
    (hP : onCurve W P = true) (hR : PtOk base s (c.pt RX RY RZ) P) :
    WP isa quad s fun s' => Kp s s' ∧ Unch base quadW s.mem s'.mem ∧
      PtOk base s' (c.pt RX RY RZ) (d16 P) := by
  have hn := hw.nowrap
  rw [quad]
  simp only [progs]
  -- The start: `a`, `b`, zero and `R`.
  obtain hI : LInv base (· ∈ wSl) [c.sl UA, c.sl UB, c.sl ZERO, c.sl RX, c.sl RY, c.sl RZ]
      (fun x => ev base s x) s := by
    refine ⟨hw, by decide, fun x hx => ?_, fun x _ => rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hK.ta
    · exact hK.tb
    · show Tight (wordsVal s.mem base (c.sl ZERO) 9); rw [hK.zero]; exact tight_zero
    exacts [hR.x, hR.y, hR.z]
  obtain e0 : ev base s (c.sl ZERO) = 0 := by simp only [ev]; rw [hK.zero]; exact uf_zero
  -- To Jacobian coordinates.
  refine WP.seq (WP.mono (toJStep_ok hL hI (by decide) hR.rep e0) fun s₁ ⟨k₁, E₁, I₁, J₁, p₁⟩ => ?_)
  -- Four doublings.
  refine WP.seq (WP.mono (dblStep_ok hL dbl_apart_DT (by decide) I₁ (by decide) hP J₁)
    fun s₂ ⟨k₂, E₂, I₂, J₂, p₂⟩ => ?_)
  refine WP.seq (WP.mono (dblStep_ok hL dbl_apart_TD (by decide) I₂ (by decide) (hL.onCurve_add hP hP) J₂)
    fun s₃ ⟨k₃, E₃, I₃, J₃, p₃⟩ => ?_)
  obtain h4 := hL.onCurve_add (hL.onCurve_add hP hP) (hL.onCurve_add hP hP)
  refine WP.seq (WP.mono (dblStep_ok hL dbl_apart_DT (by decide) I₃ (by decide) h4 J₃)
    fun s₄ ⟨k₄, E₄, I₄, J₄, p₄⟩ => ?_)
  refine WP.seq (WP.mono (dblStep_ok hL dbl_apart_TD (by decide) I₄ (by decide) (hL.onCurve_add h4 h4) J₄)
    fun s₅ ⟨k₅, E₅, I₅, J₅, p₅⟩ => ?_)
  -- Back to projective coordinates.
  refine WP.seq (WP.mono (fromJStep_ok I₅ (by decide)) fun s₆ ⟨k₆, E₆, I₆, v₆, p₆⟩ => ?_)
  obtain z₅ : E₅ (c.sl ZERO) = 0 := by
    rw [p₅ _ (by decide), p₄ _ (by decide), p₃ _ (by decide), p₂ _ (by decide), p₁ _ (by decide)]; exact e0
  simp only [Prod.mk.injEq] at v₆
  obtain ⟨vx, vy, vz⟩ := v₆
  rw [z₅, Lean.Grind.AddCommMonoid.add_zero] at vy
  have hw₆ := I₆.ws
  obtain ltx := I₆.tight (c.sl RX) (by decide)
  obtain lty := I₆.tight (c.sl RY) (by decide)
  obtain ltz := I₆.tight (c.sl RZ) (by decide)
  obtain vx' : ev base s₆ (c.sl RX) = E₆ (c.sl RX) := I₆.val (c.sl RX) (by decide)
  obtain vy' : ev base s₆ (c.sl RY) = E₆ (c.sl RY) := I₆.val (c.sl RY) (by decide)
  obtain vz' : ev base s₆ (c.sl RZ) = E₆ (c.sl RZ) := I₆.val (c.sl RZ) (by decide)
  obtain KK₆ : KeepR 9 base quadWl s s₆ :=
    ((((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans ((k₃.mono (by decide)).trans
      (k₄.mono (by decide)))).trans ((k₅.mono (by decide)).trans (k₆.mono (by decide))))
  -- `Z`'s residue into `T0`.
  refine WP.seq (WP.mono (packCall_ok (f := F.S.fn "pack") hw₆ (o := c.sl T0) (a := c.sl RZ) (b := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ltz) fun s₇ ⟨C₇, e₇⟩ => ?_)
  obtain hw₇ := hw₆.of_kp C₇.kp
  obtain KK : KeepR 9 base quadWl s s₇ := KK₆.trans ((KeepR.of_call C₇).mono (by decide))
  have UK : Unch base (quadWl.map (fun w => (w, 8 * 9)) ++ [(own 9, 64 * 9)]) s.mem s₇.mem := KK.mem
  obtain k₇ : ∀ d ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s₇.mem base d 9 = wordsVal s₆.mem base d 9 :=
    fun d hd => outs_wordsVal C₇.mem (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd hr
      rcases hd with rfl | rfl | rfl <;> rcases hr with rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl <;> decide)
  obtain onep₇ : wordsVal s₇.mem base (c.sl UONE) 9 = wordsVal s.mem base (c.sl UONE) 9 :=
    UK.wordsVal (by decide) (by decide)
  -- `Y = 1` where `Z` is zero.
  refine WP.block_append (WP.mono (zeroMask_ok hw₇ (n := 9) (a := c.sl T0) (by decide) (by decide))
    fun s₈ ⟨r₈, m₈, a7₈⟩ => ?_)
  obtain hw₈ := hw₇.of_rest r₈
  refine WP.mono (sel_ok (decide (wordsVal s₇.mem base (c.sl T0) 9 = 0)) 9 hw₈ a7₈
    (o := c.sl RY) (a := c.sl RY) (b := c.sl UONE) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (Or.inl (Nat.le_refl _)) (by decide)) fun s₉ ⟨e₉, r₉, O₉⟩ => ?_
  rw [m₈] at e₉ O₉
  obtain ex : wordsVal s₉.mem base (c.sl RX) 9 = wordsVal s₆.mem base (c.sl RX) 9 :=
    (O₉.wordsVal (by decide) (by decide)).trans (k₇ _ (by simp))
  obtain ez : wordsVal s₉.mem base (c.sl RZ) 9 = wordsVal s₆.mem base (c.sl RZ) 9 :=
    (O₉.wordsVal (by decide) (by decide)).trans (k₇ _ (by simp))
  obtain ey : wordsVal s₇.mem base (c.sl RY) 9 = wordsVal s₆.mem base (c.sl RY) 9 := k₇ _ (by simp)
  obtain hZ : (wordsVal s₇.mem base (c.sl T0) 9 = 0) ↔ E₅ (c.sl DZ) = 0 := by
    rw [show wordsVal s₇.mem base (c.sl T0) 9 = _ from e₇, pack_zero_iff]
    show ev base s₆ (c.sl RZ) = 0 ↔ _
    rw [vz', vz]
    exact ⟨fun h => by_contra fun hz => cube_ne_zero hL hz h, fun h => by rw [h]; grind⟩
  obtain hrep := InvJ.out hL J₅
  refine ⟨KK.kp.trans ((Kp.of_rest r₈).trans (Kp.of_rest r₉)), (UK.trans O₉.unch).cover (by decide),
    ⟨?_, ?_, ?_, ?_⟩⟩
  · show Rep W (ev base s₉ (c.sl RX)) (ev base s₉ (c.sl RY)) (ev base s₉ (c.sl RZ)) _
    simp only [ev]
    rw [ex, ez]
    show Rep W (ev base s₆ (c.sl RX)) _ (ev base s₆ (c.sl RZ)) _
    rw [vx', vz', vx, vz, e₉]
    by_cases h0 : E₅ (c.sl DZ) = 0
    · have hc : decide (wordsVal s₇.mem base (c.sl T0) 9 = 0) = true := decide_eq_true (hZ.mpr h0)
      have h0' : E₅ (c.pt DX DY DZ).z = 0 := h0
      rw [show (if E₅ (c.pt DX DY DZ).z = 0 then (1 : Fe W) else E₅ (c.pt DX DY DZ).y) = 1 from
        by simp [h0']] at hrep
      simp only [hc, ↓reduceIte]
      rw [onep₇]
      rw [show uf (wordsVal s.mem base (c.sl UONE) 9) = 1 from hK.vo]
      exact hrep
    · have hc : decide (wordsVal s₇.mem base (c.sl T0) 9 = 0) = false :=
        decide_eq_false fun h => h0 (hZ.mp h)
      have h0' : ¬E₅ (c.pt DX DY DZ).z = 0 := h0
      rw [show (if E₅ (c.pt DX DY DZ).z = 0 then (1 : Fe W) else E₅ (c.pt DX DY DZ).y) =
        E₅ (c.pt DX DY DZ).y from by simp [h0']] at hrep
      simp only [hc, ↓reduceIte, Bool.false_eq_true]
      rw [ey]
      show Rep W _ (ev base s₆ (c.sl RY)) _ _
      rw [vy', vy]
      exact hrep
  · show Tight (wordsVal s₉.mem base (c.sl RX) 9)
    rw [ex]; exact ltx
  · show Tight (wordsVal s₉.mem base (c.sl RY) 9)
    rw [e₉]; split
    · rw [onep₇]; exact hK.to
    · rw [ey]; exact lty
  · show Tight (wordsVal s₉.mem base (c.sl RZ) 9)
    rw [ez]; exact ltz

/-! ## The table -/

/-- Entry `e`'s slots. -/
abbrev ent (e : Nat) : Pt := ⟨4096 + 216 * e, 4096 + 216 * e + 72, 4096 + 216 * e + 144⟩

/-- The table up to entry `m`: `[e]Q` in entry `e`. -/
abbrev TabTo (base : Addr) (s : State) (Q : Point W) (m : Nat) : Prop := ∀ e ≤ m, PtOk base s (ent e) (mul e Q)

theorem TabTo.of_eq {base : Addr} {s s' : State} {Q : Point W} {m : Nat} (h : TabTo base s Q m)
    (he : ∀ d, 4096 ≤ d → d + 72 ≤ 7552 → wordsVal s'.mem base d 9 = wordsVal s.mem base d 9) (hm : m ≤ 15) :
    TabTo base s' Q m :=
  fun e hlt => (h e hlt).of_eq (he (4096 + 216 * e) (by omega_using []) (by omega_using [hm, hlt]))
    (he (4096 + 216 * e + 72) (by omega_using []) (by omega_using [hm, hlt])) (he (4096 + 216 * e + 144) (by omega_using []) (by omega_using [hm, hlt]))

/-- `o = p`, the three coordinates one after the other, for `o`'s slots in
order and `p`'s apart from them all. -/
theorem copyPt_ok {s : State} {base : Addr} (hw : WsReg s base) {o p : Pt}
    (h8 : ∀ x ∈ [o.x, o.y, o.z, p.x, p.y, p.z], x % 8 = 0 ∧ x + 72 ≤ 4096)
    (hxy : o.x + 72 ≤ o.y) (hyz : o.y + 72 ≤ o.z)
    (hp : ∀ a ∈ [p.x, p.y, p.z], a + 72 ≤ o.x ∨ o.z + 72 ≤ a) :
    WP isa (.block (copyPt c o p)) s fun s' =>
      wordsVal s'.mem base o.x 9 = wordsVal s.mem base p.x 9 ∧ wordsVal s'.mem base o.y 9 = wordsVal s.mem base p.y 9 ∧
      wordsVal s'.mem base o.z 9 = wordsVal s.mem base p.z 9 ∧ Rest [.t0] s s' ∧
      Unch base [(o.x, 72), (o.y, 72), (o.z, 72)] s.mem s'.mem := by
  have hn := hw.nowrap
  obtain g := fun x hx => h8 x hx
  obtain gp := fun x hx => hp x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g gp
  obtain ⟨⟨ox8, ox⟩, ⟨oy8, oy⟩, ⟨oz8, oz⟩, ⟨px8, px⟩, ⟨py8, py⟩, ⟨pz8, pz⟩⟩ := g
  obtain ⟨hpx, hpy, hpz⟩ := gp
  rw [copyPt, show c.n = 9 from rfl, List.append_assoc]
  refine WP.block_append (WP.mono (copy_ok 9 hw (o := o.x) (a := p.x) ox8 px8 (by omega_using [ox]) (by omega_using [px]) (by omega_using [hxy, hyz, ox8, ox, oy8, oy, oz8, oz, px8, px, py8, py, pz8, pz, hpx, hpy, hpz]))
    fun s₁ ⟨e₁, r₁, O₁⟩ => ?_)
  obtain hw₁ := hw.of_rest r₁
  refine WP.block_append (WP.mono (copy_ok 9 hw₁ (o := o.y) (a := p.y) oy8 py8 (by omega_using [oy]) (by omega_using [py]) (by omega_using [hxy, hyz, hpy]))
    fun s₂ ⟨e₂, r₂, O₂⟩ => ?_)
  obtain hw₂ := hw₁.of_rest r₂
  refine WP.mono (copy_ok 9 hw₂ (o := o.z) (a := p.z) oz8 pz8 (by omega_using [oz]) (by omega_using [pz]) (by omega_using [hxy, hyz, ox8, ox, oy8, oy, oz8, oz, px8, px, py8, py, pz8, pz, hpx, hpy, hpz]))
    fun s₃ ⟨e₃, r₃, O₃⟩ => ⟨?_, ?_, ?_, (r₁.trans r₂).trans r₃ |>.mono (by simp), ?_⟩
  · rw [O₃.wordsVal (by omega_using [hxy, hyz]) (by omega_using [ox]), O₂.wordsVal (by omega_using [hxy]) (by omega_using [ox]), e₁]
  · rw [O₃.wordsVal (by omega_using [hyz]) (by omega_using [oy]), e₂, O₁.wordsVal (by omega_using [hxy, hyz, ox8, ox, oy8, oy, oz8, oz, px8, px, py8, py, pz8, pz, hpx, hpy, hpz]) (by omega_using [py])]
  · rw [e₃, O₂.wordsVal (by omega_using [hxy, hyz, hpz]) (by omega_using [pz]), O₁.wordsVal (by omega_using [hxy, hyz, ox8, ox, oy8, oy, oz8, oz, px8, px, py8, py, pz8, pz, hpx, hpy, hpz]) (by omega_using [pz])]
  · exact ((O₁.unch.trans O₂.unch).trans O₃.unch).mono (by simp)

/-- `D`'s slots, as `copyPt` writes them. -/
theorem dSl : ∀ w ∈ ([((c.pt DX DY DZ).x, 72), ((c.pt DX DY DZ).y, 72), ((c.pt DX DY DZ).z, 72)] : List (Nat × Nat)),
    1288 ≤ w.1 ∧ w.1 + w.2 ≤ 1504 := by decide

/-- A point in slots below byte 4095 to entry `e`. -/
theorem store_ok {s : State} {base : Addr} (hw : WsReg s base) {e : Nat} (he : e < 16) {p : Pt}
    (hs : ∀ x ∈ [p.x, p.y, p.z], x % 8 = 0 ∧ x + 72 ≤ 4095) {P : Point W} (hp : PtOk base s p P) :
    WP isa (.block (Verify.Cfg.storePt c e p)) s fun s' => PtOk base s' (ent e) P ∧ Rest [.t0, .a6] s s' ∧
      Outside base (4096 + 216 * e) 216 s.mem s'.mem := by
  have hn := hw.nowrap
  obtain g := fun x hx => hs x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g
  obtain ⟨⟨hx8, hx⟩, ⟨hy8, hy⟩, ⟨hz8, hz⟩⟩ := g
  refine WP.mono (VG.Proof.Ecdsa.RISCV64.Joint.storePt_ok c hw (e := e) (by decide) (by show 4096 + 216 * e + 216 ≤ 8192; omega_using [he])
    (by show 216 * e + 216 ≤ 4095; omega_using [he]) ⟨hx8, by show _ + 72 ≤ 4095; omega_using [hx], by show _ + 72 ≤ 4096; omega_using [hx]⟩
    ⟨hy8, by show _ + 72 ≤ 4095; omega_using [hy], by show _ + 72 ≤ 4096; omega_using [hy]⟩
    ⟨hz8, by show _ + 72 ≤ 4095; omega_using [hz], by show _ + 72 ≤ 4096; omega_using [hz]⟩) fun s' ⟨ex, ey, ez, r, O⟩ => ?_
  simp only [show Verify.Cfg.jb c = 216 from rfl, Nat.reduceMul] at ex ey ez O
  exact ⟨hp.move ex ey ez, r, O⟩

/-- While the table is built: the constants, the table up to entry `m + 1`,
`[m + 1]Q` in `D` and `Q` in `R`'s first two slots and one's. -/
structure AI (base : Addr) (s : State) (Q : Point W) (m : Nat) : Prop where
  ws : WsReg s base
  kc : KC base s
  tab : TabTo base s Q (m + 1)
  d : PtOk base s (c.pt DX DY DZ) (mul (m + 1) Q)
  q : PtOk base s (c.pt RX RY UONE) Q

/-- What the table's additions write. -/
abbrev addsW : List (Nat × Nat) := [(1288, 864), (4096, 3456), (7616, 576)]

/-- An addition's writes into `T`, within `addsW`, and apart from the table. -/
theorem addW_T : ∀ w ∈ addW (c.pt TX TY TZ), (∃ w' ∈ addsW, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2) ∧
    (w.1 + w.2 ≤ 4096 ∨ 7552 ≤ w.1) := by decide

/-- `copyPt`'s writes into `D`, within `addsW`. -/
theorem dW : ∀ w ∈ ([((c.pt DX DY DZ).x, 72), ((c.pt DX DY DZ).y, 72), ((c.pt DX DY DZ).z, 72)] : List (Nat × Nat)),
    ∃ w' ∈ addsW, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := by decide

/-- Entry `e`'s bytes, within `addsW`. -/
theorem entW {e : Nat} (he : e < 16) : ∃ w' ∈ addsW, w'.1 ≤ 4096 + 216 * e ∧ 4096 + 216 * e + 216 ≤ w'.1 + w'.2 :=
  ⟨(4096, 3456), List.mem_cons_of_mem _ List.mem_cons_self, by simp only; omega_using [], by simp only; omega_using [he]⟩

/-- Entry `e`, kept by memory unchanged there. -/
theorem ent_of {base : Addr} {s s' : State} {e : Nat} {P : Point W} (h : PtOk base s (ent e) P)
    (k : ∀ d, 4096 + 216 * e ≤ d → d + 72 ≤ 4096 + 216 * e + 216 → wordsVal s'.mem base d 9 = wordsVal s.mem base d 9) :
    PtOk base s' (ent e) P :=
  h.of_eq (k (4096 + 216 * e) (Nat.le_refl _) (by omega_using [])) (k (4096 + 216 * e + 72) (by omega_using []) (by omega_using []))
    (k (4096 + 216 * e + 144) (by omega_using []) (by omega_using []))

/-- The constants and `Q`'s slots: apart from `D` and below the table. -/
abbrev cqSl : List Nat := kSl ++ [c.sl RX, c.sl RY]

/-- The additions of `[e]Q` for `e = 2 … m + 1`. -/
theorem adds_ok (hL : Law W) {base : Addr} {Q : Point W} (hQ : onCurve W Q = true) :
    ∀ m ≤ 14, ∀ {s : State}, AI base s Q 0 →
      WP isa (adds m) s fun s' => Kp s s' ∧ Unch base addsW s.mem s'.mem ∧ AI base s' Q m
  | 0, _, s, h => WP.block_nil ⟨Kp.refl _, Unch.refl _ _ _, h⟩
  | m + 1, hm, s, h => by
    rw [adds]
    refine WP.seq (WP.mono (adds_ok hL hQ m (by omega_using [hm]) h) fun s₁ ⟨k₁, U₁, A₁⟩ => ?_)
    have hw₁ := A₁.ws
    have hn := hw₁.nowrap
    -- `T = D + Q`.
    refine WP.seq (WP.mono (addPt_ok hL hw₁ A₁.kc (p := c.pt DX DY DZ) (q := c.pt RX RY UONE)
      (o := c.pt TX TY TZ) ⟨by decide, by decide⟩ (by decide) (hL.onCurve_mul hQ _) hQ A₁.d A₁.q)
      fun s₂ ⟨k₂, U₂, p₂⟩ => ?_)
    rw [mul_succ' hL hQ, show m + 1 + 1 = m + 2 by omega_using []] at p₂
    obtain hw₂ := hw₁.of_kp k₂
    obtain e₂ : ∀ d ∈ cqSl, wordsVal s₂.mem base d 9 = wordsVal s₁.mem base d 9 := keepU U₂ (by decide)
    obtain far₂ : ∀ d, 4096 ≤ d → d + 72 ≤ 7552 → wordsVal s₂.mem base d 9 = wordsVal s₁.mem base d 9 :=
      fun d h1 h2 => U₂.wordsVal (fun w hw => by have := (addW_T w hw).2; omega_using [h1, h2, this]) (by omega_using [h2])
    -- Stored to entry `m + 2`.
    refine WP.block_append (WP.mono (store_ok hw₂ (e := m + 2) (by omega_using [hm]) (by decide) p₂)
      fun s₃ ⟨p₃, r₃, O₃⟩ => ?_)
    obtain hw₃ := hw₂.of_rest r₃
    obtain e₃ : ∀ d, d + 72 ≤ 4095 → wordsVal s₃.mem base d 9 = wordsVal s₂.mem base d 9 := fun d hd =>
      O₃.wordsVal (by omega_using [hd]) (by omega_using [hd])
    obtain pT₃ : PtOk base s₃ (c.pt TX TY TZ) (mul (m + 2) Q) :=
      p₂.of_eq (e₃ _ (by decide)) (e₃ _ (by decide)) (e₃ _ (by decide))
    -- `D = T`.
    refine WP.mono (copyPt_ok hw₃ (o := c.pt DX DY DZ) (p := c.pt TX TY TZ) (by decide) (by decide) (by decide)
      (by decide)) fun s₄ ⟨x₄, y₄, z₄, r₄, U₄⟩ => ?_
    obtain e₄ : ∀ d, (d + 72 ≤ 1288 ∨ 1504 ≤ d) → d + 72 ≤ 8192 → wordsVal s₄.mem base d 9 = wordsVal s₃.mem base d 9 :=
      fun d h1 h2 => U₄.wordsVal (fun w hw => by have := dSl w hw; omega_using [h1, this]) (by omega_using [h2])
    obtain kd : ∀ d ∈ cqSl, wordsVal s₄.mem base d 9 = wordsVal s₁.mem base d 9 := fun d hd => by
      obtain hd' : (d + 72 ≤ 1288 ∨ 1504 ≤ d) ∧ d + 72 ≤ 4095 :=
        (by decide : ∀ d ∈ cqSl, (d + 72 ≤ 1288 ∨ 1504 ≤ d) ∧ d + 72 ≤ 4095) d hd
      rw [e₄ d hd'.1 (by omega_using [hd']), e₃ d hd'.2, e₂ d hd]
    refine ⟨k₁.trans (k₂.trans ((Kp.of_rest r₃).trans (Kp.of_rest r₄))), ?_, ⟨hw₃.of_rest r₄, ?_, ?_, ?_, ?_⟩⟩
    · refine (((U₁.trans U₂).trans O₃.unch).trans U₄).cover fun w hw => ?_
      rcases List.mem_append.mp hw with hw | hw
      · rcases List.mem_append.mp hw with hw | hw
        · rcases List.mem_append.mp hw with hw | hw
          · exact ⟨w, hw, Nat.le_refl _, Nat.le_refl _⟩
          · exact (addW_T w hw).1
        · rw [List.mem_singleton] at hw
          subst hw
          exact entW (by omega_using [hm])
      · exact dW w hw
    · exact A₁.kc.of_eq fun d hd => kd d (List.mem_append_left _ hd)
    · intro e he
      rcases Nat.lt_or_ge e (m + 2) with h | h
      · have pe := A₁.tab e (by omega_using [h])
        exact ent_of pe fun d h1 h2 => by
          rw [e₄ d (.inr (by omega_using [h1])) (by omega_using [hm, he, h2]), O₃.wordsVal (by omega_using [h, h2]) (by omega_using [hm, he, h2]), far₂ d (by omega_using [h1]) (by omega_using [hm, he, h2])]
      · obtain rfl : e = m + 2 := by omega_using [he, h]
        exact ent_of p₃ fun d h1 h2 => e₄ d (.inr (by omega_using [h1])) (by omega_using [h2, hm])
    · exact pT₃.move x₄ y₄ z₄
    · exact A₁.q.of_eq (kd _ (by decide)) (kd _ (by decide)) (kd _ (by decide))

/-- `Q`, the affine point of `R`'s first two slots. -/
abbrev qOf (base : Addr) (s : State) : Point W := .affine (ev base s (c.sl RX)) (ev base s (c.sl RY))

/-- What the table's construction writes. -/
abbrev buildW : List (Nat × Nat) := [(1288, 864), (4096, 3456), (7616, 576)]

/-- What the body reads at the start. -/
structure WPre (base : Addr) (s : State) : Prop where
  ws : WsReg s base
  kc : KC base s
  x : Tight (wordsVal s.mem base (c.sl RX) 9)
  y : Tight (wordsVal s.mem base (c.sl RY) 9)
  on : onCurve W (qOf base s) = true

/-- The table of `[e]Q`. -/
theorem build_ok (hL : Law W) {base : Addr} {s : State} (hp : WPre base s) :
    WP isa build s fun s' => Kp s s' ∧ Unch base buildW s.mem s'.mem ∧ KC base s' ∧
      TabTo base s' (qOf base s) 15 ∧
      ∀ d, d + 72 ≤ 1288 ∨ (2152 ≤ d ∧ d + 72 ≤ 4095) → wordsVal s'.mem base d 9 = wordsVal s.mem base d 9 := by
  have hw := hp.ws
  have hn := hw.nowrap
  have hK := hp.kc
  obtain h0 : ev base s (c.sl ZERO) = 0 := by simp only [ev]; rw [hK.zero]; exact uf_zero
  obtain t0 : Tight (wordsVal s.mem base (c.sl ZERO) 9) := by rw [hK.zero]; exact tight_zero
  obtain pO : PtOk base s (c.pt ZERO UONE ZERO) (mul 0 (qOf base s)) := by
    refine ⟨?_, t0, hK.to, t0⟩
    show Rep W (ev base s (c.sl ZERO)) (ev base s (c.sl UONE)) (ev base s (c.sl ZERO)) _
    rw [h0, hK.vo, mul_zero']
    exact rep_infinity' hL
  obtain pQ : PtOk base s (c.pt RX RY UONE) (qOf base s) := by
    refine ⟨?_, hp.x, hp.y, hK.to⟩
    show Rep W (ev base s (c.sl RX)) (ev base s (c.sl RY)) (ev base s (c.sl UONE)) _
    rw [hK.vo]
    exact rep_affine' hL _ _
  rw [build, List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (store_ok hw (e := 0) (by decide) (by decide) pO)
    fun s₁ ⟨p₁, r₁, O₁⟩ => ?_))
  obtain hw₁ := hw.of_rest r₁
  obtain e₁ : ∀ d, d + 72 ≤ 4095 → wordsVal s₁.mem base d 9 = wordsVal s.mem base d 9 := fun d hd =>
    O₁.wordsVal (by omega_using [hd]) (by omega_using [hd])
  refine WP.block_append (WP.mono (store_ok hw₁ (e := 1) (by decide) (by decide)
    (pQ.of_eq (e₁ _ (by decide)) (e₁ _ (by decide)) (e₁ _ (by decide)))) fun s₂ ⟨p₂, r₂, O₂⟩ => ?_)
  obtain hw₂ := hw₁.of_rest r₂
  obtain e₂ : ∀ d, d + 72 ≤ 4095 → wordsVal s₂.mem base d 9 = wordsVal s.mem base d 9 := fun d hd => by
    rw [O₂.wordsVal (by omega_using [hd]) (by omega_using [hd]), e₁ d hd]
  refine WP.mono (copyPt_ok hw₂ (o := c.pt DX DY DZ) (p := c.pt RX RY UONE) (by decide) (by decide) (by decide)
    (by decide)) fun s₃ ⟨x₃, y₃, z₃, r₃, U₃⟩ => ?_
  obtain hw₃ := hw₂.of_rest r₃
  obtain e₃ : ∀ d, (d + 72 ≤ 1288 ∨ 1504 ≤ d) → d + 72 ≤ 8192 → wordsVal s₃.mem base d 9 = wordsVal s₂.mem base d 9 :=
    fun d h1 h2 => U₃.wordsVal (fun w hw => by have := dSl w hw; omega_using [h1, this]) (by omega_using [h2])
  obtain e₃₀ : ∀ d, d + 72 ≤ 1288 ∨ (1504 ≤ d ∧ d + 72 ≤ 4095) →
      wordsVal s₃.mem base d 9 = wordsVal s.mem base d 9 := fun d hd => by
    rw [e₃ d (by omega_using [hd]) (by omega_using [hd]), e₂ d (by omega_using [hd])]
  obtain pQ₃ : PtOk base s₃ (c.pt RX RY UONE) (qOf base s) :=
    pQ.of_eq (e₃₀ _ (.inl (by decide))) (e₃₀ _ (.inl (by decide))) (e₃₀ _ (.inr (by decide)))
  obtain hA : AI base s₃ (qOf base s) 0 := by
    refine ⟨hw₃, hK.of_eq fun d hd => e₃₀ d ((by decide : ∀ d ∈ kSl, d + 72 ≤ 1288 ∨ (1504 ≤ d ∧ d + 72 ≤ 4095))
      d hd), fun e he => ?_, ?_, pQ₃⟩
    · rcases Nat.lt_or_ge e 1 with h | h
      · obtain rfl : e = 0 := by omega_using [h]
        exact p₁.of_eq ((e₃ _ (.inr (by decide)) (by decide)).trans (O₂.wordsVal (by decide) (by decide)))
          ((e₃ _ (.inr (by decide)) (by decide)).trans (O₂.wordsVal (by decide) (by decide)))
          ((e₃ _ (.inr (by decide)) (by decide)).trans (O₂.wordsVal (by decide) (by decide)))
      · obtain rfl : e = 1 := by omega_using [he, h]
        rw [mul_one']
        exact p₂.of_eq (e₃ _ (.inr (by decide)) (by decide)) (e₃ _ (.inr (by decide)) (by decide))
          (e₃ _ (.inr (by decide)) (by decide))
    · rw [mul_one']
      exact (pQ.of_eq (e₂ _ (by decide)) (e₂ _ (by decide)) (e₂ _ (by decide))).move x₃ y₃ z₃
  refine WP.mono (adds_ok hL hp.on 14 (Nat.le_refl _) hA) fun s₄ ⟨k₄, U₄, A₄⟩ => ?_
  refine ⟨((Kp.of_rest r₁).trans (Kp.of_rest r₂)).trans ((Kp.of_rest r₃).trans k₄), ?_, A₄.kc, A₄.tab, ?_⟩
  · refine (((O₁.unch.trans O₂.unch).trans U₃).trans U₄).cover fun w hw => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with (((hw | hw) | hw) | hw)
    · subst hw; exact ⟨(4096, 3456), by simp, by decide, by decide⟩
    · subst hw; exact ⟨(4096, 3456), by simp, by decide, by decide⟩
    · rcases hw with rfl | rfl | rfl <;> exact ⟨(1288, 864), by simp, by decide, by decide⟩
    · exact ⟨w, by simpa using hw, Nat.le_refl _, Nat.le_refl _⟩
  · intro d hd
    rw [U₄.wordsVal (by simp; omega_using [hd]) (by omega_using [hd]), e₃₀ d (by omega_using [hd])]

/-! ## The nibble's entry -/

open VG.Proof.Ecdsa.RISCV64.Joint (scansJ_ok masks4_ok wordsVal_of_words wp_addAt) in
open VG.Impl.Ecdsa.RISCV64.Comb (maskReg treeRegs) in
/-- The window's entry `[k_j]Q` to `E`. -/
theorem select_ok {s : State} {base : Addr} (hw : WsReg s base) {j : Nat} (hj : j < 144)
    (h1 : s.gpr .s1 = BitVec.ofNat 64 j) {Q : Point W} (hT : TabTo base s Q 15) :
    WP isa (.block (select c)) s fun s' =>
      PtOk base s' (c.pt c.EX c.EY c.EZ) (mul ((wordsVal s.mem base (c.sl K) 9 >>> (4 * j)) % 16) Q) ∧
      Outside base 3376 216 s.mem s'.mem ∧ Rest selRegs s s' := by
  have hn := hw.nowrap
  rw [select]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (nibble_ok c hw hj (by decide) h1) fun s₁ ⟨v₁, r₁, m₁⟩ => ?_)
  generalize ha : (wordsVal s.mem base (c.sl K) 9 >>> (4 * j)) % 16 = a at v₁
  obtain ha16 : a < 16 := ha ▸ Nat.mod_lt _ (by decide)
  obtain hw₁ := hw.of_rest r₁
  refine WP.block_append (WP.mono masks4_ok fun s₂ ⟨v₂, r₂, m₂⟩ => ?_)
  obtain hw₂ := hw₁.of_rest r₂
  refine wp_addAt (by decide) fun s₄ u₄ => ?_
  obtain r₄ : Rest [.a0] s₂ s₄ := u₄.rest (by decide)
  obtain hw₄ := hw₂.of_rest r₄
  obtain h0 : s₄.gpr .a0 = base + BitVec.ofNat 64 c.jt := by
    rw [u₄.gpr, r₂.gpr _ (by decide), r₁.gpr _ (by decide), hw.s0]
  obtain hm : ∀ b < 4, s₄.gpr (maskReg b) = maskOf (a.testBit b) := fun b hb => by
    rw [r₄.gpr _ (by
      have : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by omega_using [hb]
      rcases this with rfl | rfl | rfl | rfl <;> decide), v₂ b hb, v₁, BitVec.getLsbD_ofNat]
    simp [show b < 64 by omega_using [hb]]
  refine WP.mono (WP.rdwr (scansJ_ok c (by decide) (by decide) (by decide) (by decide) (by decide) 27
    (Nat.le_refl _) hw₄ h0 hm)) fun s₅ ⟨⟨v₅, O₅, k₅⟩, rd₅, wr₅, sp₅⟩ => ?_
  simp only [show c.sl c.EX = 3376 from rfl, Nat.reduceMul] at v₅ O₅
  obtain m₄ : s₄.mem = s.mem := by rw [u₄.mem, m₂, m₁]
  rw [m₄] at v₅ O₅
  rw [Nat.mod_eq_of_lt ha16] at v₅
  obtain he : PtOk base s (ent a) (mul a Q) := hT a (by omega_using [ha])
  obtain wv : ∀ b < 3, wordsVal s₅.mem base (3376 + 72 * b) 9 = wordsVal s.mem base (4096 + 216 * a + 72 * b) 9 :=
    fun b hb => wordsVal_of_words 9 fun q hq => by
      rw [show 3376 + 72 * b + 8 * q = 3376 + 8 * (9 * b + q) by omega_using [], v₅ _ (by omega_using [hb, hq])]
      congr 1; omega_using []
  refine ⟨he.move (wv 0 (by decide)) (wv 1 (by decide)) (wv 2 (by decide)), O₅.mono (Nat.le_refl _) (by omega_using []), ?_⟩
  exact ((r₁.mono (by decide)).trans ((r₂.mono (by decide)).trans ((r₄.mono (by decide)).trans
    ⟨fun r hr => k₅.1 r (fun h => hr ((by decide : ∀ r ∈ treeRegs, r ∈ selRegs) r h)),
      rd₅, wr₅, sp₅⟩)))

/-! ## The windows -/

/-- What the windows read and keep, from `s₀`. -/
structure WFix (base : Addr) (s₀ : State) (Q : Point W) (k : Nat) : Prop where
  kc : KC base s₀
  tab : TabTo base s₀ Q 15
  kk : wordsVal s₀.mem base (c.sl K) 9 = k
  q : onCurve W Q = true

/-- What the windows write. -/
abbrev stepW : List (Nat × Nat) := [(1072, 1080), (3376, 216), (7616, 576)]

/-- The loop's invariant at `s1 = j`: `R` represents `[k >>> 4 j]Q`. -/
structure WInv (base : Addr) (s₀ s : State) (Q : Point W) (k j : Nat) : Prop where
  ws : WsReg s base
  ctr : s.gpr .s1 = BitVec.ofNat 64 j
  keep : Kc s₀ s
  unch : Unch base stepW s₀.mem s.mem
  rep : PtOk base s (c.pt RX RY RZ) (wpt Q k j)

/-- Slots apart from what a window writes. -/
theorem stepW_far {base : Addr} {m m' : Mem} (U : Unch base stepW m m') {d : Nat}
    (h1 : d + 72 ≤ 1072 ∨ 2152 ≤ d) (h2 : d + 72 ≤ 3376 ∨ 3592 ≤ d) (h3 : d + 72 ≤ 7616) :
    wordsVal m' base d 9 = wordsVal m base d 9 :=
  U.wordsVal (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_using [h1, h2, h3]) (by omega_using [h3])

/-- A window. -/
theorem step_ok (hL : Law W) {base : Addr} {s₀ : State} {Q : Point W} {k : Nat} (hP : WFix base s₀ Q k)
    {j : Nat} (hj1 : 1 ≤ j) (hj : j ≤ 144) {s : State} (hI : WInv base s₀ s Q k j) :
    WP isa step s fun s' => WInv base s₀ s' Q k (j - 1) := by
  have hn := hI.ws.nowrap
  obtain hT : TabTo base s Q 15 := hP.tab.of_eq (fun d h1 h2 => stepW_far hI.unch (.inr (by omega_using [h1]))
    (.inr (by omega_using [h1])) (by omega_using [h2])) (by decide)
  rw [step]
  refine WP.seq (wp_decCounter hj1 hI.ctr fun s₁ u₁ => ?_)
  obtain hw₁ := hI.ws.of_kc (Kc.of_rest (u₁.rest (ws := [.s1]) (by decide)))
  refine WP.mono (select_ok hw₁ (j := j - 1) (by omega_using [hj]) u₁.gpr
    (hT.of_eq (fun d _ _ => by rw [u₁.mem]) (by decide))) fun s₂ ⟨pE, O₂, r₂⟩ => ?_
  rw [u₁.mem, stepW_far hI.unch (d := c.sl K) (.inr (by decide)) (.inl (by decide)) (by decide), hP.kk] at pE
  rw [u₁.mem] at O₂
  obtain hw₂ := hw₁.of_rest r₂
  obtain e₂ : ∀ d, (d + 72 ≤ 1072 ∨ 2152 ≤ d) → (d + 72 ≤ 3376 ∨ 3592 ≤ d) → d + 72 ≤ 7616 →
      wordsVal s₂.mem base d 9 = wordsVal s₀.mem base d 9 := fun d h1 h2 h3 => by
    rw [O₂.wordsVal (by omega_using [h2]) (by omega_using [h3]), stepW_far hI.unch h1 h2 h3]
  obtain pR₂ : PtOk base s₂ (c.pt RX RY RZ) (wpt Q k j) :=
    hI.rep.of_eq (O₂.wordsVal (by decide) (by decide)) (O₂.wordsVal (by decide) (by decide))
      (O₂.wordsVal (by decide) (by decide))
  obtain hK₂ : KC base s₂ := hP.kc.of_eq fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> exact e₂ _ (by decide) (by decide) (by decide)
  obtain hX := hL.onCurve_mul hP.q (k >>> (4 * j))
  obtain h2 := hL.onCurve_add hX hX
  obtain h4 := hL.onCurve_add h2 h2
  obtain h8 := hL.onCurve_add h4 h4
  obtain h16 := hL.onCurve_add h8 h8
  obtain hE := hL.onCurve_mul hP.q ((k >>> (4 * (j - 1))) % 16)
  -- `R = 16 R`.
  refine WP.seq (WP.mono (quad_ok hL hw₂ hK₂ hX pR₂) fun s₃ ⟨K₃, U₃, pR₃⟩ => ?_)
  obtain hw₃ := hw₂.of_kp K₃
  obtain k₃ : ∀ d, (d + 72 ≤ 1072 ∨ 2152 ≤ d) → d + 72 ≤ 7616 → wordsVal s₃.mem base d 9 = wordsVal s₂.mem base d 9 :=
    fun d h1 h2 => U₃.wordsVal (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_using [h1, h2])
      (by omega_using [h2])
  obtain pE₃ := pE.of_eq (k₃ _ (by decide) (by decide)) (k₃ _ (by decide) (by decide)) (k₃ _ (by decide) (by decide))
  obtain hK₃ : KC base s₃ := hK₂.of_eq fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> exact k₃ _ (by decide) (by decide)
  -- `T = R + E`.
  refine WP.seq (WP.mono (addPt_ok hL hw₃ hK₃ (p := c.pt RX RY RZ) (q := c.pt c.EX c.EY c.EZ)
    (o := c.pt TX TY TZ) ⟨by decide, by decide⟩ (by decide) h16 hE pR₃ pE₃) fun s₄ ⟨K₄, U₄, pT⟩ => ?_)
  obtain hw₄ := hw₃.of_kp K₄
  -- `R = T`.
  refine WP.mono (copyPt_ok hw₄ (o := c.pt RX RY RZ) (p := c.pt TX TY TZ) (by decide) (by decide)
    (by decide) (by decide)) fun s₅ ⟨x₅, y₅, z₅, r₅, U₅⟩ => ?_
  refine ⟨hw₄.of_rest r₅, ?_, ?_, ?_, ?_⟩
  · rw [r₅.gpr _ (by decide), K₄.gpr _ (by decide), K₃.gpr _ (by decide), r₂.gpr _ (by decide), u₁.gpr]
  · exact ((hI.keep.trans (Kc.of_rest (u₁.rest (ws := [.s1]) (by decide)))).trans (Kc.of_rest r₂)).trans
      (K₃.kc.trans (K₄.kc.trans (Kc.of_rest r₅)))
  · exact ((((hI.unch.trans (show Unch base [(3376, 216)] s.mem s₂.mem from O₂.unch)).trans U₃).trans U₄).trans
      U₅).cover (by decide)
  · have e := wstep hL hP.q k (j - 1)
    rw [show j - 1 + 1 = j by omega_using [hj1]] at e
    rw [← e]
    exact pT.move x₅ y₅ z₅

/-! ## The body -/

/-- What the body writes. -/
abbrev bodyW : List (Nat × Nat) := [(1072, 1080), (3376, 216), (4096, 3456), (7616, 576)]

/-- `R = [k]Q`, for `k` at `K`'s slot and `Q` affine in `R`'s first two. -/
theorem body_ok (hL : Law W) {base : Addr} {s : State} (hp : WPre base s) :
    WP isa body s fun s' => Kc s s' ∧ Unch base bodyW s.mem s'.mem ∧
      PtOk base s' (c.pt RX RY RZ) (mul (wordsVal s.mem base (c.sl K) 9) (qOf base s)) := by
  have hn := hp.ws.nowrap
  rw [body]
  refine WP.seq (WP.mono (build_ok hL hp) fun s₁ ⟨K₁, U₁, hK₁, T₁, e₁⟩ => ?_)
  obtain hw₁ := hp.ws.of_kp K₁
  refine WP.seq (WP.block_append (WP.mono (copyPt_ok hw₁ (o := c.pt RX RY RZ) (p := c.pt ZERO UONE ZERO)
    (by decide) (by decide) (by decide) (by decide)) fun s₂ ⟨x₂, y₂, z₂, r₂, U₂⟩ => ?_))
  obtain hw₂ := hw₁.of_rest r₂
  refine wp_li (imm := 144) (by decide) fun s₃ u₃ => WP.block_nil ?_
  obtain hw₃ : WsReg s₃ base := hw₂.of_kc (Kc.of_rest (u₃.rest (ws := [.s1]) (by decide)))
  obtain U₃ : Unch base [(1072, 216)] s₁.mem s₃.mem := by rw [u₃.mem]; exact U₂.cover (by decide)
  obtain k₃ : ∀ d, d + 72 ≤ 1072 ∨ 1288 ≤ d → d + 72 ≤ 8192 → wordsVal s₃.mem base d 9 = wordsVal s₁.mem base d 9 :=
    fun d h h' => U₃.wordsVal (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; omega_using [h])
      (by omega_using [h'])
  obtain hP : WFix base s₃ (qOf base s) (wordsVal s.mem base (c.sl K) 9) :=
    ⟨hK₁.of_eq fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> exact k₃ _ (by decide) (by decide),
     T₁.of_eq (fun d h1 h2 => k₃ d (by omega_using [h1]) (by omega_using [h2])) (by decide),
     by rw [k₃ _ (by decide) (by decide), U₁.wordsVal (by decide) (by decide)], hp.on⟩
  have zv : wordsVal s₁.mem base (c.sl ZERO) 9 = 0 := hK₁.zero
  obtain rx : wordsVal s₃.mem base (c.sl RX) 9 = 0 := by rw [u₃.mem]; exact x₂.trans zv
  obtain ry : wordsVal s₃.mem base (c.sl RY) 9 = wordsVal s₁.mem base (c.sl UONE) 9 := by rw [u₃.mem]; exact y₂
  obtain rz : wordsVal s₃.mem base (c.sl RZ) 9 = 0 := by rw [u₃.mem]; exact z₂.trans zv
  obtain hk : wordsVal s.mem base (c.sl K) 9 < 2 ^ (64 * 9) := wordsVal_lt _ _ _ _
  obtain hI : WInv base s₃ s₃ (qOf base s) (wordsVal s.mem base (c.sl K) 9) 144 := by
    refine ⟨hw₃, u₃.gpr, ⟨fun _ _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [show (144 : Nat) = 16 * 9 from rfl, wpt_top _ hk]
      show Rep W (ev base s₃ (c.sl RX)) (ev base s₃ (c.sl RY)) (ev base s₃ (c.sl RZ)) _
      simp only [ev]
      rw [rx, ry, rz, uf_zero, show uf (wordsVal s₁.mem base (c.sl UONE) 9) = 1 from hK₁.vo]
      exact rep_infinity' hL
    · show Tight (wordsVal _ _ (c.sl RX) 9); rw [rx]; exact tight_zero
    · show Tight (wordsVal _ _ (c.sl RY) 9); rw [ry]; exact hK₁.to
    · show Tight (wordsVal _ _ (c.sl RZ) 9); rw [rz]; exact tight_zero
  refine countLoop_ok (Inv := fun j s' => WInv base s₃ s' (qOf base s) (wordsVal s.mem base (c.sl K) 9) j)
    (n := 144) (fun j s' hi => hi.ctr) (fun j s' h1 h2 hi => step_ok hL hP h1 h2 hi) (fun s' hi => ?_)
    (by decide) (by decide) hI
  refine ⟨(K₁.kc.trans (Kc.of_rest ((r₂.mono (by decide)).trans (u₃.rest (ws := [.t0, .s1]) (by decide))))).trans
    hi.keep, ((U₁.trans U₃).trans hi.unch).cover (by decide), ?_⟩
  rw [← wpt_zero]
  exact hi.rep

end VG.Proof.Ecdsa.RISCV64.P521.Window

end

end

/-!
# `vg_p521_mul` on RISC-V: the contract

The facts of `Impl.Weierstrass.Mul.Curve.mulInRangeContract` for P-521 on
RISC-V, by register (`mulRVc`: `ws` in `a0`), and `mulFn` meets them
(`mul_rv`), given the group law: the saves of `s0`, `s1` and `ra` (past the
numbered slots, in the contract's tail), the windows' `body_ok`, and the loads that
restore them. The coordinates the specification decodes are the proofs'
(`Point.dec_eq`, given Fermat's little theorem from the group law), and
`Represents` is `Rep`. What the function writes is its own working space or
the result's (`keeps_of_unch`).
-/

-- `p`, below `2^521`, is evaluated.
set_option exponentiation.threshold 1024

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P521

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Spec.Weierstrass (Curve Fe Point)

/-- P-521's curve of `Proof/Weierstrass/MulContract.lean`. -/
abbrev MC : Impl.Weierstrass.Mul.Curve := Impl.Weierstrass.Mul.p521

/-- `vg_p521_mul(ws = a0)`. -/
def mulRVc : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .a0, 8192⟩] ∧ (s.gpr .a0).toNat + 8192 ≤ 2 ^ 64 ∧
    (s.gpr .a0).toNat % 8 = 0 ∧ MC.ConstsOk (s.gpr .a0) s.mem ∧ MC.PointOk (s.gpr .a0) s.mem
  post s s' := MC.ResultInRange (MC.scalar (s.gpr .a0) s.mem) (MC.point (s.gpr .a0) s.mem) (s.gpr .a0) s.mem s'.mem
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0

/-- `Represents` is the proofs' `Rep`. -/
theorem represents_of_rep {C : Curve} {X Y Z : Fe C} {P : Point C}
    (h : Rep C X Y Z P) : Impl.Weierstrass.MulBase.Represents X Y Z P := by
  cases P <;> exact h

/-- The coordinate at an offset below `2³²` is the number `wordsVal` reads. -/
theorem coordAt_eq (m : Mem) (ws : Addr) {o : Nat} (ho : o < 2 ^ 32) :
    MC.toPoint.coordAt m ws o = wordsVal m ws o 9 := by
  unfold Impl.Weierstrass.Point.Curve.coordAt
  rw [Impl.Weierstrass.Mont.numAt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
  exact read_eq_wordsVal m ws 9 o

/-- The saves, at `mulSave = 3304`. -/
abbrev saves : List (Nat × Nat) := [(3304, 8), (3312, 8), (3320, 8)]

/-- What the conversion in writes: `Q`'s slots, `UA` to `UC`, and the field
functions' own working space. -/
abbrev cinW : List (Nat × Nat) := [(1072, 144), (3592, 288), (7616, 576)]

/-- What the conversion out writes. -/
abbrev coutW : List (Nat × Nat) := [(1072, 216), (3808, 72), (7616, 576)]


/-- What the function writes is its own working space or the result's. -/
theorem keeps_of_unch {ws : Addr} {m m' : Mem} (hu : Unch ws (saves ++ ((cinW ++ Window.bodyW) ++ coutW)) m m') :
    MC.Keeps ws m m' := by
  intro i hi hown hp
  have h8 : Impl.Weierstrass.Mont.wsBytes = 8192 := rfl
  refine hu _ fun w hw => ?_
  rw [show ws + BitVec.ofNat 64 i = off ws i from rfl, ofs_off0 ws (by omega_using [hi, h8])]
  obtain hw' := (by decide : ∀ w ∈ saves ++ ((cinW ++ Window.bodyW) ++ coutW), (1072 ≤ w.1 ∧ w.1 + w.2 ≤ 2296) ∨ 3304 ≤ w.1) w hw
  simp only [Impl.Weierstrass.Mul.Curve.Own, Impl.Weierstrass.Mul.Curve.slot, Impl.Weierstrass.Mul.Curve.tmpAt,
    Impl.Weierstrass.Mul.Curve.bitsAt, Impl.Weierstrass.Mul.Curve.pAt, Impl.Weierstrass.Mul.Curve.ptBytes,
    MC, Impl.Weierstrass.Mul.p521, true_and] at hown hp
  omega_using [hp, hw', hown]

/-- `sd t, d(a0)` (`sdAt`) at the working space's base. -/
theorem sdAt_a0 {s : State} {base : Addr} {is : List Instr} {Q : State → Prop} (h0 : s.gpr .a0 = base)
    (hwr : (⟨base, 8192⟩ : Region) ∈ s.wr) (hal : base.toNat % 8 = 0) {t : Reg} (ht : t ≠ .a0) {d : Nat}
    (hd : d + 8 ≤ 4096) (hd8 : d % 8 = 0)
    (k : ∀ s', Mupd s s' (s.mem.writeW (off base d) (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (sdAt t .a0 d ++ is)) s Q :=
  wp_sdAt (by omega_using [hd]) ht (by rw [h0]) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hal, hd8])
    ⟨_, hwr, Offset.contains_base base (by omega_using [hd]) (by omega_using [hd])⟩ k

/-! ## The conversions -/

section Conv

open VG.Impl.Ecdsa.RISCV64.WindowU (c UA UB UONE UC F toU fromU convIn convOut setIn setOut setC)
open VG.Proof.Weierstrass.RISCV64.P521Unsat (uf Tight TightF uv wv lw umulCall_ok unpackCall_ok packCall_ok uf_eq own9)
open VG.Proof.Ecdsa.RISCV64.P521.Window (ev PtOk)
open VG.Proof.X25519.RISCV64 (Rest)

/-- Slots apart from the ones a field program wrote keep their numbers. -/
theorem keepR_wv {s s' : State} {base : Addr} {Wl : List Nat} (k : KeepR 9 base Wl s s') {d : Nat}
    (hd : ∀ o ∈ Wl, d + 72 ≤ o ∨ o + 72 ≤ d) (hd' : d + 72 ≤ 7616) : wv base s' d = wv base s d :=
  outs_wordsVal k.mem (fun r hr => by
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
    rcases hr with ⟨o, ho, rfl⟩ | rfl
    · exact hd o ho
    · exact .inl (by rw [own9]; exact hd')) (by omega_using [hd'])

theorem tight_in : Tight (2 ^ 512 * 4) := by unfold Tight TightF lw; decide
theorem uv_in : uv (2 ^ 512 * 4) = 2 ^ 466 := by decide
theorem tight_out : Tight (2 ^ 55) := by unfold Tight TightF lw; decide
theorem uv_out : uv (2 ^ 55) = 2 ^ 55 := by decide

/-- `2⁴⁶⁶` is `R⁻¹` modulo `p`. -/
theorem inv_R : (2 ^ 576 * 2 ^ 466) % W.p = 1 := by decide

/-- The limbs' element, times `2⁴⁶⁶`, of a number in Montgomery's form. -/
theorem ofNat_in (x : Nat) : (Fin.ofNat W.p (2 ^ 576 * x % W.p * 2 ^ 466) : Fe W) = Fin.ofNat W.p x := by
  apply Fin.ext
  simp only [Fin.val_ofNat]
  rw [Nat.mod_mul_mod, show 2 ^ 576 * x * 2 ^ 466 = x * (2 ^ 576 * 2 ^ 466) by ac_rfl, Nat.mul_mod, inv_R,
    Nat.mul_one, Nat.mod_mod]

/-- The limbs' element, times `2⁴⁶⁶`, of a number below `p`: its decoding. -/
theorem ofNat_in_toM {w : Nat} (hw : w < W.p) :
    (Fin.ofNat W.p (w * 2 ^ 466) : Fe W) = toM W.p (2 ^ 576) w := by
  obtain e : w * 2 ^ 466 * 2 ^ 576 % W.p = w := by
    rw [Nat.mul_assoc, Nat.mul_mod, show 2 ^ 466 * 2 ^ 576 = 2 ^ 576 * 2 ^ 466 from Nat.mul_comm _ _, inv_R,
      Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hw]
  rw [← toM_mont (R := 2 ^ 576) unit (x := w * 2 ^ 466), e]

/-- The residue of limbs times `2⁵⁵`: their element in Montgomery's form. -/
theorem toM_out (y : Nat) : toM W.p (2 ^ 576) (y * 2 ^ 55 % W.p) = Fin.ofNat W.p y := by
  obtain e : y * 2 ^ 55 % W.p = y * 2 ^ 576 % W.p := by
    rw [Nat.mul_mod, Nat.mul_mod y (2 ^ 576), show 2 ^ 55 % W.p = 2 ^ 576 % W.p by decide]
  rw [e, toM_mont unit]

/-- `UC = 2⁴⁶⁶` in limbs. -/
theorem setIn_ok {s : State} {base : Addr} (hw : WsReg s base) (hz : wordsVal s.mem base (c.sl ZERO) 9 = 0) :
    WP isa (.block setIn) s fun s' => Rest [.t0] s s' ∧ Unch base [(c.sl UC, 72)] s.mem s'.mem ∧
      Tight (wv base s' (c.sl UC)) ∧ uv (wv base s' (c.sl UC)) = 2 ^ 466 := by
  have hn := hw.nowrap
  have hUC : c.sl UC = 3808 := rfl
  rw [setIn, setC, List.append_assoc]
  refine WP.block_append (WP.mono (copy_ok 9 hw (o := c.sl UC) (a := c.sl ZERO) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₁ ⟨e₁, r₁, O₁⟩ => ?_)
  obtain hw₁ := hw.of_rest r₁
  refine wp_li (imm := 4) (by decide) fun s₂ u₂ => ?_
  obtain hw₂ := hw₁.of_rest (u₂.rest (ws := [.t0]) (by decide))
  rw [← List.append_nil (sdAt _ _ _)]
  refine sdAt_ws hw₂ (by decide) (d := c.sl UC + 8 * 8) (by decide) (by decide) fun s₃ u₃ => WP.block_nil ?_
  obtain m₃ : s₃.mem = s₁.mem.writeW (off base (c.sl UC + 8 * 8)) (BitVec.ofNat 64 4) := by rw [u₃.mem, u₂.gpr, u₂.mem]
  obtain low : wordsVal s₁.mem base (c.sl UC) 8 = 0 := by
    have := wordsVal_succ_top s₁.mem base (c.sl UC) 8
    rw [e₁, hz] at this; omega_using [this]
  obtain v₃ : wordsVal s₃.mem base (c.sl UC) 9 = 2 ^ 512 * 4 := by
    rw [wordsVal_succ_top, m₃, word_writeW_self, (writeW_outside _ _ _ (by omega_using [hUC])).wordsVal (.inl (by omega_using []))
      (by omega_using [hUC]), low]
    rfl
  refine ⟨(r₁.trans (u₂.rest (by decide))).trans (u₃.rest [.t0]), ?_,
    show Tight (wordsVal _ _ _ 9) by rw [v₃]; exact tight_in, show uv (wordsVal _ _ _ 9) = _ by rw [v₃]; exact uv_in⟩
  rw [m₃]
  exact (O₁.unch.trans ((writeW_outside _ _ _ (by omega_using [hUC])).unch)).cover (by decide)

/-- `UC = 2⁵⁵` in limbs. -/
theorem setOut_ok {s : State} {base : Addr} (hw : WsReg s base) (hz : wordsVal s.mem base (c.sl ZERO) 9 = 0) :
    WP isa (.block setOut) s fun s' => Rest [.t0] s s' ∧ Unch base [(c.sl UC, 72)] s.mem s'.mem ∧
      Tight (wv base s' (c.sl UC)) ∧ uv (wv base s' (c.sl UC)) = 2 ^ 55 := by
  have hn := hw.nowrap
  have hUC : c.sl UC = 3808 := rfl
  rw [setOut, setC, List.append_assoc]
  refine WP.block_append (WP.mono (copy_ok 9 hw (o := c.sl UC) (a := c.sl ZERO) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₁ ⟨e₁, r₁, O₁⟩ => ?_)
  obtain hw₁ := hw.of_rest r₁
  refine wp_li (imm := 1) (by decide) fun s₂ u₂ => wp_sll (by decide) fun s₃ u₃ => ?_
  obtain hw₃ := hw₁.of_rest ((u₂.rest (ws := [.t0]) (by decide)).trans (u₃.rest (by decide)))
  rw [← List.append_nil (sdAt _ _ _)]
  refine sdAt_ws hw₃ (by decide) (d := c.sl UC + 8 * 0) (by decide) (by decide) fun s₄ u₄ => WP.block_nil ?_
  obtain g₃ : s₃.gpr .t0 = BitVec.ofNat 64 (2 ^ 55) := by rw [u₃.gpr, u₂.gpr]; rfl
  obtain m₄ : s₄.mem = s₁.mem.writeW (off base (c.sl UC)) (BitVec.ofNat 64 (2 ^ 55)) := by
    rw [u₄.mem, g₃, u₃.mem, u₂.mem]; rfl
  obtain high : wordsVal s₁.mem base (c.sl UC + 8) 8 = 0 := by
    have : wordsVal s₁.mem base (c.sl UC) 9 =
        (word s₁.mem base (c.sl UC)).toNat + 2 ^ 64 * wordsVal s₁.mem base (c.sl UC + 8) 8 := rfl
    rw [e₁, hz] at this; omega_using [this]
  obtain v₄ : wordsVal s₄.mem base (c.sl UC) 9 = 2 ^ 55 := by
    show (word s₄.mem base (c.sl UC)).toNat + 2 ^ 64 * wordsVal s₄.mem base (c.sl UC + 8) 8 = _
    rw [m₄, word_writeW_self, (writeW_outside _ _ _ (by omega_using [hUC])).wordsVal (.inr (by omega_using [])) (by omega_using [hUC]), high]
    rfl
  refine ⟨((r₁.trans (u₂.rest (by decide))).trans (u₃.rest (by decide))).trans (u₄.rest [.t0]), ?_,
    show Tight (wordsVal _ _ _ 9) by rw [v₄]; exact tight_out, show uv (wordsVal _ _ _ 9) = _ by rw [v₄]; exact uv_out⟩
  rw [m₄]
  exact (O₁.unch.trans ((writeW_outside _ _ _ (by omega_using [hUC])).unch)).cover (by decide)

/-- `[o]` = the limbs of `[a]` times `2⁴⁶⁶`, for `UC = 2⁴⁶⁶`. -/
theorem toU_ok {s : State} {base : Addr} (hw : WsReg s base) {o a : Nat}
    (ho : o + 72 ≤ 4095) (ha : a + 72 ≤ 4095) (hoC : o + 72 ≤ c.sl UC ∨ c.sl UC + 72 ≤ o)
    (hA : wv base s a < 2 ^ 522) (hCt : Tight (wv base s (c.sl UC))) (hCv : uv (wv base s (c.sl UC)) = 2 ^ 466) :
    WP isa (toU o a) s fun s' => KeepR 9 base [o] s s' ∧ Tight (wv base s' o) ∧
      uf (wv base s' o) = Fin.ofNat W.p (wv base s a * 2 ^ 466) := by
  rw [toU]
  refine WP.seq (WP.mono (unpackCall_ok (f := F.S.fn "unpack") hw (o := o) (a := a) (b := 0) (by omega_using [ho]) (by omega_using [ha])
    (by decide) (by omega_using [ho]) (by omega_using [ha]) (by decide) hA) fun s₁ ⟨K₁, t₁, v₁⟩ => ?_)
  obtain k₁ := KeepR.of_call K₁
  obtain eC : wv base s₁ (c.sl UC) = wv base s (c.sl UC) :=
    keepR_wv k₁ (by simp only [List.mem_singleton, forall_eq]; omega_using [hoC]) (by decide)
  refine WP.mono (umulCall_ok (hw.of_kp K₁.kp) (o := o) (a := o) (b := c.sl UC) (by omega_using [ho]) (by omega_using [ho]) (by decide)
    (by omega_using [ho]) (by omega_using [ho]) (by decide) t₁ (by rw [eC]; exact hCt)) fun s₂ ⟨K₂, t₂, v₂⟩ =>
    ⟨k₁.trans (KeepR.of_call K₂), t₂, uf_eq (by rw [v₂, v₁, eC, hCv])⟩

/-- `[o]` = the residue of the limbs at `o` times `2⁵⁵`, for `UC = 2⁵⁵`. -/
theorem fromU_ok {s : State} {base : Addr} (hw : WsReg s base) {o : Nat}
    (ho : o + 72 ≤ 4095) (hO : Tight (wv base s o))
    (hCt : Tight (wv base s (c.sl UC))) (hCv : uv (wv base s (c.sl UC)) = 2 ^ 55) :
    WP isa (fromU o) s fun s' => KeepR 9 base [o] s s' ∧
      wv base s' o = uv (wv base s o) * 2 ^ 55 % P521Unsat.p := by
  rw [fromU]
  refine WP.seq (WP.mono (umulCall_ok hw (o := o) (a := o) (b := c.sl UC) (by omega_using [ho]) (by omega_using [ho]) (by decide)
    (by omega_using [ho]) (by omega_using [ho]) (by decide) hO hCt) fun s₁ ⟨K₁, t₁, v₁⟩ => ?_)
  refine WP.mono (packCall_ok (f := F.S.fn "pack") (hw.of_kp K₁.kp) (o := o) (a := o) (b := 0) (by omega_using [ho])
    (by omega_using [ho]) (by decide) (by omega_using [ho]) (by omega_using [ho]) (by decide) t₁) fun s₂ ⟨K₂, v₂⟩ =>
    ⟨(KeepR.of_call K₁).trans (KeepR.of_call K₂), by rw [v₂, v₁, hCv]⟩

end Conv

section ConvAll

open VG.Impl.Ecdsa.RISCV64.WindowU (c UA UB UONE UC F toU fromU convIn convOut setIn setOut setC)
open VG.Proof.Weierstrass.RISCV64.P521Unsat (uf Tight TightF uv wv lw umulCall_ok unpackCall_ok packCall_ok uf_eq own9)
open VG.Proof.X25519.RISCV64 (Rest)

/-- A step keeps what lies apart from its output. -/
theorem fr {base : Addr} {t t' : State} {o : Nat} (k : KeepR 9 base [o] t t') (d : Nat)
    (h1 : d + 72 ≤ o ∨ o + 72 ≤ d) (h2 : d + 72 ≤ 7616) : wv base t' d = wv base t d :=
  keepR_wv k (by simpa using h1) h2

/-- `Q`, one, `a` and `3 b` to limbs, and the conversions' constant, `2⁴⁶⁶`, left at `UC`. -/
theorem convInC_ok {s : State} {base : Addr} (hw : WsReg s base) (hz : wordsVal s.mem base (c.sl ZERO) 9 = 0)
    (hx : wv base s (c.sl RX) < 2 ^ 522) (hy : wv base s (c.sl RY) < 2 ^ 522)
    (ho : wv base s (c.sl ONEP) < 2 ^ 522) (ha : wv base s (c.sl AP) < 2 ^ 522)
    (hb : wv base s (c.sl B3P) < 2 ^ 522) :
    WP isa convIn s fun s' => Kp s s' ∧ Unch base cinW s.mem s'.mem ∧
      (∀ q ∈ [(c.sl RX, c.sl RX), (c.sl RY, c.sl RY), (c.sl UONE, c.sl ONEP), (c.sl UA, c.sl AP),
          (c.sl UB, c.sl B3P)],
        Tight (wv base s' q.1) ∧ uf (wv base s' q.1) = Fin.ofNat W.p (wv base s q.2 * 2 ^ 466)) ∧
      Tight (wv base s' (c.sl UC)) ∧ uv (wv base s' (c.sl UC)) = 2 ^ 466 := by
  have hn := hw.nowrap
  have hUC : c.sl UC = 3808 := rfl
  rw [convIn]
  simp only [progs]
  refine WP.seq (WP.mono (setIn_ok hw hz) fun s₁ ⟨r₁, U₁, tc₁, vc₁⟩ => ?_)
  obtain hw₁ := hw.of_rest r₁
  obtain e₁ : ∀ d, d + 72 ≤ c.sl UC ∨ c.sl UC + 72 ≤ d ∧ d + 72 ≤ 4095 → wv base s₁ d = wv base s d :=
    fun d hd => U₁.wordsVal (by simp only [List.mem_singleton, forall_eq]; omega_using [hd]) (by omega_using [hUC, hd])
  refine WP.seq (WP.mono (toU_ok hw₁ (o := c.sl RX) (a := c.sl RX) (by decide) (by decide) (by decide)
    (by rw [e₁ _ (by decide)]; exact hx) tc₁ vc₁) fun s₂ ⟨k₂, t₂, v₂⟩ => ?_)
  obtain hw₂ := hw₁.of_kp k₂.kp
  obtain c₂ : wv base s₂ (c.sl UC) = wv base s₁ (c.sl UC) := fr k₂ _ (by decide) (by decide)
  refine WP.seq (WP.mono (toU_ok hw₂ (o := c.sl RY) (a := c.sl RY) (by decide) (by decide) (by decide)
    (by rw [fr k₂ _ (by decide) (by decide), e₁ _ (by decide)]; exact hy) (by rw [c₂]; exact tc₁)
    (by rw [c₂]; exact vc₁)) fun s₃ ⟨k₃, t₃, v₃⟩ => ?_)
  obtain hw₃ := hw₂.of_kp k₃.kp
  obtain c₃ : wv base s₃ (c.sl UC) = wv base s₁ (c.sl UC) := (fr k₃ _ (by decide) (by decide)).trans c₂
  refine WP.seq (WP.mono (toU_ok hw₃ (o := c.sl UONE) (a := c.sl ONEP) (by decide) (by decide) (by decide)
    (by rw [fr k₃ _ (by decide) (by decide), fr k₂ _ (by decide) (by decide), e₁ _ (by decide)]; exact ho)
    (by rw [c₃]; exact tc₁) (by rw [c₃]; exact vc₁)) fun s₄ ⟨k₄, t₄, v₄⟩ => ?_)
  obtain hw₄ := hw₃.of_kp k₄.kp
  obtain c₄ : wv base s₄ (c.sl UC) = wv base s₁ (c.sl UC) := (fr k₄ _ (by decide) (by decide)).trans c₃
  refine WP.seq (WP.mono (toU_ok hw₄ (o := c.sl UA) (a := c.sl AP) (by decide) (by decide) (by decide)
    (by rw [fr k₄ _ (by decide) (by decide), fr k₃ _ (by decide) (by decide), fr k₂ _ (by decide) (by decide),
      e₁ _ (by decide)]; exact ha)
    (by rw [c₄]; exact tc₁) (by rw [c₄]; exact vc₁)) fun s₅ ⟨k₅, t₅, v₅⟩ => ?_)
  obtain hw₅ := hw₄.of_kp k₅.kp
  obtain c₅ : wv base s₅ (c.sl UC) = wv base s₁ (c.sl UC) := (fr k₅ _ (by decide) (by decide)).trans c₄
  refine WP.mono (toU_ok hw₅ (o := c.sl UB) (a := c.sl B3P) (by decide) (by decide) (by decide)
    (by rw [fr k₅ _ (by decide) (by decide), fr k₄ _ (by decide) (by decide), fr k₃ _ (by decide) (by decide),
      fr k₂ _ (by decide) (by decide), e₁ _ (by decide)]; exact hb)
    (by rw [c₅]; exact tc₁) (by rw [c₅]; exact vc₁)) fun s₆ ⟨k₆, t₆, v₆⟩ =>
    ⟨?_, ?_, ?_, by rw [fr k₆ _ (by decide) (by decide), c₅]; exact tc₁,
      by rw [fr k₆ _ (by decide) (by decide), c₅]; exact vc₁⟩
  · exact (Kp.of_rest r₁).trans (k₂.kp.trans (k₃.kp.trans (k₄.kp.trans (k₅.kp.trans k₆.kp))))
  · exact (U₁.trans (Unch.trans k₂.mem (Unch.trans k₃.mem (Unch.trans k₄.mem (Unch.trans k₅.mem k₆.mem))))).cover
      (by decide)
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · rw [fr k₆ _ (by decide) (by decide), fr k₅ _ (by decide) (by decide), fr k₄ _ (by decide) (by decide),
        fr k₃ _ (by decide) (by decide), ← e₁ (c.sl RX) (by decide)]
      exact ⟨t₂, v₂⟩
    · rw [fr k₆ _ (by decide) (by decide), fr k₅ _ (by decide) (by decide), fr k₄ _ (by decide) (by decide),
        ← e₁ (c.sl RY) (by decide), ← fr k₂ (c.sl RY) (by decide) (by decide)]
      exact ⟨t₃, v₃⟩
    · rw [fr k₆ _ (by decide) (by decide), fr k₅ _ (by decide) (by decide),
        ← e₁ (c.sl ONEP) (by decide), ← fr k₂ (c.sl ONEP) (by decide) (by decide),
        ← fr k₃ (c.sl ONEP) (by decide) (by decide)]
      exact ⟨t₄, v₄⟩
    · rw [fr k₆ _ (by decide) (by decide), ← e₁ (c.sl AP) (by decide), ← fr k₂ (c.sl AP) (by decide) (by decide),
        ← fr k₃ (c.sl AP) (by decide) (by decide), ← fr k₄ (c.sl AP) (by decide) (by decide)]
      exact ⟨t₅, v₅⟩
    · rw [← e₁ (c.sl B3P) (by decide), ← fr k₂ (c.sl B3P) (by decide) (by decide),
        ← fr k₃ (c.sl B3P) (by decide) (by decide), ← fr k₄ (c.sl B3P) (by decide) (by decide),
        ← fr k₅ (c.sl B3P) (by decide) (by decide)]
      exact ⟨t₆, v₆⟩

/-- `Q`, one, `a` and `3 b` to limbs. -/
theorem convIn_ok {s : State} {base : Addr} (hw : WsReg s base) (hz : wordsVal s.mem base (c.sl ZERO) 9 = 0)
    (hx : wv base s (c.sl RX) < 2 ^ 522) (hy : wv base s (c.sl RY) < 2 ^ 522)
    (ho : wv base s (c.sl ONEP) < 2 ^ 522) (ha : wv base s (c.sl AP) < 2 ^ 522)
    (hb : wv base s (c.sl B3P) < 2 ^ 522) :
    WP isa convIn s fun s' => Kp s s' ∧ Unch base cinW s.mem s'.mem ∧
      ∀ q ∈ [(c.sl RX, c.sl RX), (c.sl RY, c.sl RY), (c.sl UONE, c.sl ONEP), (c.sl UA, c.sl AP),
          (c.sl UB, c.sl B3P)],
        Tight (wv base s' q.1) ∧ uf (wv base s' q.1) = Fin.ofNat W.p (wv base s q.2 * 2 ^ 466) :=
  WP.mono (convInC_ok hw hz hx hy ho ha hb) fun _ ⟨h1, h2, h3, _⟩ => ⟨h1, h2, h3⟩

/-- `R` to Montgomery's form. -/
theorem convOut_ok {s : State} {base : Addr} (hw : WsReg s base) (hz : wordsVal s.mem base (c.sl ZERO) 9 = 0)
    (hx : Tight (wv base s (c.sl RX))) (hy : Tight (wv base s (c.sl RY))) (hzz : Tight (wv base s (c.sl RZ))) :
    WP isa convOut s fun s' => Kp s s' ∧ Unch base coutW s.mem s'.mem ∧
      ∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wv base s' x = uv (wv base s x) * 2 ^ 55 % P521Unsat.p := by
  have hn := hw.nowrap
  have hUC : c.sl UC = 3808 := rfl
  rw [convOut]
  simp only [progs]
  refine WP.seq (WP.mono (setOut_ok hw hz) fun s₁ ⟨r₁, U₁, tc₁, vc₁⟩ => ?_)
  obtain hw₁ := hw.of_rest r₁
  obtain e₁ : ∀ d, d + 72 ≤ c.sl UC ∨ c.sl UC + 72 ≤ d ∧ d + 72 ≤ 4095 → wv base s₁ d = wv base s d :=
    fun d hd => U₁.wordsVal (by simp only [List.mem_singleton, forall_eq]; omega_using [hd]) (by omega_using [hUC, hd])
  refine WP.seq (WP.mono (fromU_ok hw₁ (o := c.sl RX) (by decide) (by rw [e₁ _ (by decide)]; exact hx)
    tc₁ vc₁) fun s₂ ⟨k₂, v₂⟩ => ?_)
  obtain hw₂ := hw₁.of_kp k₂.kp
  obtain c₂ : wv base s₂ (c.sl UC) = wv base s₁ (c.sl UC) := fr k₂ _ (by decide) (by decide)
  refine WP.seq (WP.mono (fromU_ok hw₂ (o := c.sl RY) (by decide)
    (by rw [fr k₂ _ (by decide) (by decide), e₁ _ (by decide)]; exact hy) (by rw [c₂]; exact tc₁)
    (by rw [c₂]; exact vc₁)) fun s₃ ⟨k₃, v₃⟩ => ?_)
  obtain hw₃ := hw₂.of_kp k₃.kp
  obtain c₃ : wv base s₃ (c.sl UC) = wv base s₁ (c.sl UC) := (fr k₃ _ (by decide) (by decide)).trans c₂
  refine WP.mono (fromU_ok hw₃ (o := c.sl RZ) (by decide)
    (by rw [fr k₃ _ (by decide) (by decide), fr k₂ _ (by decide) (by decide), e₁ _ (by decide)]; exact hzz)
    (by rw [c₃]; exact tc₁) (by rw [c₃]; exact vc₁)) fun s₄ ⟨k₄, v₄⟩ => ⟨?_, ?_, ?_⟩
  · exact (Kp.of_rest r₁).trans (k₂.kp.trans (k₃.kp.trans k₄.kp))
  · exact (U₁.trans (Unch.trans k₂.mem (Unch.trans k₃.mem k₄.mem))).cover (by decide)
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [fr k₄ _ (by decide) (by decide), fr k₃ _ (by decide) (by decide), v₂, e₁ _ (by decide)]
    · rw [fr k₄ _ (by decide) (by decide), v₃, fr k₂ _ (by decide) (by decide), e₁ _ (by decide)]
    · rw [v₄, fr k₃ _ (by decide) (by decide), fr k₂ _ (by decide) (by decide), e₁ _ (by decide)]

end ConvAll

/-- `vg_p521_mul` meets `mulRVc`, given the group law. -/
theorem mul_rv (hL : VG.Proof.Weierstrass.Law W) (s : State) (hs : mulRVc.pre s) :
    ∃ t s', Exec isa mulP521 s t s' ∧ abiPreserved s s' ∧ mulRVc.post s s' := by
  obtain ⟨-, hwr, hfit, hal, ⟨-, hz, hone, ha, hb3⟩, ⟨hx, hy, hon⟩⟩ := hs
  generalize hb : s.gpr .a0 = base at hwr hfit hal hz hone ha hb3 hx hy hon
  obtain hwr' : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_singleton_self _
  have hpR := unit
  obtain hp0 : 0 < W.p := by decide
  obtain ca : ∀ (m : Mem) {o : Nat}, o < 4096 → MC.toPoint.coordAt m base o = wordsVal m base o 9 :=
    fun m _ ho => coordAt_eq m base (by omega_using [ho])
  obtain dq : ∀ x, MC.toPoint.dec x = toM W.p (2 ^ 576) x :=
    VG.Proof.Weierstrass.Point.dec_eq MC.toPoint hL.one_ne_zero (VG.Proof.Weierstrass.Point.fermat_of_law hL) hpR
  -- The saves and `s0 = a0`.
  suffices h : WP isa mulP521 s fun s' => abiPreserved s s' ∧ mulRVc.post s s' by
    obtain ⟨t, s', he, h⟩ := h; exact ⟨t, s', he, h⟩
  rw [mulP521, WindowU.mulFn, show WindowU.c.mulSave = 3304 from rfl]
  simp only [List.append_assoc]
  rw [← List.append_nil (ldAt .s0 .s0 3304)]
  refine WP.seq (sdAt_a0 hb hwr' hal (by decide) (d := 3304) (by decide) (by decide) fun s₁ u₁ => ?_)
  refine sdAt_a0 (by rw [u₁.gpr]; exact hb) (by rw [u₁.wr]; exact hwr') hal (by decide) (d := 3312) (by decide)
    (by decide) fun s₂ u₂ => ?_
  refine sdAt_a0 (by rw [u₂.gpr, u₁.gpr]; exact hb) (by rw [u₂.wr, u₁.wr]; exact hwr') hal (by decide)
    (d := 3320) (by decide) (by decide) fun s₃ u₃ => wp_mv fun s₄ u₄ => WP.block_nil ?_
  obtain g₄ : ∀ r, r ≠ .s0 → s₄.gpr r = s.gpr r := fun r hr => by
    rw [u₄.other r hr, u₃.gpr, u₂.gpr, u₁.gpr]
  obtain hw₄ : WsReg s₄ base := ⟨by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, hb],
    by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hwr', hfit, hal⟩
  obtain m₄ : s₄.mem = ((s.mem.writeW (off base 3304) (s.gpr .s0)).writeW (off base 3312) (s.gpr .s1)).writeW
      (off base 3320) (s.gpr .ra) := by
    simp only [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr]
  obtain O₄ : Unch base saves s.mem s₄.mem := by
    rw [m₄]
    exact (((writeW_outside _ _ _ (by omega_using [])).unch.trans (writeW_outside _ _ _ (by omega_using [])).unch).trans
      (writeW_outside _ _ _ (by omega_using [])).unch)
  obtain sv₄ : ∀ i, i < 45 → sv base s₄ i = sv base s i := fun i hi =>
    O₄.wordsVal (fun w hw => by
      simp only [saves, List.mem_cons, List.not_mem_nil, or_false] at hw
      have : p521.sl i + 72 ≤ 3304 := by simp only [Cfg.sl, slot, p521]; omega_using [hi]
      rcases hw with rfl | rfl | rfl <;> (simp only; omega_using [this])) (by simp only [Cfg.sl, slot, p521]; omega_using [hi])
  obtain cs : ∀ i, i < 45 → MC.toPoint.coordAt s.mem base (p521.sl i) = sv base s i := fun i hi =>
    ca s.mem (by simp only [Cfg.sl, slot, p521]; omega_using [hi])
  -- The slots' values, from the contract's.
  obtain hz' : sv base s₄ ZERO = 0 := by rw [sv₄ _ (by decide)]; exact (cs ZERO (by decide)).symm.trans hz
  obtain hone' : sv base s₄ ONEP = 2 ^ 576 % W.p := by
    rw [sv₄ _ (by decide)]; refine (cs ONEP (by decide)).symm.trans (hone.trans ?_)
    simp only [Impl.Weierstrass.Mul.Curve.mont, Nat.one_mul]; rfl
  obtain ha' : sv base s₄ AP = 2 ^ 576 * W.a % W.p := by
    rw [sv₄ _ (by decide)]; refine (cs AP (by decide)).symm.trans (ha.trans ?_)
    simp only [Impl.Weierstrass.Mul.Curve.mont]; rw [Nat.mul_comm]; rfl
  obtain hb3' : sv base s₄ B3P = 2 ^ 576 * (3 * W.b) % W.p := by
    rw [sv₄ _ (by decide)]; refine (cs B3P (by decide)).symm.trans (hb3.trans ?_)
    simp only [Impl.Weierstrass.Mul.Curve.mont]; rw [Nat.mul_comm]; rfl
  obtain tm : ∀ x, toM W.p (2 ^ 576) (2 ^ 576 * x % W.p) = Fin.ofNat W.p x := fun x => by
    rw [Nat.mul_comm]; exact toM_mont hpR
  obtain qx : (MC.qCoords base s.mem).1 = sv base s₄ RX := by rw [sv₄ _ (by decide)]; exact cs RX (by decide)
  obtain qy : (MC.qCoords base s.mem).2 = sv base s₄ RY := by
    rw [sv₄ _ (by decide), ← cs RY (by decide)]; rfl
  obtain eP : MC.point base s.mem = .affine (toM W.p (2 ^ 576) (sv base s₄ RX)) (toM W.p (2 ^ 576) (sv base s₄ RY)) := by
    unfold Impl.Weierstrass.Mul.Curve.point
    rw [qx, qy, dq, dq]
  have hon' := hon
  rw [eP] at hon'
  -- To limbs.
  obtain hp522 : W.p < 2 ^ 522 := by decide
  obtain m522 : ∀ x, x % W.p < 2 ^ 522 := fun x => Nat.lt_trans (Nat.mod_lt _ hp0) hp522
  refine WP.seq (WP.mono (convIn_ok hw₄ hz' (by show sv base s₄ RX < _; exact Nat.lt_trans (qx ▸ hx) hp522)
    (by show sv base s₄ RY < _; exact Nat.lt_trans (qy ▸ hy) hp522)
    (by show sv base s₄ ONEP < _; rw [hone']; exact m522 _)
    (by show sv base s₄ AP < _; rw [ha']; exact m522 _) (by show sv base s₄ B3P < _; rw [hb3']; exact m522 _))
    fun q₅ ⟨K₅, U₅, cv₅⟩ => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at cv₅
  obtain ⟨⟨tx₅, vx₅⟩, ⟨ty₅, vy₅⟩, ⟨to₅, vo₅⟩, ⟨ta₅, va₅⟩, ⟨tb₅, vb₅⟩⟩ := cv₅
  obtain hw₅ := hw₄.of_kp K₅
  obtain z₅ : wordsVal q₅.mem base (WindowU.c.sl ZERO) 9 = 0 := by
    rw [U₅.wordsVal (by decide) (by decide)]; exact hz'
  obtain eQ : Window.qOf base q₅ = .affine (toM W.p (2 ^ 576) (sv base s₄ RX)) (toM W.p (2 ^ 576) (sv base s₄ RY)) := by
    show Point.affine (P521Unsat.uf _) (P521Unsat.uf _) = _
    rw [vx₅, vy₅]
    exact congrArg₂ Point.affine (ofNat_in_toM (show sv base s₄ RX < W.p from qx ▸ hx))
      (ofNat_in_toM (show sv base s₄ RY < W.p from qy ▸ hy))
  -- The body.
  obtain hpre : Window.WPre base q₅ := by
    refine ⟨hw₅, ⟨ta₅, ?_, tb₅, ?_, z₅, to₅, ?_⟩, tx₅, ty₅, by rw [eQ]; exact hon'⟩
    · show P521Unsat.uf _ = _; rw [va₅]; show Fin.ofNat _ (sv base s₄ AP * _) = _; rw [ha', ofNat_in]
    · show P521Unsat.uf _ = _; rw [vb₅]; show Fin.ofNat _ (sv base s₄ B3P * _) = _; rw [hb3', ofNat_in]
    · show P521Unsat.uf _ = _; rw [vo₅]; show Fin.ofNat _ (sv base s₄ ONEP * _) = _
      rw [hone', ← Nat.mul_one (2 ^ 576), ofNat_in]; rfl
  refine WP.seq (WP.mono (Window.body_ok hL hpre) fun q₆ ⟨K₆, U₆, pR₆⟩ => ?_)
  obtain hw₆ := hw₅.of_kc K₆
  obtain z₆ : wordsVal q₆.mem base (WindowU.c.sl ZERO) 9 = 0 := by
    rw [U₆.wordsVal (by decide) (by decide)]; exact z₅
  -- Back to Montgomery's form.
  refine WP.seq (WP.mono (convOut_ok hw₆ z₆ pR₆.x pR₆.y pR₆.z) fun q₇ ⟨K₇, U₇, cv₇⟩ => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at cv₇
  obtain ⟨ox₇, oy₇, oz₇⟩ := cv₇
  have R₆ := pR₆.rep
  obtain KK : Kc s₄ q₇ := (K₅.kc.trans K₆).trans K₇.kc
  obtain UU : Unch base ((cinW ++ Window.bodyW) ++ coutW) s₄.mem q₇.mem := (U₅.trans U₆).trans U₇
  -- The loads.
  obtain hw₇' := hw₄.of_kc KK
  obtain far : ∀ d ∈ [3304, 3312, 3320], word q₇.mem base d = word s₄.mem base d := fun d hd =>
    UU.word (fun w hw => by
      have := (by decide : ∀ w ∈ (cinW ++ Window.bodyW) ++ coutW, w.1 + w.2 ≤ 3304 ∨ 3376 ≤ w.1) w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      omega_using [this, hd]) (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; omega_using [hd])
  obtain w20 : word q₇.mem base 3320 = s.gpr .ra := by
    rw [far 3320 (by simp), m₄, word_writeW_self]
  obtain w12 : word q₇.mem base 3312 = s.gpr .s1 := by
    rw [far 3312 (by simp), m₄, (writeW_outside (d := 3320) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []), word_writeW_self]
  obtain w04 : word q₇.mem base 3304 = s.gpr .s0 := by
    rw [far 3304 (by simp), m₄, (writeW_outside (d := 3320) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []),
      (writeW_outside (d := 3312) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []), word_writeW_self]
  refine ldAt_ws hw₇' (d := 3320) (by decide) (by decide) fun s₆ u₆ => ?_
  refine ldAt_ws (hw₇'.of_kp (Kp.of_upd u₆)) (d := 3312) (by decide) (by decide) fun s₇ u₇ => ?_
  obtain hw₇ : WsReg s₇ base := ⟨by rw [u₇.other .s0 (by decide), u₆.other .s0 (by decide)]; exact hw₇'.s0,
    by rw [u₇.wr, u₆.wr]; exact hw₇'.wr, hfit, hal⟩
  refine ldAt_ws hw₇ (d := 3304) (by decide) (by decide) fun s₈ u₈ => WP.block_nil ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · have m₇ : s₇.mem = q₇.mem := by rw [u₇.mem, u₆.mem]
    by_cases h0 : r = .s0
    · subst h0; rw [u₈.gpr, m₇, w04]
    by_cases h1 : r = .s1
    · subst h1; rw [u₈.other _ (by decide), u₇.gpr, u₆.mem, w12]
    rw [u₈.other _ h0, u₇.other _ h1, u₆.other _ (fun e => by subst e; revert hr; decide),
      KK.gpr r hr h1, g₄ r h0]
  · rw [u₈.sp, u₇.sp, u₆.sp, KK.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, w20]
  · have m₈ : s₈.mem = q₇.mem := by rw [u₈.mem, u₇.mem, u₆.mem]
    show MC.ResultInRange _ _ (s.gpr .a0) s.mem s₈.mem
    rw [hb, eP, m₈]
    refine ⟨fun _ _ => ?_, keeps_of_unch (O₄.trans UU)⟩
    obtain e : MC.scalar base s.mem = sv base s₄ K := by rw [sv₄ _ (by decide)]; exact cs K (by decide)
    obtain k₅ : wordsVal q₅.mem base (WindowU.c.sl K) 9 = sv base s₄ K := U₅.wordsVal (by decide) (by decide)
    obtain c7 : ∀ i, i < 45 → MC.toPoint.coordAt q₇.mem base (p521.sl i) = sv base q₇ i := fun i hi =>
      ca q₇.mem (by simp only [Cfg.sl, slot, p521]; omega_using [hi])
    obtain x0 : MC.toPoint.coordAt q₇.mem base MC.pAt = sv base q₇ RX := c7 RX (by decide)
    obtain x1 : MC.toPoint.coordAt q₇.mem base (MC.pAt + Impl.Weierstrass.Point.elemBytes MC.toPoint.k) =
        sv base q₇ RY := c7 RY (by decide)
    obtain x2 : MC.toPoint.coordAt q₇.mem base (MC.pAt + 2 * Impl.Weierstrass.Point.elemBytes MC.toPoint.k) =
        sv base q₇ RZ := c7 RZ (by decide)
    have ex : sv base q₇ RX = P521Unsat.uv (P521Unsat.wv base q₆ (WindowU.c.sl RX)) * 2 ^ 55 % W.p := ox₇
    have ey : sv base q₇ RY = P521Unsat.uv (P521Unsat.wv base q₆ (WindowU.c.sl RY)) * 2 ^ 55 % W.p := oy₇
    have ez : sv base q₇ RZ = P521Unsat.uv (P521Unsat.wv base q₆ (WindowU.c.sl RZ)) * 2 ^ 55 % W.p := oz₇
    rw [e]
    rw [eQ, k₅] at R₆
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x0, ex]; exact Nat.mod_lt _ hp0
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x1, ey]; exact Nat.mod_lt _ hp0
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x2, ez]; exact Nat.mod_lt _ hp0
    · rw [Impl.Weierstrass.Point.Curve.pointAt, x0, x1, x2, dq, dq, dq, ex, ey, ez, toM_out, toM_out, toM_out]
      exact represents_of_rep R₆

/-! The constant-time analyses of the calls of the functions on limbs from their arguments, each
done once for `mulSum`, whose calls of them differ in what else is public; they keep what is
public of `s0`–`s11`: the functions write none of them. -/
taint_summary uMulSum : taint (Taint.ofRegs [.a0, .a1, .a2, .a3]) (.call (Impl.Weierstrass.RISCV64.P521Unsat.S.fn "mul") Impl.Weierstrass.RISCV64.P521Unsat.mulFnA)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])
taint_summary uAddSum : taint (Taint.ofRegs [.a0, .a1, .a2, .a3]) (.call (Impl.Weierstrass.RISCV64.P521Unsat.S.fn "add") Impl.Weierstrass.RISCV64.P521Unsat.addFn)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])
taint_summary uSubSum : taint (Taint.ofRegs [.a0, .a1, .a2, .a3]) (.call (Impl.Weierstrass.RISCV64.P521Unsat.S.fn "sub") Impl.Weierstrass.RISCV64.P521Unsat.subFn)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])
taint_summary uPackSum : taint (Taint.ofRegs [.a0, .a1, .a2, .a3]) (.call (Impl.Weierstrass.RISCV64.P521Unsat.S.fn "pack") Impl.Weierstrass.RISCV64.P521Unsat.packFn)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])
taint_summary uUnpackSum : taint (Taint.ofRegs [.a0, .a1, .a2, .a3]) (.call (Impl.Weierstrass.RISCV64.P521Unsat.S.fn "unpack") Impl.Weierstrass.RISCV64.P521Unsat.unpackFn)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])

/-! The constant-time analysis of the call of `vg_p521_mul` from its argument, done once for every
check of code that calls it (`taint_decide_sum [mulSum]`: signing, ECDH and the public key), which
keeps what is public of `s2`–`s11`: the function writes none of them (`s0` and `s1` it restores
from memory). -/
taint_summary mulSum : taint (Taint.ofRegs [.a0]) (.call "vg_p521_mul" mulP521)
  keeping (Taint.ofRegs [.s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])
  using uMulSum uAddSum uSubSum uPackSum uUnpackSum

end VG.Proof.Ecdsa.RISCV64.P521
