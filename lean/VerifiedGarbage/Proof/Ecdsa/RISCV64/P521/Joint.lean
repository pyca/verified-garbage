module

-- separate module: its proofs (about 7 s) cost more than its imports, and its importer's
-- changes need not re-check them

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Verify
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Joint.Table
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Main
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.MulFn
public import VerifiedGarbage.Proof.Weierstrass.Joint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.P521.Point
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.Law3

/-!
# ECDSA verification over P-521 on RISC-V: points and their sum

What `[u]G + [v]Q` by the comb and windows (`JointComb.lean`) uses of points
in Montgomery's form: a point in slots (`PtOk`), the complete addition of
two (`addPt_ok`), and what the sum reads (`JPre`).
-/

@[expose] public section

-- `p`, below `2^576`, is evaluated.
set_option exponentiation.threshold 1024

namespace VG.Proof.Ecdsa.RISCV64.P521.Joint

open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.Verify
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.P521 (W field_ok unit)
open VG.Proof.Ecdsa.RISCV64.Joint
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Point mul onCurve)
open VG.Impl.Ecdsa.RISCV64.Comb (maskReg treeRegs)

/-! ## The complete additions -/

/-- A point in the slots `p`: its coordinates below `p`, representing `P`. -/
structure PtOk (base : Addr) (s : State) (p : Pt) (P : Point W) : Prop where
  rep : Rep W (tmv W 9 base s p.x) (tmv W 9 base s p.y) (tmv W 9 base s p.z) P
  x : wordsVal s.mem base p.x 9 < W.p
  y : wordsVal s.mem base p.y 9 < W.p
  z : wordsVal s.mem base p.z 9 < W.p

/-- The slots of the joint ladder's additions. -/
abbrev jSl : List Nat :=
  [p521.sl AP, p521.sl BP, p521.sl T0, p521.sl T1, p521.sl T2, p521.sl T3, p521.sl T4, p521.sl T5,
    p521.sl RX, p521.sl RY, p521.sl RZ, p521.sl DX, p521.sl DY, p521.sl DZ, p521.sl TX, p521.sl TY, p521.sl TZ,
    p521.sl GX, p521.sl GY, p521.sl ONEP, p521.sl CPX, p521.sl CPY,
    p521.sl G2X, p521.sl G2Y, p521.sl G2Z, p521.sl G3X, p521.sl G3Y, p521.sl G3Z,
    p521.sl Q2X, p521.sl Q2Y, p521.sl Q2Z, p521.sl p521.Q3X, p521.sl p521.Q3Y, p521.sl p521.Q3Z,
    p521.sl p521.EX, p521.sl p521.EY, p521.sl p521.EZ]

theorem jLay : Lay p521.MP' (own 9) (· ∈ jSl) :=
  ⟨by decide, fun x y hx hy => (by decide : ∀ x ∈ jSl, ∀ y ∈ jSl, x ≠ y → x + 8 * 9 ≤ y ∨ y + 8 * 9 ≤ x)
    x hx y hy, by decide, by decide⟩

theorem jShort : Short (· ∈ jSl) := by decide

/-- What the additions write. -/
abbrev addW (o : Pt) : List (Nat × Nat) :=
  (rcbW (Cfg.rcb3Slots p521) o).map (fun w => (w, 8 * 9)) ++ [(own 9, 64 * 9)]

theorem am3 : AM3 W := by unfold AM3; decide

/-- `o = p + q` by the complete addition, for points in slots of `jSl`. -/
theorem addPt_ok (hL : Law W) {base : Addr} {s : State} (hw : WsReg s base)
    (hap : wordsVal s.mem base (p521.sl AP) 9 = W.a * 2 ^ 576 % W.p)
    (hbp : wordsVal s.mem base (p521.sl BP) 9 = W.b * 2 ^ 576 % W.p)
    {p q o : Pt} (hA : RcbApart (Cfg.rcb3Slots p521) p q o)
    (hsl : ∀ x ∈ rcbW (Cfg.rcb3Slots p521) o ++ rcbR (Cfg.rcb3Slots p521) p q, x ∈ jSl)
    {P P' : Point W} (hP : onCurve W P = true) (hP' : onCurve W P' = true)
    (hp : PtOk base s p P) (hq : PtOk base s q P') :
    WP isa (Cfg.addPt p521 p q o) s fun s' =>
      Kp s s' ∧ Unch base (addW o) s.mem s'.mem ∧ PtOk base s' o (Spec.Weierstrass.add P P') := by
  obtain hp0 : 0 < W.p := by decide
  rw [Cfg.addPt_am3 _ rfl]
  obtain hI : Inv 9 base W.p (· ∈ jSl) (rcbR (Cfg.rcb3Slots p521) p q)
      (fun x => toM W.p (2 ^ (64 * 9)) (wordsVal s.mem base x 9)) s := by
    refine ⟨hw, fun x hx => hsl x (List.mem_append_right _ hx), fun x hx => ?_, fun x _ => rfl⟩
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show wordsVal _ _ (p521.sl AP) 9 < _; rw [hap]; exact Nat.mod_lt _ hp0
    · show wordsVal _ _ (p521.sl BP) 9 < _; rw [hbp]; exact Nat.mod_lt _ hp0
    exacts [hp.x, hp.y, hp.z, hq.x, hq.y, hq.z]
  refine WP.mono (rcb3_ok (F := p521Field) field_ok rfl jLay jShort unit hA hsl hI (fun x hx => hx))
    fun s₁ ⟨k₁, I₁, t₁⟩ => ?_
  obtain eb : toM W.p (2 ^ (64 * 9)) (wordsVal s.mem base (p521.sl BP) 9) = Fin.ofNat W.p W.b := by
    rw [hbp, toM_mont unit]
  generalize hE : (fun x => toM W.p (2 ^ (64 * 9)) (wordsVal s.mem base x 9)) = E at I₁ t₁
  obtain hrep := hL.add3 am3 hP hP' hp.rep hq.rep (X3 := runOps (rcb3 (Cfg.rcb3Slots p521) p q o) E o.x)
    (Y3 := runOps (rcb3 (Cfg.rcb3Slots p521) p q o) E o.y) (Z3 := runOps (rcb3 (Cfg.rcb3Slots p521) p q o) E o.z)
    (by
      subst hE
      show rcbAdd3 (Fin.ofNat W.p W.b) _ _ _ _ _ _ = _
      rw [← eb]
      exact t₁.symm)
  obtain hm : ∀ x ∈ [o.x, o.y, o.z], x ∈ [o.x, o.y, o.z] ++ rcbR (Cfg.rcb3Slots p521) p q :=
    fun x hx => List.mem_append_left _ hx
  refine ⟨k₁.kp, k₁.mem, ⟨?_, I₁.lt _ (hm _ (by simp)), I₁.lt _ (hm _ (by simp)), I₁.lt _ (hm _ (by simp))⟩⟩
  obtain vx : tmv W 9 base s₁ o.x = _ := I₁.val _ (hm _ (by simp))
  obtain vy : tmv W 9 base s₁ o.y = _ := I₁.val _ (hm _ (by simp))
  obtain vz : tmv W 9 base s₁ o.z = _ := I₁.val _ (hm _ (by simp))
  rw [vx, vy, vz]
  exact hrep

theorem PtOk.of_eq {base : Addr} {s s' : State} {p : Pt} {P : Point W} (h : PtOk base s p P)
    (hx : wordsVal s'.mem base p.x 9 = wordsVal s.mem base p.x 9)
    (hy : wordsVal s'.mem base p.y 9 = wordsVal s.mem base p.y 9)
    (hz : wordsVal s'.mem base p.z 9 = wordsVal s.mem base p.z 9) : PtOk base s' p P := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold tmv; rw [hx, hy, hz]; exact h.rep
  · rw [hx]; exact h.x
  · rw [hy]; exact h.y
  · rw [hz]; exact h.z

/-- A point copied to other slots. -/
theorem PtOk.move {base : Addr} {s s' : State} {p q : Pt} {P : Point W} (h : PtOk base s p P)
    (hx : wordsVal s'.mem base q.x 9 = wordsVal s.mem base p.x 9)
    (hy : wordsVal s'.mem base q.y 9 = wordsVal s.mem base p.y 9)
    (hz : wordsVal s'.mem base q.z 9 = wordsVal s.mem base p.z 9) : PtOk base s' q P := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold tmv; rw [hx, hy, hz]; exact h.rep
  · rw [hx]; exact h.x
  · rw [hy]; exact h.y
  · rw [hz]; exact h.z

section
variable {C : Spec.Weierstrass.Curve}

theorem mul_zero' (P : Point C) : mul 0 P = .infinity := by rw [Spec.Weierstrass.mul]; rfl

end

/-- What the construction reads: the constants, `G` and `Q`. -/
structure JPre (base : Addr) (s : State) (Q : Point W) : Prop where
  ws : WsReg s base
  ap : wordsVal s.mem base (p521.sl AP) 9 = W.a * 2 ^ 576 % W.p
  bp : wordsVal s.mem base (p521.sl BP) 9 = W.b * 2 ^ 576 % W.p
  zero : wordsVal s.mem base (p521.sl ZERO) 9 = 0
  onep : wordsVal s.mem base (p521.sl ONEP) 9 = 1 * 2 ^ 576 % W.p
  gx : wordsVal s.mem base (p521.sl GX) 9 = W.gx * 2 ^ 576 % W.p
  gy : wordsVal s.mem base (p521.sl GY) 9 = W.gy * 2 ^ 576 % W.p
  qx : wordsVal s.mem base (p521.sl CPX) 9 < W.p
  qy : wordsVal s.mem base (p521.sl CPY) 9 < W.p
  q : Point.affine (tmv W 9 base s (p521.sl CPX)) (tmv W 9 base s (p521.sl CPY)) = Q
  on : onCurve W Q = true

end VG.Proof.Ecdsa.RISCV64.P521.Joint
