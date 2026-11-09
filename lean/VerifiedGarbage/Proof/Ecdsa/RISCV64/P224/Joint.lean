module

-- separate module: its proofs (about 7 s) cost more than its imports, and its importer's
-- changes need not re-check them

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Verify
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.MulFn
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Joint.Table
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Main
public import VerifiedGarbage.Proof.Weierstrass.Joint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.P224.Point
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.Law3

/-!
# ECDSA verification over P-224 on RISC-V: the joint ladder

The pieces of the joint ladder of `Impl/Ecdsa/RISCV64/Verify.lean`, which
`JointJ.lean` puts together (`jointJ_ok`), with each step's `4 R` by Jacobian
doublings:

* `copyTo_ok`, `storePt_ok`: a point's slots to an entry of the table, through
  `a6 = s0 + JT`;
* `window_ok`: the window's entry number `4 u_j + v_j`, its
  masks, and the entry to `E`, by the comb's tree (`tree_ok`);
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P224.Joint

open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.Verify
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.P224 (W field_ok unit)
open VG.Proof.Ecdsa.RISCV64.Joint
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Point mul onCurve)
open VG.Impl.Ecdsa.RISCV64.Comb (maskReg treeRegs)

/-! ## The complete additions -/

/-- A point in the slots `p`: its coordinates below `p`, representing `P`. -/
structure PtOk (base : Addr) (s : State) (p : Pt) (P : Point W) : Prop where
  rep : Rep W (tmv W 4 base s p.x) (tmv W 4 base s p.y) (tmv W 4 base s p.z) P
  x : wordsVal s.mem base p.x 4 < W.p
  y : wordsVal s.mem base p.y 4 < W.p
  z : wordsVal s.mem base p.z 4 < W.p

/-- The slots of the joint ladder's additions. -/
abbrev jSl : List Nat :=
  [p224.sl AP, p224.sl BP, p224.sl T0, p224.sl T1, p224.sl T2, p224.sl T3, p224.sl T4, p224.sl T5,
    p224.sl RX, p224.sl RY, p224.sl RZ, p224.sl DX, p224.sl DY, p224.sl DZ, p224.sl TX, p224.sl TY, p224.sl TZ,
    p224.sl GX, p224.sl GY, p224.sl ONEP, p224.sl CPX, p224.sl CPY,
    p224.sl G2X, p224.sl G2Y, p224.sl G2Z, p224.sl G3X, p224.sl G3Y, p224.sl G3Z,
    p224.sl Q2X, p224.sl Q2Y, p224.sl Q2Z, p224.sl p224.Q3X, p224.sl p224.Q3Y, p224.sl p224.Q3Z,
    p224.sl p224.EX, p224.sl p224.EY, p224.sl p224.EZ]

theorem jLay : Lay p224.MP' (own 4) (· ∈ jSl) :=
  ⟨by decide, fun x y hx hy => (by decide : ∀ x ∈ jSl, ∀ y ∈ jSl, x ≠ y → x + 8 * 4 ≤ y ∨ y + 8 * 4 ≤ x)
    x hx y hy, by decide, by decide⟩

theorem jShort : Short (· ∈ jSl) := by decide

/-- What the additions write. -/
abbrev addW (o : Pt) : List (Nat × Nat) :=
  (rcbW (Cfg.rcb3Slots p224) o).map (fun w => (w, 8 * 4)) ++ [(own 4, 64 * 4)]

theorem am3 : AM3 W := by unfold AM3; decide

/-- `o = p + q` by the complete addition, for points in slots of `jSl`. -/
theorem addPt_ok (hL : Law W) {base : Addr} {s : State} (hw : WsReg s base)
    (hap : wordsVal s.mem base (p224.sl AP) 4 = W.a * 2 ^ 256 % W.p)
    (hbp : wordsVal s.mem base (p224.sl BP) 4 = W.b * 2 ^ 256 % W.p)
    {p q o : Pt} (hA : RcbApart (Cfg.rcb3Slots p224) p q o)
    (hsl : ∀ x ∈ rcbW (Cfg.rcb3Slots p224) o ++ rcbR (Cfg.rcb3Slots p224) p q, x ∈ jSl)
    {P P' : Point W} (hP : onCurve W P = true) (hP' : onCurve W P' = true)
    (hp : PtOk base s p P) (hq : PtOk base s q P') :
    WP isa (Cfg.addPt p224 p q o) s fun s' =>
      Kp s s' ∧ Unch base (addW o) s.mem s'.mem ∧ PtOk base s' o (Spec.Weierstrass.add P P') := by
  have hp0 : 0 < W.p := by decide
  rw [Cfg.addPt]
  have hI : Inv 4 base W.p (· ∈ jSl) (rcbR (Cfg.rcb3Slots p224) p q)
      (fun x => toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base x 4)) s := by
    refine ⟨hw, fun x hx => hsl x (List.mem_append_right _ hx), fun x hx => ?_, fun x _ => rfl⟩
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show wordsVal _ _ (p224.sl AP) 4 < _; rw [hap]; exact Nat.mod_lt _ hp0
    · show wordsVal _ _ (p224.sl BP) 4 < _; rw [hbp]; exact Nat.mod_lt _ hp0
    exacts [hp.x, hp.y, hp.z, hq.x, hq.y, hq.z]
  refine WP.mono (rcb3_ok (F := p224Field) field_ok rfl jLay jShort unit hA hsl hI (fun x hx => hx))
    fun s₁ ⟨k₁, I₁, t₁⟩ => ?_
  have eb : toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base (p224.sl BP) 4) = Fin.ofNat W.p W.b := by
    rw [hbp, toM_mont unit]
  generalize hE : (fun x => toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base x 4)) = E at I₁ t₁
  have hrep := hL.add3 am3 hP hP' hp.rep hq.rep (X3 := runOps (rcb3 (Cfg.rcb3Slots p224) p q o) E o.x)
    (Y3 := runOps (rcb3 (Cfg.rcb3Slots p224) p q o) E o.y) (Z3 := runOps (rcb3 (Cfg.rcb3Slots p224) p q o) E o.z)
    (by
      subst hE
      show rcbAdd3 (Fin.ofNat W.p W.b) _ _ _ _ _ _ = _
      rw [← eb]
      exact t₁.symm)
  have hm : ∀ x ∈ [o.x, o.y, o.z], x ∈ [o.x, o.y, o.z] ++ rcbR (Cfg.rcb3Slots p224) p q :=
    fun x hx => List.mem_append_left _ hx
  refine ⟨k₁.kp, k₁.mem, ⟨?_, I₁.lt _ (hm _ (by simp)), I₁.lt _ (hm _ (by simp)), I₁.lt _ (hm _ (by simp))⟩⟩
  have vx : tmv W 4 base s₁ o.x = _ := I₁.val _ (hm _ (by simp))
  have vy : tmv W 4 base s₁ o.y = _ := I₁.val _ (hm _ (by simp))
  have vz : tmv W 4 base s₁ o.z = _ := I₁.val _ (hm _ (by simp))
  rw [vx, vy, vz]
  exact hrep

theorem PtOk.of_eq {base : Addr} {s s' : State} {p : Pt} {P : Point W} (h : PtOk base s p P)
    (hx : wordsVal s'.mem base p.x 4 = wordsVal s.mem base p.x 4)
    (hy : wordsVal s'.mem base p.y 4 = wordsVal s.mem base p.y 4)
    (hz : wordsVal s'.mem base p.z 4 = wordsVal s.mem base p.z 4) : PtOk base s' p P :=
  ⟨by simp only [tmv]; rw [hx, hy, hz]; exact h.rep, hx ▸ h.x, hy ▸ h.y, hz ▸ h.z⟩

/-- A point copied to other slots. -/
theorem PtOk.move {base : Addr} {s s' : State} {p q : Pt} {P : Point W} (h : PtOk base s p P)
    (hx : wordsVal s'.mem base q.x 4 = wordsVal s.mem base p.x 4)
    (hy : wordsVal s'.mem base q.y 4 = wordsVal s.mem base p.y 4)
    (hz : wordsVal s'.mem base q.z 4 = wordsVal s.mem base p.z 4) : PtOk base s' q P :=
  ⟨by simp only [tmv]; rw [hx, hy, hz]; exact h.rep, hx ▸ h.x, hy ▸ h.y, hz ▸ h.z⟩

/-! ## The table's construction -/

section
variable {C : Spec.Weierstrass.Curve}

theorem mul_zero' (P : Point C) : mul 0 P = .infinity := by rw [Spec.Weierstrass.mul]; rfl

end

/-- What the construction reads: the constants, `G` and `Q`. -/
structure JPre (base : Addr) (s : State) (Q : Point W) : Prop where
  ws : WsReg s base
  ap : wordsVal s.mem base (p224.sl AP) 4 = W.a * 2 ^ 256 % W.p
  bp : wordsVal s.mem base (p224.sl BP) 4 = W.b * 2 ^ 256 % W.p
  zero : wordsVal s.mem base (p224.sl ZERO) 4 = 0
  onep : wordsVal s.mem base (p224.sl ONEP) 4 = 1 * 2 ^ 256 % W.p
  gx : wordsVal s.mem base (p224.sl GX) 4 = W.gx * 2 ^ 256 % W.p
  gy : wordsVal s.mem base (p224.sl GY) 4 = W.gy * 2 ^ 256 % W.p
  qx : wordsVal s.mem base (p224.sl CPX) 4 < W.p
  qy : wordsVal s.mem base (p224.sl CPY) 4 < W.p
  q : Point.affine (tmv W 4 base s (p224.sl CPX)) (tmv W 4 base s (p224.sl CPY)) = Q
  on : onCurve W Q = true

end VG.Proof.Ecdsa.RISCV64.P224.Joint
