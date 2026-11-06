module

-- separate module: its proofs (about 7 s) cost more than its imports, and its importer's
-- changes need not re-check them

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Verify
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Joint.Table
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP256r1.MulFn
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.RISCV64.Ecdsa
public import VerifiedGarbage.Proof.Weierstrass.Joint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.BrainpoolP256r1.Point
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.Law3

/-!
# ECDSA verification on RISC-V: the joint ladder

The pieces of the joint ladder of `Impl/Ecdsa/RISCV64/Verify.lean`, which
`JointJ.lean` puts together (`jointJ_ok`), with each step's `4 R` by Jacobian
doublings:

* `copyTo_ok`, `storePt_ok`: a point's slots to an entry of the table, through
  `a6 = s0 + JT`;
* `window_ok`: the window's entry number `4 u_j + v_j`, its
  masks, and the entry to `E`, by the comb's tree (`tree_ok`);
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.BrainpoolP256r1.Joint

open VG.Proof.Ecdsa.RISCV64.Joint

open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.Verify
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.BrainpoolP256r1 (W field_ok unit)
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
  [brainpoolp256r1.sl AP, brainpoolp256r1.sl B3P, brainpoolp256r1.sl T0, brainpoolp256r1.sl T1, brainpoolp256r1.sl T2, brainpoolp256r1.sl T3, brainpoolp256r1.sl T4, brainpoolp256r1.sl T5,
    brainpoolp256r1.sl RX, brainpoolp256r1.sl RY, brainpoolp256r1.sl RZ, brainpoolp256r1.sl DX, brainpoolp256r1.sl DY, brainpoolp256r1.sl DZ, brainpoolp256r1.sl TX, brainpoolp256r1.sl TY, brainpoolp256r1.sl TZ,
    brainpoolp256r1.sl GX, brainpoolp256r1.sl GY, brainpoolp256r1.sl ONEP, brainpoolp256r1.sl CPX, brainpoolp256r1.sl CPY,
    brainpoolp256r1.sl G2X, brainpoolp256r1.sl G2Y, brainpoolp256r1.sl G2Z, brainpoolp256r1.sl G3X, brainpoolp256r1.sl G3Y, brainpoolp256r1.sl G3Z,
    brainpoolp256r1.sl Q2X, brainpoolp256r1.sl Q2Y, brainpoolp256r1.sl Q2Z, brainpoolp256r1.sl brainpoolp256r1.Q3X, brainpoolp256r1.sl brainpoolp256r1.Q3Y, brainpoolp256r1.sl brainpoolp256r1.Q3Z,
    brainpoolp256r1.sl brainpoolp256r1.EX, brainpoolp256r1.sl brainpoolp256r1.EY, brainpoolp256r1.sl brainpoolp256r1.EZ]

theorem jLay : Lay brainpoolp256r1.MP' (own 4) (· ∈ jSl) :=
  ⟨by decide, fun x y hx hy => (by decide : ∀ x ∈ jSl, ∀ y ∈ jSl, x ≠ y → x + 8 * 4 ≤ y ∨ y + 8 * 4 ≤ x)
    x hx y hy, by decide, by decide⟩

theorem jShort : Short (· ∈ jSl) := by decide

/-- What the additions write. -/
abbrev addW (o : Pt) : List (Nat × Nat) :=
  (rcbW (Cfg.rcbSlots brainpoolp256r1) o).map (fun w => (w, 8 * 4)) ++ [(own 4, 64 * 4)]

/-- `o = p + q` by the complete addition, for points in slots of `jSl`. -/
theorem addPt_ok (hL : Law W) {base : Addr} {s : State} (hw : WsReg s base)
    (hap : wordsVal s.mem base (brainpoolp256r1.sl AP) 4 = W.a * 2 ^ 256 % W.p)
    (hbp : wordsVal s.mem base (brainpoolp256r1.sl B3P) 4 = 3 * W.b * 2 ^ 256 % W.p)
    {p q o : Pt} (hA : RcbApart (Cfg.rcbSlots brainpoolp256r1) p q o)
    (hsl : ∀ x ∈ rcbW (Cfg.rcbSlots brainpoolp256r1) o ++ rcbR (Cfg.rcbSlots brainpoolp256r1) p q, x ∈ jSl)
    {P P' : Point W} (hP : onCurve W P = true) (hP' : onCurve W P' = true)
    (hp : PtOk base s p P) (hq : PtOk base s q P') :
    WP isa (Cfg.addPt brainpoolp256r1 p q o) s fun s' =>
      Kp s s' ∧ Unch base (addW o) s.mem s'.mem ∧ PtOk base s' o (Spec.Weierstrass.add P P') := by
  have hp0 : 0 < W.p := by decide
  rw [Cfg.addPt_gen _ rfl]
  have hI : Inv 4 base W.p (· ∈ jSl) (rcbR (Cfg.rcbSlots brainpoolp256r1) p q)
      (fun x => toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base x 4)) s := by
    refine ⟨hw, fun x hx => hsl x (List.mem_append_right _ hx), fun x hx => ?_, fun x _ => rfl⟩
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show wordsVal _ _ (brainpoolp256r1.sl AP) 4 < _; rw [hap]; exact Nat.mod_lt _ hp0
    · show wordsVal _ _ (brainpoolp256r1.sl B3P) 4 < _; rw [hbp]; exact Nat.mod_lt _ hp0
    exacts [hp.x, hp.y, hp.z, hq.x, hq.y, hq.z]
  refine WP.mono (rcb_ok (F := brainpoolp256r1Field) field_ok rfl jLay jShort unit hA hsl hI (fun x hx => hx))
    fun s₁ ⟨k₁, I₁, t₁⟩ => ?_
  have ea : toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base (brainpoolp256r1.sl AP) 4) = Fin.ofNat W.p W.a := by
    rw [hap, toM_mont unit]
  have eb : toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base (brainpoolp256r1.sl B3P) 4) = Fin.ofNat W.p (3 * W.b) := by
    rw [hbp, toM_mont unit]
  generalize hE : (fun x => toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base x 4)) = E at I₁ t₁
  have hrep := Rep.add hL hP hP' hp.rep hq.rep (X3 := runOps (rcb (Cfg.rcbSlots brainpoolp256r1) p q o) E o.x)
    (Y3 := runOps (rcb (Cfg.rcbSlots brainpoolp256r1) p q o) E o.y) (Z3 := runOps (rcb (Cfg.rcbSlots brainpoolp256r1) p q o) E o.z)
    (by
      subst hE
      show rcbAdd (Fin.ofNat W.p W.a) (Fin.ofNat W.p (3 * W.b)) _ _ _ _ _ _ = _
      rw [← ea, ← eb]
      exact t₁.1.symm)
  have hm : ∀ x ∈ [o.x, o.y, o.z], x ∈ rcbW (Cfg.rcbSlots brainpoolp256r1) o ++ rcbR (Cfg.rcbSlots brainpoolp256r1) p q :=
    fun x hx => List.mem_append_left _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [rcbW])
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

theorem mul_one' (P : Point C) : mul 1 P = P := by
  rw [Spec.Weierstrass.mul, ite_eq_right (by decide), show (1 : Nat) / 2 = 0 from rfl, mul_zero',
    ite_eq_right (by decide)]
  rfl

end

/-- What the construction reads: the constants, `G` and `Q`. -/
structure JPre (base : Addr) (s : State) (Q : Point W) : Prop where
  ws : WsReg s base
  ap : wordsVal s.mem base (brainpoolp256r1.sl AP) 4 = W.a * 2 ^ 256 % W.p
  bp : wordsVal s.mem base (brainpoolp256r1.sl B3P) 4 = 3 * W.b * 2 ^ 256 % W.p
  zero : wordsVal s.mem base (brainpoolp256r1.sl ZERO) 4 = 0
  onep : wordsVal s.mem base (brainpoolp256r1.sl ONEP) 4 = 1 * 2 ^ 256 % W.p
  gx : wordsVal s.mem base (brainpoolp256r1.sl GX) 4 = W.gx * 2 ^ 256 % W.p
  gy : wordsVal s.mem base (brainpoolp256r1.sl GY) 4 = W.gy * 2 ^ 256 % W.p
  qx : wordsVal s.mem base (brainpoolp256r1.sl CPX) 4 < W.p
  qy : wordsVal s.mem base (brainpoolp256r1.sl CPY) 4 < W.p
  q : Point.affine (tmv W 4 base s (brainpoolp256r1.sl CPX)) (tmv W 4 base s (brainpoolp256r1.sl CPY)) = Q
  on : onCurve W Q = true

/-- Slots apart from what code writes are kept. -/
theorem keepU {base : Addr} {Wl : List (Nat × Nat)} {m m' : Mem} (U : Unch base Wl m m') {D : List Nat}
    (hD : ∀ d ∈ D, (∀ w ∈ Wl, d + 8 * 4 ≤ w.1 ∨ w.1 + w.2 ≤ d) ∧ d + 32 ≤ 2048) :
    ∀ d ∈ D, wordsVal m' base d 4 = wordsVal m base d 4 := fun d hd =>
  U.wordsVal (hD d hd).1 (by have := (hD d hd).2; omega)

/-- The registers `select` writes. -/
abbrev selRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a3, .a4]

end VG.Proof.Ecdsa.RISCV64.BrainpoolP256r1.Joint
