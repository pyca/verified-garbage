module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.TailAll
public import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.Check
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.MulLit
import VerifiedGarbage.Proof.Weierstrass.PointFacts
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Window
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Joint.Table
public import VerifiedGarbage.Proof.Weierstrass.Jac
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Window4All
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.P224.Point
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
meta import VerifiedGarbage.Impl.Ecdsa.RISCV64.Window
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.Joint.Table
meta import VerifiedGarbage.Proof.Weierstrass.Jac
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Weierstrass.PointFacts
meta import VerifiedGarbage.Proof.P224.Point
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.MulLit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.Window4All
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.MulFn
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.MulFn

/-! ### `Ecdsa.RISCV64.P224.Window`, which this module and modules that import it used -/

section

/-! ### `Ecdsa.RISCV64.P224.MulVerified`, which this module and modules that import it used -/

section

/-!
# `vg_p224_mul` on RISC-V: the contract

The facts of `Impl.Weierstrass.Mul.Curve.mulInRangeContract` for P-224 on
RISC-V, by register (`mulRVc`: `ws` in `a0`), which the windowed
`vg_p224_mul` meets (`Proof/Ecdh/RISCV64/P224/Tail.lean`), and a state
satisfying the precondition (`satState`: the constants and `G` in
Montgomery's form at their slots).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P224

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Spec.Weierstrass (Curve Fe Point)

/-- P-224's curve of `Proof/Weierstrass/MulContract.lean`. -/
abbrev MC : Impl.Weierstrass.Mul.Curve := Impl.Weierstrass.Mul.p224

/-- `vg_p224_mul(ws = a0)`. -/
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
    MC.toPoint.coordAt m ws o = wordsVal m ws o 4 := by
  unfold Impl.Weierstrass.Point.Curve.coordAt
  rw [Impl.Weierstrass.Mont.numAt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
  exact read_eq_wordsVal m ws 4 o

/-- The saves, at `mulSave = 1504`. -/
abbrev saves : List (Nat × Nat) := [(1504, 8), (1512, 8), (1520, 8)]

/-- Byte `a` of the number `x` at slot `i` of a working space at `0x1000`,
if `a` is in that slot. -/
def satByte (a : Addr) (i x : Nat) : Option (BitVec 8) :=
  if 0x1000 + p224.sl i ≤ a.toNat ∧ a.toNat < 0x1000 + p224.sl i + 32 then
    some (BitVec.ofNat 8 (x >>> (8 * (a.toNat - (0x1000 + p224.sl i)))))
  else none

/-- `x R mod p`. -/
abbrev mont (x : Nat) : Nat := x * 2 ^ 256 % W.p

/-- The memory of `satState`: `p`, and one, `a`, `3 b` and `G`'s coordinates
in Montgomery's form, at their slots for `ws = 0x1000`, zeros elsewhere. -/
def satMem : Mem := fun a =>
  ((satByte a MP W.p).orElse fun _ => (satByte a ONEP (mont 1)).orElse fun _ =>
    (satByte a AP (mont W.a)).orElse fun _ => (satByte a B3P (mont (3 * W.b))).orElse fun _ =>
    (satByte a RX (mont W.gx)).orElse fun _ => satByte a RY (mont W.gy)).getD 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | _ => 0
  sp := 0x10000
  mem := satMem
  rd := []
  wr := [⟨0x1000, 8192⟩]

theorem sat_consts : MC.ConstsOk 0x1000 satMem := by
  unfold Impl.Weierstrass.Mul.Curve.ConstsOk
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem sat_x : (MC.qCoords 0x1000 satMem).1 = mont W.gx := by decide +kernel

theorem sat_y : (MC.qCoords 0x1000 satMem).2 = mont W.gy := by decide +kernel

theorem sat_point (hL : VG.Proof.Weierstrass.Law W) : MC.PointOk 0x1000 satMem := by
  have dq : ∀ x, MC.toPoint.dec x = toM W.p (2 ^ 256) x :=
    VG.Proof.Weierstrass.Point.dec_eq MC.toPoint hL.one_ne_zero (VG.Proof.Weierstrass.Point.fermat_of_law hL) unit
  have hp0 : 0 < W.p := by decide
  refine ⟨by rw [sat_x]; exact Nat.mod_lt _ hp0, by rw [sat_y]; exact Nat.mod_lt _ hp0, ?_⟩
  have eG : MC.point 0x1000 satMem = Spec.Weierstrass.G W := by
    unfold Impl.Weierstrass.Mul.Curve.point
    rw [sat_x, sat_y, dq, dq]
    exact congrArg₂ Point.affine (toM_mont unit) (toM_mont unit)
  rw [eG]
  exact VG.Proof.P224.onCurve_G


end VG.Proof.Ecdsa.RISCV64.P224

end

end

/-!
# `vg_p224_mul` by windows on RISC-V: the proofs

The curve's kit for `Proof/Ecdsa/RISCV64/Window4All.lean`, what that proof
gives of the body (`body_ok`: `R = [k]Q`), and the function's contract
(`mul_rv`). What stays here is what the kit takes of the curve: the steps of
`R = 16 R` on the field's programs (`toJStep_ok`, `dblStep_ok`,
`fromJStep_ok`) and the complete addition (`addPt_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P224.Window

open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.Window
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.P224 (W field_ok unit)
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Point Fe mul onCurve)

/-! ## The points -/

/-- A point in the slots `p`: its coordinates below `p`, representing `P`. -/
structure PtOk (base : Addr) (s : State) (p : Pt) (P : Point W) : Prop where
  rep : Rep W (tmv W 4 base s p.x) (tmv W 4 base s p.y) (tmv W 4 base s p.z) P
  x : wordsVal s.mem base p.x 4 < W.p
  y : wordsVal s.mem base p.y 4 < W.p
  z : wordsVal s.mem base p.z 4 < W.p

/-- `a = -3`. -/
theorem am3 : AM3 W := by unfold AM3; decide

section
variable {C : Spec.Weierstrass.Curve}

/-- `2 P`. -/
abbrev d2 (P : Point C) : Point C := Spec.Weierstrass.add P P

end

/-! ## The slots -/

/-- The slots the windows' arithmetic may use: those at multiples of 32 from
zero's (past `p` and the field's temporary) up to the functions' own working
space. -/
abbrev wS (x : Nat) : Prop := x % 32 = 0 ∧ 160 ≤ x ∧ x + 32 ≤ 3840

theorem wLay : Lay p224.MP' (own 4) wS :=
  ⟨fun x h => h.2.2, fun x y hx hy hne => by
    obtain ⟨h1, -, -⟩ := hx; obtain ⟨h2, -, -⟩ := hy
    show x + 8 * 4 ≤ y ∨ y + 8 * 4 ≤ x; omega_using [hne, h1, h2],
   fun x h => by obtain ⟨-, h, -⟩ := h; show x + 8 * 4 ≤ 64 ∨ 64 + 8 * 4 ≤ x; omega_using [h],
   fun x h => by obtain ⟨-, h, -⟩ := h; show x + 8 * 4 ≤ 128 ∨ 128 + 8 * 4 ≤ x; omega_using [h]⟩

theorem wShort : Short wS := fun x h => by obtain ⟨-, -, h⟩ := h; omega_using [h]

/-- The Jacobian programs' slots: `S` with `b` at slot 40. -/
abbrev S3 : RcbSlots := Cfg.rcb3Slots p224

/-- What the field operations of `R = 16 R` write: `R`, `D`, `T`, the
temporaries and the functions' own working space. -/
abbrev quadW : List (Nat × Nat) := [(512, 480), (3840, 256)]

/-- The slots they write. -/
abbrev quadWl : List Nat :=
  [p224.sl T0, p224.sl T1, p224.sl T2, p224.sl T3, p224.sl T4, p224.sl T5, p224.sl RX, p224.sl RY, p224.sl RZ,
    p224.sl DX, p224.sl DY, p224.sl DZ, p224.sl TX, p224.sl TY, p224.sl TZ]

/-- The constants the windows read. -/
structure KC (base : Addr) (s : State) : Prop where
  ap : wordsVal s.mem base (p224.sl AP) 4 = W.a * 2 ^ 256 % W.p
  bp : wordsVal s.mem base (p224.sl 40) 4 = W.b * 2 ^ 256 % W.p
  zero : wordsVal s.mem base (p224.sl ZERO) 4 = 0
  onep : wordsVal s.mem base (p224.sl ONEP) 4 = 2 ^ 256 % W.p

/-! ## `R = 16 R`: its steps -/

theorem dblJ_apart_DT : RcbApart S3 (p224.pt DX DY DZ) (p224.pt DX DY DZ) (p224.pt TX TY TZ) :=
  ⟨by decide, by decide⟩
theorem dblJ_apart_TD : RcbApart S3 (p224.pt TX TY TZ) (p224.pt TX TY TZ) (p224.pt DX DY DZ) :=
  ⟨by decide, by decide⟩
theorem toJ_apart : RcbApart S3 (p224.pt RX RY RZ) (Cfg.zeroPt p224) (p224.pt DX DY DZ) := ⟨by decide, by decide⟩
theorem fromJ_apart : RcbApart S3 (p224.pt DX DY DZ) (Cfg.zeroPt p224) (p224.pt RX RY RZ) := ⟨by decide, by decide⟩

/-- A Jacobian doubling from `p` to `o` (`D` to `T` or back), on `InvJ`. -/
theorem dblStep_ok (hL : Law W) {base : Addr} {s : State} {p o : Pt} (hA : RcbApart S3 p p o)
    (hsl : ∀ x ∈ rcbW S3 o ++ rcbR S3 p p, wS x) {V : List Nat} {E : Nat → Fe W}
    (hI : Inv 4 base W.p wS V E s) (hV : ∀ x ∈ rcbR S3 p p, x ∈ V) {P : Point W}
    (hP : onCurve W P = true) (hJ : InvJ W (E p.x) (E p.y) (E p.z) P) :
    WP isa (fprog p224Field (dblJ S3 p o)) s fun s' => KeepR 4 base (rcbW S3 o) s s' ∧
      ∃ E', Inv 4 base W.p wS ([o.x, o.y, o.z] ++ V) E' s' ∧ InvJ W (E' o.x) (E' o.y) (E' o.z) (d2 P) ∧
        ∀ x, x ∉ rcbW S3 o → E' x = E x := by
  rw [dblJ_eq]
  refine WP.mono (ofN_ok (F := p224Field) field_ok rfl wLay wShort unit dblJN_ok hA hsl hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, InvJ.dbl' hL am3 hP hJ (v.trans (dblJN_run _)), kp⟩

/-- `R` into Jacobian coordinates in `D`. -/
theorem toJStep_ok (hL : Law W) {base : Addr} {s : State} {V : List Nat} {E : Nat → Fe W}
    (hI : Inv 4 base W.p wS V E s) (hV : ∀ x ∈ rcbR S3 (p224.pt RX RY RZ) (Cfg.zeroPt p224), x ∈ V) {P : Point W}
    (hR : Rep W (E (p224.sl RX)) (E (p224.sl RY)) (E (p224.sl RZ)) P) (hz : E (p224.sl ZERO) = 0) :
    WP isa (fprog p224Field (toJ S3 (p224.pt RX RY RZ) (Cfg.zeroPt p224) (p224.pt DX DY DZ))) s fun s' =>
      KeepR 4 base (rcbW S3 (p224.pt DX DY DZ)) s s' ∧
      ∃ E', Inv 4 base W.p wS ([p224.sl DX, p224.sl DY, p224.sl DZ] ++ V) E' s' ∧
        InvJ W (E' (p224.sl DX)) (E' (p224.sl DY)) (E' (p224.sl DZ)) P ∧
        ∀ x, x ∉ rcbW S3 (p224.pt DX DY DZ) → E' x = E x := by
  rw [toJ_eq]
  refine WP.mono (ofN_ok (F := p224Field) field_ok rfl wLay wShort unit toJN_ok toJ_apart (by decide) hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, InvJ.of_toJ hL hR hz (v.trans (toJN_run _)), kp⟩

/-- `D` back in projective coordinates in `R`. -/
theorem fromJStep_ok {base : Addr} {s : State} {V : List Nat} {E : Nat → Fe W}
    (hI : Inv 4 base W.p wS V E s) (hV : ∀ x ∈ rcbR S3 (p224.pt DX DY DZ) (Cfg.zeroPt p224), x ∈ V) :
    WP isa (fprog p224Field (fromJ S3 (p224.pt DX DY DZ) (Cfg.zeroPt p224) (p224.pt RX RY RZ))) s fun s' =>
      KeepR 4 base (rcbW S3 (p224.pt RX RY RZ)) s s' ∧
      ∃ E', Inv 4 base W.p wS ([p224.sl RX, p224.sl RY, p224.sl RZ] ++ V) E' s' ∧
        (E' (p224.sl RX), E' (p224.sl RY), E' (p224.sl RZ)) =
          (E (p224.sl DX) * E (p224.sl DZ), E (p224.sl DY) + E (p224.sl ZERO),
            E (p224.sl DZ) * E (p224.sl DZ) * E (p224.sl DZ)) ∧
        ∀ x, x ∉ rcbW S3 (p224.pt RX RY RZ) → E' x = E x := by
  rw [fromJ_eq]
  refine WP.mono (ofN_ok (F := p224Field) field_ok rfl wLay wShort unit fromJN_ok fromJ_apart (by decide) hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, v.trans (fromJN_run _), kp⟩

/-! ## The complete addition -/

/-- What an addition writes. -/
abbrev addW (o : Pt) : List (Nat × Nat) :=
  (rcbW S3 o).map (fun w => (w, 8 * 4)) ++ [(own 4, 64 * 4)]

/-- `o = p + q` by the complete addition, for points in slots of `wS`. -/
theorem addPt_ok (hL : Law W) {base : Addr} {s : State} (hw : WsReg s base) (hK : KC base s)
    {p q o : Pt} (hA : RcbApart S3 p q o) (hsl : ∀ x ∈ rcbW S3 o ++ rcbR S3 p q, wS x)
    {P P' : Point W} (hP : onCurve W P = true) (hP' : onCurve W P' = true)
    (hp : PtOk base s p P) (hq : PtOk base s q P') :
    WP isa (Cfg.addPt p224 p q o) s fun s' =>
      Kp s s' ∧ Unch base (addW o) s.mem s'.mem ∧ PtOk base s' o (Spec.Weierstrass.add P P') := by
  obtain hp0 : 0 < W.p := by decide
  rw [Cfg.addPt]
  obtain hI : Inv 4 base W.p wS (rcbR S3 p q) (fun x => toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base x 4)) s := by
    refine ⟨hw, fun x hx => hsl x (List.mem_append_right _ hx), fun x hx => ?_, fun x _ => rfl⟩
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show wordsVal _ _ (p224.sl AP) 4 < _; rw [hK.ap]; exact Nat.mod_lt _ hp0
    · show wordsVal _ _ (p224.sl 40) 4 < _; rw [hK.bp]; exact Nat.mod_lt _ hp0
    exacts [hp.x, hp.y, hp.z, hq.x, hq.y, hq.z]
  refine WP.mono (rcb3_ok (F := p224Field) field_ok rfl wLay wShort unit hA hsl hI (fun x hx => hx))
    fun s₁ ⟨k₁, I₁, t₁⟩ => ?_
  obtain eb : toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base (p224.sl 40) 4) = Fin.ofNat W.p W.b := by
    rw [hK.bp, toM_mont unit]
  generalize hE : (fun x => toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base x 4)) = E at I₁ t₁
  obtain hrep := hL.add3 am3 hP hP' hp.rep hq.rep (X3 := runOps (rcb3 S3 p q o) E o.x)
    (Y3 := runOps (rcb3 S3 p q o) E o.y) (Z3 := runOps (rcb3 S3 p q o) E o.z)
    (by
      subst hE
      show rcbAdd3 (Fin.ofNat W.p W.b) _ _ _ _ _ _ = _
      rw [← eb]
      exact t₁.symm)
  obtain hm : ∀ x ∈ [o.x, o.y, o.z], x ∈ [o.x, o.y, o.z] ++ rcbR S3 p q :=
    fun x hx => List.mem_append_left _ hx
  refine ⟨k₁.kp, k₁.mem, ⟨?_, I₁.lt _ (hm _ (by simp)), I₁.lt _ (hm _ (by simp)), I₁.lt _ (hm _ (by simp))⟩⟩
  obtain vx : tmv W 4 base s₁ o.x = _ := I₁.val _ (hm _ (by simp))
  obtain vy : tmv W 4 base s₁ o.y = _ := I₁.val _ (hm _ (by simp))
  obtain vz : tmv W 4 base s₁ o.z = _ := I₁.val _ (hm _ (by simp))
  rw [vx, vy, vz]
  exact hrep

/-! ## The kit -/

/-- The curve's kit. -/
def kit : Window4All.Kit where
  c := p224
  n4 := rfl
  jt := rfl
  ve := rfl
  p0 := by decide
  plt := by decide
  unit := unit
  dblStep_ok := dblStep_ok
  toJStep_ok := toJStep_ok
  fromJStep_ok := fromJStep_ok
  addPt_ok := fun hL => fun hw hK => fun hA hsl => fun hP hP' hp hq =>
    WP.mono (addPt_ok hL hw ⟨hK.ap, hK.bp, hK.zero, hK.onep⟩ hA hsl hP hP' ⟨hp.rep, hp.x, hp.y, hp.z⟩
      ⟨hq.rep, hq.x, hq.y, hq.z⟩) fun _ ⟨k, u, p⟩ => ⟨k, u, ⟨p.rep, p.x, p.y, p.z⟩⟩

/-! ## What other modules use -/

/-- `o = p`, the three coordinates one after the other, for `o`'s slots in
order and `p`'s apart from them all. -/
theorem copyPt_ok {s : State} {base : Addr} (hw : WsReg s base) {o p : Pt}
    (h8 : ∀ x ∈ [o.x, o.y, o.z, p.x, p.y, p.z], x % 8 = 0 ∧ x + 32 ≤ 4096)
    (hxy : o.x + 32 ≤ o.y) (hyz : o.y + 32 ≤ o.z)
    (hp : ∀ a ∈ [p.x, p.y, p.z], a + 32 ≤ o.x ∨ o.z + 32 ≤ a) :
    WP isa (.block (Cfg.copyPt p224 o p)) s fun s' =>
      wordsVal s'.mem base o.x 4 = wordsVal s.mem base p.x 4 ∧ wordsVal s'.mem base o.y 4 = wordsVal s.mem base p.y 4 ∧
      wordsVal s'.mem base o.z 4 = wordsVal s.mem base p.z 4 ∧ Rest [.t0] s s' ∧
      Unch base [(o.x, 32), (o.y, 32), (o.z, 32)] s.mem s'.mem :=
  kit.copyPt_ok hw h8 hxy hyz hp

/-- `Q`, the affine point of `R`'s first two slots. -/
abbrev qOf (base : Addr) (s : State) : Point W := .affine (tmv W 4 base s (p224.sl RX)) (tmv W 4 base s (p224.sl RY))

/-- What `vg_p224_mul`'s body reads at the start. -/
structure WPre (base : Addr) (s : State) : Prop where
  ws : WsReg s base
  ap : wordsVal s.mem base (p224.sl AP) 4 = W.a * 2 ^ 256 % W.p
  zero : wordsVal s.mem base (p224.sl ZERO) 4 = 0
  onep : wordsVal s.mem base (p224.sl ONEP) 4 = 2 ^ 256 % W.p
  x : wordsVal s.mem base (p224.sl RX) 4 < W.p
  y : wordsVal s.mem base (p224.sl RY) 4 < W.p
  on : onCurve W (qOf base s) = true

/-- What the body writes. -/
abbrev bodyW : List (Nat × Nat) := [(512, 480), (1344, 32), (1920, 96), (2048, 1536), (3840, 256)]

/-- `R = [k]Q`, for `k` at `K`'s slot and `Q` affine in `R`'s first two. -/
theorem body_ok (hL : Law W) {base : Addr} {s : State} (hp : WPre base s) :
    WP isa (Cfg.body p224) s fun s' => Kc s s' ∧ Unch base bodyW s.mem s'.mem ∧
      PtOk base s' (p224.pt RX RY RZ) (mul (wordsVal s.mem base (p224.sl K) 4) (qOf base s)) :=
  WP.mono (kit.body_ok hL ⟨hp.ws, hp.ap, hp.zero, hp.onep, hp.x, hp.y, hp.on⟩)
    fun _ ⟨k, u, p⟩ => ⟨k, u, ⟨p.rep, p.x, p.y, p.z⟩⟩

/-! ## The function and its contract -/

open VG.Proof.Ecdsa.RISCV64.P224 (MC mulRVc coordAt_eq represents_of_rep saves satState sat_consts sat_point sv)

/-- What the function writes, as the contract's own working space and result read it. -/
abbrev fnW : List (Nat × Nat) :=
  [(1504, 8), (1512, 8), (1520, 8), (512, 480), (1344, 32), (1920, 96), (2048, 1536), (3840, 256)]

/-- What the function writes is its own working space or the result's. -/
theorem keeps_of_unch {ws : Addr} {m m' : Mem} (hu : Unch ws fnW m m') : MC.Keeps ws m m' := by
  intro i hi hown hp
  have h8 : Impl.Weierstrass.Mont.wsBytes = 8192 := rfl
  refine hu _ fun w hw => ?_
  rw [show ws + BitVec.ofNat 64 i = off ws i from rfl, ofs_off0 ws (by omega_using [hi, h8])]
  obtain hw' := (by decide : ∀ w ∈ fnW, (512 ≤ w.1 ∧ w.1 + w.2 ≤ 1056) ∨ (1344 ≤ w.1 ∧ w.1 + w.2 ≤ 1376) ∨
    1504 ≤ w.1) w hw
  simp only [Impl.Weierstrass.Mul.Curve.Own, Impl.Weierstrass.Mul.Curve.slot, Impl.Weierstrass.Mul.Curve.tmpAt,
    Impl.Weierstrass.Mul.Curve.bitsAt, Impl.Weierstrass.Mul.Curve.pAt, Impl.Weierstrass.Mul.Curve.ptBytes,
    MC, Impl.Weierstrass.Mul.p224, true_and] at hown hp
  omega_using [hp, hw', hown]

/-- The windowed `vg_p224_mul` meets `mulRVc`, given the group law. -/
theorem mul_rv (hL : Law W) (s : State) (hs : mulRVc.pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.mulP224 s t s' ∧ abiPreserved s s' ∧ mulRVc.post s s' := by
  obtain ⟨-, hwr, hfit, hal, ⟨-, hz, hone, ha, -⟩, ⟨hx, hy, hon⟩⟩ := hs
  generalize hb : s.gpr .a0 = base at hwr hfit hal hz hone ha hx hy hon
  obtain hwr' : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_singleton_self _
  have hpR := unit
  obtain hp0 : 0 < W.p := by decide
  obtain ca : ∀ (m : Mem) {o : Nat}, o < 4096 → MC.toPoint.coordAt m base o = wordsVal m base o 4 :=
    fun m _ ho => coordAt_eq m base (by omega_using [ho])
  obtain dq : ∀ x, MC.toPoint.dec x = toM W.p (2 ^ 256) x :=
    VG.Proof.Weierstrass.Point.dec_eq MC.toPoint hL.one_ne_zero (VG.Proof.Weierstrass.Point.fermat_of_law hL) hpR
  suffices h : WP isa Impl.Ecdsa.RISCV64.mulP224 s fun s' => abiPreserved s s' ∧ mulRVc.post s s' by
    obtain ⟨t, s', he, h⟩ := h; exact ⟨t, s', he, h⟩
  rw [Impl.Ecdsa.RISCV64.mulP224, Window.Cfg.mulFn, show p224.mulSave = 1504 from rfl]
  refine WP.seq (sd_a0 hb hwr' hal (d := 1504) (by decide) (by decide) fun s₁ u₁ => ?_)
  refine sd_a0 (by rw [u₁.gpr]; exact hb) (by rw [u₁.wr]; exact hwr') hal (d := 1512) (by decide)
    (by decide) fun s₂ u₂ => ?_
  refine sd_a0 (by rw [u₂.gpr, u₁.gpr]; exact hb) (by rw [u₂.wr, u₁.wr]; exact hwr') hal (d := 1520)
    (by decide) (by decide) fun s₃ u₃ => wp_mv fun s₄ u₄ => WP.block_nil ?_
  obtain g₄ : ∀ r, r ≠ .s0 → s₄.gpr r = s.gpr r := fun r hr => by
    rw [u₄.other r hr, u₃.gpr, u₂.gpr, u₁.gpr]
  obtain hw₄ : WsReg s₄ base := ⟨by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, hb],
    by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hwr', hfit, hal⟩
  obtain m₄ : s₄.mem = ((s.mem.writeW (off base 1504) (s.gpr .s0)).writeW (off base 1512) (s.gpr .s1)).writeW
      (off base 1520) (s.gpr .ra) := by
    simp only [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr]
  obtain O₄ : Unch base saves s.mem s₄.mem := by
    rw [m₄]
    exact (((writeW_outside _ _ _ (by omega_using [])).unch.trans (writeW_outside _ _ _ (by omega_using [])).unch).trans
      (writeW_outside _ _ _ (by omega_using [])).unch)
  obtain sv₄ : ∀ i, i < 45 → sv base s₄ i = sv base s i := fun i hi =>
    O₄.wordsVal (fun w hw => by
      simp only [saves, List.mem_cons, List.not_mem_nil, or_false] at hw
      have : p224.sl i + 32 ≤ 1504 := by simp only [Cfg.sl, slot, p224]; omega_using [hi]
      rcases hw with rfl | rfl | rfl <;> (simp only; omega_using [this])) (by simp only [Cfg.sl, slot, p224]; omega_using [hi])
  obtain cs : ∀ i, i < 45 → MC.toPoint.coordAt s.mem base (p224.sl i) = sv base s i := fun i hi =>
    ca s.mem (by simp only [Cfg.sl, slot, p224]; omega_using [hi])
  obtain hz' : sv base s₄ ZERO = 0 := by rw [sv₄ _ (by decide)]; exact (cs ZERO (by decide)).symm.trans hz
  obtain hone' : sv base s₄ ONEP = 2 ^ 256 % W.p := by
    rw [sv₄ _ (by decide)]; refine (cs ONEP (by decide)).symm.trans (hone.trans ?_)
    simp only [Impl.Weierstrass.Mul.Curve.mont, Nat.one_mul]; rfl
  obtain ha' : sv base s₄ AP = W.a * 2 ^ 256 % W.p := by
    rw [sv₄ _ (by decide)]; refine (cs AP (by decide)).symm.trans (ha.trans ?_)
    simp only [Impl.Weierstrass.Mul.Curve.mont]; rw [Nat.mul_comm]; rfl
  obtain qx : (MC.qCoords base s.mem).1 = sv base s₄ RX := by rw [sv₄ _ (by decide)]; exact cs RX (by decide)
  obtain qy : (MC.qCoords base s.mem).2 = sv base s₄ RY := by
    rw [sv₄ _ (by decide), ← cs RY (by decide)]; rfl
  obtain eP : MC.point base s.mem = qOf base s₄ := by
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
  obtain hw₅ := hw₄.of_kc K₅
  obtain far : ∀ d ∈ [1504, 1512, 1520], word s₅.mem base d = word s₄.mem base d := fun d hd =>
    U₅.word (fun w hw => by
      have := (by decide : ∀ w ∈ bodyW, w.1 + w.2 ≤ 1504 ∨ 1920 ≤ w.1) w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      omega_using [this, hd]) (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; omega_using [hd])
  obtain w20 : word s₅.mem base 1520 = s.gpr .ra := by
    rw [far 1520 (by simp), m₄, word_writeW_self]
  obtain w12 : word s₅.mem base 1512 = s.gpr .s1 := by
    rw [far 1512 (by simp), m₄, (writeW_outside (d := 1520) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []), word_writeW_self]
  obtain w04 : word s₅.mem base 1504 = s.gpr .s0 := by
    rw [far 1504 (by simp), m₄, (writeW_outside (d := 1520) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []),
      (writeW_outside (d := 1512) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []), word_writeW_self]
  refine ld_ws hw₅ (d := 1520) (by decide) (by decide) fun s₆ u₆ => ?_
  refine ld_ws (hw₅.of_kp (Kp.of_upd u₆)) (d := 1512) (by decide) (by decide) fun s₇ u₇ => ?_
  obtain hw₇ : WsReg s₇ base := ⟨by rw [u₇.other .s0 (by decide), u₆.other .s0 (by decide)]; exact hw₅.s0,
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
    obtain e : MC.scalar base s.mem = sv base s₄ K := by rw [sv₄ _ (by decide)]; exact cs K (by decide)
    obtain c5 : ∀ i, i < 45 → MC.toPoint.coordAt s₅.mem base (p224.sl i) = sv base s₅ i := fun i hi =>
      ca s₅.mem (by simp only [Cfg.sl, slot, p224]; omega_using [hi])
    obtain x0 : MC.toPoint.coordAt s₅.mem base MC.pAt = sv base s₅ RX := c5 RX (by decide)
    obtain x1 : MC.toPoint.coordAt s₅.mem base (MC.pAt + Impl.Weierstrass.Point.elemBytes MC.toPoint.k) =
        sv base s₅ RY := c5 RY (by decide)
    obtain x2 : MC.toPoint.coordAt s₅.mem base (MC.pAt + 2 * Impl.Weierstrass.Point.elemBytes MC.toPoint.k) =
        sv base s₅ RZ := c5 RZ (by decide)
    rw [e]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x0]; exact R₅.x
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x1]; exact R₅.y
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x2]; exact R₅.z
    · rw [Impl.Weierstrass.Point.Curve.pointAt, x0, x1, x2, dq, dq, dq]
      exact represents_of_rep R₅.rep

end VG.Proof.Ecdsa.RISCV64.P224.Window

end

end

/-!
# ECDH and public keys over P-224 on RISC-V: the multiplication and after

What follows the point's setup in both functions (`tail`) is proven once for
every curve in `Proof/Ecdh/RISCV64/TailAll.lean` (`TKit.tail_ok`). Here is what
that proof needs of P-224, its chain of `p - 2` (`chainP_ok`) and its
multiplication's contract (`mulNF`, `mul_meets`), and that proof's statements
on P-224's slots that other proofs name.
-/

@[expose] public section

/-!
## ECDH and public keys over P-224 on RISC-V: the setup

The constants (`consts_ok`, by `TailAll.lean`'s), and what both functions'
setups share.
-/

namespace VG.Proof.Ecdh.RISCV64.P224

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.P224
open VG.Proof.X25519.RISCV64 (Rest)

/-- Constants to slots below 44, each its own. -/
theorem consts_ok : ∀ (L : List (Nat × Nat)) {s : State} {base : Addr}, WsReg s base → (∀ e ∈ L, e.1 < 44) →
    (L.map Prod.fst).Nodup →
    WP isa (.block (L.flatMap fun e => setConst 4 (p224.sl e.1) e.2)) s fun s' =>
      Rest [.t0, .t1] s s' ∧ Unch base (L.map fun e => (p224.sl e.1, 32)) s.mem s'.mem ∧
      ∀ e ∈ L, sv base s' e.1 = e.2 % 2 ^ 256 :=
  fun L _ _ hw hlt hnd =>
    TKit.consts_ok p224 (by decide) L hw (fun e he => Nat.le_trans (Nat.le_of_lt (hlt e he)) (by decide)) hnd

/-- The constants, as `consts_ok` takes them. -/
theorem constCode_eq : constCode p224 = (consts p224).flatMap fun e => setConst 4 (p224.sl e.1) e.2 := rfl

/-- The constants' slots. -/
theorem consts_slots : ∀ e ∈ consts p224, e.1 < 44 := by decide

theorem consts_nodup : ((consts p224).map Prod.fst).Nodup := by decide

/-- The constants are below `2²⁵⁶`. -/
theorem consts_lt : ∀ e ∈ consts p224, e.2 < 2 ^ 256 := by decide

/-- The saves, `s0 = s3 = r` and `s2 = a0`. -/
theorem save_ok {s : State} {r : Reg} {base : Addr} (h0 : s.gpr r = base)
    (hwr : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : base.toNat + 8192 ≤ 2 ^ 64) (hal : base.toNat % 8 = 0) :
    WP isa (.block (saveCode r)) s fun s' => WsReg s' base ∧ s'.gpr .s3 = base ∧ s'.gpr .s2 = s.gpr .a0 ∧
      (∀ x, x ≠ .s0 → x ≠ .s2 → x ≠ .s3 → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ Unch base [(0, 40)] s.mem s'.mem ∧
      word s'.mem base 0 = s.gpr .s0 ∧ word s'.mem base 8 = s.gpr .s1 ∧ word s'.mem base 16 = s.gpr .s2 ∧
      word s'.mem base 24 = s.gpr .ra ∧ word s'.mem base 32 = s.gpr .s3 :=
  TKit.save_ok h0 hwr hn hal

end VG.Proof.Ecdh.RISCV64.P224

namespace VG.Proof.Ecdh.RISCV64.P224

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.P224
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point)
open VG.Spec.Ecdsa (bytesAt)
open VG.WriteBytes (writeBytes)

/-- What `vg_p224_mul` may write, as ranges of offsets. -/
abbrev mulKW : List (Nat × Nat) := [(512, 96), (608, 448), (128, 32), (1344, 32), (1504, 2 ^ 64)]

theorem unch_of_mulKeeps {base : Addr} {m m' : Mem} (h : MC.Keeps base m m') : Unch base mulKW m m' :=
  tkit.unch_of_mulKeeps h

/-- What `vg_p224_check_point` may write, as ranges of offsets. -/
abbrev checkKW : List (Nat × Nat) :=
  [(128, 32), (1248, 32), (1376, 32), (1408, 32), (3840, 256), (1152, 32), (1184, 32), (1280, 32), (1440, 32),
    (FL, 8), (8192, 2 ^ 64)]

theorem not_mask (b : Bool) : maskOf b ^^^ BitVec.ofInt 64 (-1) = maskOf (!b) := by cases b <;> decide

/-- A call on the working space, then `s0` from `s3`. -/
theorem wsCallR_ok {f : String} {body : Prog isa} (hn : body.noFrames = true) {K : Contract isa}
    (hK : Meets body K) {s : State} {base : Addr} (hw : WsReg s base) (h3 : s.gpr .s3 = base)
    (hpre : ∀ t : State, t.rd = [] → t.wr = [⟨base, 8192⟩] → t.gpr .a0 = base → t.mem = s.mem → K.pre t)
    {Q : State → Prop}
    (hQ : ∀ s' s'' : State, Kp s s'' → s''.mem = s'.mem → ∀ t : State, t.gpr .a0 = base → t.mem = s.mem →
      K.post t (s'.withRegions [] [⟨base, 8192⟩]) → Q s'') :
    WP isa (Cfg.wsCall f body) s Q :=
  Kit.wsCallR_ok hn hK hw h3 hpre hQ

/-- A slot below the flag's. -/
theorem sl_lt {i : Nat} (hi : i < 44) : p224.sl i % 8 = 0 ∧ p224.sl i + 8 * 4 ≤ 2048 ∧ p224.sl i + 8 * 4 ≤ FL := by
  simp only [Cfg.sl, slot, show p224.n = 4 from rfl, FL]; omega_using [hi]

/-- The masks of `x < n` and `x ≠ 0` into the flag, for `x` at slot `i`. -/
theorem rangeOf_ok {i : Nat} (hi : i < 44) {s : State} {base : Addr} (hw : WsReg s base) :
    WP isa (.block (rangeOf p224 i)) s fun s' =>
      Kp s s' ∧ Outside base FL 8 s.mem s'.mem ∧
      word s'.mem base FL = word s.mem base FL &&& maskOf (decide (sv base s i < sv base s MN)) &&&
        maskOf (!decide (sv base s i = 0)) :=
  TKit.rangeOf_ok p224 (by decide) (Nat.lt_of_lt_of_le hi (by decide)) hw

/-- The constants `tail` reads. -/
structure TailConsts (base : Addr) (s : State) : Prop where
  mp : sv base s MP = W.p
  mn : sv base s MN = W.n
  zero : sv base s ZERO = 0
  one : sv base s ONE = 1
  onep : sv base s ONEP = 1 * 2 ^ 256 % W.p
  ap : sv base s AP = W.a * 2 ^ 256 % W.p
  b3p : sv base s B3P = 3 * W.b * 2 ^ 256 % W.p
  expp : sv base s EXPP = W.p - 2

theorem TailConsts.of_unch {base : Addr} {s s' : State} {W' : List (Nat × Nat)} (h : TailConsts base s)
    (U : Unch base W' s.mem s'.mem)
    (hW : ∀ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP], ∀ w ∈ W', p224.sl i + 32 ≤ w.1 ∨ w.1 + w.2 ≤ p224.sl i) :
    TailConsts base s' :=
  have g := TKit.Consts.of_unch (c := p224) (by decide) ⟨h.mp, h.mn, h.zero, h.one, h.onep, h.ap, h.b3p, h.expp⟩ U hW
  ⟨g.mp, g.mn, g.zero, g.one, g.onep, g.ap, g.b3p, g.expp⟩

theorem chainLay : ChainLayR (chainP p224) 4 :=
  TKit.chainLay p224 (by decide) (by decide)

/-- The chain is `p - 2`'s. -/
theorem chainP_ok : ChainOkR (chainP p224) (W.p - 2) := ChainOkR.of_check (by lit_decide)

/-- The coordinate `[o] = [a] Z^(p-2)` out of Montgomery's form, `Z^(p-2) R` in `ACC`. -/
theorem affine_ok {s : State} {base : Addr} (hw : WsReg s base) {t o a : Nat} (ht : t < 44) (ho : o < 44)
    (ha : a < 44) (htm : t ≠ ONE ∧ t ≠ ACC) (hacc : sv base s ACC < W.p) (hone : sv base s ONE = 1) :
    WP isa (affineCoord p224 t o a) s fun s' =>
      Kp s s' ∧ Unch base [(p224.sl t, 32), (own 4, 256), (p224.sl o, 32), (own 4, 256)] s.mem s'.mem ∧
      sv base s' o < W.p ∧
      Fin.ofNat W.p (sv base s' o) = toM W.p (2 ^ 256) (sv base s a) * toM W.p (2 ^ 256) (sv base s ACC) :=
  tkit.affine_ok hw ht ho ha htm hacc hone

/-- The coordinates the multiplication's contract decodes. -/
theorem dq (hL : VG.Proof.Weierstrass.Law W) (x : Nat) : MC.toPoint.dec x = toM W.p (2 ^ 256) x :=
  tkit.dq hL x

theorem coord_sv (m : Mem) (base : Addr) (i : Nat) (hi : i < 100 := by decide) :
    MC.toPoint.coordAt m base (p224.sl i) = wordsVal m base (p224.sl i) 4 :=
  tkit.coord_sv m base i hi

/-- The point the multiplication's contract reads. -/
theorem point_eq (hL : VG.Proof.Weierstrass.Law W) (m : Mem) (base : Addr) :
    MC.point base m = .affine (toM W.p (2 ^ 256) (wordsVal m base (p224.sl RX) 4))
      (toM W.p (2 ^ 256) (wordsVal m base (p224.sl RY) 4)) :=
  tkit.point_eq hL m base

theorem rep_of_represents {X Y Z : Fe W} {P : Point W} (h : Impl.Weierstrass.MulBase.Represents X Y Z P) :
    Rep W X Y Z P :=
  Kit.rep_of_represents h

/-- What `tail` writes. -/
abbrev tailW : List (Nat × Nat) :=
  [(FL, 8)] ++ mulKW ++ chainWx (chainP p224) 4 ++
    [(p224.sl XM, 32), (own 4, 256), (p224.sl XO, 32), (own 4, 256)]

/-- `tail` with a call of `mulName`, whose code is `mulCode`, that computes
`R = [d]P` as `vg_p224_mul`'s contract says (`hcall`, from the state after
the range's masks, which changes only the flag): the range of `d` into the
flag, `R = [d]P`, `Z^(p-2)`, and `x`. -/
theorem tailWith_ok (hL : VG.Proof.Weierstrass.Law W) {mulName : String} {mulCode : Prog isa} {s : State}
    {base : Addr} (hw : WsReg s base)
    (h3 : s.gpr .s3 = base) (hc : TailConsts base s)
    (hcall : ∀ s₁ : State, WsReg s₁ base → s₁.gpr .s3 = base → Kp s s₁ → Unch base [(FL, 8)] s.mem s₁.mem →
      s₁.syms = s.syms →
      WP isa (Cfg.wsCall mulName mulCode) s₁ fun s₂ => Kp s₁ s₂ ∧
        MC.ResultInRange (MC.scalar base s₁.mem) (MC.point base s₁.mem) base s₁.mem s₂.mem) :
    WP isa (tail p224 mulName mulCode) s fun s' =>
      Kc s s' ∧ Unch base tailW s.mem s'.mem ∧
      word s'.mem base FL = word s.mem base FL &&& maskOf (decide (sv base s K < W.n)) &&&
        maskOf (!decide (sv base s K = 0)) ∧
      (1 ≤ sv base s K → sv base s K < W.n →
        Rep W (toM W.p (2 ^ 256) (sv base s' RX)) (toM W.p (2 ^ 256) (sv base s' RY))
          (toM W.p (2 ^ 256) (sv base s' RZ))
          (Spec.Weierstrass.mul (sv base s K) (.affine (toM W.p (2 ^ 256) (sv base s RX))
            (toM W.p (2 ^ 256) (sv base s RY)))) ∧
        sv base s' RX < W.p ∧ sv base s' RY < W.p ∧ sv base s' RZ < W.p) ∧
      sv base s' XO < W.p ∧
      Fin.ofNat W.p (sv base s' XO) =
        toM W.p (2 ^ 256) (sv base s' RX) * toM W.p (2 ^ 256) (sv base s' RZ) ^ (W.p - 2) ∧
      sv base s' ACC < W.p ∧
      toM W.p (2 ^ 256) (sv base s' ACC) = toM W.p (2 ^ 256) (sv base s' RZ) ^ (W.p - 2) :=
  tkit.tailWith_ok chainP_ok hL hw h3 ⟨hc.mp, hc.mn, hc.zero, hc.one, hc.onep, hc.ap, hc.b3p, hc.expp⟩ hcall

/-- A byte of a region apart from the working space. -/
theorem out_of_disj {p base : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) (hn : p.toNat + n ≤ 2 ^ 64)
    {off i : Nat} (hi : off + i < n) : ¬ (⟨base, 8192⟩ : Region).Contains (p + BitVec.ofNat 64 (off + i)) 1 :=
  Kit.out_of_disj hd hn hi

/-- Eight bytes of a region. -/
theorem in_rd8 {rs : List Region} {p : Addr} {n : Nat} (hr : (⟨p, n⟩ : Region) ∈ rs) {off : Nat} (ho : off + 8 ≤ n)
    (hn : n ≤ 8192 := by decide) :
    InRegions rs (p + BitVec.ofNat 64 off) 8 :=
  Kit.in_rd8 hr ho hn

/-- Bytes apart from the working space survive changes within it. -/
theorem bytesAt_unch {base q : Addr} {W : List (Nat × Nat)} {n : Nat} {m m' : Mem} (U : Unch base W m m')
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ 8192)
    (hsep : ∀ i < n, ¬ (⟨base, 8192⟩ : Region).Contains (q + BitVec.ofNat 64 i) 1) :
    bytesAt m' q n = bytesAt m q n :=
  Kit.bytesAt_unch U hW hsep

/-- The value of a constant's slot. -/
theorem const_at {base : Addr} {s : State} (hc : ∀ e ∈ consts p224, sv base s e.1 = e.2) (k : Nat)
    (hk : k < (consts p224).length := by decide) : sv base s (consts p224)[k].1 = (consts p224)[k].2 :=
  hc _ (List.getElem_mem hk)

/-- The bytes just written. -/
theorem bytesAt_writeBytes (m : Mem) (q : Addr) (xs : List Byte) (h : xs.length ≤ 2 ^ 64) :
    bytesAt (writeBytes m q xs) q xs.length = xs :=
  Kit.bytesAt_writeBytes m q xs h

theorem and_one (b : Bool) : maskOf b &&& BitVec.ofInt 64 1 = if b then 1 else 0 := by cases b <;> decide

/-- Bytes of a region apart from the working space, from an offset. -/
theorem sep_at' {p base : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) (hn : p.toNat + n ≤ 2 ^ 64)
    {off k : Nat} (hk : off + k ≤ n) :
    ∀ i < k, ¬ (⟨base, 8192⟩ : Region).Contains (p + BitVec.ofNat 64 off + BitVec.ofNat 64 i) 1 := fun i hi => by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact out_of_disj hd hn (by omega_using [hk, hi])

/-- The multiplication's code pushes no frames. -/
theorem mulNF : mulP224.noFrames = true :=
  Impl.Ecdsa.RISCV64.mulP224_noFrames

/-- The multiplication meets the contract `tail` calls it by. -/
theorem mul_meets (hL : VG.Proof.Weierstrass.Law tkit.c.C) : Meets mulP224 (TKit.mulRVc tkit.MC) :=
  VG.Proof.Ecdsa.RISCV64.P224.Window.mul_rv hL

/-- `tail` with `vg_p224_mul`. -/
theorem tail_ok (hL : VG.Proof.Weierstrass.Law W) {s : State} {base : Addr} (hw : WsReg s base)
    (h3 : s.gpr .s3 = base) (hc : TailConsts base s) (hx : sv base s RX < W.p) (hy : sv base s RY < W.p)
    (hon : Spec.Weierstrass.onCurve W (.affine (toM W.p (2 ^ 256) (sv base s RX))
      (toM W.p (2 ^ 256) (sv base s RY))) = true) :
    WP isa (tail p224 "vg_p224_mul" mulP224) s fun s' =>
      Kc s s' ∧ Unch base tailW s.mem s'.mem ∧
      word s'.mem base FL = word s.mem base FL &&& maskOf (decide (sv base s K < W.n)) &&&
        maskOf (!decide (sv base s K = 0)) ∧
      (1 ≤ sv base s K → sv base s K < W.n →
        Rep W (toM W.p (2 ^ 256) (sv base s' RX)) (toM W.p (2 ^ 256) (sv base s' RY))
          (toM W.p (2 ^ 256) (sv base s' RZ))
          (Spec.Weierstrass.mul (sv base s K) (.affine (toM W.p (2 ^ 256) (sv base s RX))
            (toM W.p (2 ^ 256) (sv base s RY)))) ∧
        sv base s' RX < W.p ∧ sv base s' RY < W.p ∧ sv base s' RZ < W.p) ∧
      sv base s' XO < W.p ∧
      Fin.ofNat W.p (sv base s' XO) =
        toM W.p (2 ^ 256) (sv base s' RX) * toM W.p (2 ^ 256) (sv base s' RZ) ^ (W.p - 2) ∧
      sv base s' ACC < W.p ∧
      toM W.p (2 ^ 256) (sv base s' ACC) = toM W.p (2 ^ 256) (sv base s' RZ) ^ (W.p - 2) :=
  tkit.tail_ok chainP_ok mulNF (mul_meets hL) hL hw h3 ⟨hc.mp, hc.mn, hc.zero, hc.one, hc.onep, hc.ap, hc.b3p, hc.expp⟩ hx hy hon

end VG.Proof.Ecdh.RISCV64.P224
