import VerifiedGarbage.Impl.X448.AArch64.Base
import VerifiedGarbage.Proof.X448.AArch64.Fast.Verified
import VerifiedGarbage.Proof.X448.AArch64.Base.AddDefs
import VerifiedGarbage.Proof.X448.BaseAdd
import VerifiedGarbage.Proof.X448.AArch64.Main
import VerifiedGarbage.Proof.X448.BaseDigits
import VerifiedGarbage.Proof.Curve448.AArch64.Square
import VerifiedGarbage.Proof.X448.AArch64.Base.Const
import VerifiedGarbage.Proof.X448.AArch64.PointwiseSmall
import VerifiedGarbage.Proof.X448.Wide.TailMul
import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.X448.AArch64.Weak.Main
import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
import VerifiedGarbage.Proof.X448.Edwards.Ladder
import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Base.Add`. -/
section

/-!
# X448 of the base point on AArch64: the addition of an affine entry

Untrusted: everything here is checked by Lean. `addAffine`'s field operations
(`Impl/X448/AArch64/Base.lean`) in the ladder's slot environment
(`Proof/X448/AArch64/Weak/Env.lean`): each part runs its scalar operations,
then its pair of products in AdvSIMD (`WP.weave`, given that their footprints
are independent, which the caller evaluates for its slots); the environment
afterwards is `affEnv` of the one before.
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64
open VG.Impl.X448.AArch64 (slot)
open VG.Proof.X448.AArch64 (Scr)
open VG.Proof.X448.AArch64.Weak (Index Env opCopy)
open VG.Proof.X448.AArch64.Fast
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Impl.X448.AArch64.Fast (ops codeOf weave)
open VG.Impl.Curve448.AArch64.Neon (mul2)
open VG.AArch64.Interleave (blockFp)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- The environment after `addAffine x1 y1 z1 x2 y2`, in the order it computes: the
temporaries are slots 10–18, and slot 19 is zero. -/
def affEnv (x1 y1 z1 x2 y2 : Index) (e : Env) : Env :=
  let e := Function.update e 10 (e z1 * e z1)
  let e := Function.update (Function.update e 11 (e x1 * e x2)) 12 (e y1 * e y2)
  let e := Function.update e 13 (e 11 * e 12)
  let e := Function.update e 14 (e 10 + Spec.X448.a24 * e 13)
  let e := Function.update e 15 (e 19 - e 13)
  let e := Function.update e 10 (e 10 + Spec.X448.a24 * e 15)
  let e := Function.update (Function.update e 16 (e x1 * e y2)) 17 (e y1 * e x2)
  let e := Function.update (Function.update e 13 (e 16 + e 17)) 15 (e 16 - e 17)
  let e := Function.update (Function.update e 16 (e 12 + e 11)) 17 (e 12 - e 11)
  let e := Function.update e 18 (e 14 * e 10)
  let e := Function.update (Function.update e 11 (e z1 * e 14)) 12 (e z1 * e 10)
  let e := opCopy z1 18 e
  Function.update (Function.update e x1 (e 11 * e 13)) y1 (e 12 * e 17)

/-- The four interleaved parts and the sums between them, with the slots as indices. -/
theorem addAffine_eq (x1 y1 z1 x2 y2 : Index) :
    Impl.X448.AArch64.Base.addAffine (slot x1.val) (slot y1.val) (slot z1.val) (slot x2.val) (slot y2.val) =
      weave (codeOf [.mul (slot (10 : Index).val) (slot z1.val) (slot z1.val)])
        (mul2 (slot (11 : Index).val) (slot x1.val) (slot x2.val) (slot (12 : Index).val) (slot y1.val)
          (slot y2.val)) ++
      weave (codeOf [.mul (slot (13 : Index).val) (slot (11 : Index).val) (slot (12 : Index).val),
          .small (slot (14 : Index).val) (slot (10 : Index).val) (slot (13 : Index).val),
          .sub (slot (15 : Index).val) (slot (19 : Index).val) (slot (13 : Index).val),
          .small (slot (10 : Index).val) (slot (10 : Index).val) (slot (15 : Index).val)])
        (mul2 (slot (16 : Index).val) (slot x1.val) (slot y2.val) (slot (17 : Index).val) (slot y1.val)
          (slot x2.val)) ++
      codeOf ([.addSub (slot (13 : Index).val) (slot (15 : Index).val) (slot (16 : Index).val)
          (slot (17 : Index).val),
        .addSub (slot (16 : Index).val) (slot (17 : Index).val) (slot (12 : Index).val)
          (slot (11 : Index).val)] : List Impl.X448.AArch64.Fast.Op) ++
      weave (codeOf [.mul (slot (18 : Index).val) (slot (14 : Index).val) (slot (10 : Index).val)])
        (mul2 (slot (11 : Index).val) (slot z1.val) (slot (14 : Index).val) (slot (12 : Index).val)
          (slot z1.val) (slot (10 : Index).val)) ++
      weave (codeOf [.copy (slot z1.val) (slot (18 : Index).val)])
        (mul2 (slot x1.val) (slot (11 : Index).val) (slot (13 : Index).val) (slot y1.val)
          (slot (12 : Index).val) (slot (17 : Index).val)) := rfl

theorem copyOp {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) (o a : Index)
    {rest : List Impl.X448.AArch64.Fast.Op} {Q : State → Prop}
    (h : ∀ t, FKeep base s t → BEnv t.mem base →
      (∀ j < 8, VG.Proof.X448.AArch64.limbs t.mem base (slot o.val) j =
        VG.Proof.X448.AArch64.limbs s.mem base (slot a.val) j) →
      Same base [o] s.mem t.mem → EV t.mem base = opCopy o a (EV s.mem base) → WP isa (ops rest) t Q) :
    WP isa (ops (.copy (slot o.val) (slot a.val) :: rest)) s Q :=
  WP.seq (WP.mono (VG.Proof.X448.AArch64.Fast.copyE hs hb o a) fun t ⟨tk, tb, tl, ts, te⟩ => h t tk tb tl ts te)

section
variable {s : State} {base : Addr}

/-- The scalar half of `part1`. -/
theorem ops1_ok (z1 : Index) (hs : Scr s base) (hb : BEnv s.mem base) :
    WP isa (ops [.mul (slot (10 : Index).val) (slot z1.val) (slot z1.val)]) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base [10] s.mem t.mem ∧
      Bnd Mb t.mem base (slot (10 : Index).val) ∧
      EV t.mem base = Function.update (EV s.mem base) 10 (EV s.mem base z1 * EV s.mem base z1) :=
  mulOp hs hb 10 z1 z1 (Or.inl rfl) fun _ k1 b1 m1 s1 e1 => WP.block_nil ⟨k1, b1, s1, m1, e1⟩

/-- The first part: `b = Z²`, then `c = X x` and `e = Y y` in AdvSIMD. -/
theorem part1_ok (x1 y1 z1 x2 y2 : Index) (hs : Scr s base) (hb : BEnv s.mem base)
    (hind : ((blockFp (codeOf [.mul (slot (10 : Index).val) (slot z1.val) (slot z1.val)])).bind fun A =>
      (blockFp (mul2 (slot (11 : Index).val) (slot x1.val) (slot x2.val) (slot (12 : Index).val)
        (slot y1.val) (slot y2.val))).map fun B => A.indep B) = some true) :
    WP isa (.block (weave (codeOf [.mul (slot (10 : Index).val) (slot z1.val) (slot z1.val)])
        (mul2 (slot (11 : Index).val) (slot x1.val) (slot x2.val) (slot (12 : Index).val) (slot y1.val)
          (slot y2.val)))) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base ([10] ++ [11, 12]) s.mem t.mem ∧
      Bnd Mb t.mem base (slot (10 : Index).val) ∧ Bnd Mb t.mem base (slot (11 : Index).val) ∧
      Bnd Mb t.mem base (slot (12 : Index).val) ∧
      EV t.mem base =
        let e := EV s.mem base
        let e := Function.update e 10 (e z1 * e z1)
        Function.update (Function.update e 11 (e x1 * e x2)) 12 (e y1 * e y2) := by
  refine WP.weave hind (WP.mono (block_codeOf (ops1_ok z1 hs hb)) fun t ⟨tk, tb, ts, t10, te⟩ => ?_)
  refine WP.mono (mul2E (tk.scr hs) tb 11 x1 x2 12 y1 y2 (by decide)) fun u ⟨uk, ub, u11, u12, us, ue⟩ =>
    ⟨tk.trans uk, ub, ts.append us, us.bnd (by decide) t10, u11, u12, ?_⟩
  rw [ue, te]

/-- The scalar half of `part2`: `c·e`, `f = b + a24 (c e)`, `-(c e)` and `g = b + a24 (-(c e))`. -/
theorem ops2_ok (hs : Scr s base) (hb : BEnv s.mem base) (h10 : Bnd Mb s.mem base (slot (10 : Index).val))
    (h19 : Bnd Mb s.mem base (slot (19 : Index).val)) :
    WP isa (ops [.mul (slot (13 : Index).val) (slot (11 : Index).val) (slot (12 : Index).val),
        .small (slot (14 : Index).val) (slot (10 : Index).val) (slot (13 : Index).val),
        .sub (slot (15 : Index).val) (slot (19 : Index).val) (slot (13 : Index).val),
        .small (slot (10 : Index).val) (slot (10 : Index).val) (slot (15 : Index).val)]) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base [13, 14, 15, 10] s.mem t.mem ∧
      EV t.mem base =
        let e := EV s.mem base
        let e := Function.update e 13 (e 11 * e 12)
        let e := Function.update e 14 (e 10 + Spec.X448.a24 * e 13)
        let e := Function.update e 15 (e 19 - e 13)
        Function.update e 10 (e 10 + Spec.X448.a24 * e 15) := by
  refine mulOp hs hb 13 11 12 (by decide) fun t1 k1 b1 m1 s1 e1 => ?_
  have hs1 := k1.scr hs
  refine smallOp (o := 14) (a := 10) (e := 13) hs1 b1 (s1.bnd (by decide) h10) fun t2 k2 b2 s2 e2 => ?_
  have hs2 := k2.scr hs1
  refine subOp (o := 15) (a := 19) (b := 13) hs2 b2 (s2.bnd (by decide) (s1.bnd (by decide) h19))
    (s2.bnd (by decide) m1) (by decide) (by decide) fun t3 k3 b3 s3 e3 => ?_
  have hs3 := k3.scr hs2
  refine smallOp (o := 10) (a := 10) (e := 15) hs3 b3
    (s3.bnd (by decide) (s2.bnd (by decide) (s1.bnd (by decide) h10))) fun t4 k4 b4 s4 e4 => ?_
  refine WP.block_nil ⟨k1.trans (k2.trans (k3.trans k4)), b4, ((s1.append s2).append s3).append s4, ?_⟩
  rw [e4, e3, e2, e1]

/-- The second part: `ops2`, then `X y` and `Y x` in AdvSIMD. -/
theorem part2_ok (x1 y1 x2 y2 : Index) (hs : Scr s base) (hb : BEnv s.mem base)
    (h10 : Bnd Mb s.mem base (slot (10 : Index).val)) (h19 : Bnd Mb s.mem base (slot (19 : Index).val))
    (hind : ((blockFp (codeOf [.mul (slot (13 : Index).val) (slot (11 : Index).val) (slot (12 : Index).val),
        .small (slot (14 : Index).val) (slot (10 : Index).val) (slot (13 : Index).val),
        .sub (slot (15 : Index).val) (slot (19 : Index).val) (slot (13 : Index).val),
        .small (slot (10 : Index).val) (slot (10 : Index).val) (slot (15 : Index).val)])).bind fun A =>
      (blockFp (mul2 (slot (16 : Index).val) (slot x1.val) (slot y2.val) (slot (17 : Index).val)
        (slot y1.val) (slot x2.val))).map fun B => A.indep B) = some true) :
    WP isa (.block (weave (codeOf [.mul (slot (13 : Index).val) (slot (11 : Index).val) (slot (12 : Index).val),
        .small (slot (14 : Index).val) (slot (10 : Index).val) (slot (13 : Index).val),
        .sub (slot (15 : Index).val) (slot (19 : Index).val) (slot (13 : Index).val),
        .small (slot (10 : Index).val) (slot (10 : Index).val) (slot (15 : Index).val)])
        (mul2 (slot (16 : Index).val) (slot x1.val) (slot y2.val) (slot (17 : Index).val) (slot y1.val)
          (slot x2.val)))) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base ([13, 14, 15, 10] ++ [16, 17]) s.mem t.mem ∧
      Bnd Mb t.mem base (slot (16 : Index).val) ∧ Bnd Mb t.mem base (slot (17 : Index).val) ∧
      EV t.mem base =
        let e := EV s.mem base
        let e := Function.update e 13 (e 11 * e 12)
        let e := Function.update e 14 (e 10 + Spec.X448.a24 * e 13)
        let e := Function.update e 15 (e 19 - e 13)
        let e := Function.update e 10 (e 10 + Spec.X448.a24 * e 15)
        Function.update (Function.update e 16 (e x1 * e y2)) 17 (e y1 * e x2) := by
  refine WP.weave hind (WP.mono (block_codeOf (ops2_ok hs hb h10 h19)) fun t ⟨tk, tb, ts, te⟩ => ?_)
  refine WP.mono (mul2E (tk.scr hs) tb 16 x1 y2 17 y1 x2 (by decide)) fun u ⟨uk, ub, u16, u17, us, ue⟩ =>
    ⟨tk.trans uk, ub, ts.append us, u16, u17, ?_⟩
  rw [ue, te]

/-- The third part: `k = X y + Y x` and `e - c`. -/
theorem part3_ok (hs : Scr s base) (hb : BEnv s.mem base) (h11 : Bnd Mb s.mem base (slot (11 : Index).val))
    (h12 : Bnd Mb s.mem base (slot (12 : Index).val)) (h16 : Bnd Mb s.mem base (slot (16 : Index).val))
    (h17 : Bnd Mb s.mem base (slot (17 : Index).val)) :
    WP isa (.block (codeOf [.addSub (slot (13 : Index).val) (slot (15 : Index).val) (slot (16 : Index).val)
          (slot (17 : Index).val),
        .addSub (slot (16 : Index).val) (slot (17 : Index).val) (slot (12 : Index).val)
          (slot (11 : Index).val)])) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base [13, 15, 16, 17] s.mem t.mem ∧
      EV t.mem base =
        let e := EV s.mem base
        let e := Function.update (Function.update e 13 (e 16 + e 17)) 15 (e 16 - e 17)
        Function.update (Function.update e 16 (e 12 + e 11)) 17 (e 12 - e 11) := by
  refine block_codeOf (addSubOp (o₁ := 13) (o₂ := 15) (a := 16) (b := 17) hs hb h16 h17
    (by decide) (by decide) (by decide) (by decide) (by decide) fun t1 k1 b1 s1 e1 => ?_)
  refine addSubOp (o₁ := 16) (o₂ := 17) (a := 12) (b := 11) (k1.scr hs) b1 (s1.bnd (by decide) h12)
    (s1.bnd (by decide) h11) (by decide) (by decide) (by decide) (by decide) (by decide)
    fun t2 k2 b2 s2 e2 => ?_
  refine WP.block_nil ⟨k1.trans k2, b2, s1.append s2, ?_⟩
  rw [e2, e1]

/-- The scalar half of `part4`: `f·g`. -/
theorem ops4_ok (hs : Scr s base) (hb : BEnv s.mem base) :
    WP isa (ops [.mul (slot (18 : Index).val) (slot (14 : Index).val) (slot (10 : Index).val)]) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base [18] s.mem t.mem ∧
      Bnd Mb t.mem base (slot (18 : Index).val) ∧
      EV t.mem base = Function.update (EV s.mem base) 18 (EV s.mem base 14 * EV s.mem base 10) :=
  mulOp hs hb 18 14 10 (by decide) fun _ k1 b1 m1 s1 e1 => WP.block_nil ⟨k1, b1, s1, m1, e1⟩

/-- The fourth part: `f·g`, then `Z f` and `Z g` in AdvSIMD. -/
theorem part4_ok (z1 : Index) (hs : Scr s base) (hb : BEnv s.mem base)
    (hind : ((blockFp (codeOf [.mul (slot (18 : Index).val) (slot (14 : Index).val) (slot (10 : Index).val)])).bind
      fun A => (blockFp (mul2 (slot (11 : Index).val) (slot z1.val) (slot (14 : Index).val)
        (slot (12 : Index).val) (slot z1.val) (slot (10 : Index).val))).map fun B => A.indep B) = some true) :
    WP isa (.block (weave (codeOf [.mul (slot (18 : Index).val) (slot (14 : Index).val) (slot (10 : Index).val)])
        (mul2 (slot (11 : Index).val) (slot z1.val) (slot (14 : Index).val) (slot (12 : Index).val)
          (slot z1.val) (slot (10 : Index).val)))) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base ([18] ++ [11, 12]) s.mem t.mem ∧
      Bnd Mb t.mem base (slot (18 : Index).val) ∧ Bnd Mb t.mem base (slot (11 : Index).val) ∧
      Bnd Mb t.mem base (slot (12 : Index).val) ∧
      EV t.mem base =
        let e := EV s.mem base
        let e := Function.update e 18 (e 14 * e 10)
        Function.update (Function.update e 11 (e z1 * e 14)) 12 (e z1 * e 10) := by
  refine WP.weave hind (WP.mono (block_codeOf (ops4_ok hs hb)) fun t ⟨tk, tb, ts, t18, te⟩ => ?_)
  refine WP.mono (mul2E (tk.scr hs) tb 11 z1 14 12 z1 10 (by decide)) fun u ⟨uk, ub, u11, u12, us, ue⟩ =>
    ⟨tk.trans uk, ub, ts.append us, us.bnd (by decide) t18, u11, u12, ?_⟩
  rw [ue, te]

/-- The scalar half of `part5`: `Z := f·g`. -/
theorem ops5_ok (z1 : Index) (hs : Scr s base) (hb : BEnv s.mem base)
    (h18 : Bnd Mb s.mem base (slot (18 : Index).val)) :
    WP isa (ops [.copy (slot z1.val) (slot (18 : Index).val)]) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base [z1] s.mem t.mem ∧ Bnd Mb t.mem base (slot z1.val) ∧
      EV t.mem base = opCopy z1 18 (EV s.mem base) :=
  copyOp hs hb z1 18 fun _ k1 b1 l1 s1 e1 =>
    WP.block_nil ⟨k1, b1, s1, fun j hj => by rw [l1 j hj]; exact h18 j hj, e1⟩

/-- The fifth part: `Z := f·g`, then `X := (Z f) k` and `Y := (Z g)(e - c)` in AdvSIMD. -/
theorem part5_ok (x1 y1 z1 : Index) (hxy : x1 ≠ y1) (hzx : z1 ≠ x1) (hzy : z1 ≠ y1)
    (hs : Scr s base) (hb : BEnv s.mem base) (h18 : Bnd Mb s.mem base (slot (18 : Index).val))
    (hind : ((blockFp (codeOf [.copy (slot z1.val) (slot (18 : Index).val)])).bind fun A =>
      (blockFp (mul2 (slot x1.val) (slot (11 : Index).val) (slot (13 : Index).val) (slot y1.val)
        (slot (12 : Index).val) (slot (17 : Index).val))).map fun B => A.indep B) = some true) :
    WP isa (.block (weave (codeOf [.copy (slot z1.val) (slot (18 : Index).val)])
        (mul2 (slot x1.val) (slot (11 : Index).val) (slot (13 : Index).val) (slot y1.val)
          (slot (12 : Index).val) (slot (17 : Index).val)))) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base ([z1] ++ [x1, y1]) s.mem t.mem ∧
      Bnd Mb t.mem base (slot x1.val) ∧ Bnd Mb t.mem base (slot y1.val) ∧ Bnd Mb t.mem base (slot z1.val) ∧
      EV t.mem base =
        let e := EV s.mem base
        let e := opCopy z1 18 e
        Function.update (Function.update e x1 (e 11 * e 13)) y1 (e 12 * e 17) := by
  refine WP.weave hind (WP.mono (block_codeOf (ops5_ok z1 hs hb h18)) fun t ⟨tk, tb, ts, tz, te⟩ => ?_)
  refine WP.mono (mul2E (tk.scr hs) tb x1 11 13 y1 12 17 hxy) fun u ⟨uk, ub, ux, uy, us, ue⟩ =>
    ⟨tk.trans uk, ub, ts.append us, ux, uy, us.bnd (by simp [hzx, hzy]) tz, ?_⟩
  rw [ue, te]

/-- **The addition of an affine entry**: `(x₂, y₂)` (slots `x2`, `y2`, any limbs below `Ib`)
to `(X : Y : Z)` (slots `x1`, `y1`, `z1`), given zero's bound in slot 19 and the
independence of each part's two streams (`hind₁`–`hind₅`). -/
theorem addAffine_ok (x1 y1 z1 x2 y2 : Index) (hxy : x1 ≠ y1) (hzx : z1 ≠ x1) (hzy : z1 ≠ y1)
    (hs : Scr s base) (hb : BEnv s.mem base) (h19 : Bnd Mb s.mem base (slot (19 : Index).val))
    (hind₁ : ((blockFp (codeOf [.mul (slot (10 : Index).val) (slot z1.val) (slot z1.val)])).bind fun A =>
      (blockFp (mul2 (slot (11 : Index).val) (slot x1.val) (slot x2.val) (slot (12 : Index).val)
        (slot y1.val) (slot y2.val))).map fun B => A.indep B) = some true)
    (hind₂ : ((blockFp (codeOf [.mul (slot (13 : Index).val) (slot (11 : Index).val) (slot (12 : Index).val),
        .small (slot (14 : Index).val) (slot (10 : Index).val) (slot (13 : Index).val),
        .sub (slot (15 : Index).val) (slot (19 : Index).val) (slot (13 : Index).val),
        .small (slot (10 : Index).val) (slot (10 : Index).val) (slot (15 : Index).val)])).bind fun A =>
      (blockFp (mul2 (slot (16 : Index).val) (slot x1.val) (slot y2.val) (slot (17 : Index).val)
        (slot y1.val) (slot x2.val))).map fun B => A.indep B) = some true)
    (hind₄ : ((blockFp (codeOf [.mul (slot (18 : Index).val) (slot (14 : Index).val) (slot (10 : Index).val)])).bind
      fun A => (blockFp (mul2 (slot (11 : Index).val) (slot z1.val) (slot (14 : Index).val)
        (slot (12 : Index).val) (slot z1.val) (slot (10 : Index).val))).map fun B => A.indep B) = some true)
    (hind₅ : ((blockFp (codeOf [.copy (slot z1.val) (slot (18 : Index).val)])).bind fun A =>
      (blockFp (mul2 (slot x1.val) (slot (11 : Index).val) (slot (13 : Index).val) (slot y1.val)
        (slot (12 : Index).val) (slot (17 : Index).val))).map fun B => A.indep B) = some true) :
    WP isa (.block (Impl.X448.AArch64.Base.addAffine (slot x1.val) (slot y1.val) (slot z1.val) (slot x2.val)
        (slot y2.val))) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base (temps ++ [z1, x1, y1]) s.mem t.mem ∧
      Bnd Mb t.mem base (slot x1.val) ∧ Bnd Mb t.mem base (slot y1.val) ∧ Bnd Mb t.mem base (slot z1.val) ∧
      EV t.mem base = affEnv x1 y1 z1 x2 y2 (EV s.mem base) := by
  rw [addAffine_eq, List.append_assoc, List.append_assoc, List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono (part1_ok x1 y1 z1 x2 y2 hs hb hind₁)
    fun t1 ⟨k1, b1, s1, m10, m11, m12, e1⟩ => ?_)
  have hs1 := k1.scr hs
  refine WP.block_append_iff.mpr (WP.mono (part2_ok x1 y1 x2 y2 hs1 b1 m10 (s1.bnd (by decide) h19) hind₂)
    fun t2 ⟨k2, b2, s2, m16, m17, e2⟩ => ?_)
  have hs2 := k2.scr hs1
  refine WP.block_append_iff.mpr (WP.mono (part3_ok hs2 b2 (s2.bnd (by decide) m11) (s2.bnd (by decide) m12)
    m16 m17) fun t3 ⟨k3, b3, s3, e3⟩ => ?_)
  have hs3 := k3.scr hs2
  refine WP.block_append_iff.mpr (WP.mono (part4_ok z1 hs3 b3 hind₄) fun t4 ⟨k4, b4, s4, m18, _, _, e4⟩ => ?_)
  refine WP.mono (part5_ok x1 y1 z1 hxy hzx hzy (k4.scr hs3) b4 m18 hind₅)
    fun t5 ⟨k5, b5, s5, mx, my, mz, e5⟩ => ?_
  have hS : Same base (temps ++ [z1, x1, y1]) s.mem t5.mem :=
    VG.Proof.X448.AArch64.Base.Same.mono (s1.append (s2.append (s3.append (s4.append s5)))) fun i hi => by
      simp only [temps, List.cons_append, List.nil_append] at hi ⊢
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp
  refine ⟨k1.trans (k2.trans (k3.trans (k4.trans k5))), b5, hS, mx, my, mz, ?_⟩
  rw [e5, e4, e3, e2, e1]; rfl

end

end VG.Proof.X448.AArch64.Base

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Base.AddEnv`. -/
section

/-!
# X448 of the base point on AArch64: the addition's environment is `addPt`

Untrusted: everything here is checked by Lean. For the two accumulators' slots,
`affEnv` puts `addPt` of the accumulator and the entry (with `Z = 1`) in the
accumulator's slots, and keeps every slot but the temporaries.
-/

namespace VG.Proof.X448.AArch64.Base

open VG.Proof.X448.AArch64.Weak (Index Env opCopy)
open VG.Spec.Ed448 (Point)
open VG.Proof.X448 (addPt)

/-- What `addAffine` computes from `(X : Y : Z)` and `(x, y)`, with `z0` (zero) in slot 19. -/
def affPt (X Y Z x y z0 : Spec.X448.Fe) : Point :=
  let b := Z * Z
  let c := X * x
  let e := Y * y
  let f := b + Spec.X448.a24 * (c * e)
  let g := b + Spec.X448.a24 * (z0 - c * e)
  ⟨Z * f * (X * y + Y * x), Z * g * (e - c), f * g⟩

theorem affEnv_A (e : Env) : pt (affEnv 0 1 2 6 7 e) 0 1 2 = affPt (e 0) (e 1) (e 2) (e 6) (e 7) (e 19) := rfl

theorem affEnv_B (e : Env) : pt (affEnv 3 4 5 8 9 e) 3 4 5 = affPt (e 3) (e 4) (e 5) (e 8) (e 9) (e 19) := rfl

theorem affPt_eq (X Y Z x y : Spec.X448.Fe) : affPt X Y Z x y 0 = addPt ⟨X, Y, Z⟩ ⟨x, y, 1⟩ := by
  simp only [affPt, addPt, Point.mk.injEq]
  refine ⟨Ed448.toZ_inj.1 ?_, Ed448.toZ_inj.1 ?_, Ed448.toZ_inj.1 ?_⟩ <;>
    simp only [Ed448.toZ_add, Ed448.toZ_sub, Ed448.toZ_mul, Ed448.toZ_zero, Ed448.toZ_one] <;> ring

end VG.Proof.X448.AArch64.Base

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Base.AddGen`. -/
section

/-!
# X448 of the base point on AArch64: the complete addition

Untrusted: everything here is checked by Lean. `addOps` (`Impl/X448/AArch64/Base.lean`),
scalar field operations only, for the four doublings and the last addition: the
environment afterwards is `genEnv` of the one before, which for the slots used is
`addPt` of the two points (`genEnv_dbl`, `genEnv_add`, `genPt_eq`).
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64
open VG.Impl.X448.AArch64 (slot)
open VG.Proof.X448.AArch64 (Scr)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Impl.X448.AArch64.Fast (ops codeOf)
open VG.Spec.Ed448 (Point)
open VG.Proof.X448 (addPt)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- One operation's update of the environment. -/
def mulS (o a b : Index) (e : Env) : Env := Function.update e o (e a * e b)
def smallS (o a c : Index) (e : Env) : Env := Function.update e o (e a + Spec.X448.a24 * e c)
def subS (o a b : Index) (e : Env) : Env := Function.update e o (e a - e b)
def addSubS (o₁ o₂ a b : Index) (e : Env) : Env :=
  Function.update (Function.update e o₁ (e a + e b)) o₂ (e a - e b)

/-- The environment after `addOps x1 y1 z1 x2 y2 z2`. -/
def genEnv (x1 y1 z1 x2 y2 z2 : Index) (e : Env) : Env :=
  mulS z1 15 11 <| mulS y1 13 16 <| mulS 13 10 11 <| mulS x1 12 17 <| mulS 12 10 15 <|
  addSubS 14 16 13 12 <| addSubS 17 18 14 16 <| mulS 16 y1 x2 <| mulS 14 x1 y2 <|
  smallS 11 11 16 <| subS 16 19 14 <| smallS 15 11 14 <| mulS 14 12 13 <| mulS 13 y1 y2 <|
  mulS 12 x1 x2 <| mulS 11 10 10 <| mulS 10 z1 z2 e

theorem addOps_eq (x1 y1 z1 x2 y2 z2 : Index) :
    Impl.X448.AArch64.Base.addOps (slot x1.val) (slot y1.val) (slot z1.val) (slot x2.val) (slot y2.val)
      (slot z2.val) =
    [.mul (slot (10 : Index).val) (slot z1.val) (slot z2.val),
     .mul (slot (11 : Index).val) (slot (10 : Index).val) (slot (10 : Index).val),
     .mul (slot (12 : Index).val) (slot x1.val) (slot x2.val),
     .mul (slot (13 : Index).val) (slot y1.val) (slot y2.val),
     .mul (slot (14 : Index).val) (slot (12 : Index).val) (slot (13 : Index).val),
     .small (slot (15 : Index).val) (slot (11 : Index).val) (slot (14 : Index).val),
     .sub (slot (16 : Index).val) (slot (19 : Index).val) (slot (14 : Index).val),
     .small (slot (11 : Index).val) (slot (11 : Index).val) (slot (16 : Index).val),
     .mul (slot (14 : Index).val) (slot x1.val) (slot y2.val),
     .mul (slot (16 : Index).val) (slot y1.val) (slot x2.val),
     .addSub (slot (17 : Index).val) (slot (18 : Index).val) (slot (14 : Index).val) (slot (16 : Index).val),
     .addSub (slot (14 : Index).val) (slot (16 : Index).val) (slot (13 : Index).val) (slot (12 : Index).val),
     .mul (slot (12 : Index).val) (slot (10 : Index).val) (slot (15 : Index).val),
     .mul (slot x1.val) (slot (12 : Index).val) (slot (17 : Index).val),
     .mul (slot (13 : Index).val) (slot (10 : Index).val) (slot (11 : Index).val),
     .mul (slot y1.val) (slot (13 : Index).val) (slot (16 : Index).val),
     .mul (slot z1.val) (slot (15 : Index).val) (slot (11 : Index).val)] := rfl

theorem ne_of_lt10 {i : Index} (hi : i.val < 10) (k : Nat) (hk : 10 ≤ k) (hk' : k < 22) :
    (⟨k, hk'⟩ : Index) ≠ i := fun h => by rw [← h] at hi; exact absurd hi (by simp; omega)

section
variable {s : State} {base : Addr}

/-- **The complete addition** of the points in slots `x2, y2, z2` to those in `x1, y1, z1`
(which may be the same, to double), all below slot 10, given zero's bound in slot 19. -/
theorem addOps_ok (x1 y1 z1 x2 y2 z2 : Index) (hx1 : x1.val < 10) (hy1 : y1.val < 10) (hz1 : z1.val < 10)
    (hx2 : x2.val < 10) (hy2 : y2.val < 10) (hz2 : z2.val < 10) (hxy : x1 ≠ y1) (hzx : z1 ≠ x1)
    (hzy : z1 ≠ y1) (hs : Scr s base) (hb : BEnv s.mem base) (h19 : Bnd Mb s.mem base (slot (19 : Index).val)) :
    WP isa (ops (Impl.X448.AArch64.Base.addOps (slot x1.val) (slot y1.val) (slot z1.val) (slot x2.val)
        (slot y2.val) (slot z2.val))) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base (temps ++ [x1, y1, z1]) s.mem t.mem ∧
      Bnd Mb t.mem base (slot x1.val) ∧ Bnd Mb t.mem base (slot y1.val) ∧ Bnd Mb t.mem base (slot z1.val) ∧
      EV t.mem base = genEnv x1 y1 z1 x2 y2 z2 (EV s.mem base) := by
  -- Every temporary differs from every point slot.
  have n : ∀ {i : Index}, i.val < 10 → ∀ k : Index, 10 ≤ k.val → k ≠ i := fun hi k hk h => by
    rw [h] at hk; omega
  have nn : ∀ {i : Index}, i.val < 10 → ∀ k : Index, 10 ≤ k.val → i ∉ [k] := fun hi k hk h => by
    rw [List.mem_singleton] at h; exact n hi k hk h.symm
  have nn' : ∀ {i j : Index}, i ≠ j → i ∉ [j] := fun h hm => h (List.mem_singleton.mp hm)
  rw [addOps_eq]
  refine mulOp hs hb 10 z1 z2 (Or.inr (n hz2 10 (by decide))) fun t1 k1 b1 _ s1 e1 => ?_
  have hs1 := k1.scr hs
  refine mulOp hs1 b1 11 10 10 (Or.inl rfl) fun t2 k2 b2 m2 s2 e2 => ?_
  have hs2 := k2.scr hs1
  refine mulOp hs2 b2 12 x1 x2 (Or.inr (n hx2 12 (by decide))) fun t3 k3 b3 m3 s3 e3 => ?_
  have hs3 := k3.scr hs2
  refine mulOp hs3 b3 13 y1 y2 (Or.inr (n hy2 13 (by decide))) fun t4 k4 b4 m4 s4 e4 => ?_
  have hs4 := k4.scr hs3
  refine mulOp hs4 b4 14 12 13 (Or.inr (by decide)) fun t5 k5 b5 m5 s5 e5 => ?_
  have hs5 := k5.scr hs4
  have m2' : Bnd Mb t5.mem base (slot (11 : Index).val) :=
    s5.bnd (by decide) (s4.bnd (by decide) (s3.bnd (by decide) m2))
  refine smallOp (o := 15) (a := 11) (e := 14) hs5 b5 m2' fun t6 k6 b6 s6 e6 => ?_
  have hs6 := k6.scr hs5
  have z6 : Bnd Mb t6.mem base (slot (19 : Index).val) :=
    s6.bnd (by decide) (s5.bnd (by decide) (s4.bnd (by decide) (s3.bnd (by decide) (s2.bnd (by decide)
      (s1.bnd (by decide) h19)))))
  refine subOp (o := 16) (a := 19) (b := 14) hs6 b6 z6 (s6.bnd (by decide) m5) (by decide) (by decide)
    fun t7 k7 b7 s7 e7 => ?_
  have hs7 := k7.scr hs6
  refine smallOp (o := 11) (a := 11) (e := 16) hs7 b7 (s7.bnd (by decide) (s6.bnd (by decide) m2'))
    fun t8 k8 b8 s8 e8 => ?_
  have hs8 := k8.scr hs7
  refine mulOp hs8 b8 14 x1 y2 (Or.inr (n hy2 14 (by decide))) fun t9 k9 b9 m9 s9 e9 => ?_
  have hs9 := k9.scr hs8
  refine mulOp hs9 b9 16 y1 x2 (Or.inr (n hx2 16 (by decide))) fun t10 k10 b10 m10 s10 e10 => ?_
  have hs10 := k10.scr hs9
  refine addSubOp (o₁ := 17) (o₂ := 18) (a := 14) (b := 16) hs10 b10 (s10.bnd (by decide) m9) m10
    (by decide) (by decide) (by decide) (by decide) (by decide) fun t11 k11 b11 s11 e11 => ?_
  have hs11 := k11.scr hs10
  have m4' : Bnd Mb t11.mem base (slot (13 : Index).val) :=
    s11.bnd (by decide) (s10.bnd (by decide) (s9.bnd (by decide) (s8.bnd (by decide) (s7.bnd (by decide)
      (s6.bnd (by decide) (s5.bnd (by decide) m4))))))
  have m3' : Bnd Mb t11.mem base (slot (12 : Index).val) :=
    s11.bnd (by decide) (s10.bnd (by decide) (s9.bnd (by decide) (s8.bnd (by decide) (s7.bnd (by decide)
      (s6.bnd (by decide) (s5.bnd (by decide) (s4.bnd (by decide) m3)))))))
  refine addSubOp (o₁ := 14) (o₂ := 16) (a := 13) (b := 12) hs11 b11 m4' m3'
    (by decide) (by decide) (by decide) (by decide) (by decide) fun t12 k12 b12 s12 e12 => ?_
  have hs12 := k12.scr hs11
  refine mulOp hs12 b12 12 10 15 (Or.inr (by decide)) fun t13 k13 b13 _ s13 e13 => ?_
  have hs13 := k13.scr hs12
  refine mulOp hs13 b13 x1 12 17 (Or.inr (n hx1 17 (by decide)).symm) fun t14 k14 b14 m14 s14 e14 => ?_
  have hs14 := k14.scr hs13
  refine mulOp hs14 b14 13 10 11 (Or.inr (by decide)) fun t15 k15 b15 _ s15 e15 => ?_
  have hs15 := k15.scr hs14
  refine mulOp hs15 b15 y1 13 16 (Or.inr (n hy1 16 (by decide)).symm) fun t16 k16 b16 m16 s16 e16 => ?_
  have hs16 := k16.scr hs15
  refine mulOp hs16 b16 z1 15 11 (Or.inr (n hz1 11 (by decide)).symm) fun t17 k17 b17 m17 s17 e17 => ?_
  refine WP.block_nil ⟨k1.trans (k2.trans (k3.trans (k4.trans (k5.trans (k6.trans (k7.trans (k8.trans
    (k9.trans (k10.trans (k11.trans (k12.trans (k13.trans (k14.trans (k15.trans (k16.trans k17))))))))))))))),
    b17, ?_, ?_, ?_, m17, ?_⟩
  · refine VG.Proof.X448.AArch64.Base.Same.mono
      (s1.append (s2.append (s3.append (s4.append (s5.append (s6.append (s7.append (s8.append (s9.append
        (s10.append (s11.append (s12.append (s13.append (s14.append (s15.append (s16.append s17))))))))))))))))
      fun i hi => ?_
    simp only [temps, List.cons_append, List.nil_append] at hi ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp
  · exact s17.bnd (nn' hzx.symm) (s16.bnd (nn' hxy) (s15.bnd (nn hx1 13 (by decide)) m14))
  · exact s17.bnd (nn' hzy.symm) m16
  · exact e17.trans <| congrArg (mulS z1 15 11) <| e16.trans <| congrArg (mulS y1 13 16) <| e15.trans <|
      congrArg (mulS 13 10 11) <| e14.trans <| congrArg (mulS x1 12 17) <| e13.trans <|
      congrArg (mulS 12 10 15) <| e12.trans <| congrArg (addSubS 14 16 13 12) <| e11.trans <|
      congrArg (addSubS 17 18 14 16) <| e10.trans <| congrArg (mulS 16 y1 x2) <| e9.trans <|
      congrArg (mulS 14 x1 y2) <| e8.trans <| congrArg (smallS 11 11 16) <| e7.trans <|
      congrArg (subS 16 19 14) <| e6.trans <| congrArg (smallS 15 11 14) <| e5.trans <|
      congrArg (mulS 14 12 13) <| e4.trans <| congrArg (mulS 13 y1 y2) <| e3.trans <|
      congrArg (mulS 12 x1 x2) <| e2.trans <| congrArg (mulS 11 10 10) <| e1

end

/-- What `addOps` computes from `(X₁ : Y₁ : Z₁)` and `(X₂ : Y₂ : Z₂)`, with `z0` (zero) in slot 19. -/
def genPt (p q : Point) (z0 : Spec.X448.Fe) : Point :=
  let a := p.Z * q.Z
  let b := a * a
  let c := p.X * q.X
  let e := p.Y * q.Y
  let f := b + Spec.X448.a24 * (c * e)
  let g := b + Spec.X448.a24 * (z0 - c * e)
  ⟨a * f * (p.X * q.Y + p.Y * q.X), a * g * (e - c), f * g⟩

theorem genEnv_dbl (e : Env) : pt (genEnv 0 1 2 0 1 2 e) 0 1 2 = genPt (pt e 0 1 2) (pt e 0 1 2) (e 19) := rfl

theorem genEnv_add (e : Env) : pt (genEnv 0 1 2 3 4 5 e) 0 1 2 = genPt (pt e 0 1 2) (pt e 3 4 5) (e 19) := rfl

theorem genPt_eq (p q : Point) : genPt p q 0 = addPt p q := rfl

end VG.Proof.X448.AArch64.Base

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Base.Digit`. -/
section

/-!
# X448 of the base point on AArch64: the comb's digits and masks

Untrusted: everything here is checked by Lean. As Ed25519's comb
(`Proof/Ed25519/AArch64/CombDigit.lean`): step `j` reads the nibbles `2j + 1`
and `2j` of the decoded scalar from its bits (one per byte at `BITS`) by
Horner's rule; `magnitude` turns each into `|n - 8|`; `masks` sets the register
for `m` to all ones exactly if the magnitude is `m`, for `m = 1 … 8`, and
another to `1` exactly if it is `0`.
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Proof.X448.AArch64 (Scr Keeps off contains_sc read1_eq)
open VG.Proof.X448 (nib nib_bits nib_lt mag mag_lt)
open VG.Proof.Curve448.AArch64 (mask)

/-- The `8n` bits of the scalar `k` (for a comb of `n` tables), one per byte at `BITS`, as
`bits_ok` leaves them. -/
def Bits (n : Nat) (base : Addr) (k : Nat) (m : Mem) : Prop :=
  ∀ t < 8 * n, m (off base (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X448.bit k t)

theorem bit_eq (k t : Nat) : VG.Proof.X448.bit k t = (k / 2 ^ t) % 2 := by
  simp only [VG.Proof.X448.bit, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]

/-! ## The bit index -/

private theorem index_fact : ∀ j < 57, BitVec.ofNat 64 j <<< 3 = BitVec.ofNat 64 (8 * j) := by
  decide +kernel

theorem index_ok (s : State) {base : Addr} (hs : Scr s base) {j : Nat} (hj : j < 57)
    (hb : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block ([.lsl .x .x8 .x19 3, .add .x .x8 .x3 .x8] : List Instr)) s fun t =>
      t.gpr .x8 = off base (8 * j) ∧ Keeps [.x8] s t ∧ t.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (3 : Nat) < 64 from by decide, ite_true, RegUpd.gpr_write, BitVec.setWidth_eq,
    hb, index_fact j hj, hs.x3, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-! ## The nibble -/

private theorem bit_ext : ∀ b < 2, ((BitVec.ofNat 8 b).setWidth 32).setWidth 64 = BitVec.ofNat 64 b := by
  decide

theorem nibble_ok {s : State} {base : Addr} (hs : Scr s base) {n k i p o : Nat} (hn : n ≤ 57)
    (hi : i < 2 * n) (hp : s.gpr .x8 = off base p) (hpo : p + o = BITS + 4 * i) (ho : o + 3 < 4096)
    (hb : Bits n base k s.mem) :
    WP isa (.block (nibble o)) s fun t =>
      t.gpr .x2 = BitVec.ofNat 64 (nib k i) ∧ Keeps [.x2, .x9] s t ∧ t.mem = s.mem := by
  have hr : ∀ j < 4, InRegions (s.rd ++ s.wr) (off base (BITS + (4 * i + j))) 1 := fun j hj =>
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [BITS]; omega)⟩
  have he : ∀ j, off base p + BitVec.ofNat 64 (o + j) = off base (BITS + (4 * i + j)) :=
    fun j => by
      simp only [off]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact congrArg (base + ·) (congrArg (BitVec.ofNat 64) (by omega))
  have hv : ∀ j < 4, ((s.mem (off base (BITS + (4 * i + j)))).setWidth 32).setWidth 64 =
      BitVec.ofNat 64 ((k / 2 ^ (4 * i + j)) % 2) := fun j hj => by
    rw [hb _ (by omega), VG.Proof.X448.AArch64.Base.bit_eq]; exact bit_ext _ (Nat.mod_lt _ (by decide))
  have e0 := he 0
  have e1 := he 1
  have e2 := he 2
  have e3 := he 3
  simp only [Nat.add_zero] at e0
  have v0 := hv 0 (by decide)
  have v1 := hv 1 (by decide)
  have v2 := hv 2 (by decide)
  have v3 := hv 3 (by decide)
  have r0 := hr 0 (by decide)
  have r1 := hr 1 (by decide)
  have r2 := hr 2 (by decide)
  have r3 := hr 3 (by decide)
  simp only [Nat.add_zero] at v0 r0
  apply WP.of_runBlock
  simp only [nibble, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    State.load, addr, Size.bits, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, Nat.mod_one,
    show o + 3 < 4096 * 1 by omega, show o + 2 < 4096 * 1 by omega, show o + 1 < 4096 * 1 by omega,
    show o < 4096 * 1 by omega,
    Nat.reduceMul, and_self, hp, e0, e1, e2, e3,
    r0, r1, r2, r3, read1_eq, v0, v1, v2, v3,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
  · rw [nib_bits]
    simp only [← BitVec.ofNat_add]
    congr 1
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-! ## Sign and magnitude -/

private theorem sign_fact : ∀ n < 16,
    ((BitVec.ofNat 64 n - BitVec.ofNat 64 8) ^^^
        (((0 : BitVec 16).setWidth 32).setWidth 64 - (BitVec.ofNat 64 n - BitVec.ofNat 64 8) >>> 63)) -
      (((0 : BitVec 16).setWidth 32).setWidth 64 - (BitVec.ofNat 64 n - BitVec.ofNat 64 8) >>> 63) =
      BitVec.ofNat 64 (mag n) ∧
    ((0 : BitVec 16).setWidth 32).setWidth 64 - (BitVec.ofNat 64 n - BitVec.ofNat 64 8) >>> 63 =
      VG.Proof.X448.AArch64.mask (decide (n < 8)) := by
  decide +kernel

theorem magnitude_ok (s : State) {n : Nat} (hn : n < 16) (hx : s.gpr .x2 = BitVec.ofNat 64 n) :
    WP isa (.block magnitude) s fun t =>
      t.gpr .x2 = BitVec.ofNat 64 (mag n) ∧ t.gpr .x1 = VG.Proof.X448.AArch64.mask (decide (n < 8)) ∧
      Keeps [.x1, .x2, .x9] s t ∧ t.mem = s.mem := by
  apply WP.of_runBlock
  simp only [magnitude, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (8 : Nat) < 4096 from by decide, show (63 : Nat) < 64 from by decide,
    show 16 * 0 < 32 from by decide, Nat.mul_zero, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, BitVec.setWidth_eq, hx, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨(sign_fact n hn).1, (sign_fact n hn).2, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

/-! ## The masks -/

/-- The bit of `|d| = 0`. -/
def zeroBit (a : Nat) : BitVec 64 := if a = 0 then 1 else 0

private theorem less_fact : ∀ a < 9, ∀ k < 8,
    (BitVec.ofNat 64 a - BitVec.ofNat 64 (k + 1)) >>> 63 -
      (BitVec.ofNat 64 a - BitVec.ofNat 64 (k + 2)) >>> 63 = VG.Proof.X448.AArch64.mask (decide (a = k + 1)) := by
  decide +kernel

private theorem last_fact : ∀ a < 9,
    (BitVec.ofNat 64 a - BitVec.ofNat 64 8) >>> 63 - BitVec.ofNat 64 1 = VG.Proof.X448.AArch64.mask (decide (a = 8)) ∧
    (BitVec.ofNat 64 a - BitVec.ofNat 64 1) >>> 63 = zeroBit a := by
  decide +kernel

theorem masksOdd_ok (s : State) {a : Nat} (ha : a < 9) (hx : s.gpr .x2 = BitVec.ofNat 64 a) :
    WP isa (.block (masks oddRegs .x5)) s fun t =>
      (∀ m, 1 ≤ m → m ≤ 8 → t.gpr (oddReg m) = VG.Proof.X448.AArch64.mask (decide (a = m))) ∧ t.gpr .x5 = zeroBit a ∧
      Keeps [.x5, .x10, .x11, .x13, .x14, .x15, .x16, .x17, .x4] s t ∧ t.mem = s.mem := by
  have l := less_fact a ha
  apply WP.of_runBlock
  simp only [masks, oddRegs, oddReg, List.range, List.range.loop,
    List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_nil, List.getD_cons_zero, List.getD_cons_succ,
    Nat.reduceAdd, Nat.reduceLT, ↓reduceIte,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (63 : Nat) < 64 from by decide, show ∀ k < 9, k < 4096 from fun k hk => by omega,
    RegUpd.gpr_write, BitVec.setWidth_eq, hx, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun m hm1 hm8 => ?_, (last_fact a ha).2, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
  · have : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.reduceSub, ite_true, ite_false,
        reduceCtorEq] <;>
      first
      | exact (last_fact a ha).1
      | exact l _ (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

theorem masksEven_ok (s : State) {a : Nat} (ha : a < 9) (hx : s.gpr .x2 = BitVec.ofNat 64 a) :
    WP isa (.block (masks evenRegs .x0)) s fun t =>
      (∀ m, 1 ≤ m → m ≤ 8 → t.gpr (evenReg m) = VG.Proof.X448.AArch64.mask (decide (a = m))) ∧ t.gpr .x0 = zeroBit a ∧
      Keeps [.x0, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] s t ∧ t.mem = s.mem := by
  have l := less_fact a ha
  apply WP.of_runBlock
  simp only [masks, evenRegs, evenReg, List.range, List.range.loop,
    List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_nil, List.getD_cons_zero, List.getD_cons_succ,
    Nat.reduceAdd, Nat.reduceLT, ↓reduceIte,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (63 : Nat) < 64 from by decide, show ∀ k < 9, k < 4096 from fun k hk => by omega,
    RegUpd.gpr_write, BitVec.setWidth_eq, hx, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun m hm1 hm8 => ?_, (last_fact a ha).2, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
  · have : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.reduceSub, ite_true, ite_false,
        reduceCtorEq] <;>
      first
      | exact (last_fact a ha).1
      | exact l _ (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

/-! ## Both digits -/

/-- The registers `digits` writes. -/
def digitRegs : List Reg :=
  [.x8, .x2, .x9, .x1, .x5, .x10, .x11, .x13, .x14, .x15, .x16, .x17, .x4,
    .x0, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28]

/-- What `digits` leaves for step `j`'s two digits of the scalar `k`. -/
structure DigitsOut (s : State) (k j : Nat) (t : State) : Prop where
  oddMask : ∀ m, 1 ≤ m → m ≤ 8 → t.gpr (oddReg m) = VG.Proof.X448.AArch64.mask (decide (mag (nib k (2 * j + 1)) = m))
  oddZero : t.gpr .x5 = zeroBit (mag (nib k (2 * j + 1)))
  evenMask : ∀ m, 1 ≤ m → m ≤ 8 → t.gpr (evenReg m) = VG.Proof.X448.AArch64.mask (decide (mag (nib k (2 * j)) = m))
  evenZero : t.gpr .x0 = zeroBit (mag (nib k (2 * j)))
  keeps : Keeps digitRegs s t

theorem digits_ok {s : State} {base : Addr} (hs : Scr s base) {n k j : Nat} (hn : n ≤ 57) (hj : j < n)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j) (hb : Bits n base k s.mem) :
    WP isa (.block digits) s fun t => DigitsOut s k j t ∧ t.mem = s.mem := by
  have no : nib k (2 * j + 1) < 16 := nib_lt _ _
  have ne : nib k (2 * j) < 16 := nib_lt _ _
  simp only [digits, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (index_ok s hs (by omega) hc) fun a ⟨a8, ka, ma⟩ => ?_
  have hsa := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (nibble_ok hsa hn (k := k) (i := 2 * j + 1) (by omega) a8 (by simp only [BITS]; omega)
    (by decide) (by rw [ma]; exact hb)) fun b ⟨b2, kb, mb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (magnitude_ok b no b2) fun c ⟨c2, _, kc, mc⟩ => ?_
  have hsc := (hsa.of_keeps kb (by decide)).of_keeps kc (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (masksOdd_ok _ (mag_lt no) c2) fun e ⟨em, ez, ke, me⟩ => ?_
  have e8 : e.gpr .x8 = off base (8 * j) := by
    rw [ke.1 _ (by decide), kc.1 _ (by decide), kb.1 _ (by decide), a8]
  have hse : Scr e base := hsc.of_keeps ke (by decide)
  have hbe : Bits n base k e.mem := fun q hq => by
    rw [me, mc, mb, ma]; exact hb q hq
  rw [WP.block_append_iff]
  refine WP.mono (nibble_ok hse hn (k := k) (i := 2 * j) (by omega) e8 (by simp only [BITS]; omega)
    (by decide) hbe) fun f ⟨f2, kf, mf⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (magnitude_ok f ne f2) fun g ⟨g2, _, kg, mg⟩ => ?_
  refine WP.mono (masksEven_ok _ (mag_lt ne) g2) fun t ⟨tm, tz, kt, mt⟩ => ?_
  refine ⟨⟨fun m h1 h8 => ?_, ?_, tm, tz, ?_⟩, by rw [mt, mg, mf, me, mc, mb, ma]⟩
  · have hk : ∀ m < 9, oddReg m ∉ [Reg.x0, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] ∧
        oddReg m ∉ [Reg.x1, .x2, .x9] ∧ oddReg m ∉ [Reg.x2, .x9] := by
      decide
    obtain ⟨ht, hg, hf⟩ := hk m (by omega)
    rw [kt.1 _ ht, kg.1 _ hg, kf.1 _ hf]
    exact em m h1 h8
  · rw [kt.1 _ (by decide), kg.1 _ (by decide), kf.1 _ (by decide)]
    exact ez
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · simp only [digitRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [kt.1 _ (by simp [hr]), kg.1 _ (by simp [hr]), kf.1 _ (by simp [hr]),
        ke.1 _ (by simp [hr]), kc.1 _ (by simp [hr]), kb.1 _ (by simp [hr]), ka.1 _ (by simp [hr])]
    · rw [kt.2.1, kg.2.1, kf.2.1, ke.2.1, kc.2.1, kb.2.1, ka.2.1]
    · rw [kt.2.2, kg.2.2, kf.2.2, ke.2.2, kc.2.2, kb.2.2, ka.2.2]

end VG.Proof.X448.AArch64.Base

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Base.Select`. -/
section

/-!
# X448 of the base point on AArch64: the constant-time selection

Untrusted: everything here is checked by Lean. As Ed25519's comb
(`Proof/Ed25519/AArch64/CombSelect.lean`): with `oddReg m` (`evenReg m`) all
ones exactly for `m` the odd (even) digit's magnitude, and `x5` (`x0`) the bit
of a zero magnitude, `selectWord` builds every candidate's limb from
immediates once, ANDs it with both digits' masks and ORs it into `x1` and `x2`,
so only each digit's candidate survives, and stores them. Nothing here
unfolds a table: each lemma holds for any immediate.
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside2 ofs store_ok word_write writeW_outside)
open VG.Proof.Curve448.AArch64 (mask)

private theorem odd_regs : ∀ m < 9, oddReg m ∉ [Reg.x6, .x7, .x1, .x2] := by decide
private theorem even_regs : ∀ m < 9, evenReg m ∉ [Reg.x6, .x7, .x1, .x2] := by decide

private theorem ne_of_not_mem {r : Reg} {rs : List Reg} (h : r ∉ rs) {r' : Reg} (hr : r' ∈ rs) :
    r ≠ r' := fun e => h (e ▸ hr)

/-- One candidate's limb: built in `x6`, masked into `x1` (odd) and `x2` (even). -/
def candCode (v : Spec.X448.Fe) (m w : Nat) : List Instr :=
  const64 .x6 (limb v w) ++
    [.logic .and .x .x7 .x6 (oddReg m), .logic .orr .x .x1 .x1 .x7,
      .logic .and .x .x7 .x6 (evenReg m), .logic .orr .x .x2 .x2 .x7]

theorem cand_ok (s : State) (v : Spec.X448.Fe) {m : Nat} (hm : m < 9) (w : Nat) :
    WP isa (.block (candCode v m w)) s fun t =>
      t.gpr .x1 = s.gpr .x1 ||| (limb v w &&& s.gpr (oddReg m)) ∧
      t.gpr .x2 = s.gpr .x2 ||| (limb v w &&& s.gpr (evenReg m)) ∧
      Keeps [.x6, .x7, .x1, .x2] s t ∧ t.mem = s.mem := by
  have ho := odd_regs m hm
  have he := even_regs m hm
  have ho6 := ne_of_not_mem ho (r' := .x6) (by decide)
  have he6 := ne_of_not_mem he (r' := .x6) (by decide)
  have he7 := ne_of_not_mem he (r' := .x7) (by decide)
  have he1 := ne_of_not_mem he (r' := .x1) (by decide)
  rw [candCode, WP.block_append_iff]
  refine WP.mono (VG.AArch64.Tbl.const64_ok s .x6 (limb v w)) fun a ⟨a6, ka, ea⟩ => ?_
  have am : a.gpr (oddReg m) = s.gpr (oddReg m) := ka _ ho6
  have ae : a.gpr (evenReg m) = s.gpr (evenReg m) := ka _ he6
  have a1 : a.gpr .x1 = s.gpr .x1 := ka _ (by decide)
  have a2 : a.gpr .x2 = s.gpr .x2 := ka _ (by decide)
  have amem : a.mem = s.mem := by rw [ea]
  have ard : a.rd = s.rd := by rw [ea]
  have awr : a.wr = s.wr := by rw [ea]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, RegUpd.gpr_write,
    BitVec.setWidth_eq, he7, he1, ite_true, ite_false, reduceCtorEq, a6, am, ae, a1, a2,
    Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, ard, awr⟩, amem⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  exact ka _ hr.1

/-- Limb `w` of `vs[a]` after the candidates `m ≤ n`, zero if `a > n`. -/
def selWord (vs : List Spec.X448.Fe) (a n w : Nat) : BitVec 64 :=
  if a ≤ n then limb (vs.getD a 0) w else 0

private theorem or_and_zero (x y : BitVec 64) : x ||| (y &&& 0) = x := by ext i; simp

theorem sel_step (vs : List Spec.X448.Fe) (a n w : Nat) :
    selWord vs a n w ||| (limb (vs.getD (n + 1) 0) w &&& VG.Proof.X448.AArch64.mask (decide (a = n + 1))) =
      selWord vs a (n + 1) w := by
  unfold selWord
  by_cases h : a ≤ n
  · simp only [h, ↓reduceIte, show a ≤ n + 1 by omega, show ¬ a = n + 1 by omega, decide_false,
      VG.Proof.X448.AArch64.mask, Bool.false_eq_true]
    exact or_and_zero _ _
  · by_cases he : a = n + 1
    · subst he
      simp only [h, ↓reduceIte, Nat.le_refl, decide_true, VG.Proof.X448.AArch64.mask, BitVec.and_allOnes]
      exact BitVec.zero_or
    · simp only [h, he, ↓reduceIte, show ¬ a ≤ n + 1 by omega, decide_false, VG.Proof.X448.AArch64.mask,
        Bool.false_eq_true]
      exact or_and_zero _ _

/-- The masks of both digits, for the magnitudes `ao` and `ae`. -/
def Masks (ao ae : Nat) (s : State) : Prop :=
  (∀ m, 1 ≤ m → m ≤ 8 → s.gpr (oddReg m) = VG.Proof.X448.AArch64.mask (decide (ao = m))) ∧
  (∀ m, 1 ≤ m → m ≤ 8 → s.gpr (evenReg m) = VG.Proof.X448.AArch64.mask (decide (ae = m))) ∧
  s.gpr .x5 = zeroBit ao ∧ s.gpr .x0 = zeroBit ae

private theorem odd_regs9 : ∀ m < 9, oddReg m ∉ [Reg.x9, .x6, .x7, .x1, .x2] := by decide
private theorem even_regs9 : ∀ m < 9, evenReg m ∉ [Reg.x9, .x6, .x7, .x1, .x2] := by decide

theorem Masks.of_keeps {ao ae : Nat} {rs : List Reg} {s t : State} (h : Masks ao ae s)
    (k : Keeps rs s t) (hrs : ∀ r ∈ rs, r ∈ [Reg.x9, .x6, .x7, .x1, .x2] := by simp) :
    Masks ao ae t := by
  have nm : ∀ r, r ∉ [Reg.x9, .x6, .x7, .x1, .x2] → r ∉ rs := fun r hr hm => hr (hrs r hm)
  refine ⟨fun j h1 h8 => ?_, fun j h1 h8 => ?_, ?_, ?_⟩
  · rw [k.1 _ (nm _ (odd_regs9 j (by omega)))]; exact h.1 j h1 h8
  · rw [k.1 _ (nm _ (even_regs9 j (by omega)))]; exact h.2.1 j h1 h8
  · rw [k.1 _ (nm _ (by decide))]; exact h.2.2.1
  · rw [k.1 _ (nm _ (by decide))]; exact h.2.2.2

theorem cands_ok (s : State) {ao ae : Nat} (hm : Masks ao ae s)
    (vs : List Spec.X448.Fe) (w n : Nat) (hn : n ≤ 8)
    (h0 : s.gpr .x1 = selWord vs ao 0 w ∧ s.gpr .x2 = selWord vs ae 0 w) :
    WP isa (.block ((List.range n).flatMap fun m => candCode (vs.getD (m + 1) 0) (m + 1) w)) s
      fun t => t.gpr .x1 = selWord vs ao n w ∧ t.gpr .x2 = selWord vs ae n w ∧
        Keeps [.x6, .x7, .x1, .x2] s t ∧ t.mem = s.mem := by
  induction n with
  | zero => exact WP.block_nil ⟨h0.1, h0.2, ⟨fun _ _ => rfl, rfl, rfl⟩, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨t1, t2, kt, mt⟩ => ?_
    have tm := hm.of_keeps kt
    refine WP.mono (cand_ok t _ (by omega : n + 1 < 9) w) fun u ⟨u1, u2, ku, mu⟩ =>
      ⟨?_, ?_, kt.trans ku, mu.trans mt⟩
    · rw [u1, t1, tm.1 (n + 1) (by omega) (by omega), sel_step]
    · rw [u2, t2, tm.2.1 (n + 1) (by omega) (by omega), sel_step]

private theorem movz0 : (((0 : BitVec 16).setWidth 32).setWidth 64) = 0 := by decide

private theorem limb_one_zero : ∀ w < 8, ∀ one : Bool,
    (if (one && w == 0) = true then (1 : BitVec 64) else 0) =
      limb (if one then 1 else 0) w := by
  decide +kernel

/-- The start of word `w`'s selections: `1` for `|d| = 0` in limb 0 of `y`'s identity (`one`). -/
def startCode (one : Bool) (w : Nat) : List Instr :=
  if one && w == 0 then [.addImm .x .x1 .x5 0, .addImm .x .x2 .x0 0]
  else [.movz .w .x1 0 0, .movz .w .x2 0 0]

theorem start_ok (s : State) {ao ae : Nat} (hm : Masks ao ae s) (one : Bool)
    (vs : List Spec.X448.Fe) (h0 : vs.getD 0 0 = if one then 1 else 0) (w : Nat) (hw : w < 8) :
    WP isa (.block (startCode one w)) s fun t =>
      t.gpr .x1 = selWord vs ao 0 w ∧ t.gpr .x2 = selWord vs ae 0 w ∧
        Keeps [.x6, .x7, .x1, .x2] s t ∧ t.mem = s.mem := by
  have hz : ∀ a, (if (one && w == 0) = true then zeroBit a else 0) = selWord vs a 0 w := fun a => by
    unfold selWord zeroBit
    by_cases ha : a = 0
    · subst ha
      simp only [Nat.le_refl, ↓reduceIte, h0]
      exact limb_one_zero w hw one
    · simp [ha, show ¬ a ≤ 0 by omega]
  rw [← hz ao, ← hz ae]
  unfold startCode
  by_cases h : (one && w == 0) = true
  · simp only [h, ↓reduceIte]
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
      show (0 : Nat) < 4096 from by decide, RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero,
      ite_true, ite_false, reduceCtorEq, hm.2.2.1, hm.2.2.2, Option.some.injEq, exists_eq_left']
    refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.2.2.1, hr.2.2.2, ite_false]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
      show 16 * 0 < Size.w.bits from by decide, ite_true, RegUpd.gpr_write, ite_false, reduceCtorEq,
      Nat.mul_zero, BitVec.shiftLeft_zero, movz0, Option.some.injEq, exists_eq_left']
    refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.2.2.1, hr.2.2.2, ite_false]

theorem selectWord_eq (one : Bool) (vs : List Spec.X448.Fe) (o e w : Nat) :
    selectWord one vs o e w = startCode one w ++
      ((List.range 8).flatMap fun m => candCode (vs.getD (m + 1) 0) (m + 1) w) ++
      [st .x1 (o + 8 * w), st .x2 (e + 8 * w)] := rfl

theorem word_ok {s : State} {base : Addr} (hs : Scr s base) {ao ae : Nat} (hm : Masks ao ae s)
    (one : Bool) (vs : List Spec.X448.Fe) (h0 : vs.getD 0 0 = if one then 1 else 0)
    {o e : Nat} (ho : o % 8 = 0) (he : e % 8 = 0) (hb : o + 64 ≤ 8192) (hbe : e + 64 ≤ 8192)
    (w : Nat) (hw : w < 8) :
    WP isa (.block (selectWord one vs o e w)) s fun t =>
      t.mem = (s.mem.writeW (off base (o + 8 * w)) (selWord vs ao 8 w)).writeW (off base (e + 8 * w))
        (selWord vs ae 8 w) ∧ Keeps [.x6, .x7, .x1, .x2] s t := by
  rw [selectWord_eq, List.append_assoc, WP.block_append_iff]
  refine WP.mono (start_ok s hm one vs h0 w hw) fun a ⟨a1, a2, ka, ma⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cands_ok a (hm.of_keeps ka) vs w 8 (le_refl _) ⟨a1, a2⟩)
    fun b ⟨b1, b2, kb, mb⟩ => ?_
  have hsb : Scr b base := (hs.of_keeps ka (by decide)).of_keeps kb (by decide)
  rw [show ([st .x1 (o + 8 * w), st .x2 (e + 8 * w)] : List Instr) =
    [st .x1 (o + 8 * w)] ++ [st .x2 (e + 8 * w)] from rfl, WP.block_append_iff]
  refine WP.mono (store_ok hsb (by omega) (by omega) .x1) fun c ⟨mc, kc⟩ => ?_
  have hsc : Scr c base := hsb.of_keeps kc (by decide)
  refine WP.mono (store_ok hsc (by omega) (by omega) .x2) fun t ⟨mt, kt⟩ => ⟨?_, ?_⟩
  · rw [mt, mc, kc.1 _ (by decide), b1, b2, mb, ma]
  · exact ((ka.trans kb).trans (kc.mono (by simp))).trans (kt.mono (by simp))

theorem fieldPrefix_ok {s : State} {base : Addr} (hs : Scr s base) {ao ae : Nat}
    (hm : Masks ao ae s) (one : Bool) (vs : List Spec.X448.Fe)
    (h0 : vs.getD 0 0 = if one then 1 else 0)
    {o e : Nat} (ho : o % 8 = 0) (he : e % 8 = 0) (hoe : o + 64 ≤ e ∨ e + 64 ≤ o)
    (hb : o + 64 ≤ 8192) (hbe : e + 64 ≤ 8192) (n : Nat) (hn : n ≤ 8) :
    WP isa (.block ((List.range n).flatMap fun w => selectWord one vs o e w)) s fun t =>
      (∀ w < n, word t.mem base (o + 8 * w) = selWord vs ao 8 w ∧
        word t.mem base (e + 8 * w) = selWord vs ae 8 w) ∧
      Outside2 base o 64 e 64 s.mem t.mem ∧ Keeps [.x6, .x7, .x1, .x2] s t := by
  induction n with
  | zero => exact WP.block_nil ⟨fun w hw => absurd hw (Nat.not_lt_zero _), fun _ _ _ => rfl,
      fun _ _ => rfl, rfl, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨tv, tf, kt⟩ => ?_
    have ht : Scr t base := hs.of_keeps kt (by decide)
    refine WP.mono (word_ok ht (hm.of_keeps kt) one vs h0 ho he hb hbe n (by omega))
      fun u ⟨um, ku⟩ => ⟨fun w hw => ?_, ?_, kt.trans ku⟩
    · rw [um, VG.Proof.X448.AArch64.word_write_aligned _ _ (by omega) (by omega) (by omega) (by omega),
        VG.Proof.X448.AArch64.word_write_aligned _ _ (by omega) (by omega) (by omega) (by omega),
        VG.Proof.X448.AArch64.word_write_aligned _ _ (by omega) (by omega) (by omega) (by omega),
        VG.Proof.X448.AArch64.word_write_aligned _ _ (by omega) (by omega) (by omega) (by omega)]
      by_cases hwn : w = n
      · subst hwn
        simp only [↓reduceIte, show o + 8 * w ≠ e + 8 * w by omega]
        exact ⟨trivial, trivial⟩
      · simp only [show o + 8 * w ≠ e + 8 * n by omega, show o + 8 * w ≠ o + 8 * n by omega,
          show e + 8 * w ≠ e + 8 * n by omega, show e + 8 * w ≠ o + 8 * n by omega, ↓reduceIte]
        exact tv w (by omega)
    · rw [um]
      refine fun x h1 h2 => ?_
      rw [show ((t.mem.writeW (off base (o + 8 * n)) (selWord vs ao 8 n)).writeW (off base (e + 8 * n))
          (selWord vs ae 8 n)) x = t.mem x from ?_]
      · exact tf x h1 h2
      · rw [VG.Proof.X448.AArch64.writeW_outside _ _ _ (by omega) x (by omega),
          VG.Proof.X448.AArch64.writeW_outside _ _ _ (by omega) x (by omega)]

/-! ## The selected field's value -/

private theorem entries_getD (j a : Nat) (ha : a < 9) (f : Spec.X448.Fe × Spec.X448.Fe → Spec.X448.Fe) :
    (((List.range 9).map (Impl.X448.baseTable j)).map f).getD a 0 = f (Impl.X448.baseTable j a) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ha, Option.map_some,
    Option.getD_some]

/-- The entries' slots, 6–9, are the 512 bytes at `OX`. -/
theorem entries_span : OY = OX + 128 ∧ EX = OX + 256 ∧ EY = OX + 384 ∧ OX = 832 := by decide

/-- **Table `j`'s entries** for both digits, `|d| = ao` and `ae`, to slots 6–9, limb by limb. -/
theorem select_ok {s : State} {base : Addr} (hs : Scr s base) {ao ae : Nat} (hao : ao < 9)
    (hae : ae < 9) (hm : Masks ao ae s) (j : Nat) :
    WP isa (.block (select j)) s fun t =>
      (∀ w < 8, word t.mem base (OX + 8 * w) = limb (Impl.X448.baseTable j ao).1 w ∧
        word t.mem base (EX + 8 * w) = limb (Impl.X448.baseTable j ae).1 w ∧
        word t.mem base (OY + 8 * w) = limb (Impl.X448.baseTable j ao).2 w ∧
        word t.mem base (EY + 8 * w) = limb (Impl.X448.baseTable j ae).2 w) ∧
      VG.Proof.X448.AArch64.Outside base OX 512 s.mem t.mem ∧ Keeps [.x6, .x7, .x1, .x2] s t := by
  rw [select, WP.block_append_iff]
  refine WP.mono (fieldPrefix_ok hs hm false _ (by rw [entries_getD j 0 (by decide)]; rfl)
    (o := OX) (e := EX) (by decide) (by decide) (by decide) (by decide) (by decide) 8 (le_refl _))
    fun b ⟨bv, bf, kb⟩ => ?_
  have hsb : Scr b base := hs.of_keeps kb (by decide)
  refine WP.mono (fieldPrefix_ok hsb (hm.of_keeps kb) true _ (by rw [entries_getD j 0 (by decide)]; rfl)
    (o := OY) (e := EY) (by decide) (by decide) (by decide) (by decide) (by decide) 8 (le_refl _))
    fun t ⟨tv, tf, kt⟩ => ⟨fun w hw => ?_, ?_, kb.trans kt⟩
  · obtain ⟨b1, b2⟩ := bv w hw
    obtain ⟨t1, t2⟩ := tv w hw
    have sel : ∀ (f : Spec.X448.Fe × Spec.X448.Fe → Spec.X448.Fe) (a : Nat), a < 9 →
        selWord (((List.range 9).map (Impl.X448.baseTable j)).map f) a 8 w =
          limb (f (Impl.X448.baseTable j a)) w := fun f a ha => by
      unfold selWord; rw [ite_eq_left (by omega), entries_getD j a ha]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [tf.word (by simp only [OX, OY, slot]; omega) (by simp only [OX, EY, slot]; omega)
        (by simp only [OX, slot]; omega), b1, sel _ _ hao]
    · rw [tf.word (by simp only [EX, OY, slot]; omega) (by simp only [EX, EY, slot]; omega)
        (by simp only [EX, slot]; omega), b2, sel _ _ hae]
    · rw [t1, sel _ _ hao]
    · rw [t2, sel _ _ hae]
  · intro x hx
    rw [tf x (by simp only [OX, OY, slot] at hx ⊢; omega) (by simp only [OX, EY, slot] at hx ⊢; omega),
      bf x (by simp only [OX, slot] at hx ⊢; omega) (by simp only [OX, EX, slot] at hx ⊢; omega)]

/-- What a selection leaves: table `j`'s entries for both digits in slots 6–9. -/
def Selected (base : Addr) (j ao ae : Nat) (s t : State) : Prop :=
  (∀ w < 8, word t.mem base (OX + 8 * w) = limb (Impl.X448.baseTable j ao).1 w ∧
    word t.mem base (EX + 8 * w) = limb (Impl.X448.baseTable j ae).1 w ∧
    word t.mem base (OY + 8 * w) = limb (Impl.X448.baseTable j ao).2 w ∧
    word t.mem base (EY + 8 * w) = limb (Impl.X448.baseTable j ae).2 w) ∧
  VG.Proof.X448.AArch64.Outside base OX 512 s.mem t.mem ∧ Keeps [.x9, .x6, .x7, .x1, .x2] s t

theorem dispatch_ok (s : State) {j k : Nat} (hj : j < 57) (hk : k < 57)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block [.subImm .x .x9 .x19 k]) s fun t =>
      (t.gpr .x9 == 0) = decide (j = k) ∧ Keeps [.x9] s t ∧ t.mem = s.mem := by
  have hz : (BitVec.ofNat 64 j - BitVec.ofNat 64 k == 0) = decide (j = k) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    bv_omega_using [hj, hk]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show k < 4096 by omega, ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, hc, hz,
    Option.some.injEq, exists_eq_left']
  exact ⟨True.intro, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl⟩, rfl⟩

theorem selectFrom_ok (ks : List Nat) (hks : ∀ k ∈ ks, k < 57) {s : State} {base : Addr}
    (hs : Scr s base) {ao ae : Nat} (hao : ao < 9) (hae : ae < 9) (hm : Masks ao ae s)
    {j : Nat} (hj : j ∈ ks) (hj57 : j < 57) (hc : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (selectFrom ks) s (Selected base j ao ae s) := by
  induction ks generalizing s with
  | nil => exact absurd hj List.not_mem_nil
  | cons k ks ih =>
    have hk : k < 57 := hks k (by simp)
    rw [selectFrom]
    refine WP.seq (WP.mono (dispatch_ok s hj57 hk hc) fun t ⟨tz, kt, mt⟩ => ?_)
    have ht : Scr t base := hs.of_keeps kt (by decide)
    have hm' : Masks ao ae t := hm.of_keeps kt
    refine WP.ite (decide (j = k)) (by simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, tz])
      (fun h => ?_) (fun h => ?_)
    · obtain rfl : j = k := of_decide_eq_true h
      refine WP.mono (VG.Proof.X448.AArch64.Base.select_ok ht hao hae hm' j) fun u ⟨uv, uf, ku⟩ =>
        ⟨uv, by rw [← mt]; exact uf, (kt.mono (by simp)).trans (ku.mono (by simp))⟩
    · have hne : j ≠ k := of_decide_eq_false h
      have hj' : j ∈ ks := by
        rcases List.mem_cons.mp hj with h | h
        · exact absurd h hne
        · exact h
      refine WP.mono (ih (fun k hk => hks k (List.mem_cons_of_mem _ hk)) ht hm' hj'
        (by rw [kt.1 _ (by decide)]; exact hc)) fun u ⟨uv, uf, ku⟩ =>
        ⟨uv, by rw [← mt]; exact uf, (kt.mono (by simp)).trans ku⟩

end VG.Proof.X448.AArch64.Base

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Base.Negate`. -/
section

/-!
# X448 of the base point on AArch64: negating an entry for a negative digit

Untrusted: everything here is checked by Lean. `negate ox o w` computes
`0 - x` into slot `w`, loads the top bit of the digit's nibble (`n < 8` exactly
if it is clear) as a mask, and swaps `x` with `0 - x` under it, as Ed25519's
comb negates its cached entries.
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs contains_sc read1_eq)
open VG.Proof.X448.AArch64.Weak (Index Env opSwap)
open VG.Proof.X448.AArch64.Fast
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448 (nib nib_bits)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

private theorem bit_mask : ∀ b < 2,
    ((BitVec.ofNat 8 b).setWidth 32).setWidth 64 - BitVec.ofNat 64 1 =
      VG.Proof.X448.AArch64.mask (decide (b = 0)) := by
  decide

theorem nib_neg (k i : Nat) : decide (nib k i < 8) = decide ((k / 2 ^ (4 * i + 3)) % 2 = 0) := by
  rw [nib_bits]
  have h0 := Nat.mod_lt (k / 2 ^ (4 * i)) (show 2 > 0 by decide)
  have h1 := Nat.mod_lt (k / 2 ^ (4 * i + 1)) (show 2 > 0 by decide)
  have h2 := Nat.mod_lt (k / 2 ^ (4 * i + 2)) (show 2 > 0 by decide)
  have h3 := Nat.mod_lt (k / 2 ^ (4 * i + 3)) (show 2 > 0 by decide)
  apply decide_eq_decide.mpr
  omega

private theorem index3_fact : ∀ j < 57, BitVec.ofNat 64 j <<< 3 = BitVec.ofNat 64 (8 * j) := by
  decide +kernel

theorem signLoad_ok {s : State} {base : Addr} (hs : Scr s base) {n k j i o : Nat} (hn : n ≤ 57)
    (hj : j < 57) (hi : i < 2 * n) (hoi : 8 * j + o = BITS + 4 * i) (ho : o + 3 < 4096)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j) (hb : Bits n base k s.mem) :
    WP isa (.block [.lsl .x .x6 .x19 3, .add .x .x6 .x3 .x6, .ldrb .x6 .x6 (o + 3),
      .subImm .x .x6 .x6 1]) s fun t =>
      t.gpr .x6 = VG.Proof.X448.AArch64.mask (decide (nib k i < 8)) ∧ Keeps [.x6] s t ∧
        t.mem = s.mem := by
  have hr : InRegions (s.rd ++ s.wr) (off base (BITS + (4 * i + 3))) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [BITS]; omega)⟩
  have he : base + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 (o + 3) = off base (BITS + (4 * i + 3)) := by
    simp only [off]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (base + ·) (congrArg (BitVec.ofNat 64) (by omega))
  have hv := bit_mask _ (Nat.mod_lt (k / 2 ^ (4 * i + 3)) (show 2 > 0 by decide))
  rw [← nib_neg, ← bit_eq, ← hb _ (by omega)] at hv
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.load, addr, Size.bits,
    show (3 : Nat) < 64 from by decide, show (1 : Nat) < 4096 from by decide,
    show o + 3 < 4096 * 1 by omega, Nat.mod_one, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq,
    hc, index3_fact j hj, hs.x3, he, hr, read1_eq, hv,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨True.intro, ⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem ofs_off0 (base : Addr) {d : Nat} (h : d < 2 ^ 64) : VG.Proof.X448.AArch64.ofs base (off base d) = d := by
  have := VG.Proof.X448.AArch64.ofs_off base (d := d) (i := 0) (by omega)
  simpa only [BitVec.add_zero, Nat.add_zero] using this

/-- The scalar's bits are outside the slots and the products' working space. -/
theorem Bits.of_fkeep {base : Addr} {n k : Nat} {s t : State} (hn : n ≤ 57) (hs : Scr s base)
    (h : Bits n base k s.mem) (hk : FKeep base s t) : Bits n base k t.mem := fun q hq => by
  have hn := hs.nowrap
  rw [hk.mem _ (by rw [ofs_off0 base (by simp only [BITS]; omega)]; simp only [BITS]; omega)
    (by rw [ofs_off0 base (by simp only [BITS]; omega)]; simp only [BITS, ACC]; omega)]
  exact h q hq

/-- `0 - x` into slot 10. -/
theorem subNeg_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) (ox : Index)
    (hox : ox ≠ 10) (hx : Bnd Mb s.mem base (slot ox.val)) (h19 : Bnd Mb s.mem base (slot (19 : Index).val)) :
    WP isa (VG.Impl.X448.AArch64.Fast.ops [.sub (slot (10 : Index).val) (slot (19 : Index).val) (slot ox.val)]) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base [10] s.mem t.mem ∧
      EV t.mem base = Function.update (EV s.mem base) 10 (EV s.mem base 19 - EV s.mem base ox) :=
  subOp hs hb h19 hx (by decide) (Ne.symm hox) fun _ k b sm e => WP.block_nil ⟨k, b, sm, e⟩

theorem negate_eq (ox : Index) (n : Nat) :
    negate (slot ox.val) n (slot (10 : Index).val) =
      VG.Impl.X448.AArch64.Fast.codeOf ([.sub (slot (10 : Index).val) (slot (19 : Index).val) (slot ox.val)] :
          List Impl.X448.AArch64.Fast.Op) ++
        (([.lsl .x .x6 .x19 3, .add .x .x6 .x3 .x6, .ldrb .x6 .x6 (n + 3), .subImm .x .x6 .x6 1] : List Instr) ++
          VG.Impl.Curve448.AArch64.cswap (slot ox.val) (slot (10 : Index).val)) := by
  simp only [negate, List.append_assoc]; rfl

/-- **The negation** of the entry's `x` in slot `ox` for the digit `nib k i - 8`, if negative. -/
theorem negate_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) {k j i o : Nat}
    (ox : Index) (hox : ox ≠ 10) {n : Nat} (hn : n ≤ 57) (hj : j < 57) (hi : i < 2 * n)
    (hoi : 8 * j + o = BITS + 4 * i) (ho : o + 3 < 4096) (hc : s.gpr .x19 = BitVec.ofNat 64 j)
    (hbits : Bits n base k s.mem)
    (hx : Bnd Mb s.mem base (slot ox.val)) (h19 : Bnd Mb s.mem base (slot (19 : Index).val)) :
    WP isa (.block (negate (slot ox.val) o (slot (10 : Index).val))) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base ([10] ++ [ox, 10]) s.mem t.mem ∧
      EV t.mem base = opSwap ox 10 (decide (nib k i < 8))
        (Function.update (EV s.mem base) 10 (EV s.mem base 19 - EV s.mem base ox)) := by
  rw [negate_eq ox o, WP.block_append_iff]
  refine WP.mono (block_codeOf (subNeg_ok hs hb ox hox hx h19)) fun t1 ⟨k1, b1, s1, e1⟩ => ?_
  have hs1 := k1.scr hs
  rw [WP.block_append_iff]
  refine WP.mono (signLoad_ok hs1 hn hj hi hoi ho (by rw [k1.regs.1 _ (by decide)]; exact hc)
    (Bits.of_fkeep hn hs hbits k1)) fun t2 ⟨m2, k2, mem2⟩ => ?_
  have f2 : FKeep base t1 t2 := ⟨k2.mono (by decide), fun x _ _ => by rw [mem2]⟩
  have hs2 := f2.scr hs1
  have b2 : BEnv t2.mem base := fun i => by
    have := b1 i; intro w hw; rw [show t2.mem = t1.mem from mem2]; exact this w hw
  refine WP.mono (VG.Proof.X448.AArch64.Fast.cswapE hs2 b2 ox 10 hox m2) fun t3 ⟨k3, b3, _, _, _, s3, e3⟩ =>
    ⟨k1.trans (f2.trans k3), b3, fun i hi w hw => ?_, ?_⟩
  · have hi' : i ∉ [(10 : Index)] := fun h => hi (List.mem_append_left _ h)
    have hi'' : i ∉ [ox, 10] := fun h => hi (List.mem_append_right _ h)
    rw [s3 i hi'' w hw, show limbs t2.mem base (slot i.val) w = limbs t1.mem base (slot i.val) w by
      rw [mem2], s1 i hi' w hw]
  · rw [e3, show EV t2.mem base = EV t1.mem base by rw [mem2], e1]

end VG.Proof.X448.AArch64.Base

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Base.Step`. -/
section

/-!
# X448 of the base point on AArch64: one step of the comb

Untrusted: everything here is checked by Lean. Step `j` reads both digits,
selects table `j`'s entries, negates each for a negative digit and adds it to
its accumulator: the invariant `StepInv` (as Ed25519's `CombInv`) holds for
`j + 1` after the step if it held for `j`.
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env opSwap)
open VG.Proof.X448.AArch64.Fast
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448 (nib mag)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- The entries' slots. -/
def entrySlots : List Index := [6, 7, 8, 9]

theorem slot_entry (i : Index) : i ∈ entrySlots ↔ OX ≤ slot i.val ∧ slot i.val < OX + 512 := by
  have := i.isLt
  simp only [entrySlots, List.mem_cons, List.not_mem_nil, or_false, OX, slot, Fin.ext_iff]
  omega

/-- A selection, in the slot environment. -/
theorem selected_env {s t : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) {j ao ae : Nat}
    (h : Selected base j ao ae s t) :
    BEnv t.mem base ∧ Same base entrySlots s.mem t.mem ∧
    EV t.mem base 6 = (Impl.X448.baseTable j ao).1 ∧ EV t.mem base 7 = (Impl.X448.baseTable j ao).2 ∧
    EV t.mem base 8 = (Impl.X448.baseTable j ae).1 ∧ EV t.mem base 9 = (Impl.X448.baseTable j ae).2 ∧
    (∀ i ∈ entrySlots, Bnd Mb t.mem base (slot i.val)) := by
  obtain ⟨hv, hf, _⟩ := h
  have hn := hs.nowrap
  -- Words outside the entries' slots are kept.
  have keep : ∀ i : Index, i ∉ entrySlots → ∀ w < 8, limbs t.mem base (slot i.val) w = limbs s.mem base (slot i.val) w :=
    fun i hi w hw => by
      have := i.isLt
      have hi' := (slot_entry i).not.mp hi
      simp only [OX, slot] at hi'
      exact congrArg BitVec.toNat (hf.word (by simp only [OX, slot]; omega) (by simp only [slot]; omega))
  -- The entries' limbs.
  have lv : ∀ (v : Spec.X448.Fe) (o : Nat), (∀ w < 8, word t.mem base (o + 8 * w) = limb v w) →
      (∀ w < 8, limbs t.mem base o w = (limb v w).toNat) := fun v o h w hw => by
    show (word t.mem base (o + 8 * w)).toNat = _; rw [h w hw]
  have l6 := lv _ OX fun w hw => (hv w hw).1
  have l8 := lv _ EX fun w hw => (hv w hw).2.1
  have l7 := lv _ OY fun w hw => (hv w hw).2.2.1
  have l9 := lv _ EY fun w hw => (hv w hw).2.2.2
  have fe : ∀ (v : Spec.X448.Fe) (o : Nat), (∀ w < 8, limbs t.mem base o w = (limb v w).toNat) →
      VG.Proof.X448.AArch64.Weak.F t.mem base o = v := fun v o h => by
    simp only [VG.Proof.X448.AArch64.Weak.F]
    rw [VG.Proof.X448.Wide.valN_congr h, limb_val, VG.Proof.X448.toFe_self]
  have bd : ∀ (v : Spec.X448.Fe) (o : Nat), (∀ w < 8, limbs t.mem base o w = (limb v w).toNat) →
      Bnd Mb t.mem base o := fun v o h w hw => by
    rw [h w hw]; exact Nat.lt_of_lt_of_le (limb_lt v w) (by decide)
  refine ⟨fun i => ?_, keep, fe _ _ l6, fe _ _ l7, fe _ _ l8, fe _ _ l9, ?_⟩
  · by_cases hi : i ∈ entrySlots
    · simp only [entrySlots, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact fun w hw => Nat.lt_of_lt_of_le (bd _ _ l6 w hw) (by decide)
      · exact fun w hw => Nat.lt_of_lt_of_le (bd _ _ l7 w hw) (by decide)
      · exact fun w hw => Nat.lt_of_lt_of_le (bd _ _ l8 w hw) (by decide)
      · exact fun w hw => Nat.lt_of_lt_of_le (bd _ _ l9 w hw) (by decide)
    · intro w hw; rw [keep i hi w hw]; exact hb i w hw
  · intro i hi
    simp only [entrySlots, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact bd _ _ l6
    · exact bd _ _ l7
    · exact bd _ _ l8
    · exact bd _ _ l9

/-! ## The invariant -/

open VG.Proof.Ed448 (Rep baseAff dZ)
open VG.Proof.X448 (oddSumZ evenSumZ combG)

/-- The state of a comb of `n` tables before step `j` (of the scalar `k`), from the function's
state after its setup `s₀`. -/
structure StepInv (n : Nat) (s₀ : State) (base : Addr) (k j : Nat) (s : State) : Prop where
  bound : j ≤ n
  scr : Scr s base
  env : BEnv s.mem base
  zero : ∀ w < 8, limbs s.mem base (slot (19 : Index).val) w = 0
  counter : s.gpr .x19 = BitVec.ofNat 64 j
  bits : Bits n base k s.mem
  odd : Rep (pt (EV s.mem base) 0 1 2) (((combG n : ℤ) + oddSumZ k j) • baseAff)
  even : Rep (pt (EV s.mem base) 3 4 5) (((combG n : ℤ) + evenSumZ k j) • baseAff)
  lr : s.gpr .x30 = s₀.gpr .x30
  out : s.gpr .x20 = s₀.gpr .x20
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside2 base 64 2816 ACC 1152 s₀.mem s.mem

/-! ## One step -/

open VG.Proof.X448 (addPt addPt_rep basePt negAff baseEntry_ok nib_lt mag_lt sdig)

theorem step_eq (n : Nat) : VG.Impl.X448.AArch64.Base.stepN n =
    .seq (.block digits) (.seq (selectFrom (List.range n)) (.block (
      negate (slot (6 : Index).val) (BITS + 4) (slot (10 : Index).val) ++
      (addAffine (slot (0 : Index).val) (slot (1 : Index).val) (slot (2 : Index).val)
        (slot (6 : Index).val) (slot (7 : Index).val) ++
      (negate (slot (8 : Index).val) BITS (slot (10 : Index).val) ++
      (addAffine (slot (3 : Index).val) (slot (4 : Index).val) (slot (5 : Index).val)
        (slot (8 : Index).val) (slot (9 : Index).val) ++
      ([.addImm .x .x19 .x19 1, .subImm .x .x9 .x19 n] : List Instr))))))) := by
  simp only [VG.Impl.X448.AArch64.Base.stepN, List.append_assoc]; rfl

/-- The selected scalar slots outside `entrySlots` are kept by a selection. -/
theorem Selected.outside2 {base : Addr} {j ao ae : Nat} {s t : State} (h : Selected base j ao ae s t) :
    Outside2 base 64 2816 ACC 1152 s.mem t.mem := fun x h1 _ =>
  h.2.1 x (by simp only [OX, slot] at h1 ⊢; omega)

/-- The entry for the digit `n - 8`, negated as `negate` does. -/
theorem entry_eq (e : Spec.X448.Fe × Spec.X448.Fe) (z : Spec.X448.Fe) (hz : z = 0) (n : Nat) :
    (⟨if decide (n < 8) then z - e.1 else e.1, e.2, 1⟩ : Spec.Ed448.Point) =
      basePt (if n < 8 then negAff e else e) := by
  subst hz
  by_cases hn : n < 8
  · simp only [hn, decide_true, ↓reduceIte]; rfl
  · simp only [hn, decide_false, ↓reduceIte, Bool.false_eq_true]; rfl

theorem acc_step (G : ℤ) (S : ℤ) (n j : Nat) :
    (G + S) • baseAff + (((n : ℤ) - 8) * 256 ^ j) • baseAff = (G + (S + ((n : ℤ) - 8) * 256 ^ j)) • baseAff := by
  rw [← add_smul, add_assoc]

theorem step_ok {n : Nat} (hn : n ≤ 57) {s₀ s : State} {base : Addr} {k j : Nat}
    (h : StepInv n s₀ base k j s) (hj : j < n) :
    WP isa (VG.Impl.X448.AArch64.Base.stepN n) s fun t =>
      (t.gpr .x9 != 0) = decide (j + 1 ≠ n) ∧ StepInv n s₀ base k (j + 1) t := by
  obtain ⟨_, hs, hb, hz, hc, hbits, hodd, heven, hlr, hout, hrd, hwr, hmem⟩ := h
  have no := nib_lt k (2 * j + 1)
  have ne := nib_lt k (2 * j)
  rw [step_eq n]
  -- The digits.
  refine WP.seq (WP.mono (digits_ok hs hn hj hc hbits) fun t1 ⟨d1, m1⟩ => ?_)
  have hs1 : Scr t1 base := hs.of_keeps d1.keeps (by decide)
  have hb1 : BEnv t1.mem base := by rw [m1]; exact hb
  have hm1 : Masks (mag (nib k (2 * j + 1))) (mag (nib k (2 * j))) t1 :=
    ⟨d1.oddMask, d1.evenMask, d1.oddZero, d1.evenZero⟩
  have hc1 : t1.gpr .x19 = BitVec.ofNat 64 j := by rw [d1.keeps.1 _ (by decide)]; exact hc
  -- The selection.
  refine WP.seq (WP.mono (selectFrom_ok (List.range n) (fun k hk => by have := List.mem_range.mp hk; omega) hs1
    (mag_lt no) (mag_lt ne) hm1 (List.mem_range.mpr hj) (by omega) hc1) fun t2 h2 => ?_)
  obtain ⟨b2, s2, v6, v7, v8, v9, bnd2⟩ := selected_env hs1 hb1 h2
  have hs2 : Scr t2 base := hs1.of_keeps h2.2.2 (by decide)
  have hc2 : t2.gpr .x19 = BitVec.ofNat 64 j := by rw [h2.2.2.1 _ (by decide)]; exact hc1
  have bits2 : Bits n base k t2.mem := fun q hq => by
    have hn := hs.nowrap
    rw [h2.2.1 _ (by rw [ofs_off0 base (by simp only [BITS]; omega)]; simp only [OX, BITS, slot]; omega), m1]
    exact hbits q hq
  have z2 : ∀ w < 8, limbs t2.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    rw [s2 19 (by decide) w hw]; rw [m1]; exact hz w hw
  have e1 : EV t1.mem base = EV s.mem base := by rw [m1]
  -- The odd digit's entry, negated, and added to `A`.
  rw [WP.block_append_iff]
  refine WP.mono (negate_ok hs2 b2 (k := k) (i := 2 * j + 1) (o := BITS + 4) 6 (by decide) hn (by omega) (by omega)
    (by simp only [BITS]; omega) (by simp only [BITS]; omega) hc2 bits2 (bnd2 6 (by decide))
    (zero_env z2).2) fun t3 ⟨k3, b3, s3, e3⟩ => ?_
  have hs3 := k3.scr hs2
  have z3 : ∀ w < 8, limbs t3.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    rw [s3 19 (by decide) w hw]; exact z2 w hw
  rw [WP.block_append_iff]
  refine WP.mono (addAffine_ok 0 1 2 6 7 (by decide) (by decide) (by decide) hs3 b3 (zero_env z3).2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    fun t4 ⟨k4, b4, s4, _, _, _, e4⟩ => ?_
  have hs4 := k4.scr hs3
  have z4 : ∀ w < 8, limbs t4.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    rw [s4 19 (by decide) w hw]; exact z3 w hw
  have hc4 : t4.gpr .x19 = BitVec.ofNat 64 j := by
    rw [k4.regs.1 .x19 (by decide), k3.regs.1 .x19 (by decide)]; exact hc2
  -- The even digit's entry, negated, and added to `B`.
  rw [WP.block_append_iff]
  refine WP.mono (negate_ok hs4 b4 (k := k) (i := 2 * j) (o := BITS) 8 (by decide) hn (by omega) (by omega)
    (by omega) (by simp only [BITS]; omega) hc4
    (Bits.of_fkeep hn hs3 (Bits.of_fkeep hn hs2 bits2 k3) k4)
    (s4.bnd (by decide) (s3.bnd (by decide) (bnd2 8 (by decide)))) (zero_env z4).2)
    fun t5 ⟨k5, b5, s5, e5⟩ => ?_
  have hs5 := k5.scr hs4
  have z5 : ∀ w < 8, limbs t5.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    rw [s5 19 (by decide) w hw]; exact z4 w hw
  rw [WP.block_append_iff]
  refine WP.mono (addAffine_ok 3 4 5 8 9 (by decide) (by decide) (by decide) hs5 b5 (zero_env z5).2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    fun t6 ⟨k6, b6, s6, _, _, _, e6⟩ => ?_
  have hs6 := k6.scr hs5
  -- The counter.
  have hc6 : t6.gpr .x19 = BitVec.ofNat 64 j := by
    rw [k6.regs.1 .x19 (by decide), k5.regs.1 .x19 (by decide)]; exact hc4
  refine WP.mono (next_ok t6 hn hj hc6) fun t7 ⟨c7, n7, k7, m7⟩ => ⟨n7, ?_⟩
  have hs7 : Scr t7 base := hs6.of_keeps k7 (by decide)
  have z6 : ∀ w < 8, limbs t6.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    rw [s6 19 (by decide) w hw]; exact z5 w hw
  -- Values of the slots along the way.
  have e2s : ∀ i : Index, i ∉ entrySlots → EV t2.mem base i = EV s.mem base i := fun i hi => by
    rw [Same.env s2 hi, e1]
  have z2v : EV t2.mem base 19 = 0 := (zero_env z2).1
  have t3o : ∀ i : Index, i ≠ 6 → i ≠ 10 → EV t3.mem base i = EV t2.mem base i := fun i h6 h10 => by
    rw [e3]; simp only [opSwap, Function.update_apply, h6, h10, ite_false]
  have t36 : EV t3.mem base 6 =
      if decide (nib k (2 * j + 1) < 8) then EV t2.mem base 19 - EV t2.mem base 6 else EV t2.mem base 6 := by
    rw [e3]; simp only [opSwap, Function.update_apply, show (6 : Index) ≠ 10 by decide, ite_false, ite_true]
  have t5o : ∀ i : Index, i ≠ 8 → i ≠ 10 → EV t5.mem base i = EV t4.mem base i := fun i h8 h10 => by
    rw [e5]; simp only [opSwap, Function.update_apply, h8, h10, ite_false]
  have t58 : EV t5.mem base 8 =
      if decide (nib k (2 * j) < 8) then EV t4.mem base 19 - EV t4.mem base 8 else EV t4.mem base 8 := by
    rw [e5]; simp only [opSwap, Function.update_apply, show (8 : Index) ≠ 10 by decide, ite_false, ite_true]
  have t4s : ∀ i : Index, i ∉ temps ++ [2, 0, 1] → i ∉ [10] ++ [6, 10] →
      EV t4.mem base i = EV t2.mem base i := fun i h4 h3 => by
    rw [Same.env s4 h4, Same.env s3 h3]
  -- The odd accumulator.
  have pA : pt (EV t4.mem base) 0 1 2 = addPt (pt (EV s.mem base) 0 1 2)
      (basePt (if nib k (2 * j + 1) < 8 then negAff (Impl.X448.baseTable j (mag (nib k (2 * j + 1))))
        else Impl.X448.baseTable j (mag (nib k (2 * j + 1))))) := by
    rw [e4, affEnv_A, t3o 0 (by decide) (by decide), t3o 1 (by decide) (by decide),
      t3o 2 (by decide) (by decide), t36, t3o 7 (by decide) (by decide), t3o 19 (by decide) (by decide),
      z2v, v6, v7, e2s 0 (by decide), e2s 1 (by decide), e2s 2 (by decide), affPt_eq,
      entry_eq _ 0 rfl]
    rfl
  have pB : pt (EV t6.mem base) 3 4 5 = addPt (pt (EV s.mem base) 3 4 5)
      (basePt (if nib k (2 * j) < 8 then negAff (Impl.X448.baseTable j (mag (nib k (2 * j))))
        else Impl.X448.baseTable j (mag (nib k (2 * j))))) := by
    rw [e6, affEnv_B, t5o 3 (by decide) (by decide), t5o 4 (by decide) (by decide),
      t5o 5 (by decide) (by decide), t58, t5o 9 (by decide) (by decide), t5o 19 (by decide) (by decide),
      t4s 3 (by decide) (by decide), t4s 4 (by decide) (by decide), t4s 5 (by decide) (by decide),
      t4s 8 (by decide) (by decide), t4s 9 (by decide) (by decide), t4s 19 (by decide) (by decide),
      z2v, v8, v9, e2s 3 (by decide), e2s 4 (by decide), e2s 5 (by decide), affPt_eq,
      entry_eq _ 0 rfl]
    rfl
  have p7A : pt (EV t7.mem base) 0 1 2 = pt (EV t4.mem base) 0 1 2 := by
    simp only [pt, m7]
    rw [Same.env s6 (i := 0) (by decide), Same.env s5 (i := 0) (by decide),
      Same.env s6 (i := 1) (by decide), Same.env s5 (i := 1) (by decide),
      Same.env s6 (i := 2) (by decide), Same.env s5 (i := 2) (by decide)]
  have p7B : pt (EV t7.mem base) 3 4 5 = pt (EV t6.mem base) 3 4 5 := by simp only [pt, m7]
  refine ⟨by omega, hs7, by rw [m7]; exact b6, by rw [m7]; exact z6, c7,
    by rw [m7]; exact Bits.of_fkeep hn hs5 (Bits.of_fkeep hn hs4 (Bits.of_fkeep hn hs3 (Bits.of_fkeep hn hs2 bits2 k3) k4) k5) k6,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p7A, pA]
    have := addPt_rep hodd (baseEntry_ok j (nib k (2 * j + 1)) (by omega) no)
    rw [acc_step] at this
    exact this
  · rw [p7B, pB]
    have := addPt_rep heven (baseEntry_ok j (nib k (2 * j)) (by omega) ne)
    rw [acc_step] at this
    exact this
  · rw [k7.1 .x30 (by decide), k6.regs.1 .x30 (by decide), k5.regs.1 .x30 (by decide),
      k4.regs.1 .x30 (by decide), k3.regs.1 .x30 (by decide), h2.2.2.1 .x30 (by decide),
      d1.keeps.1 .x30 (by decide)]; exact hlr
  · rw [k7.1 .x20 (by decide), k6.regs.1 .x20 (by decide), k5.regs.1 .x20 (by decide),
      k4.regs.1 .x20 (by decide), k3.regs.1 .x20 (by decide), h2.2.2.1 .x20 (by decide),
      d1.keeps.1 .x20 (by decide)]; exact hout
  · rw [k7.2.1, k6.regs.2.1, k5.regs.2.1, k4.regs.2.1, k3.regs.2.1, h2.2.2.2.1, d1.keeps.2.1]; exact hrd
  · rw [k7.2.2, k6.regs.2.2, k5.regs.2.2, k4.regs.2.2, k3.regs.2.2, h2.2.2.2.2, d1.keeps.2.2]; exact hwr
  · rw [m7]
    refine Outside2.trans hmem ?_
    rw [← m1]
    exact (((h2.outside2.trans k3.mem).trans k4.mem).trans k5.mem).trans k6.mem

end VG.Proof.X448.AArch64.Base

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Base.Loop`. -/
section

/-!
# X448 of the base point on AArch64: the comb's loop

Untrusted: everything here is checked by Lean. The steps of a comb of `n` tables
take `StepInv` from `j` to `n`.
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64

theorem loop_ok {n : Nat} (hn : n ≤ 57) {s₀ : State} {base : Addr} {k : Nat} :
    ∀ m, ∀ s, 1 ≤ m → m ≤ n → StepInv n s₀ base k (n - m) s →
      WP isa (.loop (VG.Impl.X448.AArch64.Base.stepN n) (.nonzero .x .x9)) s fun t =>
        StepInv n s₀ base k n t := by
  intro m s h1 h2 hi
  refine WP.loop (M := isa) (body := VG.Impl.X448.AArch64.Base.stepN n) (c := .nonzero .x .x9)
    (Q := fun t => StepInv n s₀ base k n t)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ n ∧ StepInv n s₀ base k (n - m) s) ?_ m s ⟨h1, h2, hi⟩
  intro m s ⟨h1, h2, hi⟩
  refine WP.mono (step_ok hn hi (by omega)) fun t ⟨hz, ht⟩ => ?_
  simp only [eval, State.read, BitVec.setWidth_eq, hz]
  by_cases hm : m = 1
  · subst hm
    rw [show n - 1 + 1 = n by omega] at ht ⊢
    exact .inl ⟨by simp, ht⟩
  · refine .inr ⟨congrArg some (decide_eq_true (by omega)), m - 1, by omega, by omega, by omega, ?_⟩
    rw [show n - (m - 1) = n - m + 1 by omega]
    exact ht

end VG.Proof.X448.AArch64.Base

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Base.Combine`. -/
section

/-!
# X448 of the base point on AArch64: `16 A + B`

Untrusted: everything here is checked by Lean. After the comb's loop, four
doublings of `A` and the addition of `B` leave `[k] B` in `A` (`comb_total`).
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside2)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.Ed448 (Rep baseAff dZ)
open VG.Proof.EdwardsLaw (EPoint)
open VG.Proof.X448 (addPt addPt_rep)
open VG.Impl.X448.AArch64.Fast (codeOf)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- What every phase after the setup keeps. -/
structure Frame (s₀ : State) (base : Addr) (s : State) : Prop where
  scr : Scr s base
  env : BEnv s.mem base
  zero : ∀ w < 8, limbs s.mem base (slot (19 : Index).val) w = 0
  lr : s.gpr .x30 = s₀.gpr .x30
  out : s.gpr .x20 = s₀.gpr .x20
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside2 base 64 2816 ACC 1152 s₀.mem s.mem

theorem StepInv.frame {n : Nat} {s₀ s : State} {base : Addr} {k j : Nat} (h : StepInv n s₀ base k j s) :
    Frame s₀ base s := ⟨h.scr, h.env, h.zero, h.lr, h.out, h.rd, h.wr, h.mem⟩

/-- A complete addition, from `Frame`, with the points in slots `x1 y1 z1` and `x2 y2 z2`. -/
theorem addFrame_ok {s₀ s : State} {base : Addr} (h : VG.Proof.X448.AArch64.Base.Frame s₀ base s) (x1 y1 z1 x2 y2 z2 : Index)
    (hx1 : x1.val < 10) (hy1 : y1.val < 10) (hz1 : z1.val < 10) (hx2 : x2.val < 10) (hy2 : y2.val < 10)
    (hz2 : z2.val < 10) (hxy : x1 ≠ y1) (hzx : z1 ≠ x1) (hzy : z1 ≠ y1) :
    WP isa (.block (codeOf (VG.Impl.X448.AArch64.Base.addOps (slot x1.val) (slot y1.val) (slot z1.val) (slot x2.val) (slot y2.val)
        (slot z2.val)))) s fun t =>
      VG.Proof.X448.AArch64.Base.Frame s₀ base t ∧ Same base (temps ++ [x1, y1, z1]) s.mem t.mem ∧
      EV t.mem base = genEnv x1 y1 z1 x2 y2 z2 (EV s.mem base) ∧ t.gpr .x19 = s.gpr .x19 := by
  refine block_codeOf (WP.mono (addOps_ok x1 y1 z1 x2 y2 z2 hx1 hy1 hz1 hx2 hy2 hz2 hxy hzx hzy h.scr h.env
    (zero_env h.zero).2) fun t ⟨tk, tb, ts, _, _, _, te⟩ => ⟨⟨tk.scr h.scr, tb, fun w hw => ?_, ?_, ?_, ?_, ?_, ?_⟩,
      ts, te, tk.regs.1 _ (by decide)⟩)
  · have : (19 : Index) ∉ temps ++ [x1, y1, z1] := by
      simp only [temps, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨by decide, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> (subst h; simp at *)
    rw [ts 19 this w hw]; exact h.zero w hw
  · rw [tk.regs.1 _ (by decide)]; exact h.lr
  · rw [tk.regs.1 _ (by decide)]; exact h.out
  · rw [tk.regs.2.1]; exact h.rd
  · rw [tk.regs.2.2]; exact h.wr
  · exact h.mem.trans tk.mem

/-- The doublings' state with `m` of them left. -/
structure DInv (s₀ : State) (base : Addr) (v w : ℤ) (m : Nat) (s : State) : Prop where
  frame : VG.Proof.X448.AArch64.Base.Frame s₀ base s
  counter : s.gpr .x19 = BitVec.ofNat 64 m
  a : Rep (VG.Proof.X448.AArch64.Base.pt (EV s.mem base) 0 1 2) ((2 ^ (4 - m) * v) • baseAff)
  b : Rep (VG.Proof.X448.AArch64.Base.pt (EV s.mem base) 3 4 5) (w • baseAff)

theorem dbl_ok {s₀ s : State} {base : Addr} {v w : ℤ} {m : Nat} (hm : 1 ≤ m) (hm4 : m ≤ 4)
    (h : VG.Proof.X448.AArch64.Base.DInv s₀ base v w m s) :
    WP isa (.block (codeOf (VG.Impl.X448.AArch64.Base.addOps AX AY AZ AX AY AZ) ++ ([.subImm .x .x19 .x19 1] : List Instr))) s
      fun t => VG.Proof.X448.AArch64.Base.DInv s₀ base v w (m - 1) t ∧ (t.gpr .x19 == 0) = decide (m - 1 = 0) := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.Base.addFrame_ok h.frame 0 1 2 0 1 2 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun t ⟨tf, ts, te, tc⟩ => ?_
  refine WP.mono (VG.Proof.X448.AArch64.Weak.decCounter_ok (k := m - 1) (by omega)
    (by rw [tc, h.counter]; congr 1; omega)) fun u ⟨uc, ug, um, urd, uwr, uz⟩ => ⟨⟨?_, uc, ?_, ?_⟩, uz⟩
  · exact ⟨tf.scr.of_keeps (rs := [.x19]) ⟨fun r hr => ug r (by simpa using hr), urd, uwr⟩ (by decide),
      by rw [um]; exact tf.env, by rw [um]; exact tf.zero, by rw [ug _ (by decide)]; exact tf.lr,
      by rw [ug _ (by decide)]; exact tf.out, by rw [urd]; exact tf.rd, by rw [uwr]; exact tf.wr, by rw [um]; exact tf.mem⟩
  · have hz := (zero_env h.frame.zero).1
    rw [um, te, genEnv_dbl, hz, genPt_eq]
    have := addPt_rep h.a h.a
    rw [← add_smul] at this
    rw [show (2 : ℤ) ^ (4 - (m - 1)) * v = 2 ^ (4 - m) * v + 2 ^ (4 - m) * v by
      rw [show 4 - (m - 1) = (4 - m) + 1 by omega, pow_succ]; ring]
    exact this
  · rw [um]
    have e : ∀ i : Index, i ∈ [3, 4, 5] → EV t.mem base i = EV s.mem base i := fun i hi => by
      refine Same.env ts ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    simp only [VG.Proof.X448.AArch64.Base.pt]
    rw [e 3 (by simp), e 4 (by simp), e 5 (by simp)]
    exact h.b

/-- **`16 A + B`**: from the comb's last step, `[k] B` in `A`. -/
theorem combine_ok {n : Nat} {s₀ s : State} {base : Addr} {k : Nat} (hk : k < 256 ^ n)
    (h : StepInv n s₀ base k n s) :
    WP isa combine s fun t => Frame s₀ base t ∧ Rep (pt (EV t.mem base) 0 1 2) ((k : ℤ) • baseAff) := by
  let v : ℤ := VG.Proof.X448.combG n + VG.Proof.X448.oddSumZ k n
  let w : ℤ := VG.Proof.X448.combG n + VG.Proof.X448.evenSumZ k n
  unfold combine
  refine WP.seq (WP.mono (VG.Proof.X448.AArch64.Weak.setCounter_ok s 4 (by decide))
    fun s1 ⟨c1, g1, m1, rd1, wr1⟩ => ?_)
  have f1 : VG.Proof.X448.AArch64.Base.Frame s₀ base s1 :=
    ⟨h.scr.of_keeps (rs := [.x19]) ⟨fun r hr => g1 r (by simpa using hr), rd1, wr1⟩ (by decide), by rw [m1]; exact h.env,
      by rw [m1]; exact h.zero, by rw [g1 _ (by decide)]; exact h.lr, by rw [g1 _ (by decide)]; exact h.out,
      by rw [rd1]; exact h.rd,
      by rw [wr1]; exact h.wr, by rw [m1]; exact h.mem⟩
  have d1 : VG.Proof.X448.AArch64.Base.DInv s₀ base v w 4 s1 :=
    ⟨f1, c1, by rw [m1]; simpa using h.odd, by rw [m1]; exact h.even⟩
  refine WP.seq (WP.mono (WP.loop (M := isa) (Q := fun t => VG.Proof.X448.AArch64.Base.DInv s₀ base v w 0 t)
    (fun m (t : State) => 1 ≤ m ∧ m ≤ 4 ∧ VG.Proof.X448.AArch64.Base.DInv s₀ base v w m t) ?_ 4 s1 ⟨by decide, le_refl _, d1⟩) ?_)
  · intro m t ⟨h1, h4, ht⟩
    refine WP.mono (VG.Proof.X448.AArch64.Base.dbl_ok h1 h4 ht) fun u ⟨hu, hz⟩ => ?_
    simp only [eval, State.read, BitVec.setWidth_eq, bne, hz]
    by_cases hm : m = 1
    · subst hm; exact .inl ⟨rfl, hu⟩
    · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬m - 1 = 0), Bool.not_false], m - 1,
        by omega, by omega, by omega, hu⟩
  · intro t ht
    refine WP.mono (VG.Proof.X448.AArch64.Base.addFrame_ok ht.frame 0 1 2 3 4 5 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)) fun u ⟨uf, _, ue, _⟩ => ⟨uf, ?_⟩
    rw [ue, genEnv_add, (zero_env ht.frame.zero).1, genPt_eq]
    have := addPt_rep ht.a ht.b
    rw [← add_smul, show (2 : ℤ) ^ (4 - 0) * v + w = 16 * v + w by norm_num,
      VG.Proof.X448.comb_total hk] at this
    exact this

end VG.Proof.X448.AArch64.Base

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Base.Erase`. -/
section

/-!
# X448 of the base point on AArch64: the code without its immediates

Untrusted: everything here is checked by Lean. The constant-time analysis does
not read the immediates of `movz` and `movk` (`Code.eraseImm`), and without
them the selections from the tables are the same code, table 0's
(`x448Base_eraseImm`, proven without evaluating them). The kernel, evaluating
the analysis of `x448BaseErased` (`x448Base_ct`), then builds no table's
immediates, and builds and analyses one selection rather than one per table: it caches
the analysis of the same code from the same taint. The analysis is the code's
only evaluation, so the code has no literal (`materialize_code`), which would
cost more to check than it saves.
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64.Base
open VG.Impl.X448.AArch64 (BITS)

/-- `selectFrom`, with every table's selection table 0's. -/
def selectFrom0 : List Nat → Prog isa
  | [] => .block []
  | j :: js => .seq (.block [.subImm .x .x9 .x19 j])
      (.ite (.zero .x .x9) (.block (VG.Impl.X448.AArch64.Base.select 0)) (VG.Proof.X448.AArch64.Base.selectFrom0 js))

/-- `stepN n`, with every table's selection table 0's. -/
def stepN0 (n : Nat) : Prog isa :=
  .seq (.block digits) <|
  .seq (selectFrom0 (List.range n)) <|
  .block (negate OX (BITS + 4) (t 0) ++ addAffine AX AY AZ OX OY ++
    negate EX BITS (t 0) ++ addAffine BX BY BZ EX EY ++
    [.addImm .x .x19 .x19 1, .subImm .x .x9 .x19 n])

/-- `x448Base`, with every table's selection table 0's. -/
def x448Base0 : Prog isa :=
  .seq setup <| .seq (.loop (stepN0 56) (.nonzero .x .x9)) <| .seq combine finish

/-- `x448Base` without its immediates. -/
def x448BaseErased : Prog isa := Code.eraseImm VG.Proof.X448.AArch64.Base.x448Base0

/-- `const64 d v` without its immediates. -/
def const64E (d : Reg) : List Instr := (VG.Impl.X448.AArch64.Base.const64 d 0).map Instr.eraseImm

theorem const64_eraseImm (d : Reg) (v : BitVec 64) :
    (VG.Impl.X448.AArch64.Base.const64 d v).map Instr.eraseImm = VG.Proof.X448.AArch64.Base.const64E d := rfl

/-- `selectWord` without its immediates. -/
def selectWordE (one : Bool) (o e w : Nat) : List Instr :=
  (selectWord one [] o e w).map Instr.eraseImm

theorem selectWord_eraseImm (one : Bool) (vs : List Spec.X448.Fe) (o e w : Nat) :
    (selectWord one vs o e w).map Instr.eraseImm = VG.Proof.X448.AArch64.Base.selectWordE one o e w := by
  simp only [VG.Proof.X448.AArch64.Base.selectWordE, selectWord, List.map_append, List.map_flatMap, VG.Proof.X448.AArch64.Base.const64_eraseImm]

theorem select_eraseImm (j : Nat) :
    (VG.Impl.X448.AArch64.Base.select j).map Instr.eraseImm = (VG.Impl.X448.AArch64.Base.select 0).map Instr.eraseImm := by
  simp only [VG.Impl.X448.AArch64.Base.select, List.map_append, List.map_flatMap, VG.Proof.X448.AArch64.Base.selectWord_eraseImm]

theorem selectFrom_eraseImm (js : List Nat) :
    Code.eraseImm (selectFrom js) = Code.eraseImm (VG.Proof.X448.AArch64.Base.selectFrom0 js) := by
  induction js with
  | nil => rfl
  | cons j js ih => simp only [selectFrom, VG.Proof.X448.AArch64.Base.selectFrom0, Code.eraseImm, VG.Proof.X448.AArch64.Base.select_eraseImm, ih]

theorem stepN_eraseImm (n : Nat) : Code.eraseImm (stepN n) = Code.eraseImm (stepN0 n) := by
  simp only [stepN, stepN0, Code.eraseImm, selectFrom_eraseImm]

theorem x448Base_eraseImm : Code.eraseImm x448Base = x448BaseErased := by
  simp only [x448BaseErased, x448Base, x448Base0, step, Code.eraseImm, stepN_eraseImm]

end VG.Proof.X448.AArch64.Base

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Base.Setup`. -/
section

/-!
# X448 of the base point on AArch64: the setup

Untrusted: everything here is checked by Lean. The setup points `x3` at the
working space, sets `x12`, saves the callee-saved registers and the output
pointer, zeroes every slot, expands the clamped scalar's bits, and starts both
accumulators at `[G] B` (`baseG`): `StepInv` for step 0.
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 store_ok)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)

open VG.Proof.X448.AArch64 (Saved)

/-- `x3 := x2` (the working space) and `x12 := 2²⁸ - 1`. -/
theorem regs_ok (s : State) :
    WP isa (.block ([.addImm .x .x3 .x2 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1] : List Instr)) s
      fun t => t.gpr .x3 = s.gpr .x2 ∧ t.gpr .x12 = 0x0fffffff ∧ Keeps [.x3, .x12] s t ∧ t.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (0 : Nat) < 4096 from by decide, Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, by decide, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem word_store {m : Mem} {base : Addr} {d e : Nat} (hd : d + 8 ≤ 8192) (he : e + 8 ≤ 8192)
    (hdm : d % 8 = 0) (hem : e % 8 = 0) (v : BitVec 64) (hne : e ≠ d) :
    word (m.writeW (off base d) v) base e = word m base e := by
  rw [VG.Proof.X448.AArch64.word_write_aligned _ _ hd he hdm hem, ite_eq_right hne]

theorem word_store_self {m : Mem} {base : Addr} {d : Nat} (hd : d + 8 ≤ 8192) (hdm : d % 8 = 0)
    (v : BitVec 64) : word (m.writeW (off base d) v) base d = v := by
  rw [VG.Proof.X448.AArch64.word_write_aligned _ _ hd hd hdm hdm, ite_eq_left rfl]

theorem mov20_ok (s : State) :
    WP isa (.block [.addImm .x .x20 .x0 0]) s fun t =>
      t.gpr .x20 = s.gpr .x0 ∧ t.mem = s.mem ∧ Keeps [.x20] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Nat.reduceLT, BitVec.setWidth_eq, BitVec.add_zero, RegUpd.gpr_write,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- The registers, the stores of `x19` and `x20`, the output pointer to `x20`, and the save of
`x21`–`x28`. -/
theorem prefix_ok {s : State} {base : Addr} (hb : s.gpr .x2 = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hn : base.toNat + 8192 ≤ 2 ^ 64) :
    WP isa (.block (([.addImm .x .x3 .x2 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1,
        st .x19 0, st .x20 8, .addImm .x .x20 .x0 0] : List Instr) ++ VG.Impl.X448.AArch64.Fast.save)) s fun t =>
      Scr t base ∧ Saved base s.gpr t.mem ∧ t.gpr .x20 = s.gpr .x0 ∧ SavedX base s.gpr t.mem ∧
      Keeps [.x3, .x12, .x20] s t ∧ Outside base 0 8192 s.mem t.mem := by
  rw [show ([.addImm .x .x3 .x2 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1,
      st .x19 0, st .x20 8, .addImm .x .x20 .x0 0] : List Instr) =
      [.addImm .x .x3 .x2 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1] ++
        ([st .x19 0] ++ ([st .x20 8] ++ [.addImm .x .x20 .x0 0])) from rfl]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (regs_ok s) fun a ⟨a3, a12, ka, ma⟩ => ?_
  have ha : Scr a base := ⟨a3.trans hb, a12, by rw [ka.2.2]; exact hw, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (store_ok ha (d := 0) (by decide) (by decide) .x19) fun b ⟨mb, kb⟩ => ?_
  have hsb := ha.of_keeps kb (by decide)
  have b0 : word b.mem base 0 = s.gpr .x19 := by
    rw [mb, word_store_self (by decide) (by decide), ka.1 _ (by decide)]
  rw [WP.block_append_iff]
  refine WP.mono (store_ok hsb (d := 8) (by decide) (by decide) .x20) fun c ⟨mc, kc⟩ => ?_
  have hsc := hsb.of_keeps kc (by decide)
  have c0 : word c.mem base 0 = s.gpr .x19 := by
    rw [mc, word_store (by decide) (by decide) (by decide) (by decide) _ (by decide), b0]
  have c8 : word c.mem base 8 = s.gpr .x20 := by
    rw [mc, word_store_self (by decide) (by decide), kb.1 _ (by decide), ka.1 _ (by decide)]
  rw [WP.block_append_iff]
  refine WP.mono (mov20_ok c) fun d ⟨d20, md, kd⟩ => ?_
  have hsd := hsc.of_keeps kd (by decide)
  refine WP.mono (save_ok hsd) fun t ⟨tx, tOut, tg, tr, tw⟩ => ?_
  have kad : Keeps [.x3, .x12, .x20] s d :=
    (((ka.mono (by simp)).trans (kb.mono (by simp))).trans (kc.mono (by simp))).trans (kd.mono (by simp))
  have kt : Keeps [.x3, .x12, .x20] s t := ⟨fun r hr => (congrFun tg r).trans (kad.1 r hr), tr.trans kad.2.1,
    tw.trans kad.2.2⟩
  have od : Outside base 0 8192 s.mem d.mem := by
    have o1 : Outside base 0 8192 s.mem b.mem := by
      rw [mb, ← ma]; exact (VG.Proof.X448.AArch64.writeW_outside _ _ _ (by decide)).mono (by omega) (by omega)
    have o2 : Outside base 0 8192 b.mem c.mem := by
      rw [mc]; exact (VG.Proof.X448.AArch64.writeW_outside _ _ _ (by decide)).mono (by omega) (by omega)
    rw [md]; exact o1.trans o2
  refine ⟨hsd.of_keeps (rs := []) ⟨fun r _ => congrFun tg r, tr, tw⟩ (by decide), ⟨?_, ?_⟩, ?_, ?_, kt,
    od.trans (tOut.mono (by omega) (by simp only [Impl.X448.AArch64.Fast.SAVE]; omega))⟩
  · rw [tOut.word (Or.inl (by decide)) (by decide), md]; exact c0
  · rw [tOut.word (Or.inl (by decide)) (by decide), md]; exact c8
  · rw [congrFun tg .x20, d20, kc.1 _ (by decide), kb.1 _ (by decide), ka.1 _ (by decide)]
  · intro k hk
    rw [tx k hk]
    have : VG.Impl.X448.AArch64.Fast.saved k ∉ [Reg.x3, .x12, .x20] := by
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega)
        with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact kad.1 _ this

/-- The setup's first block: `prefix`, then `v8`–`v15` saved and every slot zeroed. -/
theorem block1_ok {s : State} {base : Addr} (hb : s.gpr .x2 = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hn : base.toNat + 8192 ≤ 2 ^ 64) :
    WP isa (.block VG.Impl.X448.AArch64.Base.entry) s fun t =>
      Scr t base ∧ Saved base s.gpr t.mem ∧ t.gpr .x20 = s.gpr .x0 ∧ SavedX base s.gpr t.mem ∧
      SavedV base s.v t.mem ∧ Keeps [.x3, .x12, .x4, .x20] s t ∧
      (∀ i < 352, limbs t.mem base (slot 0) i = 0) ∧ Outside base 0 8192 s.mem t.mem := by
  simp only [VG.Impl.X448.AArch64.Base.entry, List.append_assoc]
  rw [← List.append_assoc (([.addImm .x .x3 .x2 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1,
        st .x19 0, st .x20 8, .addImm .x .x20 .x0 0] : List Instr)), WP.block_append_iff]
  refine WP.mono (WP.preservedV (prefix_ok hb hw hn) (by lit_decide)) fun a ⟨⟨ha, sa, oa, xa, ka, outa⟩, va⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (vsave_ok ha) fun b ⟨vb, ob, gb, rb, wb⟩ => ?_
  have hsb : Scr b base := ha.of_keeps (rs := []) ⟨fun r _ => congrFun gb r, rb, wb⟩ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.zeroX4_ok b) fun c ⟨c4, mc, kc⟩ => ?_
  have hsc : Scr c base := hsb.of_keeps kc (by decide)
  refine WP.mono (VG.Proof.X448.AArch64.fill_ok hsc (o := slot 0) (n := 352) (by decide) (by decide) c4)
    fun t ⟨tz, tOut, kt⟩ => ?_
  have hst : Scr t base := hsc.of_keeps kt (by decide)
  have m : ∀ {d : Nat}, d + 8 ≤ 64 ∨ 2880 ≤ d → d + 8 ≤ 8192 →
      d + 8 ≤ VG.Impl.X448.AArch64.Fast.VSAVE ∨ VG.Impl.X448.AArch64.Fast.VSAVE + 128 ≤ d →
      word t.mem base d = word a.mem base d := fun h1 h2 h3 => by
    rw [tOut.word (by simp only [slot]; omega) h2, mc, ob.word h3 h2]
  have hxs : ∀ k < 8, word t.mem base (Impl.X448.AArch64.Fast.SAVE + 8 * k) = s.gpr (Impl.X448.AArch64.Fast.saved k) :=
    fun k hk => by
      rw [m (by simp only [Impl.X448.AArch64.Fast.SAVE]; omega) (by simp only [Impl.X448.AArch64.Fast.SAVE]; omega)
        (by simp only [Impl.X448.AArch64.Fast.SAVE, Impl.X448.AArch64.Fast.VSAVE]; omega)]
      exact xa k hk
  have vt : SavedV base a.v t.mem := by
    have vc : SavedV base a.v c.mem := by rw [mc]; exact vb
    exact vc.outside tOut (by simp only [slot, Impl.X448.AArch64.Fast.VSAVE]; omega)
  refine ⟨hst, ⟨by rw [m (by decide) (by decide) (by decide)]; exact sa.1,
      by rw [m (by decide) (by decide) (by decide)]; exact sa.2⟩,
    by rw [kt.1 _ (by decide), kc.1 _ (by decide), congrFun gb .x20]; exact oa,
    hxs, fun k hk => ?_, ?_, tz, ?_⟩
  · rw [vt k hk]
    have hr : VG.Impl.Curve448.AArch64.Neon.V (8 + k) ∈ preservedV := by
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega)
        with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact va _ hr
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [kt.1 _ (by simp), kc.1 _ (by simpa using hr.2.2.1), congrFun gb r,
        ka.1 _ (by simp [hr.1, hr.2.1, hr.2.2.2])]
    · rw [kt.2.1, kc.2.1, rb, ka.2.1]
    · rw [kt.2.2, kc.2.2, wb, ka.2.2]
  · refine (outa.trans (ob.mono (by simp only [Impl.X448.AArch64.Fast.VSAVE]; omega)
      (by simp only [Impl.X448.AArch64.Fast.VSAVE]; omega))).trans ?_
    rw [← mc]; exact tOut.mono (by simp only [slot]; omega) (by simp only [slot]; omega)

/-- The constant slots: both accumulators at the affine point `g`, and the counter at 0. -/
theorem consts_ok {s : State} {base : Addr} (hs : Scr s base) (g : Spec.X448.Fe × Spec.X448.Fe) :
    WP isa (.block (accs g)) s fun t =>
      (∀ w < 8, word t.mem base (AX + 8 * w) = limb g.1 w ∧
        word t.mem base (AY + 8 * w) = limb g.2 w ∧ word t.mem base (AZ + 8 * w) = limb 1 w ∧
        word t.mem base (BX + 8 * w) = limb g.1 w ∧
        word t.mem base (BY + 8 * w) = limb g.2 w ∧ word t.mem base (BZ + 8 * w) = limb 1 w) ∧
      Outside base 64 768 s.mem t.mem ∧ Keeps [.x4, .x19] s t ∧ t.gpr .x19 = 0 := by
  simp only [accs, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok hs (o := AX) (by decide) (by decide) _) fun t1 ⟨v1, o1, k1⟩ => ?_
  have h1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok h1 (o := AY) (by decide) (by decide) _) fun t2 ⟨v2, o2, k2⟩ => ?_
  have h2 := h1.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok h2 (o := AZ) (by decide) (by decide) _) fun t3 ⟨v3, o3, k3⟩ => ?_
  have h3 := h2.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok h3 (o := BX) (by decide) (by decide) _) fun t4 ⟨v4, o4, k4⟩ => ?_
  have h4 := h3.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok h4 (o := BY) (by decide) (by decide) _) fun t5 ⟨v5, o5, k5⟩ => ?_
  have h5 := h4.of_keeps k5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok h5 (o := BZ) (by decide) (by decide) _) fun t6 ⟨v6, o6, k6⟩ => ?_
  refine WP.mono (VG.Proof.X448.AArch64.Weak.setCounter_ok t6 0 (by decide))
    fun t ⟨c, g, m, rd, wr⟩ => ⟨fun w hw => ?_, ?_, ?_, by rw [c]; rfl⟩
  · have hw8 : w < 8 := hw
    simp only [AX, AY, AZ, BX, BY, BZ, slot] at v1 v2 v3 v4 v5 v6 o1 o2 o3 o4 o5 o6 ⊢
    rw [m]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [o6.word (by omega) (by omega), o5.word (by omega) (by omega), o4.word (by omega) (by omega),
        o3.word (by omega) (by omega), o2.word (by omega) (by omega)]; exact v1 w hw8
    · rw [o6.word (by omega) (by omega), o5.word (by omega) (by omega), o4.word (by omega) (by omega),
        o3.word (by omega) (by omega)]; exact v2 w hw8
    · rw [o6.word (by omega) (by omega), o5.word (by omega) (by omega), o4.word (by omega) (by omega)]
      exact v3 w hw8
    · rw [o6.word (by omega) (by omega), o5.word (by omega) (by omega)]; exact v4 w hw8
    · rw [o6.word (by omega) (by omega)]; exact v5 w hw8
    · exact v6 w hw8
  · simp only [AX, AY, AZ, BX, BY, BZ, slot] at o1 o2 o3 o4 o5 o6
    rw [m]
    exact (((((o1.mono (by omega) (by omega)).trans (o2.mono (by omega) (by omega))).trans
      (o3.mono (by omega) (by omega))).trans (o4.mono (by omega) (by omega))).trans
      (o5.mono (by omega) (by omega))).trans (o6.mono (by omega) (by omega))
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [g r hr.2, k6.1 r (by simp [hr.1]), k5.1 r (by simp [hr.1]), k4.1 r (by simp [hr.1]),
        k3.1 r (by simp [hr.1]), k2.1 r (by simp [hr.1]), k1.1 r (by simp [hr.1])]
    · rw [rd, k6.2.1, k5.2.1, k4.2.1, k3.2.1, k2.2.1, k1.2.1]
    · rw [wr, k6.2.2, k5.2.2, k4.2.2, k3.2.2, k2.2.2, k1.2.2]

open VG.Proof.Ed448 (Rep baseAff)
open VG.Proof.X448.AArch64 (bitRegs ofs)

theorem bytesAt_outside {base p : Addr} {m m' : Mem} (h : Outside base 0 8192 m m')
    (hp : ∀ i < 56, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) :
    Spec.X448.bytesAt m' p 56 = Spec.X448.bytesAt m p 56 := by
  simp only [Spec.X448.bytesAt]
  refine List.map_congr_left fun i hi => h _ (Or.inr ?_)
  simp only [List.mem_range] at hi
  exact hp i hi

/-- What the setup leaves, from the function's entry state `sE`. -/
structure Ready (sE : State) (base : Addr) (k : Nat) (t : State) : Prop where
  inv : StepInv 56 t base k 0 t
  saved : Saved base sE.gpr t.mem
  out : t.gpr .x20 = sE.gpr .x0
  savedX : SavedX base sE.gpr t.mem
  savedV : SavedV base sE.v t.mem
  lr : t.gpr .x30 = sE.gpr .x30
  rd : t.rd = sE.rd
  wr : t.wr = sE.wr
  mem : Outside base 0 8192 sE.mem t.mem

theorem setup_ok {s : State} {base kp : Addr} (hb : s.gpr .x2 = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hn : base.toNat + 8192 ≤ 2 ^ 64) (hk : s.gpr .x1 = kp)
    (hkr : ∀ q < 56, InRegions (s.rd ++ s.wr) (kp + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 56, 8192 ≤ VG.Proof.X448.AArch64.ofs base (kp + BitVec.ofNat 64 q)) :
    WP isa VG.Impl.X448.AArch64.Base.setup s
      (Ready s base (Spec.X448.decodeScalar448 (Spec.X448.bytesAt s.mem kp 56))) := by
  unfold VG.Impl.X448.AArch64.Base.setup
  refine WP.seq (WP.mono (block1_ok hb hw hn) fun a ⟨ha, sa, oa, xa, va, ka, za, outa⟩ => ?_)
  refine WP.seq (WP.mono (bits_ok ha (by rw [ka.1 _ (by decide)]; exact hk)
    (by rw [ka.2.1, ka.2.2]; exact hkr) hkd) fun b ⟨gb, rdb, wrb, ob, bitsb⟩ => ?_)
  have kb : Keeps bitRegs a b := ⟨gb, rdb, wrb⟩
  have hsb : Scr b base := ha.of_keeps kb (by decide)
  rw [bytesAt_outside outa hkd] at bitsb
  refine WP.mono (consts_ok hsb _) fun t ⟨tv, tOut, kt, tc⟩ => ?_
  have hst : Scr t base := hsb.of_keeps kt (by decide)
  -- Every word outside the constant slots and the bits is as `block1` left it.
  have wt : ∀ {d : Nat}, d + 8 ≤ 64 ∨ 832 ≤ d → d + 8 ≤ BITS ∨ BITS + 448 ≤ d → d + 8 ≤ 8192 →
      word t.mem base d = word a.mem base d := fun h1 h2 h3 => by
    rw [tOut.word (by omega) h3, ob.word h2 h3]
  -- The slots `block1` zeroed.
  have zs : ∀ i : Index, ∀ w < 8, word a.mem base (slot i.val + 8 * w) = 0 := fun i w hw => by
    have := i.isLt
    have hz := za (16 * i.val + w) (by omega)
    have e : slot 0 + 8 * (16 * i.val + w) = slot i.val + 8 * w := by simp only [slot]; omega
    rw [show VG.Proof.X448.AArch64.limbs a.mem base (slot 0) (16 * i.val + w) =
      (word a.mem base (slot i.val + 8 * w)).toNat by
        simp only [VG.Proof.X448.AArch64.limbs]; rw [e]] at hz
    exact BitVec.eq_of_toNat_eq hz
  have zt : ∀ i : Index, 6 ≤ i.val → ∀ w < 8, word t.mem base (slot i.val + 8 * w) = 0 := fun i hi w hw => by
    have := i.isLt
    rw [wt (by simp only [slot]; omega) (by simp only [slot, BITS]; omega) (by simp only [slot]; omega)]
    exact zs i w hw
  have ev : ∀ (i : Index) (v : Spec.X448.Fe), (∀ w < 8, word t.mem base (slot i.val + 8 * w) = limb v w) →
      VG.Proof.X448.AArch64.Weak.E t.mem base i = v := fun i v h => F_of_words h
  have pA : pt (VG.Proof.X448.AArch64.Weak.E t.mem base) 0 1 2 = VG.Proof.X448.basePt Impl.X448.baseG := by
    simp only [pt, VG.Proof.X448.basePt]
    rw [ev 0 _ fun w hw => (tv w hw).1, ev 1 _ fun w hw => (tv w hw).2.1, ev 2 _ fun w hw => (tv w hw).2.2.1]
  have pB : pt (VG.Proof.X448.AArch64.Weak.E t.mem base) 3 4 5 = VG.Proof.X448.basePt Impl.X448.baseG := by
    simp only [pt, VG.Proof.X448.basePt]
    rw [ev 3 _ fun w hw => (tv w hw).2.2.2.1, ev 4 _ fun w hw => (tv w hw).2.2.2.2.1,
      ev 5 _ fun w hw => (tv w hw).2.2.2.2.2]
  have hG : Rep (VG.Proof.X448.basePt Impl.X448.baseG) (((VG.Proof.X448.combG 56 : ℤ) + 0) • baseAff) := by
    rw [VG.Proof.X448.combG_56, add_zero, natCast_zsmul]; exact VG.Proof.X448.baseG_ok
  have bsaved : ∀ {d : Nat}, d + 8 ≤ 64 ∨ 832 ≤ d → d + 8 ≤ BITS ∨ BITS + 448 ≤ d → d + 8 ≤ 8192 →
      word t.mem base d = word a.mem base d := wt
  refine ⟨⟨by decide, hst, fun i w hw => ?_, fun w hw => ?_, by rw [tc]; rfl, fun q hq => ?_,
      by rw [pA]; exact hG, by rw [pB]; exact hG, rfl, rfl, rfl, rfl, Outside2.refl _ _ _ _ _ _⟩,
    ⟨by rw [bsaved (by decide) (by decide) (by decide)]; exact sa.1,
      by rw [bsaved (by decide) (by decide) (by decide)]; exact sa.2⟩,
    by rw [kt.1 _ (by decide), kb.1 _ (by decide)]; exact oa,
    fun k hk => by
      rw [bsaved (by simp only [Impl.X448.AArch64.Fast.SAVE]; omega)
        (by simp only [Impl.X448.AArch64.Fast.SAVE, BITS]; omega) (by simp only [Impl.X448.AArch64.Fast.SAVE]; omega)]
      exact xa k hk,
    (va.outside ob (by simp only [BITS, Impl.X448.AArch64.Fast.VSAVE]; omega)).outside tOut
      (by simp only [Impl.X448.AArch64.Fast.VSAVE]; omega),
    by rw [kt.1 _ (by decide), kb.1 _ (by decide), ka.1 _ (by decide)],
    by rw [kt.2.1, kb.2.1, ka.2.1], by rw [kt.2.2, kb.2.2, ka.2.2],
    (outa.trans (ob.mono (by omega) (by simp only [BITS]; omega))).trans (tOut.mono (by omega) (by omega))⟩
  · -- Every slot's limbs are below `Ib`.
    by_cases hi : i.val < 6
    · have hi6 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
        rcases i with ⟨i, hlt⟩; simp only [Fin.ext_iff] at hi ⊢; omega
      rcases hi6 with rfl | rfl | rfl | rfl | rfl | rfl
      · exact bnd_of_words (fun w hw => (tv w hw).1) w hw
      · exact bnd_of_words (fun w hw => (tv w hw).2.1) w hw
      · exact bnd_of_words (fun w hw => (tv w hw).2.2.1) w hw
      · exact bnd_of_words (fun w hw => (tv w hw).2.2.2.1) w hw
      · exact bnd_of_words (fun w hw => (tv w hw).2.2.2.2.1) w hw
      · exact bnd_of_words (fun w hw => (tv w hw).2.2.2.2.2) w hw
    · show (word t.mem base (slot i.val + 8 * w)).toNat < Ib
      rw [zt i (by omega) w hw]; decide
  · show (word t.mem base (slot (19 : Index).val + 8 * w)).toNat = 0
    rw [zt 19 (by decide) w hw]; rfl
  · have hn' := hn
    rw [tOut _ (by rw [Base.ofs_off0 base (by simp only [BITS]; omega)]; simp only [BITS]; omega)]
    exact bitsb q hq

end VG.Proof.X448.AArch64.Base

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Base.Finish`. -/
section

/-!
# X448 of the base point on AArch64: `Y² / X²`, encoded

Untrusted: everything here is checked by Lean. `Y²` and `X²` go to the ladder's
`x₂` and `z₂` slots; the ladder's inversion and finish (`Fast.invert_ok`,
`Fast.finish_ok`) encode `Y² · (X²)^(p-2)` to the output, reloaded from the
working space, and restore the callee-saved registers.
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 Saved ofs)
open VG.Proof.X448.AArch64.Weak (Index Env invEnv invEnv_eval invEnv_x2)
open VG.Proof.X448.AArch64.Fast
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- `Y²` to slot 1 and `X²` to slot 2. -/
theorem squares_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) :
    WP isa (.block (Impl.X448.AArch64.Fast.codeOf [.mul X2 AY AY, .mul Z2 AX AX])) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧
      EV t.mem base = Function.update (Function.update (EV s.mem base) 1 (EV s.mem base 1 * EV s.mem base 1)) 2
        (EV s.mem base 0 * EV s.mem base 0) := by
  refine block_codeOf (mulOp hs hb 1 1 1 (Or.inl rfl) fun t1 k1 b1 _ _ e1 => ?_)
  refine mulOp (k1.scr hs) b1 2 0 0 (Or.inl rfl) fun t2 k2 b2 _ _ e2 => WP.block_nil ⟨k1.trans k2, b2, ?_⟩
  rw [e2, e1]
  rfl

end VG.Proof.X448.AArch64.Base

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Base.Main`. -/
section

/-!
# X448 of the base point on AArch64: the whole function

Untrusted: everything here is checked by Lean. The contract the proof is
written against (the facts of `Spec.X448.x448BaseContract` it uses, stated for
AArch64), and `vg_x448_base`'s correctness against it: the comb leaves `[k] B`
on edwards448, whose `y² / x²` is `X448(k, 5)` (`x448_basePoint`).
-/

namespace VG.Proof.X448

open VG VG.AArch64 in
/-- `vg_x448_base(out = x0, scalar = x1, scratch = x2)`. -/
def x448BaseAArch64 : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 56⟩
    let scalar : Region := ⟨s.gpr .x1, 56⟩
    let scratch : Region := ⟨s.gpr .x2, 8192⟩
    s.rd = [scalar] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ scalar.Disjoint scratch ∧
      (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64
  post s s' := Spec.X448.bytesAt s'.mem (s.gpr .x0) 56 =
    Spec.X448.x448 (Spec.X448.bytesAt s.mem (s.gpr .x1) 56) Spec.X448.basePoint
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.sp = s₂.sp

end VG.Proof.X448

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 Saved ofs)
open VG.Proof.X448.AArch64.Weak (Index Env invEnv invEnv_eval invEnv_x2)
open VG.Proof.X448.AArch64.Fast

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- The precondition, by name. -/
structure Pre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x1, 56⟩]
  wr : s.wr = [⟨s.gpr .x0, 56⟩, ⟨s.gpr .x2, 8192⟩]
  out_sc : (⟨s.gpr .x0, 56⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩
  scalar_sc : (⟨s.gpr .x1, 56⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩
  sc_fit : (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64

theorem Pre.of (s : State) (h : Proof.X448.x448BaseAArch64.pre s) : VG.Proof.X448.AArch64.Base.Pre s := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- A byte of a region disjoint from the working space is beyond it. -/
theorem far {base p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < n) (hn : n ≤ 2 ^ 64) : 8192 ≤ ofs base (p + BitVec.ofNat 64 i) := by
  refine Nat.le_of_not_lt fun h => hd _ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega) (by omega)) ?_
  simp only [Region.Contains]; simp only [ofs] at h; omega

theorem far_output {base p : Addr} (hd : (⟨p, 56⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < 8192) : 56 ≤ ofs p (off base i) := by
  refine Nat.le_of_not_lt fun h => hd _ ?_ (Offset.contains_base base (d := i) (n := 1) (k := 8192) (by omega) (by omega))
  simp only [Region.Contains]
  change ofs p (off base i) + 1 ≤ 56
  omega

theorem decodeScalar448_lt (kb : List Byte) : Spec.X448.decodeScalar448 kb < 256 ^ 56 := by
  rw [Spec.X448.decodeScalar448, VG.Proof.X448.decodeLittleEndian_eq]
  exact Nat.lt_of_lt_of_le (VG.Proof.X25519.leNum_lt _)
    (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _))

open VG.Proof.Ed448 (Rep baseAff)

theorem correct {sE : State} (hp : VG.Proof.X448.AArch64.Base.Pre sE) :
    WP isa x448Base sE fun s' => (∀ r ∈ preserved, s'.gpr r = sE.gpr r) ∧
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (sE.v r).extractLsb' 0 64) ∧
      Proof.X448.x448BaseAArch64.post sE s' := by
  have hn := hp.sc_fit
  have hw : (⟨sE.gpr .x2, 8192⟩ : Region) ∈ sE.wr := by rw [hp.wr]; simp
  have kr : ∀ q < 56, InRegions (sE.rd ++ sE.wr) (sE.gpr .x1 + BitVec.ofNat 64 q) 1 := fun q hq =>
    ⟨⟨sE.gpr .x1, 56⟩, by rw [hp.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have kd : ∀ q < 56, 8192 ≤ ofs (sE.gpr .x2) (sE.gpr .x1 + BitVec.ofNat 64 q) :=
    fun q hq => VG.Proof.X448.AArch64.Base.far hp.scalar_sc hq (by decide)
  set base := sE.gpr .x2 with hbase
  set kb := Spec.X448.bytesAt sE.mem (sE.gpr .x1) 56
  set k := Spec.X448.decodeScalar448 kb
  unfold x448Base
  refine WP.seq (WP.mono (setup_ok rfl hw hn rfl kr kd) fun s1 R => ?_)
  refine WP.seq (WP.mono (loop_ok (by decide) (s₀ := s1) 56 s1 (by decide) le_rfl (by rw [Nat.sub_self]; exact R.inv))
    fun s2 h2 => ?_)
  refine WP.seq (WP.mono (VG.Proof.X448.AArch64.Base.combine_ok (VG.Proof.X448.AArch64.Base.decodeScalar448_lt kb) h2) fun s3 ⟨f3, r3⟩ => ?_)
  unfold VG.Impl.X448.AArch64.Base.finish
  refine WP.seq (WP.mono (VG.Proof.X448.AArch64.Base.squares_ok f3.scr f3.env) fun s4 ⟨k4, b4, e4⟩ => ?_)
  have hs4 := k4.scr f3.scr
  refine WP.seq (WP.mono (VG.Proof.X448.AArch64.Fast.invert_ok hs4 b4) fun s5 ⟨k5, b5, e5⟩ => ?_)
  have hs5 : Scr s5 base := hs4.of_keeps k5.regs (by decide)
  simp only [List.cons_append]
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.moveOutput_ok s5) fun s6 ⟨x16, m6, k6⟩ => ?_
  have hs6 : Scr s6 base := hs5.of_keeps k6 (by decide)
  -- The working space outside the slots and the products' working space, from `s1` on.
  have o15 : Outside2 base 64 2816 ACC 1152 s1.mem s5.mem := (f3.mem.trans k4.mem).trans k5.mem
  have o16 : Outside2 base 64 2816 ACC 1152 s1.mem s6.mem := by rw [m6]; exact o15
  have out6 : s6.gpr .x1 = sE.gpr .x0 := by
    rw [x16, k5.regs.1 _ (by decide), k4.regs.1 _ (by decide), f3.out, R.out]
  have wr6 : s6.wr = sE.wr := by rw [k6.2.2, k5.regs.2.2, k4.regs.2.2, f3.wr, R.wr]
  have hw6 : ∀ j < 56, InRegions s6.wr (off (sE.gpr .x0) j) 1 := fun j hj =>
    ⟨⟨sE.gpr .x0, 56⟩, by rw [wr6, hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have sv6 : VG.Proof.X448.AArch64.Saved base sE.gpr s6.mem := R.saved.outside2 o16 (by decide) (by decide)
  have svx6 : SavedX base sE.gpr s6.mem := R.savedX.outside2 o16 (by decide) (by decide)
  have svV6 : SavedV base sE.v s6.mem := R.savedV.outside2 o16 (by decide) (by decide)
  refine WP.mono (VG.Proof.X448.AArch64.Fast.finish_ok hs6 (by rw [m6]; exact b5) out6 hw6 (fun j hj => VG.Proof.X448.AArch64.Base.far_output hp.out_sc hj)
    sv6 svx6 svV6) fun s' ⟨rb, x20, rx, rv, kf, _, result⟩ => ⟨?_, ?_, ?_⟩
  · intro r hr
    have lr : s'.gpr .x30 = sE.gpr .x30 := by
      rw [kf.1 _ (by decide), k6.1 _ (by decide), k5.regs.1 _ (by decide), k4.regs.1 _ (by decide),
        f3.lr, R.lr]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rb
    · exact x20
    · exact rx 0 (by decide)
    · exact rx 1 (by decide)
    · exact rx 2 (by decide)
    · exact rx 3 (by decide)
    · exact rx 4 (by decide)
    · exact rx 5 (by decide)
    · exact rx 6 (by decide)
    · exact rx 7 (by decide)
    · exact lr
  · intro r hr
    simp only [preservedV, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rv 0 (by decide)
    · exact rv 1 (by decide)
    · exact rv 2 (by decide)
    · exact rv 3 (by decide)
    · exact rv 4 (by decide)
    · exact rv 5 (by decide)
    · exact rv 6 (by decide)
    · exact rv 7 (by decide)
  · change Spec.X448.bytesAt s'.mem (sE.gpr .x0) 56 = _
    rw [result, m6, e5, VG.Proof.X448.AArch64.Weak.invEnv_x2, VG.Proof.X448.AArch64.Weak.invEnv_eval, e4]
    refine (VG.Proof.X448.Edwards.x448_basePoint kb _ ?_).symm
    have hu := VG.Proof.X448.u_rep r3
    rw [natCast_zsmul] at hu
    rw [← hu, VG.Proof.X448.invert_eq]
    rfl

end VG.Proof.X448.AArch64.Base

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Base.Verified`. -/
section

/-!
# X448 of the base point on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Constant time (by taint
tracking: the only branches are on the counters, every address is an argument
plus a constant or a counter, and the digits' masks only select; checked on the code
without its immediates, `Base/Erase.lean`), and the
shared contract of `Spec/`.
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64

theorem x448Base_ct : ConstantTime isa Proof.X448.x448BaseAArch64.pre Proof.X448.x448BaseAArch64.pub
    Impl.X448.AArch64.Base.x448Base := by
  refine Taint.constantTime_eraseImm_of_eq (Taint.ofRegs [.x0, .x1, .x2]) ?_ VG.Proof.X448.AArch64.Base.x448Base_eraseImm
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 56⟩]
  wr := [⟨0x1000, 56⟩, ⟨0x4000, 8192⟩]

theorem x448Base_ok (s : State) (hs : Proof.X448.x448BaseAArch64.pre s) :
    ∃ t s', Exec isa Impl.X448.AArch64.Base.x448Base s t s' ∧ abiPreserved s s' ∧
      Proof.X448.x448BaseAArch64.post s s' := by
  obtain ⟨t, s', he, h⟩ := VG.Proof.X448.AArch64.Base.correct (Pre.of s hs)
  exact ⟨t, s', he, ⟨h.1, Exec.sp he, h.2.1⟩, h.2.2⟩

theorem x448Base_verified :
    Verified AArch64.target Impl.X448.AArch64.Base.x448Base (Spec.X448.x448BaseContract AArch64.abi) :=
  Verified.of_correct VG.Proof.X448.AArch64.Base.x448Base_ok VG.Proof.X448.AArch64.Base.x448Base_ct (by
    sig_implies [Spec.X448.x448BaseContract, Spec.X448.x448BaseSig, AArch64.abi, AArch64.argRegs,
      Proof.X448.x448BaseAArch64] [satState] using VG.Proof.X448.AArch64.Base.satState)

end VG.Proof.X448.AArch64.Base

end
