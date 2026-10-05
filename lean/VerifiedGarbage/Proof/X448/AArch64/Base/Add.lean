import VerifiedGarbage.Impl.X448.AArch64.Base
import VerifiedGarbage.Proof.X448.AArch64.Fast.Phases
import VerifiedGarbage.Proof.X448.AArch64.Fast.StepOps
import VerifiedGarbage.Proof.X448.AArch64.Base.AddDefs

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
